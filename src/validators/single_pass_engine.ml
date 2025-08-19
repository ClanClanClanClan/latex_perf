(* SINGLE-PASS VALIDATOR ENGINE - ULTRA-OPTIMIZED *)
(* Based on expert recommendations for O(n) validation with per-kind dispatch *)

open Bigarray

(* Token kinds are densely numbered 0..K-1 for dispatch *)
type token_kind = int

(* Token kind constants - map catcodes and special tokens *)
let kind_escape = 0
let kind_begin_group = 1
let kind_end_group = 2
let kind_math_shift = 3
let kind_align_tab = 4
let kind_end_line = 5
let kind_param = 6
let kind_superscript = 7
let kind_subscript = 8
let kind_ignored = 9
let kind_space = 10
let kind_letter = 11
let kind_other = 12
let kind_active = 13
let kind_comment = 14
let kind_invalid = 15
let kind_macro = 16
let kind_group_open = 17
let kind_group_close = 18
let kind_eof = 19
let kind_count = 20

(* Minimal per-token read API over SoA *)
module SoA = struct
  type t = {
    kinds   : (int32, int32_elt, c_layout) Array1.t;
    codes   : (int32, int32_elt, c_layout) Array1.t;  (* Unicode codepoints *)
    start   : (int32, int32_elt, c_layout) Array1.t;  (* Byte offsets *)
    lines   : (int32, int32_elt, c_layout) Array1.t;  (* Line numbers *)
    cols    : (int32, int32_elt, c_layout) Array1.t;   (* Column numbers *)
    len     : int;
  }

  let create ~capacity =
    { kinds = Array1.create int32 c_layout capacity;
      codes = Array1.create int32 c_layout capacity;
      start = Array1.create int32 c_layout capacity;
      lines = Array1.create int32 c_layout capacity;
      cols  = Array1.create int32 c_layout capacity;
      len = 0 }

  [@inline] let len s = s.len

  [@inline] let kind  s i = Int32.to_int (Array1.unsafe_get s.kinds i)
  [@inline] let code  s i = Int32.to_int (Array1.unsafe_get s.codes i)
  [@inline] let start s i = Int32.to_int (Array1.unsafe_get s.start i)
  [@inline] let line  s i = Int32.to_int (Array1.unsafe_get s.lines i)
  [@inline] let col   s i = Int32.to_int (Array1.unsafe_get s.cols  i)
end

(* Issue buffer: preallocate & reuse (off-heap) *)
module Issues = struct
  type severity = Error | Warning | Info
  
  type t = {
    rule_ids : (int32, int32_elt, c_layout) Array1.t;  (* Rule ID codes *)
    positions: (int32, int32_elt, c_layout) Array1.t;  (* Token positions *)
    severities: (int32, int32_elt, c_layout) Array1.t; (* Severity levels *)
    mutable n : int; (* count *)
    capacity : int;
  }

  let create ~cap =
    { rule_ids = Array1.create int32 c_layout cap;
      positions = Array1.create int32 c_layout cap;
      severities = Array1.create int32 c_layout cap;
      n = 0;
      capacity = cap }

  [@inline] let clear b = b.n <- 0

  [@inline] let push b ~rule_id ~pos ~severity =
    if b.n < b.capacity then begin
      let i = b.n in
      Array1.unsafe_set b.rule_ids i (Int32.of_int rule_id);
      Array1.unsafe_set b.positions i (Int32.of_int pos);
      Array1.unsafe_set b.severities i (Int32.of_int (match severity with Error -> 0 | Warning -> 1 | Info -> 2));
      b.n <- i + 1
    end
end

(* Token view for validators *)
type token_view = {
  kind  : int;
  code  : int;  (* Unicode codepoint *)
  pos   : int;  (* Token position in stream *)
  line  : int;
  col   : int;
}

type step_fn = Issues.t -> token_view -> int -> SoA.t -> unit
type flush_fn = Issues.t -> unit

type validator = {
  id        : int;
  name      : string;
  interests : int list;    (* list of token kinds this validator cares about *)
  step      : step_fn;     (* called only when kind ∈ interests *)
  flush     : flush_fn;    (* finalize state if needed *)
}

(* Rule ID constants *)
let rule_typo_001 = 1  (* ASCII quotes *)
let rule_typo_002 = 2  (* Double hyphen *)
let rule_typo_003 = 3  (* Triple hyphen *)
let rule_typo_005 = 5  (* Ellipsis *)
let rule_typo_006 = 6  (* Tab character *)
let rule_typo_007 = 7  (* Trailing spaces *)
let rule_delim_001 = 101  (* Unmatched braces *)
let rule_delim_002 = 102  (* Extra closing braces *)
let rule_spc_001 = 201  (* Differential spacing *)
let rule_spc_002 = 202  (* Space before punctuation *)

(* Fused text validators - multiple cheap checks in one function *)
let[@inline] fused_text_typography : step_fn =
  fun issues t i soa ->
    (* TYPO-001: ASCII straight quotes *)
    if t.code = 34 then (* ASCII double-quote *)
      Issues.push issues ~rule_id:rule_typo_001 ~pos:i ~severity:Error;
    
    (* TYPO-006: Tab character *)
    if t.code = 9 then (* Tab *)
      Issues.push issues ~rule_id:rule_typo_006 ~pos:i ~severity:Error;
    
    (* TYPO-002/003: Double/triple hyphen (needs lookahead) *)
    if t.code = 45 && i + 1 < SoA.len soa then begin (* Hyphen *)
      let next_kind = SoA.kind soa (i + 1) in
      let next_code = SoA.code soa (i + 1) in
      if next_kind = kind_other && next_code = 45 then begin
        (* Double hyphen detected *)
        if i + 2 < SoA.len soa then begin
          let next2_kind = SoA.kind soa (i + 2) in
          let next2_code = SoA.code soa (i + 2) in
          if next2_kind = kind_other && next2_code = 45 then
            (* Triple hyphen *)
            Issues.push issues ~rule_id:rule_typo_003 ~pos:i ~severity:Warning
          else
            (* Just double hyphen *)
            Issues.push issues ~rule_id:rule_typo_002 ~pos:i ~severity:Warning
        end else
          Issues.push issues ~rule_id:rule_typo_002 ~pos:i ~severity:Warning
      end
    end;
    
    (* TYPO-005: Three periods (ellipsis) *)
    if t.code = 46 && i + 2 < SoA.len soa then begin (* Period *)
      let n1_kind = SoA.kind soa (i + 1) in
      let n1_code = SoA.code soa (i + 1) in
      let n2_kind = SoA.kind soa (i + 2) in
      let n2_code = SoA.code soa (i + 2) in
      if n1_kind = kind_other && n1_code = 46 &&
         n2_kind = kind_other && n2_code = 46 then
        Issues.push issues ~rule_id:rule_typo_005 ~pos:i ~severity:Warning
    end

(* Fused space validators *)
let[@inline] fused_space_rules : step_fn =
  fun issues t i soa ->
    (* TYPO-007: Trailing spaces before newline *)
    if t.code = 32 && i + 1 < SoA.len soa then begin
      let next_kind = SoA.kind soa (i + 1) in
      if next_kind = kind_end_line then
        Issues.push issues ~rule_id:rule_typo_007 ~pos:i ~severity:Info
    end;
    
    (* SPC-002: Space before punctuation *)
    if t.code = 32 && i + 1 < SoA.len soa then begin
      let next_code = SoA.code soa (i + 1) in
      if next_code = 44 || next_code = 46 || next_code = 59 || next_code = 58 then
        Issues.push issues ~rule_id:rule_spc_002 ~pos:i ~severity:Info
    end

(* Delimiter validator with state *)
let delim_validator =
  let brace_stack = Stack.create () in
  let step : step_fn = fun issues t i soa ->
    if t.code = 123 then (* { *)
      Stack.push i brace_stack
    else if t.code = 125 then begin (* } *)
      if Stack.is_empty brace_stack then
        Issues.push issues ~rule_id:rule_delim_002 ~pos:i ~severity:Error
      else
        ignore (Stack.pop brace_stack)
    end
  in
  let flush : flush_fn = fun issues ->
    (* Report unclosed braces *)
    Stack.iter (fun pos ->
      Issues.push issues ~rule_id:rule_delim_001 ~pos ~severity:Error
    ) brace_stack;
    Stack.clear brace_stack
  in
  { id = 1000;
    name = "delimiter_validator";
    interests = [kind_begin_group; kind_end_group];
    step;
    flush }

(* Build dispatch tables *)
let build_dispatch (validators : validator array) ~(kinds:int) : step_fn list array * flush_fn array =
  let tbl = Array.make kinds [] in
  Array.iter (fun v ->
    List.iter (fun k -> tbl.(k) <- v.step :: tbl.(k)) v.interests
  ) validators;
  let flushers = Array.map (fun v -> v.flush) validators in
  (tbl, flushers)

(* SINGLE-PASS ENGINE - The heart of the optimization *)
let run_single_pass ~(soa:SoA.t) ~(dispatch:step_fn list array) ~(flushers:flush_fn array) (issues:Issues.t) =
  Issues.clear issues;
  
  let n = SoA.len soa in
  for i = 0 to n - 1 do
    let k  = SoA.kind  soa i in
    let c  = SoA.code  soa i in
    let ln = SoA.line  soa i in
    let cl = SoA.col   soa i in
    
    (* Build token view *)
    let token = { kind = k; code = c; pos = i; line = ln; col = cl } in
    
    (* Dispatch to interested validators only *)
    let rec call = function
      | [] -> ()
      | f :: tl -> f issues token i soa; call tl
    in
    call dispatch.(k)
  done;
  
  (* Finalize validators that accumulated state *)
  Array.iter (fun fl -> fl issues) flushers;
  
  issues.n

(* Convert old-style tokens to SoA *)
let tokens_to_soa tokens =
  let n = List.length tokens in
  let soa = SoA.create ~capacity:n in
  let soa_mut = { soa with len = n } in
  
  List.iteri (fun i tok ->
    let open Validator_core_fixed in
    let (kind, code) = match tok.token with
      | TChar (uc, Escape) -> (kind_escape, Uchar.to_int uc)
      | TChar (uc, BeginGroup) -> (kind_begin_group, Uchar.to_int uc)
      | TChar (uc, EndGroup) -> (kind_end_group, Uchar.to_int uc)
      | TChar (uc, MathShift) -> (kind_math_shift, Uchar.to_int uc)
      | TChar (uc, AlignTab) -> (kind_align_tab, Uchar.to_int uc)
      | TChar (uc, EndLine) -> (kind_end_line, Uchar.to_int uc)
      | TChar (uc, Param) -> (kind_param, Uchar.to_int uc)
      | TChar (uc, Superscript) -> (kind_superscript, Uchar.to_int uc)
      | TChar (uc, Subscript) -> (kind_subscript, Uchar.to_int uc)
      | TChar (uc, Ignored) -> (kind_ignored, Uchar.to_int uc)
      | TChar (uc, Space) -> (kind_space, Uchar.to_int uc)
      | TChar (uc, Letter) -> (kind_letter, Uchar.to_int uc)
      | TChar (uc, Other) -> (kind_other, Uchar.to_int uc)
      | TChar (uc, Active) -> (kind_active, Uchar.to_int uc)
      | TChar (uc, Comment) -> (kind_comment, Uchar.to_int uc)
      | TChar (uc, Invalid) -> (kind_invalid, Uchar.to_int uc)
      | TMacro _ -> (kind_macro, 0)
      | TParam _ -> (kind_param, 0)
      | TGroupOpen -> (kind_group_open, 123)
      | TGroupClose -> (kind_group_close, 125)
      | TEOF -> (kind_eof, 0)
    in
    Array1.set soa.kinds i (Int32.of_int kind);
    Array1.set soa.codes i (Int32.of_int code);
    Array1.set soa.start i (Int32.of_int tok.location.offset);
    Array1.set soa.lines i (Int32.of_int tok.location.line);
    Array1.set soa.cols i (Int32.of_int tok.location.column)
  ) tokens;
  
  soa_mut

(* Create optimized validators *)
let create_text_validator () =
  { id = 1;
    name = "fused_text_typography";
    interests = [kind_other; kind_letter];
    step = fused_text_typography;
    flush = (fun _ -> ()) }

let create_space_validator () =
  { id = 2;
    name = "fused_space_rules";
    interests = [kind_space];
    step = fused_space_rules;
    flush = (fun _ -> ()) }

(* Benchmark harness *)
let bench (runs:int) (soa:SoA.t) (validators:validator array) =
  let (dispatch, flushers) = build_dispatch validators ~kinds:kind_count in
  let issues = Issues.create ~cap:65536 in
  let best = ref max_float and worst = ref 0.0 and tot = ref 0.0 in
  for _ = 1 to runs do
    let t0 = Unix.gettimeofday () in
    let count = run_single_pass ~soa ~dispatch ~flushers issues in
    let t1 = Unix.gettimeofday () in
    let dt = (t1 -. t0) *. 1000.0 in
    best := min !best dt; 
    worst := max !worst dt; 
    tot := !tot +. dt;
  done;
  Printf.printf "runs=%d mean=%.3fms best=%.3fms worst=%.3fms tokens=%d\n%!"
    runs (!tot /. float runs) !best !worst (SoA.len soa)

(* High-level API for compatibility *)
let validate_document tokens =
  let soa = tokens_to_soa tokens in
  let validators = [|
    create_text_validator ();
    create_space_validator ();
    delim_validator;
  |] in
  let (dispatch, flushers) = build_dispatch validators ~kinds:kind_count in
  let issues = Issues.create ~cap:65536 in
  let count = run_single_pass ~soa ~dispatch ~flushers issues in
  (count, issues)