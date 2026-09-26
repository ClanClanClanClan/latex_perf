(* The single verdict type and its only renderer. See verdict.mli and ADR-012.

   The rendered text must never contain a bare T-digit token or a token of the
   shape AB-123. diff_real_roots.py scrapes reasons with the regular expression
   \b(T\d|[A-Z]{2,8}-\d{3})\b, and although that script now stops reading at the
   TIER line, the fixed text here stays clean as well. *)

type loc = { file : string; line : int; col : int }

type fatal_reason =
  | E0_no_pdf
  | E1_undefined_cs
  | E2_undefined_env
  | E3_mode_violation
  | E4_double_script
  | E5_stack_discipline
  | E6_par_in_math_or_short_arg
  | E7_missing_argument
  | E8_definer_clash
  | E9_unknown_counter
  | E10_missing_file
  | E11_unicode_undefined
  | E12_configuration_fatal
  | E13_bad_argument
  | E14_capacity_overflow

let all_fatal_reasons =
  [
    E0_no_pdf;
    E1_undefined_cs;
    E2_undefined_env;
    E3_mode_violation;
    E4_double_script;
    E5_stack_discipline;
    E6_par_in_math_or_short_arg;
    E7_missing_argument;
    E8_definer_clash;
    E9_unknown_counter;
    E10_missing_file;
    E11_unicode_undefined;
    E12_configuration_fatal;
    E13_bad_argument;
    E14_capacity_overflow;
  ]

let e_code = function
  | E0_no_pdf -> "E0"
  | E1_undefined_cs -> "E1"
  | E2_undefined_env -> "E2"
  | E3_mode_violation -> "E3"
  | E4_double_script -> "E4"
  | E5_stack_discipline -> "E5"
  | E6_par_in_math_or_short_arg -> "E6"
  | E7_missing_argument -> "E7"
  | E8_definer_clash -> "E8"
  | E9_unknown_counter -> "E9"
  | E10_missing_file -> "E10"
  | E11_unicode_undefined -> "E11"
  | E12_configuration_fatal -> "E12"
  | E13_bad_argument -> "E13"
  | E14_capacity_overflow -> "E14"

type boundary = {
  b_kind : string;
  b_where : string option;
  b_construct : string;
  b_nudge : string;
}

type t =
  | Proven_ready of { contract : string; pin : string; decider : string }
  | Proven_not_ready of {
      reason : fatal_reason;
      message : string;
      loc : loc;
      rule : string;
      probe : string;
      contract : string;
    }
  | Pending of { predicted : [ `Ready | `Not_ready ]; missing : string list }
  | Likely_ok of { basis : string; why_not_strict : boundary list }
  | Likely_fail of {
      reasons : Compile_contract.reason list;
      why_not_strict : boundary list;
    }
  | Foreign of {
      construct : string;
      where : string option;
      why_not_strict : boundary list;
    }

let is_proven = function
  | Proven_ready _ | Proven_not_ready _ -> true
  | Pending _ | Likely_ok _ | Likely_fail _ | Foreign _ -> false

let max_why_not_strict = 3
let require_proof_exit = 4

(* The reserved word is spelled out in exactly one place, this binding. Only
   [proven_kind_and_headline] reads it. *)
let reserved_word = "PROVEN"

let defang s =
  let r = reserved_word and rl = String.length reserved_word in
  let n = String.length s in
  let b = Buffer.create n in
  let i = ref 0 in
  while !i < n do
    if !i + rl <= n && String.sub s !i rl = r then (
      Buffer.add_string b "Proven";
      i := !i + rl)
    else (
      Buffer.add_char b s.[!i];
      incr i)
  done;
  Buffer.contents b

let tier_token = function
  | Proven_ready _ | Proven_not_ready _ -> "proven"
  | Pending _ | Likely_ok _ | Likely_fail _ -> "heuristic"
  | Foreign _ -> "foreign"

let short_hash h = if String.length h > 8 then String.sub h 0 8 else h

(* The only function that may write the reserved word. *)
let proven_kind_and_headline = function
  | Proven_ready { contract; pin; decider } ->
      ( reserved_word ^ "-READY",
        Printf.sprintf "%s READY (decided by %s under contract %s, pin %s)"
          reserved_word decider (short_hash contract) pin )
  | Proven_not_ready { reason; message; loc; rule; probe; contract } ->
      ( reserved_word ^ "-NOT-READY",
        Printf.sprintf
          "%s NOT-READY %s:%d:%d %s [%s, rule %s, probe %s, contract %s]"
          reserved_word loc.file loc.line loc.col message (e_code reason) rule
          probe (short_hash contract) )
  | Pending _ | Likely_ok _ | Likely_fail _ | Foreign _ ->
      invalid_arg "Verdict.proven_kind_and_headline: not a proven verdict"

(* Heuristic kinds and headlines. Nothing here may use [reserved_word]; the
   output is defanged by [render] regardless, so user data cannot smuggle the
   word in either. *)
let heuristic_kind_and_headline = function
  | Pending { predicted; missing } ->
      ( "PENDING",
        Printf.sprintf
          "PENDING (predicted %s; heuristic) — not a proof; awaiting \
           attestation of: %s"
          (match predicted with `Ready -> "READY" | `Not_ready -> "NOT-READY")
          (match missing with
          | [] -> "(nothing listed)"
          | l -> String.concat ", " l) )
  | Likely_ok { basis; _ } ->
      ( "LIKELY-OK",
        Printf.sprintf "LIKELY OK (heuristic; %s) — not a proof" basis )
  | Likely_fail { reasons; _ } ->
      let n = List.length reasons in
      ( "LIKELY-FAIL",
        if n = 0 then
          "LIKELY FAIL (heuristic) — not a proof; the model-connected checks \
           above reject it"
        else
          Printf.sprintf
            "LIKELY FAIL (heuristic) — not a proof; %d blocking reason%s \
             listed above"
            n
            (if n = 1 then "" else "s") )
  | Foreign { construct; where; _ } ->
      ( "FOREIGN",
        Printf.sprintf
          "FOREIGN — %s%s is outside every supported tier (neither the exact \
           tier nor the heuristic tier applies); not a proof"
          construct
          (match where with Some w -> " at " ^ w | None -> "") )
  | Proven_ready _ | Proven_not_ready _ ->
      invalid_arg "Verdict.heuristic_kind_and_headline: proven verdict"

let kind_and_headline v =
  if is_proven v then proven_kind_and_headline v
  else
    let k, h = heuristic_kind_and_headline v in
    (defang k, defang h)

let kind_token v = fst (kind_and_headline v)
let headline v = snd (kind_and_headline v)

let render_boundary (b : boundary) =
  Printf.sprintf "  why not strict: %s%s — %s" b.b_construct
    (match b.b_where with Some w -> " at " ^ w | None -> "")
    b.b_nudge

let why_not_strict = function
  | Likely_ok { why_not_strict; _ }
  | Likely_fail { why_not_strict; _ }
  | Foreign { why_not_strict; _ } ->
      why_not_strict
  | Pending _ | Proven_ready _ | Proven_not_ready _ -> []

let render v =
  let kind, head = kind_and_headline v in
  let first = String.concat "\t" [ "TIER"; tier_token v; kind; head ] in
  if is_proven v then [ first ]
  else
    let rec take k = function
      | [] -> []
      | _ when k = 0 -> []
      | x :: r -> x :: take (k - 1) r
    in
    first
    :: List.map
         (fun b -> defang (render_boundary b))
         (take max_why_not_strict (why_not_strict v))

let m0_boundary =
  {
    b_kind = "strict_unavailable";
    b_where = None;
    b_construct = "strict tier not yet available (M0)";
    b_nudge =
      "no document is decided by proof yet; the first exact verdicts arrive \
       with the Coq kernel in milestones M2 and M3 \
       (docs/v27/STRICT_TIER_DESIGN.md)";
  }
