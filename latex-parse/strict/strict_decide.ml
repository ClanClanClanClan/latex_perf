(* strict_decide — run the EXTRACTED L_S0 kernel on documents given as trees.

   ADR-012, milestone M2 phase 1. This executable is the harness side of the
   generated differential (scripts/tools/strict_differential.py) and of the
   signature generator (scripts/tools/gen_strict_signatures.py). It is NOT
   linked into the product: the CLI's strict tier stays a stub in phase 1.

   What is proved and what is not. [Strict_kernel_extracted.decide] and
   [Strict_kernel_extracted.render] are the extracted Coq functions the theorems
   are about (proofs/Strict). Everything in THIS file is trusted harness code
   (design §G.2 T5): it builds the contract record from the committed JSON files
   and reads and writes JSON.

   Usage: strict_decide.exe --kernel K.json --contract C.json [--signatures
   S.json] reads one JSON object per line on stdin, {"id": _, "doc": {"body":
   [node...], "has_end": bool}}, and writes one JSON object per line: the
   verdict, the reason and token index of a fatal, the rendered document (the
   exact bytes to give pdflatex) and the line of the fatal's token in it.

   Node encoding: ["text", "abc"] | ["space"] | ["par", explicit] | ["group",
   [..]] | ["stray"] | ["math", "dollar"|"display"|"paren"|"bracket", [..]] |
   ["script", up, node] | ["cmd", "name"]. *)

module K = Strict_kernel_extracted

let die fmt =
  Printf.ksprintf
    (fun s ->
      prerr_endline s;
      exit 2)
    fmt

let chars_of_string s = List.init (String.length s) (String.get s)

let string_of_chars l =
  let b = Buffer.create 64 in
  List.iter (Buffer.add_char b) l;
  Buffer.contents b

(* ---- the contract record (trusted loader, T5) ---------------------------- *)

let load_json path =
  try Yojson.Safe.from_file path
  with e ->
    die "strict_decide: cannot read %s: %s" path (Printexc.to_string e)

let member k = function
  | `Assoc l -> ( try List.assoc k l with Not_found -> `Null)
  | _ -> `Null

(* Closed world at body start: the kernel's format-state names, updated by the
   configuration's defined_names (kind Undefined = removed by the
   configuration). *)
let load_members kernel_path contract_path =
  let kernel = load_json kernel_path in
  let contract = load_json contract_path in
  (match member "complete" kernel with
  | `Bool true -> ()
  | _ -> die "strict_decide: kernel %s is not complete" kernel_path);
  (match member "complete" contract with
  | `Bool true -> ()
  | _ -> die "strict_decide: contract %s is not complete" contract_path);
  let tbl = Hashtbl.create 40000 in
  (match member "names" kernel with
  | `Assoc l -> List.iter (fun (n, _) -> Hashtbl.replace tbl n ()) l
  | _ -> die "strict_decide: kernel has no names");
  (match member "defined_names" contract with
  | `Assoc l ->
      List.iter
        (fun (n, v) ->
          match member "kind" v with
          | `String "Undefined" -> Hashtbl.remove tbl n
          | _ -> Hashtbl.replace tbl n ())
        l
  | _ -> die "strict_decide: contract has no defined_names");
  tbl

let reason_of_string = function
  | "E0" -> K.E0
  | "E1" -> K.E1
  | "E3" -> K.E3
  | "E4" -> K.E4
  | "E5" -> K.E5
  | "E6" -> K.E6
  | s -> die "strict_decide: unknown reason %S" s

let string_of_reason = function
  | K.E0 -> "E0"
  | K.E1 -> "E1"
  | K.E3 -> "E3"
  | K.E4 -> "E4"
  | K.E5 -> "E5"
  | K.E6 -> "E6"

let text_beh_of = function
  | `String "material" -> K.TxMaterial
  | `String "noop" -> K.TxNoop
  | `List [ `String "fatal"; `String r ] -> K.TxFatal (reason_of_string r)
  | _ -> die "strict_decide: bad text behaviour in signatures"

let math_beh_of = function
  | `String "noad" -> K.MxNoad
  | `String "noop" -> K.MxNoop
  | `List [ `String "fatal"; `String r ] -> K.MxFatal (reason_of_string r)
  | _ -> die "strict_decide: bad math behaviour in signatures"

(* The signature file names the kernel and contract it was generated from by
   their own content keys (the kernel's [meanings_sha256], the contract's
   [config_key]); the Python callers also compare whole-file sha256. *)
let content_key path field =
  match member field (load_json path) with
  | `String s -> s
  | _ -> die "strict_decide: %s has no %s" path field

let load_signatures path members ~kernel_key ~contract_key =
  let tbl = Hashtbl.create 512 in
  (match path with
  | None -> ()
  | Some p -> (
      let j = load_json p in
      let src = member "source" j in
      (match
         (member "kernel_meanings_sha256" src, member "contract_config_key" src)
       with
      | `String k, `String c when k = kernel_key && c = contract_key -> ()
      | _ ->
          die
            "strict_decide: %s was generated from other kernel/contract files \
             than the ones given"
            p);
      match member "signatures" j with
      | `Assoc l ->
          List.iter
            (fun (n, v) ->
              (* contract_wf: a signature only for a defined name *)
              if not (Hashtbl.mem members n) then
                die "strict_decide: signature for undefined name %S" n;
              Hashtbl.replace tbl n
                {
                  K.sig_text = text_beh_of (member "text" v);
                  K.sig_math = math_beh_of (member "math" v);
                })
            l
      | _ -> die "strict_decide: %s has no signatures" p));
  tbl

(* ---- documents ----------------------------------------------------------- *)

let rec node_of = function
  | `List [ `String "text"; `String w ] -> K.NText (chars_of_string w)
  | `List [ `String "space" ] -> K.NSpace
  | `List [ `String "par"; `Bool e ] -> K.NPar e
  | `List [ `String "group"; `List b ] -> K.NGroup (List.map node_of b)
  | `List [ `String "stray" ] -> K.NStrayClose
  | `List [ `String "math"; `String k; `List b ] ->
      let k =
        match k with
        | "dollar" -> K.MkDollar
        | "display" -> K.MkDisplayDollar
        | "paren" -> K.MkParen
        | "bracket" -> K.MkBracket
        | _ -> failwith ("bad math kind " ^ k)
      in
      K.NMath (k, List.map node_of b)
  | `List [ `String "script"; `Bool up; a ] -> K.NScript (up, node_of a)
  | `List [ `String "cmd"; `String n ] -> K.NCmd (chars_of_string n)
  | j -> failwith ("bad node " ^ Yojson.Safe.to_string j)

let doc_of j =
  let body =
    match member "body" j with
    | `List b -> List.map node_of b
    | _ -> failwith "doc without body"
  in
  let has_end =
    match member "has_end" j with
    | `Bool b -> b
    | _ -> failwith "doc without has_end"
  in
  { K.d_body = body; K.d_has_end = has_end }

(* A raw token stream (for probes of [Runs] rules that no node tree reaches;
   e.g. a lone [$] ending a display at end of file). *)
let tok_of = function
  | `List [ `String "char"; `String c ] when String.length c = 1 ->
      K.TChar c.[0]
  | `List [ `String "space" ] -> K.TSpace
  | `List [ `String "par"; `Bool e ] -> K.TPar e
  | `List [ `String "open" ] -> K.TOpen
  | `List [ `String "close" ] -> K.TClose
  | `List [ `String "dollar" ] -> K.TDollar
  | `List [ `String "open_paren" ] -> K.TMOpenInline
  | `List [ `String "close_paren" ] -> K.TMCloseInline
  | `List [ `String "open_bracket" ] -> K.TMOpenDisplay
  | `List [ `String "close_bracket" ] -> K.TMCloseDisplay
  | `List [ `String "sup" ] -> K.TScript true
  | `List [ `String "sub" ] -> K.TScript false
  | `List [ `String "cs"; `String n ] -> K.TCs (chars_of_string n)
  | `List [ `String "end" ] -> K.TEnd
  | j -> failwith ("bad token " ^ Yojson.Safe.to_string j)

let tok_name = function
  | K.TChar _ -> "char"
  | K.TSpace -> "space"
  | K.TPar false -> "blank_line"
  | K.TPar true -> "par"
  | K.TOpen -> "open"
  | K.TClose -> "close"
  | K.TDollar -> "dollar"
  | K.TMOpenInline -> "open_paren"
  | K.TMCloseInline -> "close_paren"
  | K.TMOpenDisplay -> "open_bracket"
  | K.TMCloseDisplay -> "close_bracket"
  | K.TScript true -> "sup"
  | K.TScript false -> "sub"
  | K.TCs _ -> "cs"
  | K.TEnd -> "end"

let rec take n = function x :: r when n > 0 -> x :: take (n - 1) r | _ -> []

(* The line pdfTeX reports for the token at index [i]: the line holding its
   first byte, except that a blank-line paragraph break is reported on the first
   line that is blank, which is the current line when everything on it so far is
   spaces (Syntax.v, rendering rule). *)
let line_of_token toks i =
  let prefix = string_of_chars (K.header @ K.render_toks (take i toks)) in
  let nls = ref 0 in
  String.iter (fun c -> if c = '\n' then incr nls) prefix;
  let line = !nls + 1 in
  match List.nth_opt toks i with
  | Some (K.TPar false) ->
      let start =
        match String.rindex_opt prefix '\n' with Some k -> k + 1 | None -> 0
      in
      let cur = String.sub prefix start (String.length prefix - start) in
      if String.for_all (fun c -> c = ' ') cur then line else line + 1
  | _ -> line

(* The [Runs] constructor each step of the extracted run corresponds to, for
   COVERAGE REPORTING ONLY (which rules a document exercised; the probe families
   of Semantics.v are keyed by these names). It never feeds a verdict: a
   mislabel here can only misstate coverage. *)
let rule_of c s t nx res =
  let fs = s.K.s_frames in
  let math = K.in_math fs in
  let head = match fs with f :: _ -> Some f | [] -> None in
  match (t, res) with
  | K.TEnd, K.Stop K.Compiles -> "R_end_ok"
  | K.TEnd, K.Stop (K.Fatal (K.E0, _)) -> "R_end_empty"
  | K.TEnd, _ -> "R_end_math"
  | K.TChar _, _ -> if math then "R_char_math" else "R_char_text"
  | K.TSpace, _ -> "R_space"
  | K.TPar _, _ -> if math then "R_par_math" else "R_par_text"
  | K.TOpen, _ -> if math then "R_open_math" else "R_open_text"
  | K.TClose, _ -> (
      match head with
      | Some K.FSimple -> "R_close_simple"
      | Some (K.FMGroup _) -> "R_close_group"
      | Some (K.FShift _) -> "R_close_shift"
      | None -> "R_close_top")
  | K.TDollar, _ -> (
      match (head, nx) with
      | Some (K.FShift (false, _, _)), _ -> "R_dollar_inline_close"
      | Some (K.FShift (true, _, _)), Some K.TDollar -> "R_dollar_display_close"
      | Some (K.FShift (true, _, _)), Some (K.TCs n) when not (c.K.c_defined n)
        ->
          "R_dollar_display_undef"
      | Some (K.FShift (true, _, _)), None -> "R_dollar_display_eof"
      | Some (K.FShift (true, _, _)), _ -> "R_dollar_display_bad"
      | Some (K.FMGroup _), _ -> "R_dollar_group"
      | _, Some K.TDollar -> "R_dollar_display_open"
      | _, _ -> "R_dollar_inline_open")
  | K.TMOpenInline, _ -> if math then "R_mopen_inline_bad" else "R_mopen_inline"
  | K.TMCloseInline, _ -> (
      match head with
      | Some (K.FShift (false, _, _)) -> "R_mclose_inline"
      | _ -> "R_mclose_inline_bad")
  | K.TMOpenDisplay, _ ->
      if math then "R_mopen_display_bad" else "R_mopen_display"
  | K.TMCloseDisplay, _ -> (
      match head with
      | Some (K.FShift (true, _, _)) -> "R_mclose_display"
      | _ -> "R_mclose_display_bad")
  | K.TScript up, _ -> (
      if not math then "R_script_text"
      else if K.tail_has up fs then "R_script_double"
      else
        match nx with
        | Some (K.TChar _) -> "R_script_char"
        | Some K.TOpen -> "R_script_group"
        | _ -> "stuck")
  | K.TCs n, _ -> (
      if not (c.K.c_defined n) then "R_cs_undefined"
      else
        match c.K.c_sig n with
        | None -> "stuck"
        | Some sg -> (
            if math then
              match sg.K.sig_math with
              | K.MxNoad -> "R_cs_math_noad"
              | K.MxNoop -> "R_cs_math_noop"
              | K.MxFatal _ -> "R_cs_math_fatal"
            else
              match sg.K.sig_text with
              | K.TxMaterial -> "R_cs_text_material"
              | K.TxNoop -> "R_cs_text_noop"
              | K.TxFatal _ -> "R_cs_text_fatal"))

(* The BRANCH each step took, for COVERAGE REPORTING ONLY (like [rule_of]):
   "<head>|<token>|<follower>|<tail>", where <head> is the innermost frame (top,
   simple, inline, display, mgroup), <token> the token's class (a control word
   by its behaviour in the current mode: cs:undef, cs:t.<text behaviour>,
   cs:m.<math behaviour>), <follower> the class of the NEXT token for the tokens
   whose step reads it ($, ^, _; a control word by its whole signature,
   cs:<text>/<math>; eof at the end of the stream) and "-" otherwise, and <tail>
   whether the tail noad already has the script (^ and _ only).
   check_strict_kernel.py requires every cell of this matrix that the grammar
   allows to be exercised by an agreeing rule probe (C-85: the follower of a
   look-ahead was the class nobody had probed). *)
let head_label = function
  | [] -> "top"
  | K.FSimple :: _ -> "simple"
  | K.FShift (false, _, _) :: _ -> "inline"
  | K.FShift (true, _, _) :: _ -> "display"
  | K.FMGroup _ :: _ -> "mgroup"

let text_cls = function
  | K.TxMaterial -> "material"
  | K.TxNoop -> "noop"
  | K.TxFatal r -> "fatal." ^ string_of_reason r

let math_cls = function
  | K.MxNoad -> "noad"
  | K.MxNoop -> "noop"
  | K.MxFatal r -> "fatal." ^ string_of_reason r

let cs_label c math n =
  if not (c.K.c_defined n) then "cs:undef"
  else
    match c.K.c_sig n with
    | None -> "cs:nosig"
    | Some sg ->
        if math then "cs:m." ^ math_cls sg.K.sig_math
        else "cs:t." ^ text_cls sg.K.sig_text

let follower_label c = function
  | None -> "eof"
  | Some (K.TCs n) -> (
      if not (c.K.c_defined n) then "cs:undef"
      else
        match c.K.c_sig n with
        | None -> "cs:nosig"
        | Some sg ->
            "cs:" ^ text_cls sg.K.sig_text ^ "/" ^ math_cls sg.K.sig_math)
  | Some t -> tok_name t

let branch_of c s t nx =
  let fs = s.K.s_frames in
  let math = K.in_math fs in
  let tok = match t with K.TCs n -> cs_label c math n | _ -> tok_name t in
  let reads_next =
    match t with K.TDollar | K.TScript _ -> true | _ -> false
  in
  let tail =
    match t with
    | K.TScript up -> if K.tail_has up fs then "tail+" else "tail-"
    | _ -> "-"
  in
  String.concat "|"
    [
      head_label fs;
      tok;
      (if reads_next then follower_label c nx else "-");
      tail;
    ]

let rules_used c toks =
  let acc = ref [] and br = ref [] in
  let add r = if not (List.mem r !acc) then acc := r :: !acc in
  let addb b = if not (List.mem b !br) then br := b :: !br in
  let rec walk s = function
    | [] -> add "R_eof"
    | t :: rest -> (
        let nx = match rest with x :: _ -> Some x | [] -> None in
        let res = K.step c s t nx in
        add (rule_of c s t nx res);
        addb (branch_of c s t nx);
        match res with
        | K.Go1 s' -> walk s' rest
        | K.Go2 s' -> ( match rest with _ :: r -> walk s' r | [] -> ())
        | K.Stop _ | K.Stuck -> ())
  in
  walk K.init toks;
  (List.rev !acc, List.rev !br)

(* A token prefix completed by the frames the EXTRACTED run has open at its end,
   innermost first, then [\end{document}] (request field "close": true; the rule
   probes' branch matrix). If the run stops or leaves the tier inside the
   prefix, only [\end{document}] is appended. The closer is computed from the
   model's own state, so a model that is wrong about the state closes the wrong
   frames and the oracle disagrees. *)
let close_toks c toks =
  let rec walk s = function
    | [] -> Some s
    | t :: rest -> (
        match
          K.step c s t (match rest with x :: _ -> Some x | [] -> None)
        with
        | K.Go1 s' -> walk s' rest
        | K.Go2 s' -> ( match rest with _ :: r -> walk s' r | [] -> None)
        | K.Stop _ | K.Stuck -> None)
  in
  let closer = function
    | K.FSimple | K.FMGroup _ -> K.TClose
    | K.FShift (false, _, _) -> K.TMCloseInline
    | K.FShift (true, _, _) -> K.TMCloseDisplay
  in
  match walk K.init toks with
  | Some s -> toks @ List.map closer s.K.s_frames @ [ K.TEnd ]
  | None -> toks @ [ K.TEnd ]

(* The mode in force when the fatal at token [l] is raised: the state the
   extracted [step] reaches when it stops (trusted harness use of extracted
   code; the differential's message check needs it, because pdfTeX words a
   text-mode and a math-mode violation differently). *)
let mode_at c toks =
  let rec walk s = function
    | [] -> s
    | t :: rest -> (
        match
          K.step c s t (match rest with x :: _ -> Some x | [] -> None)
        with
        | K.Go1 s' -> walk s' rest
        | K.Go2 s' -> ( match rest with _ :: r -> walk s' r | [] -> s)
        | K.Stop _ | K.Stuck -> s)
  in
  if K.in_math (walk K.init toks).K.s_frames then "math" else "text"

(* The tree mode of phase 1: JSON lines of trees or token streams. *)
let tree_mode ~kernel ~contract ~sigs =
  let members = load_members kernel contract in
  let sg =
    load_signatures sigs members
      ~kernel_key:(content_key kernel "meanings_sha256")
      ~contract_key:(content_key contract "config_key")
  in
  (* A request may carry "signatures": {name: {text, math}}, a HYPOTHESIS for
     this request only (gen_strict_signatures.py asks what the kernel predicts
     under each candidate signature). They override the file's for that request,
     and contract_wf is checked for them too. *)
  let contract_for extra =
    let local = Hashtbl.create 8 in
    (match extra with
    | `Assoc l ->
        List.iter
          (fun (n, v) ->
            if not (Hashtbl.mem members n) then
              failwith ("signature for undefined name " ^ n);
            Hashtbl.replace local n
              {
                K.sig_text = text_beh_of (member "text" v);
                K.sig_math = math_beh_of (member "math" v);
              })
          l
    | _ -> ());
    {
      K.c_defined = (fun n -> Hashtbl.mem members (string_of_chars n));
      K.c_sig =
        (fun n ->
          let n = string_of_chars n in
          match Hashtbl.find_opt local n with
          | Some x -> Some x
          | None -> Hashtbl.find_opt sg n);
    }
  in
  try
    while true do
      let line = input_line stdin in
      if String.trim line <> "" then
        let j = Yojson.Safe.from_string line in
        let id = member "id" j in
        let out =
          try
            let c = contract_for (member "signatures" j) in
            (* A document goes through [decide] (membership, then the run); a
               raw token stream through [run] from [init] directly: by
               run_sound/run_complete that IS the relation [Runs]. *)
            let toks, tex, strict, verdict =
              match member "toks" j with
              | `List ts ->
                  let toks = List.map tok_of ts in
                  let toks =
                    match member "close" j with
                    | `Bool true -> close_toks c toks
                    | _ -> toks
                  in
                  (* Token-level requests pass the same membership as documents:
                     [in_strict_toks] (every token admitted, every script with
                     its argument) and the capacity bounds ([bounded],
                     Decide.v). The extracted [tok_ok], [scripts_ok] and
                     [bounded] are the functions [in_strict_b] is made of. *)
                  let strict =
                    List.for_all (fun t -> K.tok_ok c t) toks
                    && K.scripts_ok toks
                    && K.bounded toks
                  in
                  ( toks,
                    string_of_chars (K.header @ K.render_toks toks),
                    strict,
                    if strict then K.verdict_of (K.run c K.init toks)
                    else K.NotStrict )
              | _ ->
                  let d = doc_of (member "doc" j) in
                  ( K.flatten_doc d,
                    string_of_chars (K.render d),
                    K.in_strict_b c d,
                    K.decide c d )
            in
            let ntoks = List.length toks in
            let rules, branches = rules_used c toks in
            let base =
              [
                ("id", id);
                ("tex", `String tex);
                ("ntoks", `Int ntoks);
                ("in_strict", `Bool strict);
                ("rules", `List (List.map (fun r -> `String r) rules));
                ("branches", `List (List.map (fun b -> `String b) branches));
              ]
            in
            match verdict with
            | K.ProvenReady -> `Assoc (base @ [ ("verdict", `String "ready") ])
            | K.ProvenNotReady (r, l) ->
                let tok =
                  match List.nth_opt toks l with
                  | Some t -> `String (tok_name t)
                  | None -> `String "eof"
                in
                let line =
                  if l >= ntoks then `Null else `Int (line_of_token toks l)
                in
                `Assoc
                  (base
                  @ [
                      ("verdict", `String "not_ready");
                      ("reason", `String (string_of_reason r));
                      ("loc", `Int l);
                      ("loc_tok", tok);
                      ("loc_line", line);
                      ("loc_mode", `String (mode_at c toks));
                    ])
            | K.NotStrict ->
                `Assoc (base @ [ ("verdict", `String "not_strict") ])
          with Failure m -> `Assoc [ ("id", id); ("error", `String m) ]
        in
        print_endline (Yojson.Safe.to_string out)
    done
  with End_of_file -> ()

(* ======================================================================== *)
(* M2 phase 2: the decision on BYTES                                         *)
(* ======================================================================== *)

(* [Strict_bytes_extracted.decide_bytes] is the extracted Coq decider on bytes
   (proofs/Strict/DecideBytes.v, decide_bytes_exact); [lex] and [parse] its
   reader and parser (Lexer.v lex_exact, Front.v parse_exact). What follows is
   trusted harness code (design §G.2 T5 and T9): the loader of the lexical
   contract, the conversion of the extracted module's types to the phase-1
   module's (the same Coq inductives, extracted twice) for COVERAGE REPORTING,
   and the labelling of the reader's rules, also for coverage reporting only. *)

module B = Strict_bytes_extracted

let b_reason = function
  | K.E0 -> B.E0
  | K.E1 -> B.E1
  | K.E3 -> B.E3
  | K.E4 -> B.E4
  | K.E5 -> B.E5
  | K.E6 -> B.E6

let k_reason = function
  | B.E0 -> K.E0
  | B.E1 -> K.E1
  | B.E3 -> K.E3
  | B.E4 -> K.E4
  | B.E5 -> K.E5
  | B.E6 -> K.E6

let b_sig (s : K.signature) : B.signature =
  {
    B.sig_text =
      (match s.K.sig_text with
      | K.TxMaterial -> B.TxMaterial
      | K.TxNoop -> B.TxNoop
      | K.TxFatal r -> B.TxFatal (b_reason r));
    B.sig_math =
      (match s.K.sig_math with
      | K.MxNoad -> B.MxNoad
      | K.MxNoop -> B.MxNoop
      | K.MxFatal r -> B.MxFatal (b_reason r));
  }

let k_tok = function
  | B.TChar c -> K.TChar c
  | B.TSpace -> K.TSpace
  | B.TPar e -> K.TPar e
  | B.TOpen -> K.TOpen
  | B.TClose -> K.TClose
  | B.TDollar -> K.TDollar
  | B.TMOpenInline -> K.TMOpenInline
  | B.TMCloseInline -> K.TMCloseInline
  | B.TMOpenDisplay -> K.TMOpenDisplay
  | B.TMCloseDisplay -> K.TMCloseDisplay
  | B.TScript u -> K.TScript u
  | B.TCs n -> K.TCs n
  | B.TEnd -> K.TEnd

let cat_of_int = function
  | 0 -> B.CEscape
  | 1 -> B.CBgroup
  | 2 -> B.CEgroup
  | 3 -> B.CMath
  | 4 -> B.CAlign
  | 5 -> B.CEol
  | 6 -> B.CParam
  | 7 -> B.CSup
  | 8 -> B.CSub
  | 9 -> B.CIgnored
  | 10 -> B.CSpacer
  | 11 -> B.CLetter
  | 12 -> B.COther
  | 13 -> B.CActive
  | 14 -> B.CComment
  | 15 -> B.CInvalid
  | n -> die "strict_decide: catcode %d out of range" n

let cat_name = function
  | B.CEscape -> "escape"
  | B.CBgroup -> "bgroup"
  | B.CEgroup -> "egroup"
  | B.CMath -> "math"
  | B.CAlign -> "align"
  | B.CEol -> "eol"
  | B.CParam -> "param"
  | B.CSup -> "sup"
  | B.CSub -> "sub"
  | B.CIgnored -> "ignored"
  | B.CSpacer -> "spacer"
  | B.CLetter -> "letter"
  | B.COther -> "other"
  | B.CActive -> "active"
  | B.CComment -> "comment"
  | B.CInvalid -> "invalid"

(* The lexical contract (corpora/contracts/strict/article-s0-lexical.json,
   written by scripts/tools/gen_strict_lexical.py from the pinned image). *)
let load_lexcon path ~kernel_key ~contract_key =
  let j = load_json path in
  let src = member "source" j in
  (match
     (member "kernel_meanings_sha256" src, member "contract_config_key" src)
   with
  | `String k, `String c when k = kernel_key && c = contract_key -> ()
  | _ ->
      die
        "strict_decide: %s was generated from other kernel/contract files than \
         the ones given"
        path);
  let cats =
    match member "catcodes" j with
    | `List l when List.length l = 256 ->
        Array.of_list
          (List.map
             (function
               | `Int n -> cat_of_int n
               | _ -> die "strict_decide: bad catcode in %s" path)
             l)
    | _ -> die "strict_decide: %s has no 256 catcodes" path
  in
  let endline =
    match member "endlinechar" j with
    | `Int n when n >= 0 && n <= 255 -> Some (Char.chr n)
    | `Int _ -> None
    | _ -> die "strict_decide: %s has no endlinechar" path
  in
  let st = member "structural" j in
  let str k =
    match member k st with
    | `String s when s <> "" -> s
    | _ -> die "strict_decide: %s: structural.%s missing" path k
  in
  let delim k =
    match member k (member "math_delimiters" st) with
    | `String s when String.length s = 1 -> s.[0]
    | _ -> die "strict_decide: %s: math_delimiters.%s missing" path k
  in
  {
    B.lx_cat = (fun c -> cats.(Char.code c));
    B.lx_endline = endline;
    B.lx_par = chars_of_string (str "par");
    B.lx_end = chars_of_string (str "end");
    B.lx_begin = chars_of_string (str "begin");
    B.lx_docclass = chars_of_string (str "documentclass");
    B.lx_class = chars_of_string (str "class");
    B.lx_docenv = chars_of_string (str "document_env");
    B.lx_mopen_inline = delim "open_inline";
    B.lx_mclose_inline = delim "close_inline";
    B.lx_mopen_display = delim "open_display";
    B.lx_mclose_display = delim "close_display";
  }

let why_name = function
  | B.WTooBig -> "file too large"
  | B.WLexBad B.BadCat -> "character of a category outside the fragment"
  | B.WLexBad B.BadHatHat -> "^^ notation"
  | B.WLexBad B.BadNullCs -> "escape character at the end of a line"
  | B.WLexBad B.BadLongLine -> "line too long"
  | B.WLexBad B.BadFirstLine ->
      "first line starts with %& (TeX Live loads the format it names)"
  | B.WPrologue ->
      "front matter is not \\documentclass{article} .. \\begin{document}"
  | B.WToken -> "token outside the fragment"
  | B.WNotAdmitted -> "character or name not admitted"
  | B.WScriptArg -> "script without a character or { argument"
  | B.WBound -> "capacity bound"
  | B.WEndsDollar -> "file ends with $"

let why_code = function
  | B.WTooBig -> "too_big"
  | B.WLexBad B.BadCat -> "bad_cat"
  | B.WLexBad B.BadHatHat -> "hathat"
  | B.WLexBad B.BadNullCs -> "null_cs"
  | B.WLexBad B.BadLongLine -> "long_line"
  | B.WLexBad B.BadFirstLine -> "first_line"
  | B.WPrologue -> "prologue"
  | B.WToken -> "token"
  | B.WNotAdmitted -> "not_admitted"
  | B.WScriptArg -> "script_arg"
  | B.WBound -> "bound"
  | B.WEndsDollar -> "ends_dollar"

(* ---- coverage labels of the reader (REPORTING ONLY) ---------------------- *)

(* The constructors of Lexer.LineLex / LinesLex / Lines each byte went through,
   and the BRANCH cells "<state>|<class>" of the line reader (class: the
   category of the byte, with the escape character refined by what follows it
   and ^ by ^^). This mirrors [B.lexl]; a mislabel can only misstate coverage,
   never a verdict. Nothing at an offset beyond [cut] (the closing brace of
   \end{document}, where TeX stops reading) is labelled. *)
let reader_labels (lx : B.lexcon) (b : char list) (cut : int) =
  let rules = ref [] and brs = ref [] in
  let add r = if not (List.mem r !rules) then rules := r :: !rules in
  let addb x = if not (List.mem x !brs) then brs := x :: !brs in
  let st_name = function B.SN -> "N" | B.SM -> "M" | B.SS -> "S" in
  let bytes = Array.of_list b in
  let n = Array.length bytes in
  let lines = B.split_lines b in
  let rec go st buf =
    match buf with
    | [] -> add "LL_end"
    | (_, o) :: _ when o > cut -> ()
    | (c, _) :: rest -> (
        let cell cls = addb (st_name st ^ "|" ^ cls) in
        match lx.B.lx_cat c with
        | B.CEol ->
            cell "eol";
            add
              (match st with
              | B.SN -> "LL_eol_new"
              | B.SM -> "LL_eol_mid"
              | B.SS -> "LL_eol_skip")
        | B.CSpacer ->
            cell "spacer";
            if st = B.SM then (
              add "LL_space_emit";
              go B.SS rest)
            else (
              add "LL_space_skip";
              go st rest)
        | B.CComment ->
            cell "comment";
            add "LL_comment"
        | (B.CLetter | B.COther) as k ->
            cell (cat_name k);
            add "LL_char";
            go B.SM rest
        | (B.CBgroup | B.CEgroup | B.CMath | B.CSub) as k ->
            cell (cat_name k);
            add
              (match k with
              | B.CBgroup -> "LL_bgroup"
              | B.CEgroup -> "LL_egroup"
              | B.CMath -> "LL_math"
              | _ -> "LL_sub");
            go B.SM rest
        | B.CSup ->
            if B.hathat lx c rest then (
              cell "sup.hathat";
              add "LL_hathat")
            else (
              cell "sup";
              add "LL_sup";
              go B.SM rest)
        | B.CEscape -> (
            match rest with
            | [] ->
                cell "esc.null";
                add "LL_nullcs"
            | (d, _) :: rest' ->
                if lx.B.lx_cat d = B.CLetter then (
                  let _, after = B.split_letters lx rest in
                  match after with
                  | (x, _) :: after' when B.hathat lx x after' ->
                      cell "esc.word.hathat";
                      add "LL_word_hathat"
                  | _ ->
                      cell "esc.word";
                      add "LL_word";
                      go B.SS after)
                else if B.hathat lx d rest' then (
                  cell "esc.sym.hathat";
                  add "LL_sym_hathat")
                else (
                  cell "esc.sym";
                  add "LL_sym";
                  go (B.sym_state lx d) rest'))
        | k ->
            cell (cat_name k);
            add "LL_bad")
  in
  let rec walk = function
    | [] -> ()
    | (l, eo) :: r ->
        let start = match l with (_, o) :: _ -> o | [] -> eo in
        if start <= cut then (
          if eo >= n then add "Lines_last"
          else if bytes.(eo) = '\n' then add "Lines_lf"
          else if eo + 1 < n && bytes.(eo + 1) = '\n' then add "Lines_crlf"
          else add "Lines_cr";
          if List.length l > B.max_line_bytes then add "LX_long"
          else (
            add "LX_line";
            go B.SN (B.buffer lx l eo));
          walk r)
  in
  add (if B.first_directive b then "FL_directive" else "FL_none");
  walk lines;
  (* [Lines] ends with [Lines_nil] iff the file is empty or ends with a line
     terminator, and [LinesLex] with [LX_nil]; both only when every line was
     read. *)
  if cut >= n then (
    add "LX_nil";
    if n = 0 || bytes.(n - 1) = '\n' || bytes.(n - 1) = '\r' then
      add "Lines_nil");
  (List.rev !rules, List.rev !brs)

(* Front.Prologue / Front.Body labels, and the offset of the closing brace of
   \end{document} (where TeX stops reading), or max_int. *)
let front_labels (lx : B.lexcon) (ts : B.lt list) =
  let rules = ref [] and brs = ref [] in
  let add r = if not (List.mem r !rules) then rules := r :: !rules in
  let addb x = if not (List.mem x !brs) then brs := x :: !brs in
  let filler_label (t : B.lt) =
    match t.B.lt_tok with
    | B.RSpace -> "space"
    | B.RPar -> "par_line"
    | B.RWord _ -> "par_word"
    | _ -> "?"
  in
  let rec fill_labels where = function
    | t :: r when B.fillerb lx t ->
        addb ("P|" ^ where ^ "|" ^ filler_label t);
        fill_labels where r
    | _ -> ()
  in
  let cut = ref max_int in
  (match B.prologue lx ts with
  | None -> ()
  | Some rest ->
      add "P_prologue";
      fill_labels "pre" ts;
      (match B.braced lx.B.lx_docclass lx.B.lx_class (B.skip_fill lx ts) with
      | Some (_, r) -> fill_labels "mid" r
      | None -> ());
      let rec body s = function
        | [] -> add "B_eof"
        | (t : B.lt) :: r -> (
            match t.B.lt_tok with
            | B.RWord nm ->
                if nm = lx.B.lx_par then (
                  add "B_par_word";
                  body false r)
                else if nm = lx.B.lx_end then
                  match B.braced lx.B.lx_end lx.B.lx_docenv (t :: r) with
                  | Some (cb, _) ->
                      add "B_end";
                      addb
                        (if cb.B.lt_line <> t.B.lt_line then "B_end|split"
                         else "B_end|one_line");
                      cut := cb.B.lt_off
                  | None -> ()
                else (
                  add "B_word";
                  body false r)
            | B.RSpace ->
                add (if s then "B_space_script" else "B_space");
                body s r
            | B.RPar ->
                add "B_par_line";
                body false r
            | B.RSym _ ->
                add "B_sym";
                body false r
            | B.RChar _ ->
                add "B_char";
                body false r
            | B.RBgroup ->
                add "B_open";
                body false r
            | B.REgroup ->
                add "B_close";
                body false r
            | B.RMath ->
                add "B_math";
                body false r
            | B.RSup | B.RSub ->
                add "B_script";
                body true r
            | B.RBad _ -> ())
      in
      body false rest);
  (List.rev !rules, List.rev !brs, !cut)

let hex_decode s =
  let n = String.length s / 2 in
  List.init n (fun i ->
      Char.chr (int_of_string ("0x" ^ String.sub s (2 * i) 2)))

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* The contracts of the bytes decision, from the committed files. *)
let bytes_contract ~kernel ~contract ~sigs ~lexical =
  let members = load_members kernel contract in
  let kernel_key = content_key kernel "meanings_sha256" in
  let contract_key = content_key contract "config_key" in
  let sg = load_signatures sigs members ~kernel_key ~contract_key in
  let lx = load_lexcon lexical ~kernel_key ~contract_key in
  let kc =
    {
      K.c_defined = (fun n -> Hashtbl.mem members (string_of_chars n));
      K.c_sig = (fun n -> Hashtbl.find_opt sg (string_of_chars n));
    }
  in
  let bc =
    {
      B.bc_kernel =
        {
          B.c_defined = (fun n -> Hashtbl.mem members (string_of_chars n));
          B.c_sig =
            (fun n ->
              Option.map b_sig (Hashtbl.find_opt sg (string_of_chars n)));
        };
      B.bc_lex = lx;
    }
  in
  (kc, bc)

(* One file through the extracted decider; the JSON record of the evidence. *)
let decide_bytes_json kc (bc : B.bcontract) (b : char list) =
  let lx = bc.B.bc_lex in
  let verdict = B.decide_bytes bc b in
  let explain = B.explain bc b in
  let raw = B.lex lx b in
  let frules, fbranches, cut = front_labels lx raw in
  let cut =
    match (verdict, explain) with
    | B.NotStrict, Some (off, _) when cut = max_int -> off
    | _ -> cut
  in
  let lrules, lbranches = reader_labels lx b cut in
  let parsed = B.parse lx b in
  let toks = match parsed with Some ks -> B.toks_of ks | None -> [] in
  let ktoks = List.map k_tok toks in
  let rules, branches =
    match parsed with Some _ -> rules_used kc ktoks | None -> ([], [])
  in
  let strs l = `List (List.map (fun r -> `String r) l) in
  let base =
    [
      ("ntoks", `Int (List.length toks));
      ("nbytes", `Int (List.length b));
      ("in_strict", `Bool (B.in_strict_bytes_b bc b));
      ("rules", strs rules);
      ("branches", strs branches);
      ("lex_rules", strs (lrules @ frules));
      ("lex_branches", strs (lbranches @ fbranches));
      ( "explain",
        match explain with
        | Some (off, w) -> `List [ `Int off; `String (why_code w) ]
        | None -> `Null );
    ]
  in
  match verdict with
  | B.ProvenReady -> `Assoc (base @ [ ("verdict", `String "ready") ])
  | B.ProvenNotReady (r, line) ->
      let l =
        match B.run bc.B.bc_kernel B.init toks with
        | Some (B.Fatal (_, l)) -> l
        | _ -> -1
      in
      let tok =
        match List.nth_opt ktoks l with
        | Some t -> `String (tok_name t)
        | None -> `String "eof"
      in
      `Assoc
        (base
        @ [
            ("verdict", `String "not_ready");
            ("reason", `String (string_of_reason (k_reason r)));
            ("loc", `Int l);
            ("loc_tok", tok);
            ("loc_line", if line = 0 then `Null else `Int line);
            ("loc_mode", `String (mode_at kc ktoks));
          ])
  | B.NotStrict -> `Assoc (base @ [ ("verdict", `String "not_strict") ])

let bytes_mode ~kernel ~contract ~sigs ~lexical =
  let kc, bc = bytes_contract ~kernel ~contract ~sigs ~lexical in
  try
    while true do
      let line = input_line stdin in
      if String.trim line <> "" then
        let j = Yojson.Safe.from_string line in
        let id = member "id" j in
        let out =
          try
            match member "hex" j with
            | `String h -> (
                match decide_bytes_json kc bc (hex_decode h) with
                | `Assoc l -> `Assoc (("id", id) :: l)
                | x -> x)
            | _ -> failwith "request without hex"
          with Failure m -> `Assoc [ ("id", id); ("error", `String m) ]
        in
        print_endline (Yojson.Safe.to_string out)
    done
  with End_of_file -> ()

(* strict_decide.exe FILE.tex: the verdict of the extracted decider on the
   file's bytes, on one line. Exit 0 on a verdict (either way), 3 outside the
   fragment, 2 on a usage or contract error. The verdict word is a fixed token
   of this printer; the file name follows it, quoted. *)
let file_mode ~kernel ~contract ~sigs ~lexical path =
  let _, bc = bytes_contract ~kernel ~contract ~sigs ~lexical in
  let s = try read_file path with Sys_error m -> die "strict_decide: %s" m in
  let b = List.init (String.length s) (String.get s) in
  match B.decide_bytes bc b with
  | B.ProvenReady ->
      Printf.printf "PROVEN-READY %S\n" path;
      exit 0
  | B.ProvenNotReady (r, line) ->
      let r = string_of_reason (k_reason r) in
      if line = 0 then
        Printf.printf "PROVEN-NOT-READY %S %s at the end of the file (no l.N)\n"
          path r
      else Printf.printf "PROVEN-NOT-READY %S %s l.%d\n" path r line;
      exit 0
  | B.NotStrict ->
      (match B.explain bc b with
      | Some (off, w) ->
          Printf.printf "NOT-IN-FRAGMENT %S byte %d: %s\n" path off (why_name w)
      | None -> Printf.printf "NOT-IN-FRAGMENT %S\n" path);
      exit 3

(* The committed contract files, found from the current directory upwards (file
   mode's defaults). *)
let find_repo () =
  let rec up d =
    if Sys.file_exists (Filename.concat d "corpora/contracts/article.json") then
      Some d
    else
      let p = Filename.dirname d in
      if p = d then None else up p
  in
  up (Sys.getcwd ())

let () =
  let kernel = ref "" and contract = ref "" and sigs = ref None in
  let lexical = ref "" and bytes = ref false and file = ref None in
  Arg.parse
    [
      ("--kernel", Arg.Set_string kernel, "kernel names file");
      ("--contract", Arg.Set_string contract, "configuration contract");
      ("--signatures", Arg.String (fun s -> sigs := Some s), "signatures file");
      ("--lexical", Arg.Set_string lexical, "lexical contract (bytes)");
      ("--bytes", Arg.Set bytes, "JSON lines of files as hex (bytes mode)");
    ]
    (fun f -> file := Some f)
    "strict_decide.exe --kernel K --contract C [--signatures S]   (trees)\n\
     strict_decide.exe --bytes --kernel K --contract C --signatures S \
     --lexical X\n\
     strict_decide.exe FILE.tex   (contracts from the repository)";
  match !file with
  | Some path ->
      let repo =
        match find_repo () with
        | Some r -> r
        | None ->
            die
              "strict_decide: run it inside the repository (contracts not \
               found)"
      in
      let p r = Filename.concat repo r in
      let contract_path =
        if !contract = "" then p "corpora/contracts/article.json" else !contract
      in
      let kernel_path =
        if !kernel <> "" then !kernel
        else
          match member "file" (member "kernel" (load_json contract_path)) with
          | `String f -> p f
          | _ -> die "strict_decide: the contract names no kernel file"
      in
      let sigs =
        match !sigs with
        | Some s -> Some s
        | None -> Some (p "corpora/contracts/strict/article-s0-signatures.json")
      in
      let lexical =
        if !lexical = "" then
          p "corpora/contracts/strict/article-s0-lexical.json"
        else !lexical
      in
      file_mode ~kernel:kernel_path ~contract:contract_path ~sigs ~lexical path
  | None ->
      if !kernel = "" || !contract = "" then
        die "strict_decide: need --kernel and --contract";
      if !bytes then (
        if !lexical = "" then die "strict_decide: --bytes needs --lexical";
        bytes_mode ~kernel:!kernel ~contract:!contract ~sigs:!sigs
          ~lexical:!lexical)
      else tree_mode ~kernel:!kernel ~contract:!contract ~sigs:!sigs
