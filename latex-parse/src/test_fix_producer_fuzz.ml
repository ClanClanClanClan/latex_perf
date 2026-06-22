(** Property/fuzz test for the fix-producer pipeline (P4).

    The corpus safety gate (scripts/tools/check_apply_fixes_safety.py) validates
    convergence + valid-UTF-8 on the 330 FIXED real corpus files. This is its
    in-process, RANDOMISED complement: it generates adversarial inputs the
    finite corpus cannot contain — dense runs of every fix-producer trigger,
    math / verbatim boundary stress, and raw random byte soup — runs the REAL
    validators to collect their REAL fix edits, applies them through the same
    Cst_edit path the CLI uses, and asserts the fix-producer SAFETY invariants
    on every input:

    A. run_all never raises (robustness against arbitrary bytes). B. apply_all
    returns Ok | Error `Overlap — never raises (no out-of-bounds). F. every
    emitted edit is well-formed: 0 <= start <= end <= length. C. convergence:
    iterating apply to a fixpoint terminates within a cap (no oscillation) — the
    in-process mirror of the gate + the P1a CLI loop. D. idempotence:
    re-applying at the fixpoint changes nothing. E. UTF-8 preservation:
    valid-UTF-8 in => valid-UTF-8 out at EVERY pass (no producer turns valid
    text into invalid bytes; ENC-004 may still go invalid->valid, which is
    allowed — only valid->invalid is a defect).

    Reproducible: the PRNG seed is fixed (override via FIX_FUZZ_SEED) and
    printed; any failure prints the seed + the offending input (hex-escaped) so
    it can be replayed deterministically. Runs both the default and pilot
    validator sets so the pilot-gated TYPO producers are exercised too. *)

open Latex_parse_lib
open Test_helpers

(* Fixpoint cap — matches validators_cli.ml's apply_fixes_cap intent. The corpus
   converges in <=8 passes; anything beyond this on a fuzz input means a cycle
   or a non-terminating cascade, which is a defect. *)
let cap = 64

let env_int name default =
  match Sys.getenv_opt name with
  | Some s -> ( match int_of_string_opt s with Some n -> n | None -> default)
  | None -> default

(* Collect every rule's fix edits, exactly as validators_cli.collect_fix_edits
   does for the unfiltered --apply-fixes path. *)
let collect_all_fix_edits src =
  Validators.run_all src
  |> List.concat_map (fun (r : Validators.result) ->
         match r.fix with Some edits -> edits | None -> [])

let well_formed_edits src edits =
  let n = String.length src in
  List.for_all
    (fun (e : Cst_edit.t) ->
      e.start_offset >= 0 && e.start_offset <= e.end_offset && e.end_offset <= n)
    edits

let hex_escape s =
  let b = Buffer.create (String.length s * 2) in
  String.iter
    (fun c ->
      let x = Char.code c in
      if x >= 0x20 && x < 0x7f && c <> '\\' then Buffer.add_char b c
      else Buffer.add_string b (Printf.sprintf "\\x%02x" x))
    s;
  Buffer.contents b

(* Drive [src] to a fixpoint. Returns the outcome; on any violation the variant
   carries enough to report. valid_in flags whether [src] was valid UTF-8 (so we
   only demand UTF-8 preservation when the input itself was valid). *)
type outcome =
  | Converged
  | Overlap_terminal
    (* apply_all reported overlap — a defined CLI exit-2 state *)
  | Bad_edit of string (* offset out of range *)
  | Utf8_broken of string (* valid input produced invalid-UTF-8 output *)
  | No_fixpoint (* hit the pass cap without stabilising *)
  | Cycle (* a previously-seen state recurred — oscillation *)
  | Raised of string

(* Returns the outcome and the number of fix passes actually APPLIED (>=1 means
   the input fired at least one producer; >=2 means a multi-pass cascade — the
   convergence machinery did real work). The pass count feeds the coverage floor
   that guards against a vacuously-green fuzzer. *)
let drive src =
  let valid_in = String.is_valid_utf_8 src in
  let seen = Hashtbl.create 16 in
  Hashtbl.replace seen (Digest.string src) ();
  let rec loop cur passes =
    if passes > cap then (No_fixpoint, passes)
    else
      let edits = collect_all_fix_edits cur in
      if not (well_formed_edits cur edits) then (Bad_edit cur, passes)
      else if edits = [] then (Converged, passes)
      else
        match Cst_edit.apply_all cur edits with
        | Error (`Overlap _) -> (Overlap_terminal, passes)
        | Ok nxt ->
            if valid_in && not (String.is_valid_utf_8 nxt) then
              (Utf8_broken nxt, passes)
            else if String.equal nxt cur then (Converged, passes)
            else
              let d = Digest.string nxt in
              if Hashtbl.mem seen d then (Cycle, passes)
              else (
                Hashtbl.replace seen d ();
                loop nxt (passes + 1))
  in
  try loop src 0 with e -> (Raised (Printexc.to_string e), 0)

(* ── Input generator ───────────────────────────────────────────────── *)

(* Fragments biased toward firing fix producers across families. Unicode and
   Windows-1252 triggers are written as raw bytes. *)
let palette =
  [|
    (* TYPO family *)
    "\"quoted\"";
    "a -- b";
    "a --- b";
    "word , next";
    "spaced  out   text";
    "et.al";
    "5\xc2\xb0C";
    (* 5°C — TYPO-057 thin space *)
    "x => y";
    "\xc3\x97";
    (* × U+00D7 *)
    (* SPC family *)
    "\\url{ http://x }";
    "trailing   \n";
    "tab\there";
    "\\item\tbody";
    (* ENC family — Windows-1252 C1 bytes (invalid standalone UTF-8) *)
    "dash\x96here";
    "ellipsis\x85end";
    "quote\x93x\x94";
    (* CHAR family *)
    "\xe2\x80\x8d";
    (* ZWJ U+200D *)
    "\xef\xac\x81";
    (* ﬁ ligature *)
    (* CJK family *)
    "\xef\xbc\x8c";
    (* fullwidth comma U+FF0C *)
    "\xef\xbc\x8e";
    (* fullwidth period U+FF0E *)
    "\xe4\xb8\xad\xef\xbc\x8c\xe6\x96\x87";
    (* Han,Han with fullwidth comma — CJK adjacency *)
    "\xe3\x80\x80";
    (* fullwidth space U+3000 *)
    "a,\xe4\xb8\xad";
    (* ASCII comma adjacent to Han — CJK-010 *)
    (* MATH family *)
    "$\\frac{1}{2}$";
    "$\\left( x$";
    "$$x$$";
    (* structural / boundary *)
    "\\documentclass{article}";
    "\\begin{document}";
    "\\end{document}";
    "$x+y=z$";
    "\\verb|raw_code|";
    "{nested {braces}}";
    "plain words here";
    "\n\n\n";
    "   ";
  |]

let rng_word st =
  let n = 1 + Random.State.int st 6 in
  String.init n (fun _ -> Char.chr (Char.code 'a' + Random.State.int st 26))

let rng_raw_bytes st =
  let n = Random.State.int st 8 in
  String.init n (fun _ -> Char.chr (Random.State.int st 256))

let gen_input st =
  let segs = 1 + Random.State.int st 24 in
  let b = Buffer.create 64 in
  (* ~1 in 6 inputs is wrapped as a document so STRUCT-001 + math contexts
     fire *)
  let wrap = Random.State.int st 6 = 0 in
  if wrap then
    Buffer.add_string b "\\documentclass{article}\n\\begin{document}\n";
  for _ = 1 to segs do
    (match Random.State.int st 10 with
    | 0 | 1 | 2 | 3 | 4 ->
        Buffer.add_string b palette.(Random.State.int st (Array.length palette))
    | 5 | 6 | 7 -> Buffer.add_string b (rng_word st)
    | 8 -> Buffer.add_string b (rng_raw_bytes st)
    | _ -> Buffer.add_char b ' ');
    if Random.State.int st 3 = 0 then Buffer.add_char b ' '
  done;
  if wrap then Buffer.add_string b "\n\\end{document}\n";
  Buffer.contents b

(* ── Driver ────────────────────────────────────────────────────────── *)

let seed = env_int "FIX_FUZZ_SEED" 0x5eed1234
let iters = env_int "FIX_FUZZ_ITERS" 1200

let sweep mode_label =
  let st = Random.State.make [| seed |] in
  let failures = ref [] in
  let fired = ref 0 in
  let multipass = ref 0 in
  for _ = 1 to iters do
    let src = gen_input st in
    let outcome, passes = drive src in
    if passes >= 1 then incr fired;
    if passes >= 2 then incr multipass;
    let problem =
      match outcome with
      | Converged | Overlap_terminal -> None
      | Bad_edit cur -> Some ("edit offset out of range on: " ^ hex_escape cur)
      | Utf8_broken nxt ->
          Some ("valid UTF-8 input produced invalid output: " ^ hex_escape nxt)
      | No_fixpoint -> Some "no fixpoint within cap (cascade/oscillation)"
      | Cycle -> Some "fix cycle detected (oscillation)"
      | Raised e -> Some ("exception: " ^ e)
    in
    match problem with
    | Some why -> failures := (src, why) :: !failures
    | None -> ()
  done;
  Printf.printf
    "[fix-producer-fuzz] %s: %d/%d inputs fired a fix, %d needed >=2 passes\n%!"
    mode_label !fired iters !multipass;
  run (Printf.sprintf "fuzz: fix-producer safety invariants (%s)" mode_label)
    (fun tag ->
      (match !failures with
      | [] -> ()
      | fs ->
          Printf.eprintf
            "[fix-producer-fuzz] %s: %d/%d inputs violated an invariant \
             (seed=0x%x)\n"
            mode_label (List.length fs) iters seed;
          List.iteri
            (fun i (src, why) ->
              if i < 5 then
                Printf.eprintf "  - %s\n      input: %s\n" why (hex_escape src))
            (List.rev fs));
      expect (!failures = [])
        (Printf.sprintf
           "%s: %d/%d invariant violations (seed=0x%x; set FIX_FUZZ_SEED to \
            replay)"
           tag (List.length !failures) iters seed));
  (* Anti-vacuity floor: the generator is heavily biased toward fix-producer
     triggers, so a healthy fraction of inputs MUST fire (and some must cascade
     through >=2 passes, exercising the convergence machinery). If this drops to
     near zero a refactor has silently neutered the fuzzer — fail loudly rather
     than report a meaningless green. *)
  run (Printf.sprintf "fuzz: coverage is non-vacuous (%s)" mode_label)
    (fun tag ->
      expect
        (!fired * 4 >= iters && !multipass > 0)
        (Printf.sprintf
           "%s: only %d/%d fired (need >=25%%) and %d multi-pass (need >0)" tag
           !fired iters !multipass))

let () =
  Printf.printf "[fix-producer-fuzz] seed=0x%x iters=%d/mode\n%!" seed iters;
  (* Default validator set. *)
  Unix.putenv "L0_VALIDATORS" "";
  sweep "default";
  (* Pilot set — exercises the pilot-gated TYPO producers. *)
  Unix.putenv "L0_VALIDATORS" "pilot";
  sweep "pilot";
  Unix.putenv "L0_VALIDATORS" "";
  finalise "fix-producer-fuzz"
