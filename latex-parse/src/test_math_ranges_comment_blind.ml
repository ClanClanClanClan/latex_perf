(* OPEN-097 regression: [find_math_ranges] must not pair a `$` that lives inside
   a `%` line comment (or verbatim, or a URL) with the next real `$`.

   Before the fix this produced ranges that swallowed prose, and every producer
   gated on [is_in_math_range] then fired inside them. It was the single
   upstream cause of both remaining OPEN-094 real-paper breaks, via two
   different producers (SCRIPT-019 on `2507.05786v1`, MATH-009 on
   `2507.04362v1`) -- neither of which was itself defective: both correctly
   asked "is this byte in math" and were told yes.

   ⚠ The assertions are DIRECTIONAL. A test that merely checked "the helper
   returns a list of ranges" would have passed against the broken version too,
   so every case below names a byte that must, or must not, be covered -- and
   case 3 is the opposite arm, pinning that comment-free input is unchanged. *)

open Latex_parse_lib.Validators_common

let failures = ref 0

let check name cond =
  if cond then Printf.printf "  ok   %s\n" name
  else (
    incr failures;
    Printf.printf "  FAIL %s\n" name)

let covers rs off = List.exists (fun (a, b) -> a <= off && off < b) rs
let widest rs = List.fold_left (fun acc (a, b) -> max acc (b - a)) 0 rs

(* Byte offset of [needle] in [hay]; raises if absent, so a test that stops
   describing its own fixture fails loudly instead of silently checking 0. *)
let at (hay : string) (needle : string) : int =
  let n = String.length hay and m = String.length needle in
  let rec go i =
    if i + m > n then failwith ("fixture drift: no " ^ needle)
    else if String.sub hay i m = needle then i
    else go (i + 1)
  in
  go 0

let () =
  print_endline "[math-ranges-comment-blind]";

  (* 1. The minimal reproduction from the OPEN-097 ledger row. *)
  let repro =
    "Hello.\n%%% $ pdfinfo x.pdf\nprose here\nThen $x+y$ real math.\n"
  in
  let r = find_math_ranges repro in
  check "a comment `$` does not open a range over the following prose"
    (not (covers r (at repro "prose here")));
  check "the genuine inline `$x+y$` IS still a math range"
    (covers r (at repro "$x+y$" + 1));
  check "no range is wider than the document's real math" (widest r < 16);

  (* 2. Verbatim, same shape. *)
  let vb = "Text $a$ and \\verb|$| more text and $b$ end.\n" in
  let rv = find_math_ranges vb in
  check "a `$` inside \\verb does not pair with the next real `$`"
    (not (covers rv (at vb "more text")));

  (* 3. The opposite arm: comment-free input must be untouched by the fix. *)
  let plain = "Let $x$ be and $y+z$ too.\n" in
  check "comment-free input still yields exactly its two real math spans"
    (List.length (find_math_ranges plain) = 2);

  (* 4. A comment `$` with no later real `$` must not run to EOF. `2507.04362v1`
     produced a 47,607-byte unclosed range exactly this way. *)
  let eof = "Intro.\n% price is $5 today\nbody text with no math at all.\n" in
  check "an unclosed comment `$` does not swallow the rest of the file"
    (find_math_ranges eof = []);

  (* 5. [find_exempt_ranges] must agree: it now shares the same math scan, and
     the asymmetry between the two paths is what hid this defect for so long. *)
  let ex = find_exempt_ranges repro in
  check "exempt ranges cover the comment itself"
    (covers ex (at repro "pdfinfo"));

  if !failures = 0 then print_endline "[math-ranges-comment-blind] PASS"
  else (
    Printf.printf "[math-ranges-comment-blind] FAIL: %d\n" !failures;
    exit 1)
