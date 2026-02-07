(* Catcode classifier aligned with Data.Types.Catcode and v25_R1 mapping. *)

(* Integer codes follow data/types.ml:Catcode.catcode_to_int *)
let cc_escape = 0
let cc_beginGrp = 1
let cc_endGrp = 2
let cc_math = 3
let cc_alignTab = 4
let cc_newline = 5
let cc_param = 6
let cc_superscr = 7
let cc_subscr = 8
let cc_ignored = 9
let cc_space = 10
let cc_letter = 11
let cc_other = 12
let cc_active = 13
let cc_comment = 14
let cc_invalid = 15
let is_letter c = (c >= 65 && c <= 90) || (c >= 97 && c <= 122)

let classify_ascii (b : int) : int =
  match b land 0xFF with
  | 92 -> cc_escape (* \\ *)
  | 123 -> cc_beginGrp (* { *)
  | 125 -> cc_endGrp (* } *)
  | 36 -> cc_math (* $ *)
  | 38 -> cc_alignTab (* & *)
  | 10 | 13 -> cc_newline (* LF/CR *)
  | 35 -> cc_param (* # *)
  | 94 -> cc_superscr (* ^ *)
  | 95 -> cc_subscr (* _ *)
  | 0 -> cc_ignored (* NUL *)
  | 32 | 9 -> cc_space (* space/tab *)
  | 126 -> cc_active (* ~ *)
  | 37 -> cc_comment (* % *)
  | 127 -> cc_invalid (* DEL *)
  | c when is_letter c -> cc_letter
  | _ -> cc_other
