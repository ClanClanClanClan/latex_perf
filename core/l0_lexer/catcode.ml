module Catcode = Data.Types.Catcode
include Catcode

let of_int_opt = function
  | 0 -> Some Escape
  | 1 -> Some BeginGrp
  | 2 -> Some EndGrp
  | 3 -> Some Math
  | 4 -> Some AlignTab
  | 5 -> Some Newline
  | 6 -> Some Param
  | 7 -> Some Superscr
  | 8 -> Some Subscr
  | 9 -> Some Ignored
  | 10 -> Some Space
  | 11 -> Some Letter
  | 12 -> Some Other
  | 13 -> Some Active
  | 14 -> Some Comment
  | 15 -> Some Invalid
  | _ -> None

let of_ascii_code code =
  match of_int_opt code with Some cat -> cat | None -> Other

let classify_char ch = of_ascii_code (Char.code ch)
