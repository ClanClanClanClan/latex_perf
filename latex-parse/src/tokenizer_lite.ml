type kind =
  | Word
  | Space
  | Newline
  | Command
  | Bracket_open
  | Bracket_close
  | Quote
  | Symbol

type tok = { kind : kind; s : int; e : int; ch : char option }

let is_letter c =
  ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')

let tokenize (src : string) : tok list =
  let n = String.length src in
  let buf = ref [] in
  let push k i j ch = buf := { kind = k; s = i; e = j; ch } :: !buf in
  let rec word_end i =
    if i < n && is_letter (String.unsafe_get src i) then word_end (i + 1) else i
  in
  let rec cmd_end i =
    if i < n && is_letter (String.unsafe_get src i) then cmd_end (i + 1) else i
  in
  let rec loop i =
    if i >= n then ()
    else
      let c = String.unsafe_get src i in
      match c with
      | ' ' | '\t' ->
          let j = ref i in
          while
            !j < n
            &&
            let d = String.unsafe_get src !j in
            d = ' ' || d = '\t'
          do
            incr j
          done;
          push Space i !j None;
          loop !j
      | '\n' ->
          push Newline i (i + 1) (Some '\n');
          loop (i + 1)
      | ('(' | '[' | '{') as b ->
          push Bracket_open i (i + 1) (Some b);
          loop (i + 1)
      | (')' | ']' | '}') as b ->
          push Bracket_close i (i + 1) (Some b);
          loop (i + 1)
      | '"' ->
          push Quote i (i + 1) (Some '"');
          loop (i + 1)
      | '\\' ->
          let j = cmd_end (i + 1) in
          push Command i j None;
          loop j
      | _ when is_letter c ->
          let j = word_end i in
          push Word i j None;
          loop j
      | _ ->
          push Symbol i (i + 1) (Some c);
          loop (i + 1)
  in
  loop 0;
  List.rev !buf
