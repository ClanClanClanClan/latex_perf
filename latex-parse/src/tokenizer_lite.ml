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

(* ── UTF-8 helpers ─────────────────────────────────────────────── *)

(** Decode a UTF-8 codepoint at byte offset [i] in [src]. Returns (codepoint,
    byte_count). *)
let decode_uchar_at (src : string) (i : int) : int * int =
  let n = String.length src in
  let b0 = Char.code (String.unsafe_get src i) in
  if b0 land 0x80 = 0 then (b0, 1)
  else if b0 land 0xE0 = 0xC0 && i + 1 < n then
    let b1 = Char.code (String.unsafe_get src (i + 1)) in
    (((b0 land 0x1F) lsl 6) lor (b1 land 0x3F), 2)
  else if b0 land 0xF0 = 0xE0 && i + 2 < n then
    let b1 = Char.code (String.unsafe_get src (i + 1)) in
    let b2 = Char.code (String.unsafe_get src (i + 2)) in
    (((b0 land 0x0F) lsl 12) lor ((b1 land 0x3F) lsl 6) lor (b2 land 0x3F), 3)
  else if b0 land 0xF8 = 0xF0 && i + 3 < n then
    let b1 = Char.code (String.unsafe_get src (i + 1)) in
    let b2 = Char.code (String.unsafe_get src (i + 2)) in
    let b3 = Char.code (String.unsafe_get src (i + 3)) in
    ( ((b0 land 0x07) lsl 18)
      lor ((b1 land 0x3F) lsl 12)
      lor ((b2 land 0x3F) lsl 6)
      lor (b3 land 0x3F),
      4 )
  else (0xFFFD, 1)

(** Is a Unicode codepoint a "letter" for word tokenization? Covers Latin, Latin
    Extended, Greek, Cyrillic, CJK, Arabic. *)
let is_unicode_letter (cp : int) : bool =
  (cp >= 0xC0 && cp <= 0x24F) (* Latin Extended *)
  || (cp >= 0x0370 && cp <= 0x03FF) (* Greek *)
  || (cp >= 0x0400 && cp <= 0x04FF) (* Cyrillic *)
  || (cp >= 0x0600 && cp <= 0x06FF) (* Arabic *)
  || (cp >= 0x0750 && cp <= 0x077F) (* Arabic Supplement *)
  || (cp >= 0x3040 && cp <= 0x30FF) (* Hiragana + Katakana *)
  || (cp >= 0x3400 && cp <= 0x4DBF) (* CJK Extension A *)
  || (cp >= 0x4E00 && cp <= 0x9FFF) (* CJK Unified *)
  || (cp >= 0xAC00 && cp <= 0xD7AF) (* Hangul *)
  || (cp >= 0xF900 && cp <= 0xFAFF)

(* CJK Compat *)

(** Is a codepoint CJK (each character = its own word)? *)
let is_cjk (cp : int) : bool =
  (cp >= 0x3040 && cp <= 0x30FF)
  || (cp >= 0x3400 && cp <= 0x4DBF)
  || (cp >= 0x4E00 && cp <= 0x9FFF)
  || (cp >= 0xF900 && cp <= 0xFAFF)
  || (cp >= 0x20000 && cp <= 0x2A6DF)

let tokenize (src : string) : tok list =
  let n = String.length src in
  let buf = ref [] in
  let push k i j ch = buf := { kind = k; s = i; e = j; ch } :: !buf in
  let rec word_end i =
    if i < n then
      let c = String.unsafe_get src i in
      if is_letter c then word_end (i + 1)
      else if Char.code c >= 0x80 then
        (* Check if this is a continuation of the word with UTF-8 chars *)
        let cp, seq_len = decode_uchar_at src i in
        if is_unicode_letter cp && not (is_cjk cp) then word_end (i + seq_len)
        else i
      else i
    else i
  in
  let rec cmd_end i =
    if i < n && is_letter (String.unsafe_get src i) then cmd_end (i + 1) else i
  in
  (* Consume consecutive non-CJK Unicode letters starting at [i]. *)
  let rec utf8_word_end i =
    if i >= n then i
    else
      let c = String.unsafe_get src i in
      let b = Char.code c in
      if b < 0x80 then
        (* ASCII: continue if letter, stop otherwise *)
        if is_letter c then utf8_word_end (i + 1) else i
      else
        let cp, seq_len = decode_uchar_at src i in
        if is_unicode_letter cp && not (is_cjk cp) then
          utf8_word_end (i + seq_len)
        else i
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
      | _ when Char.code c >= 0x80 ->
          (* Multi-byte UTF-8 *)
          let cp, seq_len = decode_uchar_at src i in
          if is_cjk cp then (
            (* CJK: each character is its own Word *)
            push Word i (i + seq_len) None;
            loop (i + seq_len))
          else if is_unicode_letter cp then (
            (* Non-CJK letter: accumulate into Word *)
            let j = utf8_word_end i in
            push Word i j None;
            loop j)
          else (
            push Symbol i (i + seq_len) None;
            loop (i + seq_len))
      | _ ->
          push Symbol i (i + 1) (Some c);
          loop (i + 1)
  in
  loop 0;
  List.rev !buf
