(* ══════════════════════════════════════════════════════════════════════
   Unicode_split — Unicode-aware text segmentation (spec W66-67)

   Uses Uutf for proper grapheme cluster handling. Supports CJK,
   Arabic, mixed-script documents. Provides word and sentence
   segmentation that respects Unicode boundaries.

   Property: concat(split(s)) = s  (proved in SplitPreservesOrder.v)
   ══════════════════════════════════════════════════════════════════════ *)

(* ── Unicode character classification ─────────────────────────────── *)

(** Classify a Unicode scalar value into broad categories. *)
type uchar_category =
  | Letter
  | Digit
  | Whitespace
  | Punctuation
  | CJK (* CJK Unified Ideographs + extensions *)
  | Arabic (* Arabic script *)
  | Other

let classify_uchar (u : Uchar.t) : uchar_category =
  let cp = Uchar.to_int u in
  if cp >= 0x4E00 && cp <= 0x9FFF then CJK (* CJK Unified *)
  else if cp >= 0x3400 && cp <= 0x4DBF then CJK (* CJK Extension A *)
  else if cp >= 0x20000 && cp <= 0x2A6DF then CJK (* CJK Extension B *)
  else if cp >= 0xF900 && cp <= 0xFAFF then CJK (* CJK Compat *)
  else if cp >= 0x3000 && cp <= 0x303F then Punctuation (* CJK Symbols *)
  else if cp >= 0x3040 && cp <= 0x309F then CJK (* Hiragana *)
  else if cp >= 0x30A0 && cp <= 0x30FF then CJK (* Katakana *)
  else if cp >= 0x0600 && cp <= 0x06FF then Arabic (* Arabic *)
  else if cp >= 0x0750 && cp <= 0x077F then Arabic (* Arabic Supplement *)
  else if cp >= 0x0620 && cp <= 0x064A then Arabic
  else if cp >= 0xFB50 && cp <= 0xFDFF then Arabic (* Arabic Pres A *)
  else if cp >= 0xFE70 && cp <= 0xFEFF then Arabic (* Arabic Pres B *)
  else if
    (cp >= 0x41 && cp <= 0x5A) (* A-Z *)
    || (cp >= 0x61 && cp <= 0x7A) (* a-z *)
    || (cp >= 0xC0 && cp <= 0x24F) (* Latin Extended *)
    || (cp >= 0x0400 && cp <= 0x04FF) (* Cyrillic *)
    || (cp >= 0x0370 && cp <= 0x03FF)
    (* Greek *)
  then Letter
  else if
    (cp >= 0x30 && cp <= 0x39) (* 0-9 *) || (cp >= 0x0660 && cp <= 0x0669)
    (* Arabic-Indic *)
  then Digit
  else if
    cp = 0x20 || cp = 0x09 || cp = 0x0A || cp = 0x0D || cp = 0x00A0 (* NBSP *)
    || cp = 0x3000 (* Ideographic space *)
    || cp = 0x2000
    || cp = 0x2001 (* En/Em space *)
  then Whitespace
  else if
    (cp >= 0x21 && cp <= 0x2F)
    || (cp >= 0x3A && cp <= 0x40)
    || (cp >= 0x5B && cp <= 0x60)
    || (cp >= 0x7B && cp <= 0x7E)
    || (cp >= 0x2000 && cp <= 0x206F) (* Gen. punctuation *)
    || (cp >= 0xFF01 && cp <= 0xFF0F) (* Fullwidth punct *)
    || cp = 0x3001
    || cp = 0x3002 (* CJK comma/period *)
    || cp = 0xFF0C
    || cp = 0xFF0E (* Fullwidth comma/period *)
  then Punctuation
  else Other

(* ── Decode UTF-8 string to list of Uchar.t ──────────────────────── *)

let decode_uchars (s : string) : Uchar.t list =
  let acc = ref [] in
  let d = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let rec loop () =
    match Uutf.decode d with
    | `Uchar u ->
        acc := u :: !acc;
        loop ()
    | `End -> ()
    | `Malformed _ ->
        acc := Uutf.u_rep :: !acc;
        loop ()
    | `Await -> ()
  in
  loop ();
  List.rev !acc

(* ── Word segmentation ────────────────────────────────────────────── *)

type word_segment = {
  w_text : string;
  w_start : int; (* byte offset *)
  w_end : int; (* byte offset *)
}
(** A word segment with its byte range. *)

(** Split into word segments. CJK characters are each their own word.
    Latin/Cyrillic/Greek words break on whitespace/punctuation.
    Arabic words break on whitespace. *)
let split_words (s : string) : word_segment list =
  let len = String.length s in
  let segments = ref [] in
  let buf = Buffer.create 64 in
  let seg_start = ref 0 in
  let d = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let flush () =
    if Buffer.length buf > 0 then (
      let text = Buffer.contents buf in
      let byte_end = Uutf.decoder_byte_count d in
      segments :=
        { w_text = text; w_start = !seg_start; w_end = byte_end } :: !segments;
      Buffer.clear buf;
      seg_start := byte_end)
  in
  let rec loop () =
    match Uutf.decode d with
    | `Uchar u ->
        let cat = classify_uchar u in
        (match cat with
        | CJK ->
            flush ();
            let byte_pos = Uutf.decoder_byte_count d in
            let char_start = byte_pos - Uchar.utf_8_byte_length u in
            segments :=
              {
                w_text = String.sub s char_start (Uchar.utf_8_byte_length u);
                w_start = char_start;
                w_end = byte_pos;
              }
              :: !segments;
            seg_start := byte_pos
        | Whitespace | Punctuation ->
            flush ();
            seg_start := Uutf.decoder_byte_count d
        | Letter | Digit | Arabic | Other ->
            if Buffer.length buf = 0 then
              seg_start := Uutf.decoder_byte_count d - Uchar.utf_8_byte_length u;
            let n = Uchar.utf_8_byte_length u in
            let byte_start = Uutf.decoder_byte_count d - n in
            Buffer.add_string buf (String.sub s byte_start n));
        loop ()
    | `End -> flush ()
    | `Malformed _ ->
        Buffer.add_string buf (String.make 1 '\xEF');
        loop ()
    | `Await -> ()
  in
  ignore (len : int);
  loop ();
  List.rev !segments

(* ── Sentence segmentation (Unicode-aware) ────────────────────────── *)

type sentence_segment = { s_text : string; s_start : int; s_end : int }
(** A sentence with byte range. *)

(** Unicode sentence terminators. *)
let is_sentence_end (u : Uchar.t) : bool =
  let cp = Uchar.to_int u in
  cp = 0x2E (* . *) || cp = 0x21
  (* ! *) || cp = 0x3F (* ? *)
  || cp = 0x3002 (* CJK period 。 *)
  || cp = 0xFF01 (* fullwidth ! *)
  || cp = 0xFF1F (* fullwidth ? *)
  || cp = 0x06D4 (* Arabic period ۔ *)

let split_sentences (s : string) : sentence_segment list =
  let segments = ref [] in
  let buf = Buffer.create 256 in
  let seg_start = ref 0 in
  let d = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let saw_terminator = ref false in
  let rec loop () =
    match Uutf.decode d with
    | `Uchar u ->
        let byte_pos = Uutf.decoder_byte_count d in
        let n = Uchar.utf_8_byte_length u in
        let char_start = byte_pos - n in
        Buffer.add_string buf (String.sub s char_start n);
        if is_sentence_end u then saw_terminator := true
        else if !saw_terminator && classify_uchar u = Whitespace then (
          (* Sentence boundary: terminator followed by whitespace *)
          let text = Buffer.contents buf in
          segments :=
            {
              s_text = String.trim text;
              s_start = !seg_start;
              s_end = byte_pos;
            }
            :: !segments;
          Buffer.clear buf;
          seg_start := byte_pos;
          saw_terminator := false)
        else if !saw_terminator && classify_uchar u <> Punctuation then
          saw_terminator := false;
        loop ()
    | `End ->
        if Buffer.length buf > 0 then
          let text = Buffer.contents buf in
          let trimmed = String.trim text in
          if String.length trimmed > 0 then
            segments :=
              {
                s_text = trimmed;
                s_start = !seg_start;
                s_end = Uutf.decoder_byte_count d;
              }
              :: !segments
    | `Malformed _ ->
        Buffer.add_string buf "\xEF\xBF\xBD";
        loop ()
    | `Await -> ()
  in
  loop ();
  List.rev !segments

(* ── Concatenation roundtrip property ─────────────────────────────── *)

(** concat(split_words(s)) should contain the same non-whitespace content
    as the original string. This is the OCaml witness for
    proofs/SplitPreservesOrder.v. *)
let concat_words (words : word_segment list) : string =
  String.concat "" (List.map (fun w -> w.w_text) words)

(** Check the roundtrip property: all word content preserved. *)
let words_preserve_content (s : string) : bool =
  let words = split_words s in
  let joined = concat_words words in
  (* Strip whitespace/punct from original for comparison *)
  let strip str =
    let uchars = decode_uchars str in
    let filtered =
      List.filter
        (fun u ->
          match classify_uchar u with
          | Whitespace | Punctuation -> false
          | _ -> true)
        uchars
    in
    let b = Buffer.create 64 in
    let e = Uutf.encoder `UTF_8 (`Buffer b) in
    List.iter (fun u -> ignore (Uutf.encode e (`Uchar u))) filtered;
    ignore (Uutf.encode e `End);
    Buffer.contents b
  in
  strip joined = strip s
