(* ══════════════════════════════════════════════════════════════════════
   Pdf_reader — production-grade PDF structure inspector

   Architecture:
   1. Xref parser: scan from EOF for startxref, read xref table
   2. Token/object parser: dicts, arrays, strings, names, numbers, refs
   3. Catalog navigator: Root → StructTreeRoot, MarkInfo, Lang, etc.
   4. Page tree walker: Pages → Resources → Font, ColorSpace, Annots
   5. Font inspector: FontDescriptor → FontFile presence
   6. Annotation inspector: Link → Contents
   7. Structure tree walker: K → Figure → Alt
   8. ColorSpace inspector: Separation, DeviceN
   9. Stream inspector: Filter presence

   No external dependencies.  No zlib — inspects dict keys only.
   ══════════════════════════════════════════════════════════════════════ *)

type pdf_value =
  | PdfBool of bool
  | PdfInt of int
  | PdfFloat of float
  | PdfString of string
  | PdfName of string
  | PdfArray of pdf_value list
  | PdfDict of (string * pdf_value) list
  | PdfRef of int * int
  | PdfStream of (string * pdf_value) list * bytes
  | PdfNull

type pdf_document = {
  objects : (int, pdf_value) Hashtbl.t;
  trailer : (string * pdf_value) list;
}

type pdf_info = {
  has_struct_tree_root : bool;
  has_mark_info : bool;
  figures_without_alt : int;
  links_without_contents : int;
  lang : string option;
  fonts : (string * bool * bool) list;
  page_label_count : int;
  page_count : int;
  has_spot_colour : bool;
  has_spot_colour_vector : bool;
  streams_all_compressed : bool;
}

(* ══════════════════════════════════════════════════════════════════════
   §1  Utilities
   ══════════════════════════════════════════════════════════════════════ *)

let dict_get (key : string) (entries : (string * pdf_value) list) :
    pdf_value option =
  List.assoc_opt key entries

let is_whitespace = function
  | '\000' | '\t' | '\n' | '\012' | '\r' | ' ' -> true
  | _ -> false

let is_digit c = c >= '0' && c <= '9'

(* ══════════════════════════════════════════════════════════════════════
   §2  Tokenizer / Object Parser
   ══════════════════════════════════════════════════════════════════════ *)

type parse_state = {
  buf : bytes;
  mutable pos : int;
  len : int;
}

let ps_of_bytes b = { buf = b; pos = 0; len = Bytes.length b }

let _ps_peek ps =
  if ps.pos >= ps.len then None
  else Some (Bytes.get ps.buf ps.pos)

let _ps_advance ps n = ps.pos <- min ps.len (ps.pos + n)

let ps_skip_whitespace ps =
  while ps.pos < ps.len && is_whitespace (Bytes.get ps.buf ps.pos) do
    ps.pos <- ps.pos + 1
  done;
  (* Also skip comments *)
  if ps.pos < ps.len && Bytes.get ps.buf ps.pos = '%' then begin
    while ps.pos < ps.len && Bytes.get ps.buf ps.pos <> '\n' do
      ps.pos <- ps.pos + 1
    done;
    if ps.pos < ps.len then ps.pos <- ps.pos + 1;
    (* Recursive skip *)
    while ps.pos < ps.len && is_whitespace (Bytes.get ps.buf ps.pos) do
      ps.pos <- ps.pos + 1
    done
  end

let ps_match_keyword ps kw =
  let klen = String.length kw in
  if ps.pos + klen > ps.len then false
  else
    let ok = ref true in
    for i = 0 to klen - 1 do
      if Bytes.get ps.buf (ps.pos + i) <> kw.[i] then ok := false
    done;
    if !ok then begin ps.pos <- ps.pos + klen; true end
    else false

(** Parse a PDF name: /SomeName *)
let parse_name ps =
  if ps.pos >= ps.len || Bytes.get ps.buf ps.pos <> '/' then None
  else begin
    ps.pos <- ps.pos + 1;
    let start = ps.pos in
    while ps.pos < ps.len &&
          let c = Bytes.get ps.buf ps.pos in
          not (is_whitespace c) &&
          c <> '/' && c <> '[' && c <> ']' &&
          c <> '<' && c <> '>' && c <> '(' && c <> ')' &&
          c <> '{' && c <> '}'
    do
      ps.pos <- ps.pos + 1
    done;
    Some (Bytes.sub_string ps.buf start (ps.pos - start))
  end

(** Parse a number (int or float). *)
let parse_number ps =
  let start = ps.pos in
  let has_dot = ref false in
  if ps.pos < ps.len && (Bytes.get ps.buf ps.pos = '-' || Bytes.get ps.buf ps.pos = '+') then
    ps.pos <- ps.pos + 1;
  while ps.pos < ps.len &&
        let c = Bytes.get ps.buf ps.pos in
        is_digit c || (c = '.' && not !has_dot)
  do
    if Bytes.get ps.buf ps.pos = '.' then has_dot := true;
    ps.pos <- ps.pos + 1
  done;
  let s = Bytes.sub_string ps.buf start (ps.pos - start) in
  if !has_dot then
    try Some (PdfFloat (float_of_string s)) with Failure _ -> None
  else
    try Some (PdfInt (int_of_string s)) with Failure _ -> None

(** Parse a literal string: (text) with nested parens. *)
let parse_literal_string ps =
  if ps.pos >= ps.len || Bytes.get ps.buf ps.pos <> '(' then None
  else begin
    ps.pos <- ps.pos + 1;
    let b = Buffer.create 64 in
    let depth = ref 1 in
    while ps.pos < ps.len && !depth > 0 do
      let c = Bytes.get ps.buf ps.pos in
      ps.pos <- ps.pos + 1;
      match c with
      | '\\' when ps.pos < ps.len ->
          let esc = Bytes.get ps.buf ps.pos in
          ps.pos <- ps.pos + 1;
          begin match esc with
          | 'n' -> Buffer.add_char b '\n'
          | 'r' -> Buffer.add_char b '\r'
          | 't' -> Buffer.add_char b '\t'
          | 'b' -> Buffer.add_char b '\b'
          | '(' -> Buffer.add_char b '('
          | ')' -> Buffer.add_char b ')'
          | '\\' -> Buffer.add_char b '\\'
          | c when is_digit c ->
              (* Octal escape *)
              let oct = ref (Char.code c - Char.code '0') in
              for _ = 1 to 2 do
                if ps.pos < ps.len && is_digit (Bytes.get ps.buf ps.pos)
                   && Char.code (Bytes.get ps.buf ps.pos) <= Char.code '7' then begin
                  oct := !oct * 8 + (Char.code (Bytes.get ps.buf ps.pos) - Char.code '0');
                  ps.pos <- ps.pos + 1
                end
              done;
              Buffer.add_char b (Char.chr (!oct land 0xFF))
          | _ -> Buffer.add_char b esc
          end
      | '(' -> incr depth; Buffer.add_char b c
      | ')' -> decr depth; if !depth > 0 then Buffer.add_char b c
      | _ -> Buffer.add_char b c
    done;
    Some (PdfString (Buffer.contents b))
  end

(** Parse a hex string: <48656C6C6F> *)
let parse_hex_string ps =
  if ps.pos >= ps.len || Bytes.get ps.buf ps.pos <> '<' then None
  else begin
    ps.pos <- ps.pos + 1;
    let b = Buffer.create 32 in
    let hi = ref (-1) in
    while ps.pos < ps.len && Bytes.get ps.buf ps.pos <> '>' do
      let c = Bytes.get ps.buf ps.pos in
      ps.pos <- ps.pos + 1;
      if not (is_whitespace c) then begin
        let nibble =
          if c >= '0' && c <= '9' then Char.code c - Char.code '0'
          else if c >= 'a' && c <= 'f' then Char.code c - Char.code 'a' + 10
          else if c >= 'A' && c <= 'F' then Char.code c - Char.code 'A' + 10
          else 0
        in
        if !hi < 0 then hi := nibble
        else begin
          Buffer.add_char b (Char.chr ((!hi lsl 4) lor nibble));
          hi := -1
        end
      end
    done;
    if !hi >= 0 then Buffer.add_char b (Char.chr (!hi lsl 4));
    if ps.pos < ps.len then ps.pos <- ps.pos + 1; (* skip '>' *)
    Some (PdfString (Buffer.contents b))
  end

(** Parse a single PDF value. Recursive for dicts and arrays. *)
let rec parse_value ps =
  ps_skip_whitespace ps;
  if ps.pos >= ps.len then None
  else
    let c = Bytes.get ps.buf ps.pos in
    match c with
    | '/' -> (* Name *)
        begin match parse_name ps with
        | Some n -> Some (PdfName n)
        | None -> None
        end
    | '(' -> (* Literal string *)
        parse_literal_string ps
    | '<' ->
        if ps.pos + 1 < ps.len && Bytes.get ps.buf (ps.pos + 1) = '<' then
          (* Dictionary *)
          parse_dict ps
        else
          (* Hex string *)
          parse_hex_string ps
    | '[' -> (* Array *)
        ps.pos <- ps.pos + 1;
        let items = ref [] in
        let stop = ref false in
        while not !stop do
          ps_skip_whitespace ps;
          if ps.pos >= ps.len then stop := true
          else if Bytes.get ps.buf ps.pos = ']' then begin
            ps.pos <- ps.pos + 1;
            stop := true
          end else
            match parse_value ps with
            | Some v -> items := v :: !items
            | None -> stop := true
        done;
        Some (PdfArray (List.rev !items))
    | 't' when ps_match_keyword ps "true" -> Some (PdfBool true)
    | 'f' when ps_match_keyword ps "false" -> Some (PdfBool false)
    | 'n' when ps_match_keyword ps "null" -> Some PdfNull
    | c when is_digit c || c = '-' || c = '+' || c = '.' ->
        (* Number — could be int, float, or start of indirect ref "N G R" *)
        let saved_pos = ps.pos in
        begin match parse_number ps with
        | Some (PdfInt n) ->
            (* Check for "G R" pattern = indirect ref *)
            let saved2 = ps.pos in
            ps_skip_whitespace ps;
            let saved3 = ps.pos in
            begin match parse_number ps with
            | Some (PdfInt g) ->
                ps_skip_whitespace ps;
                if ps.pos < ps.len && Bytes.get ps.buf ps.pos = 'R' then begin
                  ps.pos <- ps.pos + 1;
                  Some (PdfRef (n, g))
                end else begin
                  ps.pos <- saved3;
                  ps.pos <- saved2;
                  Some (PdfInt n)
                end
            | _ ->
                ps.pos <- saved2;
                Some (PdfInt n)
            end
        | Some v -> Some v
        | None -> ps.pos <- saved_pos; None
        end
    | _ -> None

and parse_dict ps =
  if ps.pos + 1 >= ps.len then None
  else begin
    ps.pos <- ps.pos + 2; (* skip << *)
    let entries = ref [] in
    let stop = ref false in
    while not !stop do
      ps_skip_whitespace ps;
      if ps.pos + 1 >= ps.len then stop := true
      else if Bytes.get ps.buf ps.pos = '>' && Bytes.get ps.buf (ps.pos + 1) = '>' then begin
        ps.pos <- ps.pos + 2;
        stop := true
      end else
        match parse_name ps with
        | Some key ->
            begin match parse_value ps with
            | Some value -> entries := (key, value) :: !entries
            | None -> stop := true
            end
        | None -> stop := true
    done;
    Some (PdfDict (List.rev !entries))
  end

(* ══════════════════════════════════════════════════════════════════════
   §3  Xref Table Parser
   ══════════════════════════════════════════════════════════════════════ *)

(** Find startxref position by scanning backwards from EOF. *)
let find_startxref (buf : bytes) : int option =
  let len = Bytes.length buf in
  let search_start = max 0 (len - 1024) in
  let keyword = "startxref" in
  let klen = String.length keyword in
  let result = ref None in
  for i = search_start to len - klen - 1 do
    if !result = None && Bytes.sub_string buf i klen = keyword then begin
      (* Skip whitespace after keyword *)
      let j = ref (i + klen) in
      while !j < len && is_whitespace (Bytes.get buf !j) do incr j done;
      (* Read number *)
      let start = !j in
      while !j < len && is_digit (Bytes.get buf !j) do incr j done;
      if !j > start then
        try result := Some (int_of_string (Bytes.sub_string buf start (!j - start)))
        with Failure _ -> ()
    end
  done;
  !result

(** Parse a standard xref table starting at [pos].
    Returns (object_offsets, trailer_dict). *)
let parse_xref_table (buf : bytes) (pos : int) :
    ((int, int) Hashtbl.t * (string * pdf_value) list) option =
  let ps = ps_of_bytes buf in
  ps.pos <- pos;
  (* Expect "xref" keyword *)
  ps_skip_whitespace ps;
  if not (ps_match_keyword ps "xref") then None
  else begin
    let offsets = Hashtbl.create 64 in
    let finished = ref false in
    while not !finished do
      ps_skip_whitespace ps;
      if ps.pos >= ps.len then finished := true
      else if Bytes.get ps.buf ps.pos = 't' then
        (* trailer keyword *)
        finished := true
      else begin
        (* Read subsection: first_obj count *)
        match parse_number ps with
        | Some (PdfInt first_obj) ->
            ps_skip_whitespace ps;
            begin match parse_number ps with
            | Some (PdfInt count) ->
                for i = 0 to count - 1 do
                  ps_skip_whitespace ps;
                  (* Each entry: 10-digit offset, 5-digit gen, 'n'/'f' *)
                  if ps.pos + 20 <= ps.len then begin
                    let offset_str = Bytes.sub_string ps.buf ps.pos 10 in
                    ps.pos <- ps.pos + 11; (* skip offset + space *)
                    let _gen_str = Bytes.sub_string ps.buf ps.pos 5 in
                    ps.pos <- ps.pos + 6; (* skip gen + space *)
                    let flag = Bytes.get ps.buf ps.pos in
                    ps.pos <- ps.pos + 1;
                    (* Skip trailing whitespace (CR, LF, or CRLF) *)
                    while ps.pos < ps.len && (Bytes.get ps.buf ps.pos = '\r' || Bytes.get ps.buf ps.pos = '\n') do
                      ps.pos <- ps.pos + 1
                    done;
                    if flag = 'n' then begin
                      try
                        let off = int_of_string (String.trim offset_str) in
                        if off > 0 then Hashtbl.replace offsets (first_obj + i) off
                      with Failure _ -> ()
                    end
                  end else
                    ps.pos <- ps.len
                done
            | _ -> finished := true
            end
        | _ -> finished := true
      end
    done;
    (* Parse trailer dict *)
    ps_skip_whitespace ps;
    if ps_match_keyword ps "trailer" then begin
      ps_skip_whitespace ps;
      match parse_dict ps with
      | Some (PdfDict entries) -> Some (offsets, entries)
      | _ -> None
    end else
      None
  end

(* ══════════════════════════════════════════════════════════════════════
   §4  Object Reader
   ══════════════════════════════════════════════════════════════════════ *)

(** Read an indirect object at the given byte offset.
    Format: "N G obj ... endobj" *)
let read_object_at (buf : bytes) (offset : int) : pdf_value option =
  let ps = ps_of_bytes buf in
  ps.pos <- offset;
  ps_skip_whitespace ps;
  (* Read "N G obj" *)
  match parse_number ps with
  | Some (PdfInt _obj_num) ->
      ps_skip_whitespace ps;
      begin match parse_number ps with
      | Some (PdfInt _gen) ->
          ps_skip_whitespace ps;
          if ps_match_keyword ps "obj" then begin
            ps_skip_whitespace ps;
            let value = parse_value ps in
            (* Check for stream *)
            ps_skip_whitespace ps;
            match value with
            | Some (PdfDict entries) when ps_match_keyword ps "stream" ->
                (* Skip the newline after "stream" *)
                if ps.pos < ps.len && Bytes.get ps.buf ps.pos = '\r' then
                  ps.pos <- ps.pos + 1;
                if ps.pos < ps.len && Bytes.get ps.buf ps.pos = '\n' then
                  ps.pos <- ps.pos + 1;
                let stream_len =
                  match dict_get "Length" entries with
                  | Some (PdfInt n) -> n
                  | _ -> 0
                in
                let stream_data =
                  if ps.pos + stream_len <= ps.len then
                    Bytes.sub ps.buf ps.pos stream_len
                  else Bytes.empty
                in
                Some (PdfStream (entries, stream_data))
            | _ -> value
          end else None
      | _ -> None
      end
  | _ -> None

(* ══════════════════════════════════════════════════════════════════════
   §5  Document Assembly
   ══════════════════════════════════════════════════════════════════════ *)

let parse_pdf (path : string) : pdf_document option =
  let ic = try Some (open_in_bin path) with Sys_error _ -> None in
  match ic with
  | None -> None
  | Some ic ->
      Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
      let file_len = in_channel_length ic in
      if file_len < 20 then None
      else begin
        let buf = Bytes.create file_len in
        really_input ic buf 0 file_len;
        (* Check PDF header *)
        if not (Bytes.sub_string buf 0 (min 5 file_len) = "%PDF-") then None
        else
          (* Check for encryption — bail out early *)
          match find_startxref buf with
          | None -> None
          | Some xref_pos ->
              match parse_xref_table buf xref_pos with
              | None -> None
              | Some (offsets, trailer) ->
                  (* Check for /Encrypt — refuse encrypted PDFs *)
                  begin match dict_get "Encrypt" trailer with
                  | Some _ -> None
                  | None ->
                      (* Read all objects *)
                      let objects = Hashtbl.create (Hashtbl.length offsets) in
                      Hashtbl.iter (fun obj_num offset ->
                        if offset < file_len then
                          match read_object_at buf offset with
                          | Some v -> Hashtbl.replace objects obj_num v
                          | None -> ()
                      ) offsets;
                      (* Handle /Prev for incremental updates *)
                      begin match dict_get "Prev" trailer with
                      | Some (PdfInt prev_xref) when prev_xref > 0 ->
                          begin match parse_xref_table buf prev_xref with
                          | Some (prev_offsets, _) ->
                              Hashtbl.iter (fun obj_num offset ->
                                if not (Hashtbl.mem objects obj_num) && offset < file_len then
                                  match read_object_at buf offset with
                                  | Some v -> Hashtbl.replace objects obj_num v
                                  | None -> ()
                              ) prev_offsets
                          | None -> ()
                          end
                      | _ -> ()
                      end;
                      Some { objects; trailer }
                  end
      end

(* ══════════════════════════════════════════════════════════════════════
   §6  Resolution and Navigation
   ══════════════════════════════════════════════════════════════════════ *)

let resolve (doc : pdf_document) (v : pdf_value) : pdf_value =
  let rec go depth v =
    if depth > 20 then PdfNull  (* guard against cycles *)
    else match v with
    | PdfRef (n, _) ->
        begin match Hashtbl.find_opt doc.objects n with
        | Some v' -> go (depth + 1) v'
        | None -> PdfNull
        end
    | _ -> v
  in
  go 0 v

let resolve_dict doc v =
  match resolve doc v with
  | PdfDict entries -> Some entries
  | PdfStream (entries, _) -> Some entries
  | _ -> None

let resolve_array doc v =
  match resolve doc v with
  | PdfArray items -> Some items
  | _ -> None

let _resolve_name doc v =
  match resolve doc v with
  | PdfName n -> Some n
  | _ -> None

let resolve_string doc v =
  match resolve doc v with
  | PdfString s -> Some s
  | _ -> None

let _resolve_int doc v =
  match resolve doc v with
  | PdfInt n -> Some n
  | _ -> None

(* ══════════════════════════════════════════════════════════════════════
   §7  Catalog & Page Tree
   ══════════════════════════════════════════════════════════════════════ *)

let get_catalog (doc : pdf_document) : (string * pdf_value) list option =
  match dict_get "Root" doc.trailer with
  | Some root_ref -> resolve_dict doc root_ref
  | None -> None

(** Collect all page objects from the page tree. *)
let collect_pages (doc : pdf_document) : (string * pdf_value) list list =
  let pages = ref [] in
  let rec walk v depth =
    if depth > 50 then ()  (* guard *)
    else
      match resolve_dict doc v with
      | Some entries ->
          begin match dict_get "Type" entries with
          | Some (PdfName "Pages") ->
              begin match dict_get "Kids" entries with
              | Some kids ->
                  begin match resolve_array doc kids with
                  | Some items -> List.iter (fun kid -> walk kid (depth + 1)) items
                  | None -> ()
                  end
              | None -> ()
              end
          | Some (PdfName "Page") | _ ->
              pages := entries :: !pages
          end
      | None -> ()
  in
  begin match get_catalog doc with
  | Some cat ->
      begin match dict_get "Pages" cat with
      | Some pages_ref -> walk pages_ref 0
      | None -> ()
      end
  | None -> ()
  end;
  List.rev !pages

(* ══════════════════════════════════════════════════════════════════════
   §8  Structure Tree Inspector
   ══════════════════════════════════════════════════════════════════════ *)

(** Count /Figure structure elements without /Alt text. *)
let count_figures_without_alt (doc : pdf_document) (struct_tree : (string * pdf_value) list) : int =
  let count = ref 0 in
  let rec walk v depth =
    if depth > 100 then ()
    else
      match resolve_dict doc v with
      | Some entries ->
          (* Check if this is a /Figure element *)
          let is_figure =
            match dict_get "S" entries with
            | Some (PdfName "Figure") -> true
            | _ -> false
          in
          if is_figure then begin
            match dict_get "Alt" entries with
            | Some (PdfString s) when String.length s > 0 -> ()
            | _ -> incr count
          end;
          (* Recurse into /K *)
          begin match dict_get "K" entries with
          | Some (PdfArray items) ->
              List.iter (fun item -> walk item (depth + 1)) items
          | Some item -> walk item (depth + 1)
          | None -> ()
          end
      | None -> ()
  in
  begin match dict_get "K" struct_tree with
  | Some (PdfArray items) ->
      List.iter (fun item -> walk item 0) items
  | Some item -> walk item 0
  | None -> ()
  end;
  !count

(* ══════════════════════════════════════════════════════════════════════
   §9  Annotation Inspector
   ══════════════════════════════════════════════════════════════════════ *)

(** Count /Link annotations without /Contents across all pages. *)
let count_links_without_contents (doc : pdf_document)
    (pages : (string * pdf_value) list list) : int =
  let count = ref 0 in
  List.iter (fun page_entries ->
    match dict_get "Annots" page_entries with
    | Some annots_val ->
        begin match resolve_array doc annots_val with
        | Some annots ->
            List.iter (fun annot ->
              match resolve_dict doc annot with
              | Some entries ->
                  let is_link =
                    match dict_get "Subtype" entries with
                    | Some (PdfName "Link") -> true
                    | _ -> false
                  in
                  if is_link then begin
                    match dict_get "Contents" entries with
                    | Some (PdfString s) when String.length s > 0 -> ()
                    | _ -> incr count
                  end
              | None -> ()
            ) annots
        | None -> ()
        end
    | None -> ()
  ) pages;
  !count

(* ══════════════════════════════════════════════════════════════════════
   §10  Font Inspector
   ══════════════════════════════════════════════════════════════════════ *)

(** Extract font info from all pages. *)
let extract_fonts (doc : pdf_document)
    (pages : (string * pdf_value) list list) :
    (string * bool * bool) list =
  let fonts = Hashtbl.create 16 in
  List.iter (fun page_entries ->
    match dict_get "Resources" page_entries with
    | Some res_val ->
        begin match resolve_dict doc res_val with
        | Some res_entries ->
            begin match dict_get "Font" res_entries with
            | Some font_dict_val ->
                begin match resolve_dict doc font_dict_val with
                | Some font_entries ->
                    List.iter (fun (_key, font_ref) ->
                      match resolve_dict doc font_ref with
                      | Some font ->
                          let base_name =
                            match dict_get "BaseFont" font with
                            | Some (PdfName n) -> n
                            | _ -> "Unknown"
                          in
                          if not (Hashtbl.mem fonts base_name) then begin
                            let embedded, subsetted =
                              match dict_get "FontDescriptor" font with
                              | Some fd_val ->
                                  begin match resolve_dict doc fd_val with
                                  | Some fd ->
                                      let has_file =
                                        dict_get "FontFile" fd <> None
                                        || dict_get "FontFile2" fd <> None
                                        || dict_get "FontFile3" fd <> None
                                      in
                                      (* Subsetted fonts have 6-letter prefix + '+' *)
                                      let is_subsetted =
                                        String.length base_name >= 7
                                        && base_name.[6] = '+'
                                        && (let prefix = String.sub base_name 0 6 in
                                            String.uppercase_ascii prefix = prefix)
                                      in
                                      (has_file, is_subsetted)
                                  | None -> (false, false)
                                  end
                              | None -> (false, false)
                            in
                            Hashtbl.replace fonts base_name (embedded, subsetted)
                          end
                      | None -> ()
                    ) font_entries
                | None -> ()
                end
            | None -> ()
            end
        | None -> ()
        end
    | None -> ()
  ) pages;
  Hashtbl.fold (fun name (emb, sub) acc -> (name, emb, sub) :: acc) fonts []

(* ══════════════════════════════════════════════════════════════════════
   §11  ColorSpace Inspector
   ══════════════════════════════════════════════════════════════════════ *)

(** Check for spot colours (Separation / DeviceN) across all pages. *)
let check_spot_colours (doc : pdf_document)
    (pages : (string * pdf_value) list list) : bool * bool =
  let has_spot = ref false in
  let has_spot_vector = ref false in
  List.iter (fun page_entries ->
    match dict_get "Resources" page_entries with
    | Some res_val ->
        begin match resolve_dict doc res_val with
        | Some res_entries ->
            begin match dict_get "ColorSpace" res_entries with
            | Some cs_val ->
                begin match resolve_dict doc cs_val with
                | Some cs_entries ->
                    List.iter (fun (_key, cs_ref) ->
                      match resolve doc cs_ref with
                      | PdfArray (PdfName "Separation" :: _) ->
                          has_spot := true
                      | PdfArray (PdfName "DeviceN" :: _) ->
                          has_spot := true;
                          has_spot_vector := true
                      | _ -> ()
                    ) cs_entries
                | None ->
                    (* Could be an array directly *)
                    match resolve doc cs_val with
                    | PdfArray (PdfName "Separation" :: _) ->
                        has_spot := true
                    | PdfArray (PdfName "DeviceN" :: _) ->
                        has_spot := true;
                        has_spot_vector := true
                    | _ -> ()
                end
            | None -> ()
            end
        | None -> ()
        end
    | None -> ()
  ) pages;
  (!has_spot, !has_spot_vector)

(* ══════════════════════════════════════════════════════════════════════
   §12  Stream Compression Inspector
   ══════════════════════════════════════════════════════════════════════ *)

(** Check if all stream objects have /Filter (compressed). *)
let check_streams_compressed (doc : pdf_document) : bool =
  let all_compressed = ref true in
  let has_streams = ref false in
  Hashtbl.iter (fun _obj_num v ->
    match v with
    | PdfStream (entries, _) ->
        has_streams := true;
        begin match dict_get "Filter" entries with
        | Some _ -> ()
        | None -> all_compressed := false
        end
    | _ -> ()
  ) doc.objects;
  if !has_streams then !all_compressed else true

(* ══════════════════════════════════════════════════════════════════════
   §13  Outline / Bookmark Text
   ══════════════════════════════════════════════════════════════════════ *)

let _extract_outline_texts (doc : pdf_document)
    (cat : (string * pdf_value) list) : string list =
  let texts = ref [] in
  let rec walk v depth =
    if depth > 200 then ()
    else
      match resolve_dict doc v with
      | Some entries ->
          begin match dict_get "Title" entries with
          | Some (PdfString t) -> texts := t :: !texts
          | _ -> ()
          end;
          (* Follow /First for children *)
          begin match dict_get "First" entries with
          | Some child -> walk child (depth + 1)
          | None -> ()
          end;
          (* Follow /Next for siblings *)
          begin match dict_get "Next" entries with
          | Some sibling -> walk sibling (depth + 1)
          | None -> ()
          end
      | None -> ()
  in
  begin match dict_get "Outlines" cat with
  | Some outlines_ref -> walk outlines_ref 0
  | None -> ()
  end;
  List.rev !texts

(* ══════════════════════════════════════════════════════════════════════
   §14  Page Labels
   ══════════════════════════════════════════════════════════════════════ *)

let count_page_labels (doc : pdf_document)
    (cat : (string * pdf_value) list) : int =
  match dict_get "PageLabels" cat with
  | Some pl_ref ->
      begin match resolve_dict doc pl_ref with
      | Some pl_entries ->
          begin match dict_get "Nums" pl_entries with
          | Some nums_val ->
              begin match resolve_array doc nums_val with
              | Some items -> List.length items / 2  (* pairs of page_num, label_dict *)
              | None -> 0
              end
          | None -> 0
          end
      | None -> 0
      end
  | None -> 0

(* ══════════════════════════════════════════════════════════════════════
   §15  High-Level Info Extraction
   ══════════════════════════════════════════════════════════════════════ *)

let read_pdf_info (path : string) : pdf_info option =
  match parse_pdf path with
  | None -> None
  | Some doc ->
      match get_catalog doc with
      | None -> None
      | Some cat ->
          let pages = collect_pages doc in
          let page_count = List.length pages in

          (* StructTreeRoot *)
          let has_struct_tree_root =
            match dict_get "StructTreeRoot" cat with
            | Some _ -> true
            | None -> false
          in

          (* MarkInfo *)
          let has_mark_info =
            match dict_get "MarkInfo" cat with
            | Some mi_ref ->
                begin match resolve_dict doc mi_ref with
                | Some entries ->
                    begin match dict_get "Marked" entries with
                    | Some (PdfBool true) -> true
                    | _ -> false
                    end
                | None -> false
                end
            | None -> false
          in

          (* Figures without Alt *)
          let figures_without_alt =
            match dict_get "StructTreeRoot" cat with
            | Some st_ref ->
                begin match resolve_dict doc st_ref with
                | Some st -> count_figures_without_alt doc st
                | None -> 0
                end
            | None -> 0
          in

          (* Links without Contents *)
          let links_without_contents =
            count_links_without_contents doc pages
          in

          (* Lang *)
          let lang =
            match dict_get "Lang" cat with
            | Some v -> resolve_string doc v
            | None -> None
          in

          (* Fonts *)
          let fonts = extract_fonts doc pages in

          (* Page labels *)
          let page_label_count = count_page_labels doc cat in

          (* Spot colours *)
          let has_spot_colour, has_spot_colour_vector =
            check_spot_colours doc pages
          in

          (* Stream compression *)
          let streams_all_compressed = check_streams_compressed doc in

          Some {
            has_struct_tree_root;
            has_mark_info;
            figures_without_alt;
            links_without_contents;
            lang;
            fonts;
            page_label_count;
            page_count;
            has_spot_colour;
            has_spot_colour_vector;
            streams_all_compressed;
          }
