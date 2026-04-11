(* ══════════════════════════════════════════════════════════════════════
   Test_binary_gen — programmatic binary fixture generators

   Generates minimal valid PNG, JPEG, PDF, and TTF files with
   configurable properties for testing readers and validators.
   ══════════════════════════════════════════════════════════════════════ *)

(* ── Helpers ───────────────────────────────────────────────────────── *)

let put_u32_be buf off v =
  Bytes.set buf off (Char.chr ((v lsr 24) land 0xFF));
  Bytes.set buf (off + 1) (Char.chr ((v lsr 16) land 0xFF));
  Bytes.set buf (off + 2) (Char.chr ((v lsr 8) land 0xFF));
  Bytes.set buf (off + 3) (Char.chr (v land 0xFF))

let put_u16_be buf off v =
  Bytes.set buf off (Char.chr ((v lsr 8) land 0xFF));
  Bytes.set buf (off + 1) (Char.chr (v land 0xFF))

let write_to_temp_file (data : bytes) (suffix : string) : string =
  let path = Filename.temp_file "test_bin_" suffix in
  let oc = open_out_bin path in
  output_bytes oc data;
  close_out oc;
  path

(* ── CRC-32 for PNG ────────────────────────────────────────────────── *)

let crc_table =
  let tbl = Array.make 256 0l in
  for i = 0 to 255 do
    let c = ref (Int32.of_int i) in
    for _ = 0 to 7 do
      if Int32.logand !c 1l = 1l then
        c := Int32.logxor (Int32.shift_right_logical !c 1) 0xEDB88320l
      else c := Int32.shift_right_logical !c 1
    done;
    tbl.(i) <- !c
  done;
  tbl

let crc32 (data : bytes) (off : int) (len : int) : int32 =
  let c = ref 0xFFFFFFFFl in
  for i = off to off + len - 1 do
    let idx =
      Int32.to_int (Int32.logand (Int32.logxor !c (Int32.of_int (Char.code (Bytes.get data i)))) 0xFFl)
    in
    c := Int32.logxor (Int32.shift_right_logical !c 8) crc_table.(idx)
  done;
  Int32.logxor !c 0xFFFFFFFFl

(* ── PNG generation ────────────────────────────────────────────────── *)

type png_opts = {
  width : int;
  height : int;
  color_type : int;  (* 0,2,3,4,6 *)
  bit_depth : int;
  dpi : int;         (* 0 = no pHYs *)
  has_trns : bool;
  has_iccp : bool;
  iccp_name : string;
  has_srgb : bool;
  plte_size : int;   (* 0 = no PLTE *)
}

let default_png_opts = {
  width = 100; height = 100; color_type = 2; bit_depth = 8;
  dpi = 0; has_trns = false; has_iccp = false; iccp_name = "";
  has_srgb = false; plte_size = 0;
}

let make_png_chunk (ctype : string) (data : bytes) : bytes =
  let dlen = Bytes.length data in
  let chunk = Bytes.create (4 + 4 + dlen + 4) in
  put_u32_be chunk 0 dlen;
  Bytes.blit_string ctype 0 chunk 4 4;
  Bytes.blit data 0 chunk 8 dlen;
  let crc = crc32 chunk 4 (4 + dlen) in
  let crc_off = 8 + dlen in
  Bytes.set chunk crc_off (Char.chr (Int32.to_int (Int32.shift_right_logical crc 24) land 0xFF));
  Bytes.set chunk (crc_off + 1) (Char.chr (Int32.to_int (Int32.shift_right_logical crc 16) land 0xFF));
  Bytes.set chunk (crc_off + 2) (Char.chr (Int32.to_int (Int32.shift_right_logical crc 8) land 0xFF));
  Bytes.set chunk (crc_off + 3) (Char.chr (Int32.to_int crc land 0xFF));
  chunk

let make_png (opts : png_opts) : bytes =
  let chunks = ref [] in

  (* IHDR *)
  let ihdr = Bytes.create 13 in
  put_u32_be ihdr 0 opts.width;
  put_u32_be ihdr 4 opts.height;
  Bytes.set ihdr 8 (Char.chr opts.bit_depth);
  Bytes.set ihdr 9 (Char.chr opts.color_type);
  Bytes.set ihdr 10 '\000'; (* compression *)
  Bytes.set ihdr 11 '\000'; (* filter *)
  Bytes.set ihdr 12 '\000'; (* interlace *)
  chunks := make_png_chunk "IHDR" ihdr :: !chunks;

  (* Optional PLTE *)
  if opts.plte_size > 0 then begin
    let plte = Bytes.create (opts.plte_size * 3) in
    for i = 0 to opts.plte_size - 1 do
      Bytes.set plte (i * 3) (Char.chr (i land 0xFF));
      Bytes.set plte (i * 3 + 1) (Char.chr ((i * 17) land 0xFF));
      Bytes.set plte (i * 3 + 2) (Char.chr ((i * 37) land 0xFF))
    done;
    chunks := make_png_chunk "PLTE" plte :: !chunks
  end;

  (* Optional sRGB *)
  if opts.has_srgb then begin
    let srgb = Bytes.create 1 in
    Bytes.set srgb 0 '\000';
    chunks := make_png_chunk "sRGB" srgb :: !chunks
  end;

  (* Optional iCCP *)
  if opts.has_iccp then begin
    let name = opts.iccp_name in
    let nlen = String.length name in
    let data = Bytes.create (nlen + 2 + 10) in
    Bytes.blit_string name 0 data 0 nlen;
    Bytes.set data nlen '\000';  (* null terminator *)
    Bytes.set data (nlen + 1) '\000';  (* compression method *)
    (* Fake compressed ICC data *)
    for i = 0 to 9 do
      Bytes.set data (nlen + 2 + i) (Char.chr (i + 1))
    done;
    chunks := make_png_chunk "iCCP" data :: !chunks
  end;

  (* Optional tRNS *)
  if opts.has_trns then begin
    let trns = Bytes.create 6 in
    put_u16_be trns 0 0;
    put_u16_be trns 2 0;
    put_u16_be trns 4 0;
    chunks := make_png_chunk "tRNS" trns :: !chunks
  end;

  (* Optional pHYs *)
  if opts.dpi > 0 then begin
    let phys = Bytes.create 9 in
    let ppm = int_of_float (float opts.dpi /. 0.0254) in
    put_u32_be phys 0 ppm;
    put_u32_be phys 4 ppm;
    Bytes.set phys 8 '\001';  (* unit = meter *)
    chunks := make_png_chunk "pHYs" phys :: !chunks
  end;

  (* Minimal IDAT (empty compressed data: zlib header + empty block) *)
  let idat = Bytes.of_string "\x78\x01\x01\x00\x00\xFF\xFF\x00\x00\x00\x01" in
  chunks := make_png_chunk "IDAT" idat :: !chunks;

  (* IEND *)
  chunks := make_png_chunk "IEND" Bytes.empty :: !chunks;

  (* Assemble *)
  let magic = Bytes.of_string "\137PNG\r\n\026\n" in
  let all_chunks = List.rev !chunks in
  let total_len =
    8 + List.fold_left (fun acc c -> acc + Bytes.length c) 0 all_chunks
  in
  let result = Bytes.create total_len in
  Bytes.blit magic 0 result 0 8;
  let pos = ref 8 in
  List.iter (fun c ->
    let clen = Bytes.length c in
    Bytes.blit c 0 result !pos clen;
    pos := !pos + clen
  ) all_chunks;
  result

(* ── JPEG generation ───────────────────────────────────────────────── *)

type jpeg_opts = {
  j_width : int;
  j_height : int;
  j_components : int;  (* 1, 3, or 4 *)
  j_dpi : int;         (* 0 = no JFIF DPI *)
  j_has_icc : bool;
  j_icc_color_space : string;  (* "RGB ", "CMYK", "GRAY" *)
  j_adobe_transform : int;     (* -1 = no Adobe marker *)
}

let default_jpeg_opts = {
  j_width = 100; j_height = 100; j_components = 3;
  j_dpi = 0; j_has_icc = false; j_icc_color_space = "RGB ";
  j_adobe_transform = -1;
}

let make_jpeg (opts : jpeg_opts) : bytes =
  let parts = ref [] in
  let add b = parts := b :: !parts in

  (* SOI *)
  add (Bytes.of_string "\xFF\xD8");

  (* APP0 JFIF *)
  if opts.j_dpi > 0 then begin
    let app0 = Bytes.create 18 in
    Bytes.set app0 0 '\xFF';
    Bytes.set app0 1 '\xE0';
    put_u16_be app0 2 16;  (* segment length *)
    Bytes.blit_string "JFIF\000" 0 app0 4 5;
    Bytes.set app0 9 '\001';  (* version major *)
    Bytes.set app0 10 '\001'; (* version minor *)
    Bytes.set app0 11 '\001'; (* units = DPI *)
    put_u16_be app0 12 opts.j_dpi;
    put_u16_be app0 14 opts.j_dpi;
    Bytes.set app0 16 '\000'; (* thumbnail w *)
    Bytes.set app0 17 '\000'; (* thumbnail h *)
    add app0
  end;

  (* APP2 ICC_PROFILE *)
  if opts.j_has_icc then begin
    (* ICC header is at least 128 bytes *)
    let icc_header = Bytes.make 128 '\000' in
    (* Color space at offset 16 *)
    let cs = opts.j_icc_color_space in
    if String.length cs >= 4 then
      Bytes.blit_string cs 0 icc_header 16 4;
    let prefix = "ICC_PROFILE\000\001\001" in
    let plen = String.length prefix in
    let seg_len = 2 + plen + 128 in
    let app2 = Bytes.create (2 + seg_len) in
    Bytes.set app2 0 '\xFF';
    Bytes.set app2 1 '\xE2';
    put_u16_be app2 2 seg_len;
    Bytes.blit_string prefix 0 app2 4 plen;
    Bytes.blit icc_header 0 app2 (4 + plen) 128;
    add app2
  end;

  (* APP14 Adobe *)
  if opts.j_adobe_transform >= 0 then begin
    let app14 = Bytes.create 16 in
    Bytes.set app14 0 '\xFF';
    Bytes.set app14 1 '\xEE';
    put_u16_be app14 2 14;
    Bytes.blit_string "Adobe" 0 app14 4 5;
    Bytes.set app14 9 '\000';
    Bytes.set app14 10 '\000';
    Bytes.set app14 11 '\000';
    Bytes.set app14 12 '\000';
    Bytes.set app14 13 '\000';
    Bytes.set app14 14 '\000';
    Bytes.set app14 15 (Char.chr opts.j_adobe_transform);
    add app14
  end;

  (* SOF0 *)
  let sof_len = 8 + opts.j_components * 3 in
  let sof = Bytes.create (2 + 2 + sof_len - 2) in
  Bytes.set sof 0 '\xFF';
  Bytes.set sof 1 '\xC0';
  put_u16_be sof 2 sof_len;
  Bytes.set sof 4 '\x08';  (* precision *)
  put_u16_be sof 5 opts.j_height;
  put_u16_be sof 7 opts.j_width;
  Bytes.set sof 9 (Char.chr opts.j_components);
  for i = 0 to opts.j_components - 1 do
    let off = 10 + i * 3 in
    if off + 2 < Bytes.length sof then begin
      Bytes.set sof off (Char.chr (i + 1));       (* component id *)
      Bytes.set sof (off + 1) '\x11';             (* sampling factor *)
      Bytes.set sof (off + 2) (Char.chr 0)        (* quant table *)
    end
  done;
  add sof;

  (* EOI *)
  add (Bytes.of_string "\xFF\xD9");

  (* Assemble *)
  let all = List.rev !parts in
  let total = List.fold_left (fun acc b -> acc + Bytes.length b) 0 all in
  let result = Bytes.create total in
  let pos = ref 0 in
  List.iter (fun b ->
    let blen = Bytes.length b in
    Bytes.blit b 0 result !pos blen;
    pos := !pos + blen
  ) all;
  result

(* ── Minimal PDF generation ────────────────────────────────────────── *)

type pdf_opts = {
  has_struct_tree : bool;
  has_mark_info : bool;
  has_lang : string option;
  figures_without_alt : int;
  links_without_contents : int;
  fonts : (string * bool * bool) list;  (* name, embedded, subsetted *)
  has_spot_colour : bool;
  has_spot_colour_vector : bool;
  streams_compressed : bool;
}

let default_pdf_opts = {
  has_struct_tree = false; has_mark_info = false; has_lang = None;
  figures_without_alt = 0; links_without_contents = 0;
  fonts = []; has_spot_colour = false; has_spot_colour_vector = false;
  streams_compressed = true;
}

let make_pdf (opts : pdf_opts) : bytes =
  let buf = Buffer.create 4096 in
  let objs = ref [] in
  let next_obj = ref 1 in
  let add_obj content =
    let n = !next_obj in
    incr next_obj;
    let off = Buffer.length buf in
    Buffer.add_string buf (Printf.sprintf "%d 0 obj\n%s\nendobj\n" n content);
    objs := (n, off) :: !objs;
    n
  in

  Buffer.add_string buf "%PDF-1.7\n";

  (* Catalog (obj 1) — placeholder, will be rewritten *)
  let catalog_off = Buffer.length buf in
  let catalog_num = !next_obj in
  incr next_obj;
  objs := (catalog_num, catalog_off) :: !objs;

  (* Build catalog dict parts *)
  let cat_parts = ref ["/Type /Catalog"] in

  (* Pages object *)
  let pages_num = !next_obj in
  let page_num = pages_num + 1 in

  (* StructTreeRoot *)
  let struct_tree_num =
    if opts.has_struct_tree then begin
      let st_content = Buffer.create 128 in
      Buffer.add_string st_content "<< /Type /StructTreeRoot /K [";
      for _ = 1 to opts.figures_without_alt do
        Buffer.add_string st_content " << /Type /StructElem /S /Figure >> "
      done;
      Buffer.add_string st_content "] >>";
      Some (add_obj (Buffer.contents st_content))
    end else None
  in
  begin match struct_tree_num with
  | Some n -> cat_parts := Printf.sprintf "/StructTreeRoot %d 0 R" n :: !cat_parts
  | None -> ()
  end;

  if opts.has_mark_info then
    cat_parts := "/MarkInfo << /Marked true >>" :: !cat_parts;

  begin match opts.has_lang with
  | Some lang -> cat_parts := Printf.sprintf "/Lang (%s)" lang :: !cat_parts
  | None -> ()
  end;

  cat_parts := Printf.sprintf "/Pages %d 0 R" pages_num :: !cat_parts;

  (* Write catalog *)
  let cat_content = Printf.sprintf "<< %s >>" (String.concat " " !cat_parts) in
  let cat_str = Printf.sprintf "%d 0 obj\n%s\nendobj\n" catalog_num cat_content in
  (* Replace placeholder *)
  let buf_str = Buffer.contents buf in
  Buffer.clear buf;
  Buffer.add_string buf buf_str;
  (* Actually we appended objects after catalog_off, so just rewrite *)
  (* Simpler approach: build all objects then assemble *)
  ignore cat_str;

  (* Reset and rebuild properly *)
  Buffer.clear buf;
  objs := [];
  next_obj := 1;
  Buffer.add_string buf "%PDF-1.7\n";

  (* Build objects in order *)
  (* Obj 1: Catalog *)
  let cat_buf = Buffer.create 256 in
  Buffer.add_string cat_buf "<< /Type /Catalog";

  (* Obj 2: Pages *)
  let pages_obj_num = 2 in
  let page_obj_num = 3 in
  Buffer.add_string cat_buf (Printf.sprintf " /Pages %d 0 R" pages_obj_num);

  (* Prepare extra objects we'll need *)
  let extra_objs = ref [] in
  let alloc_extra content =
    let n = 4 + List.length !extra_objs in
    extra_objs := (n, content) :: !extra_objs;
    n
  in

  (* StructTreeRoot *)
  if opts.has_struct_tree then begin
    let st_buf = Buffer.create 128 in
    Buffer.add_string st_buf "<< /Type /StructTreeRoot /K [";
    for _ = 1 to opts.figures_without_alt do
      Buffer.add_string st_buf " << /Type /StructElem /S /Figure >>"
    done;
    Buffer.add_string st_buf " ] >>";
    let n = alloc_extra (Buffer.contents st_buf) in
    Buffer.add_string cat_buf (Printf.sprintf " /StructTreeRoot %d 0 R" n)
  end;

  if opts.has_mark_info then
    Buffer.add_string cat_buf " /MarkInfo << /Marked true >>";

  begin match opts.has_lang with
  | Some lang ->
      Buffer.add_string cat_buf (Printf.sprintf " /Lang (%s)" lang)
  | None -> ()
  end;

  Buffer.add_string cat_buf " >>";
  let cat_content = Buffer.contents cat_buf in

  (* Build resource dict *)
  let res_buf = Buffer.create 256 in
  Buffer.add_string res_buf "<< ";

  (* Fonts in resources *)
  if opts.fonts <> [] then begin
    Buffer.add_string res_buf "/Font << ";
    List.iteri (fun i (name, embedded, subsetted) ->
      let font_name =
        if subsetted then "ABCDEF+" ^ name else name
      in
      let fd_content =
        if embedded then
          Printf.sprintf "<< /Type /FontDescriptor /FontName /%s /FontFile2 << /Length 0 >> >>" font_name
        else
          Printf.sprintf "<< /Type /FontDescriptor /FontName /%s >>" font_name
      in
      let fd_num = alloc_extra fd_content in
      let font_content =
        Printf.sprintf "<< /Type /Font /BaseFont /%s /FontDescriptor %d 0 R >>" font_name fd_num
      in
      let f_num = alloc_extra font_content in
      Buffer.add_string res_buf (Printf.sprintf "/F%d %d 0 R " i f_num)
    ) opts.fonts;
    Buffer.add_string res_buf ">> "
  end;

  (* ColorSpace in resources *)
  if opts.has_spot_colour then begin
    Buffer.add_string res_buf "/ColorSpace << ";
    Buffer.add_string res_buf "/CS1 [/Separation /PANTONE#20Red /DeviceCMYK << >>] ";
    if opts.has_spot_colour_vector then
      Buffer.add_string res_buf "/CS2 [/DeviceN [/Cyan /Magenta] /DeviceCMYK << >>] ";
    Buffer.add_string res_buf ">> "
  end;

  Buffer.add_string res_buf ">>";
  let res_content = Buffer.contents res_buf in
  let res_num = alloc_extra res_content in

  (* Build annotations *)
  let annots_str =
    if opts.links_without_contents > 0 then begin
      let annot_nums = ref [] in
      for _ = 1 to opts.links_without_contents do
        let n = alloc_extra "<< /Type /Annot /Subtype /Link /Rect [0 0 100 100] >>" in
        annot_nums := n :: !annot_nums
      done;
      let refs = List.map (fun n -> Printf.sprintf "%d 0 R" n) (List.rev !annot_nums) in
      Printf.sprintf " /Annots [%s]" (String.concat " " refs)
    end else ""
  in

  (* Stream object for compression test *)
  let stream_num =
    if not opts.streams_compressed then
      let n = alloc_extra "" in
      ignore n;  (* will be written as stream *)
      Some (List.length !extra_objs + 3)
    else None
  in
  ignore stream_num;

  (* Now write all objects *)
  (* Obj 1: Catalog *)
  let off1 = Buffer.length buf in
  Buffer.add_string buf (Printf.sprintf "1 0 obj\n%s\nendobj\n" cat_content);

  (* Obj 2: Pages *)
  let off2 = Buffer.length buf in
  Buffer.add_string buf
    (Printf.sprintf "2 0 obj\n<< /Type /Pages /Kids [%d 0 R] /Count 1 >>\nendobj\n" page_obj_num);

  (* Obj 3: Page *)
  let off3 = Buffer.length buf in
  Buffer.add_string buf
    (Printf.sprintf "3 0 obj\n<< /Type /Page /Parent %d 0 R /Resources %d 0 R%s >>\nendobj\n"
       pages_obj_num res_num annots_str);

  let obj_offsets = ref [(1, off1); (2, off2); (3, off3)] in

  (* Write extra objects *)
  List.iter (fun (n, content) ->
    let off = Buffer.length buf in
    if not opts.streams_compressed && content = "" then begin
      (* Write as uncompressed stream *)
      Buffer.add_string buf (Printf.sprintf "%d 0 obj\n<< /Length 5 >>\nstream\nhello\nendstream\nendobj\n" n)
    end else
      Buffer.add_string buf (Printf.sprintf "%d 0 obj\n%s\nendobj\n" n content);
    obj_offsets := (n, off) :: !obj_offsets
  ) (List.rev !extra_objs);

  (* Xref table *)
  let xref_off = Buffer.length buf in
  let max_obj = List.fold_left (fun mx (n, _) -> max mx n) 0 !obj_offsets in
  Buffer.add_string buf "xref\n";
  Buffer.add_string buf (Printf.sprintf "0 %d\n" (max_obj + 1));
  Buffer.add_string buf "0000000000 65535 f \n";
  for i = 1 to max_obj do
    match List.assoc_opt i !obj_offsets with
    | Some off -> Buffer.add_string buf (Printf.sprintf "%010d 00000 n \n" off)
    | None -> Buffer.add_string buf "0000000000 00000 f \n"
  done;

  (* Trailer *)
  Buffer.add_string buf "trailer\n";
  Buffer.add_string buf (Printf.sprintf "<< /Size %d /Root 1 0 R >>\n" (max_obj + 1));
  Buffer.add_string buf (Printf.sprintf "startxref\n%d\n%%%%EOF\n" xref_off);

  Bytes.of_string (Buffer.contents buf)

(* ── Minimal TTF generation ────────────────────────────────────────── *)

let make_ttf ~(has_cjk : bool) : bytes =
  (* Build a minimal TTF with just an offset table and cmap *)
  let buf = Buffer.create 512 in

  (* Offset table: 1 table (cmap) *)
  let header = Bytes.create 12 in
  put_u32_be header 0 0x00010000;  (* sfnt version *)
  put_u16_be header 4 1;           (* numTables *)
  put_u16_be header 6 16;          (* searchRange *)
  put_u16_be header 8 0;           (* entrySelector *)
  put_u16_be header 10 16;         (* rangeShift *)
  Buffer.add_bytes buf header;

  (* Table record for cmap *)
  let cmap_offset = 12 + 16 in  (* after header + 1 table record *)
  let table_rec = Bytes.create 16 in
  Bytes.blit_string "cmap" 0 table_rec 0 4;
  put_u32_be table_rec 4 0;           (* checksum *)
  put_u32_be table_rec 8 cmap_offset; (* offset *)

  (* Build cmap with format 12 *)
  let cmap_buf = Buffer.create 256 in
  let cmap_header = Bytes.create 4 in
  put_u16_be cmap_header 0 0;  (* version *)
  put_u16_be cmap_header 2 1;  (* numTables *)
  Buffer.add_bytes cmap_buf cmap_header;

  (* Encoding record: platform 3, encoding 10 (full Unicode) *)
  let enc_rec = Bytes.create 8 in
  put_u16_be enc_rec 0 3;   (* platformID *)
  put_u16_be enc_rec 2 10;  (* encodingID *)
  put_u32_be enc_rec 4 12;  (* offset to subtable from cmap start *)
  Buffer.add_bytes cmap_buf enc_rec;

  (* Format 12 subtable *)
  let groups =
    if has_cjk then
      (* ASCII + CJK Unified Ideographs *)
      [ (0x0020, 0x007E); (0x4E00, 0x9FFF) ]
    else
      (* ASCII only *)
      [ (0x0020, 0x007E) ]
  in
  let n_groups = List.length groups in
  let subtable_len = 16 + n_groups * 12 in
  let subtable = Bytes.create subtable_len in
  put_u16_be subtable 0 12;            (* format *)
  put_u16_be subtable 2 0;             (* reserved *)
  put_u32_be subtable 4 subtable_len;  (* length *)
  put_u32_be subtable 8 0;             (* language *)
  put_u32_be subtable 12 n_groups;     (* numGroups *)
  List.iteri (fun i (start_code, end_code) ->
    let off = 16 + i * 12 in
    put_u32_be subtable off start_code;
    put_u32_be subtable (off + 4) end_code;
    put_u32_be subtable (off + 8) (start_code + 1)  (* startGlyphID *)
  ) groups;
  Buffer.add_bytes cmap_buf subtable;

  let cmap_data = Buffer.contents cmap_buf in
  put_u32_be table_rec 12 (String.length cmap_data);  (* length *)
  Buffer.add_bytes buf table_rec;

  (* Write cmap *)
  Buffer.add_string buf cmap_data;

  Bytes.of_string (Buffer.contents buf)
