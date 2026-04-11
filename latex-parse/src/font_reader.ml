(* ══════════════════════════════════════════════════════════════════════
   Font_reader — TrueType/OpenType cmap table reader

   Reads the font's character mapping table to check glyph coverage
   for CJK Unified Ideographs (U+4E00–U+9FFF).  Supports format 4
   (BMP) and format 12 (full Unicode) subtables.
   ══════════════════════════════════════════════════════════════════════ *)

(* ── Binary helpers ────────────────────────────────────────────────── *)

let read_u16_be (buf : bytes) (off : int) : int =
  (Char.code (Bytes.get buf off) lsl 8)
  lor Char.code (Bytes.get buf (off + 1))

let read_u32_be (buf : bytes) (off : int) : int =
  (Char.code (Bytes.get buf off) lsl 24)
  lor (Char.code (Bytes.get buf (off + 1)) lsl 16)
  lor (Char.code (Bytes.get buf (off + 2)) lsl 8)
  lor Char.code (Bytes.get buf (off + 3))

(* CJK Unified Ideographs range *)
let _cjk_start = 0x4E00
let _cjk_end = 0x9FFF

(* We check a sample of codepoints rather than all 20,992.
   If at least 80% of samples are covered, we declare coverage. *)
let cjk_sample_points = [
  0x4E00; 0x4E2D; 0x4EBA; 0x5927; 0x5B66;
  0x65E5; 0x672C; 0x7684; 0x8005; 0x9053;
  0x5E73; 0x6210; 0x7406; 0x8BBA; 0x9AD8;
  0x6587; 0x5316; 0x79D1; 0x5B9A; 0x884C;
]
let cjk_sample_count = List.length cjk_sample_points
let cjk_coverage_threshold = 0.80

(* ── Cmap format 4 (BMP segments) ──────────────────────────────────── *)

(** Check if codepoint [cp] is covered by a format 4 subtable at [off]. *)
let format4_has_codepoint (buf : bytes) (off : int) (cp : int) : bool =
  let len = Bytes.length buf in
  if cp > 0xFFFF || off + 14 > len then false
  else
    let seg_count = read_u16_be buf (off + 6) / 2 in
    if seg_count <= 0 || off + 14 + seg_count * 8 > len then false
    else
      let end_codes_off = off + 14 in
      let start_codes_off = end_codes_off + seg_count * 2 + 2 in
      let found = ref false in
      for i = 0 to seg_count - 1 do
        if not !found then begin
          let seg_off = i * 2 in
          if end_codes_off + seg_off + 1 < len
             && start_codes_off + seg_off + 1 < len then begin
            let end_code = read_u16_be buf (end_codes_off + seg_off) in
            let start_code = read_u16_be buf (start_codes_off + seg_off) in
            if cp >= start_code && cp <= end_code then
              found := true
          end
        end
      done;
      !found

(* ── Cmap format 12 (segmented coverage) ───────────────────────────── *)

(** Check if codepoint [cp] is covered by a format 12 subtable at [off]. *)
let format12_has_codepoint (buf : bytes) (off : int) (cp : int) : bool =
  let len = Bytes.length buf in
  if off + 16 > len then false
  else
    let n_groups = read_u32_be buf (off + 12) in
    let groups_off = off + 16 in
    let found = ref false in
    let i = ref 0 in
    while !i < n_groups && not !found do
      let g_off = groups_off + !i * 12 in
      if g_off + 12 > len then
        i := n_groups  (* stop *)
      else begin
        let start_code = read_u32_be buf g_off in
        let end_code = read_u32_be buf (g_off + 4) in
        if cp >= start_code && cp <= end_code then
          found := true;
        incr i
      end
    done;
    !found

(* ── Main entry point ──────────────────────────────────────────────── *)

let has_cjk_coverage (path : string) : bool option =
  let ic = try Some (open_in_bin path) with Sys_error _ -> None in
  match ic with
  | None -> None
  | Some ic ->
      Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
      let file_len = in_channel_length ic in
      if file_len < 12 then None
      else begin
        let buf = Bytes.create file_len in
        really_input ic buf 0 file_len;
        (* Read sfnt offset table *)
        let _sfnt_version = read_u32_be buf 0 in
        let num_tables = read_u16_be buf 4 in
        (* Find cmap table *)
        let cmap_off = ref (-1) in
        for i = 0 to num_tables - 1 do
          let entry_off = 12 + i * 16 in
          if entry_off + 16 <= file_len then begin
            let tag = Bytes.sub_string buf entry_off 4 in
            if tag = "cmap" then
              cmap_off := read_u32_be buf (entry_off + 8)
          end
        done;
        if !cmap_off < 0 || !cmap_off + 4 > file_len then None
        else begin
          let cmap_base = !cmap_off in
          let _version = read_u16_be buf cmap_base in
          let num_subtables = read_u16_be buf (cmap_base + 2) in
          (* Find the best subtable: prefer format 12, then format 4
             (platform 3 = Windows, encoding 1 = Unicode BMP or 10 = full) *)
          let best_off = ref (-1) in
          let best_fmt = ref 0 in
          for i = 0 to num_subtables - 1 do
            let rec_off = cmap_base + 4 + i * 8 in
            if rec_off + 8 <= file_len then begin
              let _platform = read_u16_be buf rec_off in
              let _encoding = read_u16_be buf (rec_off + 2) in
              let sub_offset = read_u32_be buf (rec_off + 4) in
              let abs_off = cmap_base + sub_offset in
              if abs_off + 2 <= file_len then begin
                let fmt = read_u16_be buf abs_off in
                (* Prefer format 12 > format 4 *)
                if fmt = 12 && !best_fmt < 12 then begin
                  best_off := abs_off; best_fmt := 12
                end else if fmt = 4 && !best_fmt < 4 then begin
                  best_off := abs_off; best_fmt := 4
                end
              end
            end
          done;
          if !best_off < 0 then None
          else begin
            let check_cp cp =
              match !best_fmt with
              | 4 -> format4_has_codepoint buf !best_off cp
              | 12 -> format12_has_codepoint buf !best_off cp
              | _ -> false
            in
            let hits =
              List.fold_left
                (fun acc cp -> if check_cp cp then acc + 1 else acc)
                0 cjk_sample_points
            in
            let ratio = float hits /. float cjk_sample_count in
            Some (ratio >= cjk_coverage_threshold)
          end
        end
      end
