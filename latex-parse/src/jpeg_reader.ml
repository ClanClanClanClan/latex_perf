(* ══════════════════════════════════════════════════════════════════════
   Jpeg_reader — minimal JPEG metadata reader

   Walks JPEG markers (FF xx) to extract dimensions, DPI, ICC profile
   info, and Adobe color transform.  No external dependencies.
   ══════════════════════════════════════════════════════════════════════ *)

type jpeg_info = {
  width : int;
  height : int;
  components : int;
  dpi_x : float;
  dpi_y : float;
  has_icc_profile : bool;
  icc_color_space : [ `RGB | `CMYK | `Gray | `Unknown ];
  adobe_color_transform : int;
}

(* ── Binary helpers ────────────────────────────────────────────────── *)

let read_u16_be (buf : bytes) (off : int) : int =
  (Char.code (Bytes.get buf off) lsl 8)
  lor Char.code (Bytes.get buf (off + 1))

let read_u32_be (buf : bytes) (off : int) : int =
  (Char.code (Bytes.get buf off) lsl 24)
  lor (Char.code (Bytes.get buf (off + 1)) lsl 16)
  lor (Char.code (Bytes.get buf (off + 2)) lsl 8)
  lor Char.code (Bytes.get buf (off + 3))

let read_u16_le (buf : bytes) (off : int) : int =
  Char.code (Bytes.get buf off)
  lor (Char.code (Bytes.get buf (off + 1)) lsl 8)

let read_u32_le (buf : bytes) (off : int) : int =
  Char.code (Bytes.get buf off)
  lor (Char.code (Bytes.get buf (off + 1)) lsl 8)
  lor (Char.code (Bytes.get buf (off + 2)) lsl 16)
  lor (Char.code (Bytes.get buf (off + 3)) lsl 24)

let starts_with (buf : bytes) (off : int) (prefix : string) : bool =
  let plen = String.length prefix in
  if off + plen > Bytes.length buf then false
  else
    let rec loop i =
      if i >= plen then true
      else if Bytes.get buf (off + i) <> prefix.[i] then false
      else loop (i + 1)
    in
    loop 0

(* ── EXIF IFD parsing for DPI ──────────────────────────────────────── *)

(** Parse a TIFF rational (two u32) into float. *)
let parse_rational (buf : bytes) (off : int) (le : bool) : float =
  let num = if le then read_u32_le buf off else read_u32_be buf off in
  let den =
    if le then read_u32_le buf (off + 4) else read_u32_be buf (off + 4)
  in
  if den = 0 then 0.0 else float num /. float den

(** Extract DPI from EXIF APP1 segment data (after "Exif\0\0").
    Returns (dpi_x, dpi_y) or (0.0, 0.0) if not found. *)
let parse_exif_dpi (buf : bytes) (tiff_start : int) : float * float =
  let len = Bytes.length buf in
  if tiff_start + 8 > len then (0.0, 0.0)
  else
    (* Determine byte order *)
    let b0 = Char.code (Bytes.get buf tiff_start) in
    let b1 = Char.code (Bytes.get buf (tiff_start + 1)) in
    let le = b0 = 0x49 && b1 = 0x49 in
    let _be = b0 = 0x4D && b1 = 0x4D in
    if not (le || _be) then (0.0, 0.0)
    else
      let read_u16 off =
        if le then read_u16_le buf off else read_u16_be buf off
      in
      let read_u32 off =
        if le then read_u32_le buf off else read_u32_be buf off
      in
      (* IFD0 offset *)
      let ifd_off = tiff_start + read_u32 (tiff_start + 4) in
      if ifd_off + 2 > len then (0.0, 0.0)
      else
        let n_entries = read_u16 ifd_off in
        let dpi_x = ref 0.0 in
        let dpi_y = ref 0.0 in
        let res_unit = ref 2 in (* default = inch *)
        for i = 0 to n_entries - 1 do
          let entry_off = ifd_off + 2 + (i * 12) in
          if entry_off + 12 <= len then begin
            let tag = read_u16 entry_off in
            match tag with
            | 0x011A (* XResolution *) ->
                let val_off = tiff_start + read_u32 (entry_off + 8) in
                if val_off + 8 <= len then
                  dpi_x := parse_rational buf val_off le
            | 0x011B (* YResolution *) ->
                let val_off = tiff_start + read_u32 (entry_off + 8) in
                if val_off + 8 <= len then
                  dpi_y := parse_rational buf val_off le
            | 0x0128 (* ResolutionUnit *) ->
                let v = read_u16 (entry_off + 8) in
                res_unit := v
            | _ -> ()
          end
        done;
        (* Convert cm to inch if unit=3 *)
        let scale = if !res_unit = 3 then 2.54 else 1.0 in
        (!dpi_x *. scale, !dpi_y *. scale)

(* ── ICC profile color space detection ─────────────────────────────── *)

(** Parse ICC color space from 4 bytes at offset 16 in profile header.
    Returns [`RGB], [`CMYK], [`Gray], or [`Unknown]. *)
let parse_icc_color_space (buf : bytes) (profile_start : int) : [ `RGB | `CMYK | `Gray | `Unknown ] =
  if profile_start + 20 > Bytes.length buf then `Unknown
  else
    let cs = Bytes.sub_string buf (profile_start + 16) 4 in
    match cs with
    | "RGB " -> `RGB
    | "CMYK" -> `CMYK
    | "GRAY" -> `Gray
    | _ -> `Unknown

(* ── Main reader ───────────────────────────────────────────────────── *)

let read_jpeg_info (path : string) : jpeg_info option =
  let ic = try Some (open_in_bin path) with Sys_error _ -> None in
  match ic with
  | None -> None
  | Some ic ->
      Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
      let file_len = in_channel_length ic in
      if file_len < 4 then None
      else begin
        (* Check SOI marker *)
        let soi = Bytes.create 2 in
        really_input ic soi 0 2;
        if Char.code (Bytes.get soi 0) <> 0xFF
           || Char.code (Bytes.get soi 1) <> 0xD8 then None
        else begin
          let width = ref 0 in
          let height = ref 0 in
          let components = ref 0 in
          let dpi_x = ref 0.0 in
          let dpi_y = ref 0.0 in
          let has_icc = ref false in
          let icc_cs = ref `Unknown in
          let adobe_ct = ref (-1) in
          let has_sof = ref false in
          let finished = ref false in
          let marker_buf = Bytes.create 2 in

          while not !finished do
            try
              (* Find next marker *)
              really_input ic marker_buf 0 2;
              let b0 = Char.code (Bytes.get marker_buf 0) in
              let b1 = Char.code (Bytes.get marker_buf 1) in
              if b0 <> 0xFF then
                finished := true
              else match b1 with
              | 0xD9 (* EOI *) -> finished := true
              | 0xD8 (* SOI — skip *) -> ()
              | m when m >= 0xD0 && m <= 0xD7 -> () (* RST markers, no payload *)
              | _ ->
                  (* Read segment length *)
                  let len_buf = Bytes.create 2 in
                  really_input ic len_buf 0 2;
                  let seg_len = read_u16_be len_buf 0 in
                  let data_len = seg_len - 2 in
                  if data_len < 0 then finished := true
                  else begin
                    let data = Bytes.create data_len in
                    really_input ic data 0 data_len;
                    match b1 with
                    (* SOF0 or SOF2 — Start of Frame *)
                    | 0xC0 | 0xC2 when data_len >= 6 && not !has_sof ->
                        has_sof := true;
                        height := read_u16_be data 1;
                        width := read_u16_be data 3;
                        components := Char.code (Bytes.get data 5)

                    (* APP0 — JFIF *)
                    | 0xE0 when data_len >= 12 && starts_with data 0 "JFIF\000" ->
                        let units = Char.code (Bytes.get data 7) in
                        let dx = float (read_u16_be data 8) in
                        let dy = float (read_u16_be data 10) in
                        begin match units with
                        | 1 -> (* DPI *)
                            if !dpi_x = 0.0 then dpi_x := dx;
                            if !dpi_y = 0.0 then dpi_y := dy
                        | 2 -> (* dots per cm *)
                            if !dpi_x = 0.0 then dpi_x := dx *. 2.54;
                            if !dpi_y = 0.0 then dpi_y := dy *. 2.54
                        | _ -> ()
                        end

                    (* APP1 — EXIF *)
                    | 0xE1 when data_len >= 14 && starts_with data 0 "Exif\000\000" ->
                        let ex, ey = parse_exif_dpi data 6 in
                        if ex > 0.0 then dpi_x := ex;
                        if ey > 0.0 then dpi_y := ey

                    (* APP2 — ICC_PROFILE *)
                    | 0xE2 when data_len >= 18 && starts_with data 0 "ICC_PROFILE\000" ->
                        (* bytes 12-13: sequence number, total chunks *)
                        has_icc := true;
                        let cs = parse_icc_color_space data 14 in
                        if cs <> `Unknown then icc_cs := cs

                    (* APP14 — Adobe *)
                    | 0xEE when data_len >= 12 && starts_with data 0 "Adobe" ->
                        adobe_ct := Char.code (Bytes.get data 11)

                    | _ -> ()
                  end
            with End_of_file | Sys_error _ ->
              finished := true
          done;

          if !has_sof then
            Some {
              width = !width;
              height = !height;
              components = !components;
              dpi_x = !dpi_x;
              dpi_y = !dpi_y;
              has_icc_profile = !has_icc;
              icc_color_space = !icc_cs;
              adobe_color_transform = !adobe_ct;
            }
          else None
        end
      end
