(* ══════════════════════════════════════════════════════════════════════
   Png_reader — minimal PNG metadata reader

   Reads PNG chunk headers and small metadata chunks (IHDR, pHYs, tRNS,
   iCCP, sRGB, PLTE) without decompressing IDAT.  No external
   dependencies — pure OCaml binary parsing.
   ══════════════════════════════════════════════════════════════════════ *)

type png_info = {
  width : int;
  height : int;
  bit_depth : int;
  color_type : int;
  has_trns : bool;
  phys_x : int;
  phys_y : int;
  phys_unit : int;
  has_iccp : bool;
  iccp_name : string;
  has_srgb : bool;
  plte_entries : int;
}

(* ── Binary helpers ────────────────────────────────────────────────── *)

let read_u32_be (buf : bytes) (off : int) : int =
  (Char.code (Bytes.get buf off) lsl 24)
  lor (Char.code (Bytes.get buf (off + 1)) lsl 16)
  lor (Char.code (Bytes.get buf (off + 2)) lsl 8)
  lor Char.code (Bytes.get buf (off + 3))

let read_u8 (buf : bytes) (off : int) : int =
  Char.code (Bytes.get buf off)

let chunk_type_str (buf : bytes) (off : int) : string =
  Bytes.sub_string buf off 4

(* PNG magic: 89 50 4E 47 0D 0A 1A 0A *)
let png_magic = "\137PNG\r\n\026\n"

(* ── Main reader ───────────────────────────────────────────────────── *)

let read_png_info (path : string) : png_info option =
  let ic =
    try Some (open_in_bin path) with Sys_error _ -> None
  in
  match ic with
  | None -> None
  | Some ic ->
      Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
      let file_len = in_channel_length ic in
      if file_len < 8 + 25 then None  (* magic + minimum IHDR chunk *)
      else
        let header = Bytes.create 8 in
        really_input ic header 0 8;
        if Bytes.sub_string header 0 8 <> png_magic then None
        else
          (* Initialize result fields *)
          let width = ref 0 in
          let height = ref 0 in
          let bit_depth = ref 0 in
          let color_type = ref 0 in
          let has_trns = ref false in
          let phys_x = ref 0 in
          let phys_y = ref 0 in
          let phys_unit = ref 0 in
          let has_iccp = ref false in
          let iccp_name = ref "" in
          let has_srgb = ref false in
          let plte_entries = ref 0 in
          let ok = ref true in

          (* Read IHDR — must be first chunk *)
          let chunk_hdr = Bytes.create 8 in
          (try
             really_input ic chunk_hdr 0 8;
             let chunk_len = read_u32_be chunk_hdr 0 in
             let ctype = chunk_type_str chunk_hdr 4 in
             if ctype <> "IHDR" || chunk_len < 13 then ok := false
             else begin
               let ihdr_data = Bytes.create chunk_len in
               really_input ic ihdr_data 0 chunk_len;
               (* skip 4-byte CRC *)
               let _crc = Bytes.create 4 in
               really_input ic _crc 0 4;
               width := read_u32_be ihdr_data 0;
               height := read_u32_be ihdr_data 4;
               bit_depth := read_u8 ihdr_data 8;
               color_type := read_u8 ihdr_data 9
             end
           with End_of_file -> ok := false);

          (* Walk remaining chunks *)
          if !ok then begin
            let finished = ref false in
            while not !finished do
              try
                really_input ic chunk_hdr 0 8;
                let chunk_len = read_u32_be chunk_hdr 0 in
                let ctype = chunk_type_str chunk_hdr 4 in
                begin match ctype with
                | "pHYs" when chunk_len >= 9 ->
                    let data = Bytes.create chunk_len in
                    really_input ic data 0 chunk_len;
                    phys_x := read_u32_be data 0;
                    phys_y := read_u32_be data 4;
                    phys_unit := read_u8 data 8;
                    let _crc = Bytes.create 4 in
                    really_input ic _crc 0 4

                | "tRNS" ->
                    has_trns := true;
                    (* skip chunk data + CRC *)
                    seek_in ic (pos_in ic + chunk_len + 4)

                | "iCCP" when chunk_len >= 2 ->
                    let data = Bytes.create (min chunk_len 256) in
                    let to_read = min chunk_len 256 in
                    really_input ic data 0 to_read;
                    (* Profile name is null-terminated *)
                    let name_end = ref 0 in
                    while !name_end < to_read
                          && Char.code (Bytes.get data !name_end) <> 0
                    do incr name_end done;
                    has_iccp := true;
                    iccp_name := Bytes.sub_string data 0 !name_end;
                    (* skip rest of chunk data + CRC *)
                    let remaining = chunk_len - to_read in
                    if remaining > 0 then
                      seek_in ic (pos_in ic + remaining);
                    seek_in ic (pos_in ic + 4)

                | "sRGB" ->
                    has_srgb := true;
                    seek_in ic (pos_in ic + chunk_len + 4)

                | "PLTE" when chunk_len >= 3 ->
                    plte_entries := chunk_len / 3;
                    seek_in ic (pos_in ic + chunk_len + 4)

                | "IEND" ->
                    finished := true

                | _ ->
                    (* Skip unknown/unneeded chunks *)
                    seek_in ic (pos_in ic + chunk_len + 4)
                end
              with End_of_file | Sys_error _ ->
                finished := true
            done
          end;

          if !ok then
            Some {
              width = !width;
              height = !height;
              bit_depth = !bit_depth;
              color_type = !color_type;
              has_trns = !has_trns;
              phys_x = !phys_x;
              phys_y = !phys_y;
              phys_unit = !phys_unit;
              has_iccp = !has_iccp;
              iccp_name = !iccp_name;
              has_srgb = !has_srgb;
              plte_entries = !plte_entries;
            }
          else None
