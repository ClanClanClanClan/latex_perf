(* ══════════════════════════════════════════════════════════════════════
   Jpeg_reader — minimal JPEG metadata reader

   Reads SOF0/SOF2 dimensions, APP0 (JFIF DPI), APP1 (EXIF DPI),
   APP2 (ICC profile), APP14 (Adobe color transform).
   ══════════════════════════════════════════════════════════════════════ *)

type jpeg_info = {
  width : int;
  height : int;
  components : int;  (** 1=gray, 3=YCbCr, 4=CMYK *)
  dpi_x : float;  (** 0.0 = not specified *)
  dpi_y : float;
  has_icc_profile : bool;
  icc_color_space : [ `RGB | `CMYK | `Gray | `Unknown ];
  adobe_color_transform : int;  (** -1=absent, 0=CMYK, 1=YCbCr, 2=YCCK *)
}

val read_jpeg_info : string -> jpeg_info option
(** [read_jpeg_info path] reads JPEG metadata from [path].
    Returns [None] on I/O error or invalid JPEG. *)
