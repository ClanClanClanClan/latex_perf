(* ══════════════════════════════════════════════════════════════════════
   Png_reader — minimal PNG metadata reader

   Reads IHDR, pHYs, tRNS, iCCP, sRGB, PLTE chunks from a PNG file without
   decompressing image data.
   ══════════════════════════════════════════════════════════════════════ *)

type png_info = {
  width : int;
  height : int;
  bit_depth : int;
  color_type : int;  (** 0=gray, 2=RGB, 3=indexed, 4=gray+alpha, 6=RGBA *)
  has_trns : bool;
  phys_x : int;  (** pixels per unit X, 0 if no pHYs *)
  phys_y : int;  (** pixels per unit Y, 0 if no pHYs *)
  phys_unit : int;  (** 0=unknown, 1=meter *)
  has_iccp : bool;
  iccp_name : string;  (** "" if no iCCP *)
  has_srgb : bool;
  plte_entries : int;  (** 0 if no PLTE *)
}

val read_png_info : string -> png_info option
(** [read_png_info path] reads PNG metadata from [path]. Returns [None] on I/O
    error or invalid PNG. *)
