(* ══════════════════════════════════════════════════════════════════════
   Pdf_reader — production-grade PDF structure inspector

   Reads PDF cross-reference tables, resolves indirect object references,
   and navigates catalog/pages/fonts/annotations/structure tree to extract
   metadata needed by L3 validator rules.

   Handles standard xref tables and cross-reference streams (PDF 1.5+).
   Encrypted PDFs and malformed files return [None] gracefully.
   No zlib decompression — inspects dictionary keys only.
   ══════════════════════════════════════════════════════════════════════ *)

(** Low-level PDF value representation. *)
type pdf_value =
  | PdfBool of bool
  | PdfInt of int
  | PdfFloat of float
  | PdfString of string
  | PdfName of string
  | PdfArray of pdf_value list
  | PdfDict of (string * pdf_value) list
  | PdfRef of int * int  (** obj_num, gen_num *)
  | PdfStream of (string * pdf_value) list * bytes
  | PdfNull

(** Parsed PDF document with resolved objects. *)
type pdf_document = {
  objects : (int, pdf_value) Hashtbl.t;
  trailer : (string * pdf_value) list;
}

(** High-level PDF metadata for L3 validators. *)
type pdf_info = {
  has_struct_tree_root : bool;
  has_mark_info : bool;
  figures_without_alt : int;
  links_without_contents : int;
  lang : string option;
  fonts : (string * bool * bool) list;
      (** (name, is_embedded, is_subsetted) *)
  page_label_count : int;
  page_count : int;
  has_spot_colour : bool;
  has_spot_colour_vector : bool;
  streams_all_compressed : bool;
}

val parse_pdf : string -> pdf_document option
(** [parse_pdf path] parses a PDF file and returns the document structure.
    Returns [None] on I/O error, encrypted PDF, or malformed structure. *)

val read_pdf_info : string -> pdf_info option
(** [read_pdf_info path] extracts high-level metadata from a PDF file.
    Returns [None] on I/O error or unparseable PDF. *)

val resolve : pdf_document -> pdf_value -> pdf_value
(** [resolve doc v] follows indirect references to their target value. *)

val dict_get : string -> (string * pdf_value) list -> pdf_value option
(** [dict_get key entries] looks up [key] in a PDF dictionary. *)
