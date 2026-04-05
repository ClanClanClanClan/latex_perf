(** Section tree extraction, renumbering, and structural validation (spec
    W48-49). *)

type section_node = {
  level : int;
  title : string;
  number : int;
  label : string option;
  children : section_node list;
  source_offset : int;
}

type section_tree = section_node list

type violation = {
  v_title : string;
  v_expected_max_level : int;
  v_actual_level : int;
  v_offset : int;
}

type raw_section = {
  rs_level : int;
  rs_name : string;
  rs_title : string;
  rs_label : string option;
  rs_offset : int;
}

val extract_sections : string -> raw_section list
val build_tree : raw_section list -> section_tree
val extract_tree : string -> section_tree
val renumber : section_tree -> section_tree
val validate : section_tree -> violation list
val flatten : section_tree -> raw_section list
