external set_interactive_qos : unit -> unit = "ocaml_set_interactive_qos"
external set_affinity : int -> unit = "ocaml_set_affinity"

let init_for_worker ~core =
  (try set_interactive_qos () with _ -> ());
  try set_affinity core with _ -> ()
