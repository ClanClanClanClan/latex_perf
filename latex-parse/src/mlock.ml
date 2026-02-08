external mlockall : unit -> unit = "ocaml_mlockall"

let init () =
  match Sys.getenv_opt "L0_NO_MLOCK" with
  | Some "1" -> () (* Skip mlock for CI / constrained environments *)
  | _ -> ( try mlockall () with _ -> ())
