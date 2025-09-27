external mlockall : unit -> unit = "ocaml_mlockall"

let init () = try mlockall () with _ -> ()
