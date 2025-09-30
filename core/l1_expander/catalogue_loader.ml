type control_policy = { arity : int }

type config = {
  strip_controls : string list;
  bfseries_until_brace : bool;
  controls : (string * control_policy) list;
}

let default =
  {
    strip_controls = [ "textbf"; "emph"; "section" ];
    bfseries_until_brace = true;
    controls =
      [
        ("section", { arity = 1 });
        ("textbf", { arity = 1 });
        ("emph", { arity = 1 });
      ];
  }

let load path : config =
  try
    let j = Yojson.Safe.from_file path in
    let open Yojson.Safe.Util in
    let strip = j |> member "strip_controls" |> to_list |> List.map to_string in
    let bf = j |> member "bfseries_until_brace" |> to_bool in
    let ctrls =
      j
      |> member "controls"
      |> to_assoc
      |> List.map (fun (k, v) ->
             let ar = v |> member "arity" |> to_int in
             (k, { arity = ar }))
    in
    { strip_controls = strip; bfseries_until_brace = bf; controls = ctrls }
  with _ -> default
