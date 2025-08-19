
(* check_catalogue_v3.ml — run structural & epsilon checks over the catalogue *)
open Printf

let () =
  if Array.length Sys.argv < 2 then (
    eprintf "usage: %s /path/to/macro_catalogue.argsafe.v25r1.json\n" Sys.argv.(0);
    exit 2
  );
  let file = Sys.argv.(1) in
  let module L = struct include (val (module struct
      include (struct
        include Yojson.Safe
      end)
    end)) end in
  let open Yojson.Safe in
  let open Str in
  (* Bring in the loader *)
  #use "load_catalogue_v3.ml";;
  let cat = load_catalogue file in
  let seen = Hashtbl.create 211 in
  let failures = ref 0 in
  List.iter (fun m ->
    if Hashtbl.mem seen m.name then (
      eprintf "DUPLICATE name: %s\n" m.name; incr failures
    ) else Hashtbl.add seen m.name ();
    let (ok, err) = validate_macro m in
    if not ok then (incr failures; eprintf "INVALID %s: %s\n" m.name (match err with Some e -> e | None -> "unknown"))
  ) cat.macros;
  if !failures = 0 then (
    printf "OK: %d macros validated (epsilon-safe).\n" (List.length cat.macros);
    exit 0
  ) else (
    eprintf "FAILED: %d issues.\n" !failures;
    exit 1
  )
