(* Simple standalone benchmark - no dune required *)

#directory "src/core";;
#directory "src/data";;

(* First compile the dependencies *)
#load "unix.cma";;

let () = 
  (* Compile data modules *)
  let compile_cmds = [
    "ocamlc -c -I src/data src/data/location.ml";
    "ocamlc -c -I src/data src/data/catcode.ml";
    "ocamlc -c -I src/data src/data/chunk.ml";
    "ocamlc -c -I src/data src/data/dlist.ml";
    "ocamlc -a -o src/data/data.cma src/data/location.cmo src/data/catcode.cmo src/data/chunk.cmo src/data/dlist.cmo";
    
    (* Compile core modules *)
    "ocamlc -c -I src/data -I src/core src/core/lexer_v25.ml";
    "ocamlc -c -I src/data -I src/core src/core/l0_lexer.ml";
    "ocamlc -c -I src/data -I src/core src/core/l0_lexer_track_a_simple.ml";
    "ocamlc -c -I src/data -I src/core src/core/l0_lexer_track_a_ultra.ml";
  ] in
  
  List.iter (fun cmd ->
    Printf.printf "Running: %s\n" cmd;
    let ret = Sys.command cmd in
    if ret <> 0 then Printf.printf "Warning: command failed with code %d\n" ret
  ) compile_cmds;
  
  Printf.printf "\nNow run: ocaml -I src/data -I src/core bench/simple_bench.ml\n"