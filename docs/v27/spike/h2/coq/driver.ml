(* Driver for the extracted PS program (spike H.2): pdftex -ini, terminal input from
   the lines given, texmf.cnf integer variables from a file of name=value lines. *)
let z = Big_int_Z.big_int_of_int
let bytes_of s = Stdlib.List.init (Stdlib.String.length s) (fun i -> z (Stdlib.Char.code (Stdlib.String.get s i)))
let () =
  let fuel = int_of_string Sys.argv.(1) in
  let env_file = Sys.argv.(2) in
  let stdin_lines = Stdlib.Array.to_list (Stdlib.Array.sub Sys.argv 3 (Stdlib.Array.length Sys.argv - 3)) in
  let env = ref [] in
  let ic = open_in env_file in
  (try while true do
     let l = input_line ic in
     match Stdlib.String.index_opt l '=' with
     | Some i -> (match int_of_string_opt (Stdlib.String.sub l (i+1) (Stdlib.String.length l - i - 1)) with
                  | Some v -> env := (bytes_of (Stdlib.String.sub l 0 i), z v) :: !env | None -> ())
     | None -> ()
   done with End_of_file -> ());
  let io = { Values.io_out = []; io_stdin = Stdlib.List.concat_map (fun l -> bytes_of l @ [z 10]) stdin_lines; io_argv = [bytes_of "-ini"];
             io_char_signed = false; io_files = []; io_next_handle = z 3; io_fs = []; io_env = !env; io_cstate = [] } in
  let t0 = Unix.gettimeofday () in
  let r = Main0.run fuel io in
  let t1 = Unix.gettimeofday () in
  let show st =
    (match Sys.getenv_opt "PS_DUMPDIR" with
     | Some d -> Stdlib.List.iter (fun (h, bs) ->
         let oc = open_out_bin (Filename.concat d ("handle-" ^ Big_int_Z.string_of_big_int h)) in
         Stdlib.List.iter (fun b -> output_char oc (Stdlib.Char.chr (Big_int_Z.int_of_big_int b))) (Stdlib.List.rev bs);
         close_out oc) st.Values.st_io.Values.io_out;
       Stdlib.List.iter (fun (h, name) ->
         Printf.printf "--- file handle %s = %s\n" (Big_int_Z.string_of_big_int h)
           (Stdlib.String.concat "" (Stdlib.List.map (fun b -> Stdlib.String.make 1 (Stdlib.Char.chr (Big_int_Z.int_of_big_int b))) name)))
         st.Values.st_io.Values.io_files
     | None -> ());
    Printf.printf "--- stdin bytes not read: %d\n" (Stdlib.List.length st.Values.st_io.Values.io_stdin);
    Stdlib.List.iter (fun (h, bs) ->
      Printf.printf "--- handle %s (%d bytes)\n" (Big_int_Z.string_of_big_int h) (Stdlib.List.length bs);
      Stdlib.List.iter (fun b -> print_char (Stdlib.Char.chr (Big_int_Z.int_of_big_int b))) (Stdlib.List.rev bs);
      print_newline ()) st.Values.st_io.Values.io_out in
  let str l = Stdlib.String.of_seq (Stdlib.List.to_seq l) in
  (match r with
   | Interp.EOk (_, st) -> show st; print_endline "RESULT: returned"
   | Interp.EHalt (c, st) -> show st; Printf.printf "RESULT: exit %s\n" (Big_int_Z.string_of_big_int c)
   | Interp.EStk (s, st) -> show st;
     let names = (try
       let ic = open_in (Sys.getenv "PS_PROCNAMES") in
       let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> Stdlib.List.rev acc in
       Stdlib.Array.of_list (go []) with _ -> [||]) in
     let pname p = let i = Big_int_Z.int_of_big_int p in
       if i < Stdlib.Array.length names then names.(i) else string_of_int i in
     let rec why s = match s with
       | Values.StIn (p, s') -> pname p ^ " > " ^ why s' 
       | Values.StOverflow -> "signed overflow" | Values.StDivZero -> "division by zero"
       | Values.StConv m -> "conversion: " ^ str m | Values.StUninit -> "read of an uninitialised value"
       | Values.StBounds m -> "bounds: " ^ str m | Values.StType m -> "type: " ^ str m
       | Values.StExternal m -> "unmodelled external: " ^ str m | Values.StFuel -> "out of fuel"
       | Values.StGoto n -> "goto " ^ Big_int_Z.string_of_big_int n | Values.StCharSign -> "char signedness"
       | Values.StNaNBits -> "NaN bits" | Values.StOther m -> str m in
     Printf.printf "RESULT: stuck: %s\n" (why s));
  Printf.printf "TIME: %.2f s\n" (t1 -. t0)
