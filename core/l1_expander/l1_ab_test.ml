(* Minimal L1 expander A/B test driver.
   Intentionally simple: prints a placeholder and exits 0.
   Extend in a feature branch to compare two expander strategies on inputs. *)

let read_all path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
    let len = in_channel_length ic in really_input_string ic len

let () =
  let csv = ref None in
  let file = ref None in
  let rec loop i =
    if i >= Array.length Sys.argv then () else
      match Sys.argv.(i) with
      | "--csv" -> if i+1 >= Array.length Sys.argv then (prerr_endline "--csv PATH"; exit 2); csv := Some Sys.argv.(i+1); loop (i+2)
      | s when !file=None -> file := Some s; loop (i+1)
      | _ -> prerr_endline "usage: l1_ab_test [--csv PATH] FILE"; exit 2
  in
  loop 1;
  let file = match !file with Some f -> f | None -> prerr_endline "usage: l1_ab_test [--csv PATH] FILE"; exit 2 in
  let s = read_all file in
  let module L = L1_expander in
  let ta = L.L1_ab_api.tokenize_a s in
  let tb = L.L1_ab_api.tokenize_b s in
  let (c_ctrl_a, c_text_a) = L.L1_ab_api.summarize ta in
  let (c_ctrl_b, c_text_b) = L.L1_ab_api.summarize tb in
  let eq = L.L1_ab_api.equal_toks ta tb in
  Printf.printf "[l1-ab] %s: A(controls=%d text=%d) B(controls=%d text=%d) equal=%b\n%!"
    file c_ctrl_a c_text_a c_ctrl_b c_text_b eq;
  (match !csv with
   | None -> ()
   | Some path ->
       let oc = open_out_gen [Open_creat; Open_text; Open_wronly; Open_append] 0o644 path in
       Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
         if in_channel_length (open_in path) = 0 then output_string oc "file,ctrl_a,text_a,ctrl_b,text_b,equal\n";
         Printf.fprintf oc "%s,%d,%d,%d,%d,%b\n" file c_ctrl_a c_text_a c_ctrl_b c_text_b eq)
  ;
  if not eq then begin
    (* Emit a small mismatch snippet around the first differing token *)
    let module T = struct
      type tok = L.L1_ab_api.tok = Control of string | Text of string
      let to_str = function Control n -> Printf.sprintf "\\%s" n | Text t -> Printf.sprintf "T(%s)" t
    end in
    let rec find_i i a b = match a,b with
      | [],[] -> None | _::_,[] | [],_::_ -> Some i
      | x::xs, y::ys -> if x=y then find_i (i+1) xs ys else Some i in
    let i0 = find_i 0 ta tb in
    (match i0 with
    | None -> ()
    | Some i ->
        let slice lst =
          let rec take n l = if n=0 then [] else match l with []->[] | x::xs -> x::take (n-1) xs in
          let rec drop n l = if n=0 then l else match l with []->[] | _::xs -> drop (n-1) xs in
          let start = max 0 (i-2) in
          let l = take 5 (drop start lst) in
          (start,l)
        in
        let (sa,wa) = slice ta in
        let (_sb,wb) = slice tb in
        let show arr = String.concat " | " (List.map T.to_str arr) in
        Printf.eprintf "[l1-ab:mismatch] i=%d\nA[%d..]: %s\nB[%d..]: %s\n%!" i sa (show wa) sa (show wb)
    )
  end
