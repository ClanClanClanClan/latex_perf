(* Profile lexer to identify bottlenecks *)

let profile_lexer () =
  let content = String.make 1_000_000 'a' in
  let content = content ^ "\n\\command{test} $math$ {group}\n" ^ content in
  
  (* Time different operations *)
  let time_op name f =
    let start = Unix.gettimeofday () in
    let result = f () in
    let elapsed = Unix.gettimeofday () -. start in
    Printf.printf "%s: %.3f ms\n" name (elapsed *. 1000.0);
    result
  in
  
  (* Test Uchar.of_char *)
  time_op "1M Uchar.of_char" (fun () ->
    for _i = 0 to 999_999 do
      ignore (Uchar.of_char 'a')
    done
  );
  
  (* Test catcode_of *)
  time_op "1M catcode_of" (fun () ->
    let u = Uchar.of_char 'a' in
    for _i = 0 to 999_999 do
      ignore (Data.Catcode.catcode_of Data.Catcode.PdfTeX u)
    done
  );
  
  (* Test String.sub *)
  time_op "10K String.sub" (fun () ->
    let s = String.make 100 'a' in
    for _i = 0 to 9_999 do
      ignore (String.sub s 10 50)
    done
  );
  
  (* Test Array allocation *)
  time_op "154K array alloc" (fun () ->
    let arr = Array.make 154_293 0 in
    for i = 0 to 154_292 do
      Array.unsafe_set arr i i
    done
  );
  
  (* Test full lexer *)
  ignore (time_op "Full L0_lexer" (fun () ->
    let tokens = Core.Lexer_optimized_v25.tokenize_to_list content in
    List.length tokens
  ));
  
  ignore (time_op "Track A simple" (fun () ->
    let tokens = Core.L0_lexer_track_a_simple.tokenize content in
    List.length tokens
  ));
  
  ignore (time_op "Track A zero" (fun () ->
    let tokens = Core.L0_lexer_track_a_perfect.tokenize content in
    List.length tokens
  ))

let () = profile_lexer ()