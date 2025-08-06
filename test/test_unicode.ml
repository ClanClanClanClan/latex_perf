let test_alpha () =
  let alpha_code = 945 in
  Printf.printf "Greek alpha code: %d (0x%X)
" alpha_code alpha_code;
  let ranges = [(0x0370, 0x037D); (0x037F, 0x1FFF)] in
  let is_in_range code = List.exists (fun (start, stop) -> code >= start && code <= stop) ranges in
  Printf.printf "Is alpha in ranges? %b
" (is_in_range alpha_code);
  List.iteri (fun i (start, stop) ->
    if alpha_code >= start && alpha_code <= stop then
      Printf.printf "Found in range %d: (0x%X, 0x%X)
" i start stop
  ) ranges

let () = test_alpha ()
