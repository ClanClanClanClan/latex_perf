let test_domains () =
  try
    let d = Domain.spawn (fun () -> 42) in
    let result = Domain.join d in
    Printf.printf "Domains supported: result = %d\n" result;
    true
  with
  | _ -> 
    Printf.printf "Domains not supported\n";
    false

let () = ignore (test_domains ())