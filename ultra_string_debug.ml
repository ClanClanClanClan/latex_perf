(* Debug Ultra V3 String Operations *)

(* Copy the relevant UltraStringOps functions to test in isolation *)
module UltraStringOps = struct
  let single_char_macro_ids = Array.make 256 (-1)
  let macro_table : (string, int) Hashtbl.t = Hashtbl.create 2048
  let reverse_macro_table : (int, string) Hashtbl.t = Hashtbl.create 2048
  let macro_counter = ref 0
  
  let register_single_char_macro char =
    let code = Char.code char in
    if single_char_macro_ids.(code) = -1 then (
      let id = !macro_counter in
      incr macro_counter;
      single_char_macro_ids.(code) <- id;
      let name = String.make 1 char in
      Hashtbl.add reverse_macro_table id name;
      Printf.printf "  Registered single char '%c' with ID %d and name '%s'\n" char id name
    );
    single_char_macro_ids.(code)
  
  let initialize_builtin_macros () =
    Printf.printf "Initializing built-in macros...\n";
    let add_macro name =
      let id = !macro_counter in
      incr macro_counter;
      Hashtbl.add macro_table name id;
      Hashtbl.add reverse_macro_table id name;
      Printf.printf "  Added macro '%s' with ID %d\n" name id
    in
    
    ignore (register_single_char_macro '[');  (* \[ *)
    ignore (register_single_char_macro ']');  (* \] *)
    add_macro "textbf";
    Printf.printf "Initialization complete. macro_counter = %d\n" !macro_counter
  
  let get_single_char_macro_id char_code =
    let id = single_char_macro_ids.(char_code) in
    Printf.printf "  get_single_char_macro_id(%d = '%c') = %d\n" char_code (Char.chr char_code) id;
    id
  
  let get_macro_name_by_id id =
    let name = try Hashtbl.find reverse_macro_table id
               with Not_found -> "unknown" in
    Printf.printf "  get_macro_name_by_id(%d) = '%s'\n" id name;
    name
end

let test_ultra_string_ops () =
  print_endline "=== ULTRA STRING OPS DEBUG ===";
  
  UltraStringOps.initialize_builtin_macros ();
  
  print_endline "\n--- Testing '[' macro lookup ---";
  let bracket_code = Char.code '[' in
  Printf.printf "Looking up '[' (char code %d):\n" bracket_code;
  
  let macro_id = UltraStringOps.get_single_char_macro_id bracket_code in
  if macro_id >= 0 then (
    Printf.printf "Found macro ID: %d\n" macro_id;
    let macro_name = UltraStringOps.get_macro_name_by_id macro_id in
    Printf.printf "Retrieved macro name: '%s'\n" macro_name;
    
    if macro_name = "[" then
      Printf.printf "✅ CORRECT: '[' lookup works properly\n"
    else
      Printf.printf "❌ BUG: Expected '[', got '%s'\n" macro_name
  ) else (
    Printf.printf "❌ BUG: '[' not found in single char table\n"
  );
  
  print_endline "\n--- Testing hash table contents ---";
  Printf.printf "Reverse table contents:\n";
  Hashtbl.iter (fun id name ->
    Printf.printf "  ID %d -> '%s'\n" id name
  ) UltraStringOps.reverse_macro_table;
  
  print_endline "\n=== DEBUG COMPLETE ==="

let () = test_ultra_string_ops ()