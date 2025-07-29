(* c_interface.ml - C interface for Python FFI bridge *)

(* This file would be compiled to a shared library that Python can load *)

open Incremental_lexer

(* Global lexer instance - in practice would use handles *)
let lexer_instances = Hashtbl.create 10
let next_handle = ref 0

(* Create new lexer instance *)
let create_lexer () =
  let handle = !next_handle in
  incr next_handle;
  let lexer = create () in
  Hashtbl.add lexer_instances handle lexer;
  handle

(* Load document *)
let load_string handle content =
  match Hashtbl.find_opt lexer_instances handle with
  | Some lexer -> 
      load_string lexer content;
      1 (* success *)
  | None -> 0 (* failure *)

(* Edit line *)
let edit_line handle line_no new_text =
  match Hashtbl.find_opt lexer_instances handle with
  | Some lexer ->
      let lines_processed, bytes_processed, elapsed_ms = 
        edit_line lexer line_no new_text in
      (lines_processed, bytes_processed, int_of_float elapsed_ms)
  | None -> (0, 0, 0)

(* Get token count *)
let get_token_count handle start_line end_line =
  match Hashtbl.find_opt lexer_instances handle with
  | Some lexer ->
      let tokens = get_tokens lexer start_line end_line in
      List.length tokens
  | None -> 0

(* Get speedup *)
let get_speedup handle =
  match Hashtbl.find_opt lexer_instances handle with
  | Some lexer ->
      let stats = lexer.document.stats in
      Line_processor.calculate_speedup lexer.document
  | None -> 1.0

(* Export C functions *)
let () =
  (* Register callbacks that C can call *)
  Callback.register "create_lexer" create_lexer;
  Callback.register "load_string" load_string;
  Callback.register "edit_line" edit_line;
  Callback.register "get_token_count" get_token_count;
  Callback.register "get_speedup" get_speedup

(* C stub functions would be in a separate .c file:

CAMLprim value caml_create_lexer(value unit) {
    return Val_int(create_lexer());
}

CAMLprim value caml_load_string(value handle, value content) {
    return Val_int(load_string(Int_val(handle), String_val(content)));
}

etc...
*)