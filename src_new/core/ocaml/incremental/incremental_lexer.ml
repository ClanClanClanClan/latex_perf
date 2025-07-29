(* incremental_lexer.ml - Main incremental lexer API for v24-R3 *)

open Types

(** Incremental lexer instance *)
type t = {
  mutable document : Line_processor.document;
  checkpoint_mgr : Checkpoint_manager.t;
  mutable ring_buffer : Ring_buffer.t option;
  mutable last_edit_line : int;
  config : config;
}

and config = {
  enable_checkpoints : bool;
  enable_ring_buffer : bool;
  checkpoint_interval : int;
  ring_buffer_size : int;
}

(** Default configuration *)
let default_config = {
  enable_checkpoints = true;
  enable_ring_buffer = true;
  checkpoint_interval = 1000;
  ring_buffer_size = 1_000_000;
}

(** Create new incremental lexer *)
let create ?(config=default_config) () =
  {
    document = Line_processor.create_document [||];
    checkpoint_mgr = Checkpoint_manager.create ();
    ring_buffer = None;
    last_edit_line = 0;
    config = config;
  }

(** Load document from string *)
let load_string lexer content =
  let lines = 
    content 
    |> String.split_on_char '\n'
    |> Array.of_list in
  
  lexer.document <- Line_processor.relex_document lines;
  
  (* Create checkpoints if enabled *)
  if lexer.config.enable_checkpoints then begin
    Checkpoint_manager.clear lexer.checkpoint_mgr;
    let mgr = Checkpoint_manager.create_checkpoints_from_doc lexer.document in
    lexer.checkpoint_mgr.checkpoints <- mgr.checkpoints;
    lexer.checkpoint_mgr.size <- mgr.size
  end;
  
  (* Create ring buffer if enabled *)
  if lexer.config.enable_ring_buffer then
    lexer.ring_buffer <- Some (Ring_buffer.from_document lexer.document)

(** Load document from file *)
let load_file lexer filename =
  let ic = open_in_bin filename in
  let len = in_channel_length ic in
  let content = really_input_string ic len in
  close_in ic;
  load_string lexer content

(** Apply edit operation *)
let edit lexer op =
  let start_time = Unix.gettimeofday () in
  
  (* Apply edit to document *)
  let affected_line = Line_processor.apply_edit lexer.document op in
  
  (* Find recovery point using checkpoints *)
  let recovery_line = 
    if lexer.config.enable_checkpoints then
      match op with
      | Insert (line, _) | Delete (line, _) | Replace (line, _, _) ->
          let byte_offset = 
            if line > 0 && line <= lexer.document.line_table.size then
              lexer.document.line_table.lines.(line - 1).li_end_pos
            else
              0 in
          let recovery_line, _ = 
            Checkpoint_manager.find_recovery_point lexer.checkpoint_mgr byte_offset in
          min affected_line recovery_line
    else
      affected_line in
  
  (* Process incrementally from recovery point *)
  let lines_processed, bytes_processed = 
    Line_processor.process_incremental lexer.document recovery_line in
  
  (* Update checkpoints *)
  if lexer.config.enable_checkpoints then begin
    (* Regenerate checkpoints for affected region *)
    let mgr = Checkpoint_manager.create_checkpoints_from_doc lexer.document in
    lexer.checkpoint_mgr.checkpoints <- mgr.checkpoints;
    lexer.checkpoint_mgr.size <- mgr.size
  end;
  
  (* Update ring buffer *)
  if lexer.config.enable_ring_buffer then
    lexer.ring_buffer <- Some (Ring_buffer.from_document lexer.document);
  
  lexer.last_edit_line <- affected_line;
  
  let elapsed_ms = (Unix.gettimeofday () -. start_time) *. 1000. in
  (lines_processed, bytes_processed, elapsed_ms)

(** Edit line (convenience function) *)
let edit_line lexer line_no new_text =
  edit lexer (Replace (line_no, 1, new_text))

(** Insert line *)
let insert_line lexer line_no text =
  edit lexer (Insert (line_no, text))

(** Delete lines *)
let delete_lines lexer start_line count =
  edit lexer (Delete (start_line, count))

(** Get tokens for line range *)
let get_tokens lexer start_line end_line =
  Line_processor.get_tokens lexer.document start_line end_line

(** Get all tokens *)
let get_all_tokens lexer =
  Line_processor.get_all_tokens lexer.document

(** Get document statistics *)
let get_stats lexer =
  let doc_stats = lexer.document.stats in
  let cp_count, cp_avg_dist, cp_max_dist = 
    Checkpoint_manager.get_stats lexer.checkpoint_mgr in
  let rb_size, rb_capacity, rb_util, rb_evicted =
    match lexer.ring_buffer with
    | Some rb -> Ring_buffer.get_stats rb
    | None -> (0, 0, 0., 0) in
  
  {|
    Document Statistics:
    - Total lines: %d
    - Total bytes: %d
    - Incremental bytes processed: %d
    - Cache hits: %d
    - Cache misses: %d
    - Parse time: %d μs
    - Speedup: %.1fx
    
    Checkpoint Statistics:
    - Total checkpoints: %d
    - Average distance: %d bytes
    - Max distance: %d bytes
    
    Ring Buffer Statistics:
    - Size: %d / %d (%.1f%% utilization)
    - Total evicted: %d
  |}
    (Array.length lexer.document.lines)
    doc_stats.total_bytes
    doc_stats.incremental_bytes
    doc_stats.cache_hits
    doc_stats.cache_misses
    doc_stats.parse_time_us
    (Line_processor.calculate_speedup lexer.document)
    cp_count cp_avg_dist cp_max_dist
    rb_size rb_capacity (rb_util *. 100.) rb_evicted

(** Save checkpoint state *)
let save_checkpoints lexer filename =
  let data = Checkpoint_manager.serialize lexer.checkpoint_mgr in
  let oc = open_out_bin filename in
  output_string oc data;
  close_out oc

(** Load checkpoint state *)
let load_checkpoints lexer filename =
  try
    let ic = open_in_bin filename in
    let len = in_channel_length ic in
    let data = really_input_string ic len in
    close_in ic;
    match Checkpoint_manager.deserialize data with
    | Some mgr ->
        lexer.checkpoint_mgr.checkpoints <- mgr.checkpoints;
        lexer.checkpoint_mgr.size <- mgr.size;
        true
    | None -> false
  with _ -> false

(** Export tokens to JSON (for debugging) *)
let export_tokens_json lexer filename =
  let tokens = get_all_tokens lexer in
  let oc = open_out filename in
  output_string oc "[\n";
  List.iteri (fun i tok ->
    let json = match tok with
      | TChar c -> Printf.sprintf {|{"type":"char","value":"%c"}|} c
      | TCommand s -> Printf.sprintf {|{"type":"command","value":"%s"}|} s
      | TNewline -> {|{"type":"newline"}|}
      | TSpace -> {|{"type":"space"}|}
      | TMath -> {|{"type":"math"}|}
      | TComment s -> Printf.sprintf {|{"type":"comment","value":"%s"}|} s
      | TBeginEnv s -> Printf.sprintf {|{"type":"begin_env","value":"%s"}|} s
      | TEndEnv s -> Printf.sprintf {|{"type":"end_env","value":"%s"}|} s
      | TError s -> Printf.sprintf {|{"type":"error","value":"%s"}|} s
    in
    output_string oc "  ";
    output_string oc json;
    if i < List.length tokens - 1 then
      output_string oc ",";
    output_string oc "\n"
  ) tokens;
  output_string oc "]\n";
  close_out oc