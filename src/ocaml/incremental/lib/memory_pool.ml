(* memory_pool.ml - Efficient memory management for tokens *)

open Core_lexer_real

(* Token allocation statistics *)
type pool_stats = {
  mutable allocated : int;
  mutable reused : int;
  mutable gc_pressure : int;
}

let stats = {
  allocated = 0;
  reused = 0;
  gc_pressure = 0;
}

(* String interning for commands and environments *)
module StringPool = struct
  type t = {
    table : (string, string) Hashtbl.t;
    mutable size : int;
    mutable memory_used : int;
  }
  
  let create initial_size =
    {
      table = Hashtbl.create initial_size;
      size = 0;
      memory_used = 0;
    }
  
  let intern pool str =
    match Hashtbl.find_opt pool.table str with
    | Some interned -> 
        interned  (* Reuse existing *)
    | None ->
        Hashtbl.add pool.table str str;
        pool.size <- pool.size + 1;
        pool.memory_used <- pool.memory_used + String.length str + 24; (* OCaml string overhead *)
        str
  
  let clear pool =
    Hashtbl.clear pool.table;
    pool.size <- 0;
    pool.memory_used <- 0
  
  let get_stats pool =
    (pool.size, pool.memory_used)
end

(* Token object pools *)
module TokenPool = struct
  type pool = {
    (* Pools for different token types *)
    mutable char_pool : token Queue.t;
    mutable space_pool : token Queue.t;
    mutable newline_pool : token Queue.t;
    mutable math_pool : token Queue.t;
    
    (* Specialized pools *)
    mutable begin_group_pool : token Queue.t;
    mutable end_group_pool : token Queue.t;
    
    (* Size limits *)
    max_pool_size : int;
    
    (* String interning *)
    string_pool : StringPool.t;
  }
  
  let create () = {
    char_pool = Queue.create ();
    space_pool = Queue.create ();
    newline_pool = Queue.create ();
    math_pool = Queue.create ();
    begin_group_pool = Queue.create ();
    end_group_pool = Queue.create ();
    max_pool_size = 10000;
    string_pool = StringPool.create 5000;
  }
  
  let global_pool = create ()
  
  (* Allocate tokens with pooling *)
  let alloc_char c =
    if c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' then begin
      (* Common characters - try pool first *)
      try
        stats.reused <- stats.reused + 1;
        let tok = Queue.pop global_pool.char_pool in
        (* Rewrite the character *)
        match tok with
        | TChar _ -> TChar c
        | _ -> TChar c  (* Shouldn't happen *)
      with Queue.Empty ->
        stats.allocated <- stats.allocated + 1;
        TChar c
    end else
      TChar c  (* Less common - allocate fresh *)
  
  let alloc_space () =
    try
      stats.reused <- stats.reused + 1;
      Queue.pop global_pool.space_pool
    with Queue.Empty ->
      stats.allocated <- stats.allocated + 1;
      TSpace
  
  let alloc_newline () =
    try
      stats.reused <- stats.reused + 1;
      Queue.pop global_pool.newline_pool
    with Queue.Empty ->
      stats.allocated <- stats.allocated + 1;
      TNewline
  
  let alloc_math () =
    try
      stats.reused <- stats.reused + 1;
      Queue.pop global_pool.math_pool
    with Queue.Empty ->
      stats.allocated <- stats.allocated + 1;
      TMath
  
  let alloc_command cmd =
    let interned = StringPool.intern global_pool.string_pool cmd in
    stats.allocated <- stats.allocated + 1;
    TCommand interned
  
  let alloc_begin_env env =
    let interned = StringPool.intern global_pool.string_pool env in
    stats.allocated <- stats.allocated + 1;
    TBeginEnv interned
  
  let alloc_end_env env =
    let interned = StringPool.intern global_pool.string_pool env in
    stats.allocated <- stats.allocated + 1;
    TEndEnv interned
  
  let alloc_comment text =
    (* Comments are usually unique - no interning *)
    stats.allocated <- stats.allocated + 1;
    TComment text
  
  let alloc_verbatim text =
    (* Verbatim content is unique - no interning *)
    stats.allocated <- stats.allocated + 1;
    TVerbatim text
  
  let alloc_begin_group () =
    try
      stats.reused <- stats.reused + 1;
      Queue.pop global_pool.begin_group_pool
    with Queue.Empty ->
      stats.allocated <- stats.allocated + 1;
      TBeginGroup
  
  let alloc_end_group () =
    try
      stats.reused <- stats.reused + 1;
      Queue.pop global_pool.end_group_pool
    with Queue.Empty ->
      stats.allocated <- stats.allocated + 1;
      TEndGroup
  
  let alloc_error msg =
    stats.allocated <- stats.allocated + 1;
    TError msg
  
  (* Return tokens to pool *)
  let free_token tok =
    let try_return pool tok =
      if Queue.length pool < global_pool.max_pool_size then
        Queue.push tok pool
    in
    
    match tok with
    | TChar c when c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' ->
        try_return global_pool.char_pool tok
    | TSpace ->
        try_return global_pool.space_pool tok
    | TNewline ->
        try_return global_pool.newline_pool tok
    | TMath ->
        try_return global_pool.math_pool tok
    | TBeginGroup ->
        try_return global_pool.begin_group_pool tok
    | TEndGroup ->
        try_return global_pool.end_group_pool tok
    | _ -> ()  (* Don't pool other tokens *)
  
  (* Free a list of tokens *)
  let free_tokens tokens =
    List.iter free_token tokens
  
  (* Get pool statistics *)
  let get_stats () =
    let pool_sizes = [
      ("char", Queue.length global_pool.char_pool);
      ("space", Queue.length global_pool.space_pool);
      ("newline", Queue.length global_pool.newline_pool);
      ("math", Queue.length global_pool.math_pool);
      ("begin_group", Queue.length global_pool.begin_group_pool);
      ("end_group", Queue.length global_pool.end_group_pool);
    ] in
    
    let total_pooled = List.fold_left (fun acc (_, size) -> acc + size) 0 pool_sizes in
    let string_count, string_memory = StringPool.get_stats global_pool.string_pool in
    
    Printf.sprintf 
      "Token pools: %d pooled, %d allocated, %d reused (%.1f%% reuse rate)\n\
       String pool: %d strings, %d bytes\n\
       Pool sizes: %s"
      total_pooled
      stats.allocated
      stats.reused
      (float_of_int stats.reused /. float_of_int (stats.allocated + stats.reused) *. 100.0)
      string_count
      string_memory
      (String.concat ", " (List.map (fun (name, size) -> 
        Printf.sprintf "%s=%d" name size) pool_sizes))
  
  (* Clear all pools *)
  let clear_pools () =
    Queue.clear global_pool.char_pool;
    Queue.clear global_pool.space_pool;
    Queue.clear global_pool.newline_pool;
    Queue.clear global_pool.math_pool;
    Queue.clear global_pool.begin_group_pool;
    Queue.clear global_pool.end_group_pool;
    StringPool.clear global_pool.string_pool
  
  (* Trigger GC if memory pressure is high *)
  let check_memory_pressure () =
    stats.gc_pressure <- stats.gc_pressure + 1;
    if stats.gc_pressure mod 10000 = 0 then begin
      (* Check if we should run minor GC *)
      let stat = Gc.quick_stat () in
      if stat.Gc.minor_words > 10_000_000.0 then
        Gc.minor ()
    end
end

(* Efficient token list building *)
module TokenBuffer = struct
  type t = {
    mutable chunks : token list list;
    mutable current : token list;
    mutable size : int;
  }
  
  let create () = {
    chunks = [];
    current = [];
    size = 0;
  }
  
  let add_token buf tok =
    buf.current <- tok :: buf.current;
    buf.size <- buf.size + 1;
    
    (* Flush chunks periodically to avoid long lists *)
    if buf.size mod 1000 = 0 then begin
      buf.chunks <- buf.current :: buf.chunks;
      buf.current <- []
    end
  
  let add_char buf c =
    add_token buf (TokenPool.alloc_char c)
  
  let add_space buf =
    add_token buf (TokenPool.alloc_space ())
  
  let add_newline buf =
    add_token buf (TokenPool.alloc_newline ())
  
  let add_command buf cmd =
    add_token buf (TokenPool.alloc_command cmd)
  
  let to_list buf =
    let all_chunks = 
      if buf.current = [] then buf.chunks
      else buf.current :: buf.chunks in
    
    (* Reverse and concatenate efficiently *)
    List.fold_left (fun acc chunk -> 
      List.rev_append chunk acc
    ) [] all_chunks
  
  let clear buf =
    (* Return tokens to pool before clearing *)
    TokenPool.free_tokens buf.current;
    List.iter TokenPool.free_tokens buf.chunks;
    buf.chunks <- [];
    buf.current <- [];
    buf.size <- 0
end

(* Memory-efficient token comparison *)
let token_equal t1 t2 =
  match t1, t2 with
  | TChar c1, TChar c2 -> c1 = c2
  | TSpace, TSpace -> true
  | TNewline, TNewline -> true
  | TMath, TMath -> true
  | TCommand s1, TCommand s2 -> s1 == s2  (* Physical equality due to interning *)
  | TBeginEnv s1, TBeginEnv s2 -> s1 == s2
  | TEndEnv s1, TEndEnv s2 -> s1 == s2
  | TBeginGroup, TBeginGroup -> true
  | TEndGroup, TEndGroup -> true
  | TComment s1, TComment s2 -> s1 = s2
  | TVerbatim s1, TVerbatim s2 -> s1 = s2
  | TError s1, TError s2 -> s1 = s2
  | _ -> false

(* Estimate memory usage of tokens *)
let estimate_token_memory tokens =
  List.fold_left (fun acc tok ->
    acc + match tok with
    | TChar _ -> 24  (* OCaml object header + char *)
    | TSpace | TNewline | TMath | TBeginGroup | TEndGroup -> 16  (* Just header *)
    | TCommand _ | TBeginEnv _ | TEndEnv _ -> 24 + 8  (* Header + pointer (interned) *)
    | TComment s | TVerbatim s | TError s -> 24 + String.length s + 24  (* Header + string *)
  ) 0 tokens

(* Memory pressure monitor *)
let monitor_memory () =
  let stat = Gc.stat () in
  let heap_mb = float_of_int stat.Gc.heap_words *. 8.0 /. 1024.0 /. 1024.0 in
  let live_mb = float_of_int stat.Gc.live_words *. 8.0 /. 1024.0 /. 1024.0 in
  
  if heap_mb > 500.0 then begin
    (* High memory usage - trigger major GC *)
    Gc.full_major ();
    TokenPool.clear_pools ()
  end else if heap_mb > 200.0 then begin
    (* Medium memory usage - compact *)
    Gc.compact ()
  end;
  
  (heap_mb, live_mb)