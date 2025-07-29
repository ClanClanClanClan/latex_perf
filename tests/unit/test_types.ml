
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (succ n) m
 end

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::t -> app (f x) (flat_map f t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> (||) (f a) (existsb f l0)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x::tl -> if f x then Some x else find f tl

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val length : char list -> int **)

let rec length = function
| [] -> 0
| _::s' -> succ (length s')

(** val prefix : char list -> char list -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | [] -> true
  | a::s1' ->
    (match s2 with
     | [] -> false
     | b::s2' -> if (=) a b then prefix s1' s2' else false)

type validation_issue = { rule_id : char list; issue_severity : severity;
                          message : char list; loc : (int * int) option;
                          suggested_fix : char list option;
                          rule_owner : char list }

type document_state = { tokens : latex_token list;
                        expanded_tokens : latex_token list option;
                        ast : char list option; semantics : char list option;
                        filename : char list; doc_layer : layer }

(** val get_expanded_tokens : document_state -> latex_token list **)

let get_expanded_tokens doc =
  match doc.expanded_tokens with
  | Some tokens0 -> tokens0
  | None -> doc.tokens

(** val is_expanded : document_state -> bool **)

let is_expanded doc =
  match doc.doc_layer with
  | L1_Expanded -> true
  | _ -> false

type env_entry =
| EnvBegin of char list * int
| EnvEnd of char list * int

type semantic_context = { env_stack : env_entry list; math_mode : bool;
                          current_line : int;
                          packages_loaded : char list list;
                          labels_defined : char list list;
                          refs_used : char list list; figures_count : 
                          int; tables_count : int; equations_count : 
                          int }

(** val init_context : semantic_context **)

let init_context =
  { env_stack = []; math_mode = false; current_line = (succ 0);
    packages_loaded = []; labels_defined = []; refs_used = [];
    figures_count = 0; tables_count = 0; equations_count = 0 }

(** val string_contains_substring : char list -> char list -> bool **)

let rec string_contains_substring s sub =
  match s with
  | [] -> eqb sub []
  | _::rest ->
    if prefix sub s then true else string_contains_substring rest sub

(** val update_context :
    semantic_context -> latex_token -> semantic_context **)

let update_context ctx = function
| TCommand s ->
  (match s with
   | [] -> ctx
   | a::s0 ->
     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
       (fun b b0 b1 b2 b3 b4 b5 b6 ->
       if b
       then if b0
            then ctx
            else if b1
                 then if b2
                      then ctx
                      else if b3
                           then if b4
                                then if b5
                                     then if b6
                                          then ctx
                                          else (match s0 with
                                                | [] -> ctx
                                                | a0::s1 ->
                                                  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                    (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                    if b7
                                                    then if b8
                                                         then if b9
                                                              then ctx
                                                              else if b10
                                                                   then ctx
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then ctx
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then ctx
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then ctx
                                                                    else 
                                                                    if b19
                                                                    then ctx
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then ctx
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then ctx
                                                                    else 
                                                                    if b24
                                                                    then ctx
                                                                    else 
                                                                    if b25
                                                                    then ctx
                                                                    else 
                                                                    if b26
                                                                    then ctx
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then ctx
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then ctx
                                                                    else 
                                                                    if b33
                                                                    then ctx
                                                                    else 
                                                                    if b34
                                                                    then ctx
                                                                    else 
                                                                    if b35
                                                                    then ctx
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then ctx
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then ctx
                                                                    else 
                                                                    if b42
                                                                    then ctx
                                                                    else 
                                                                    if b43
                                                                    then ctx
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then ctx
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then ctx
                                                                    else 
                                                                    if b50
                                                                    then 
                                                                    if b51
                                                                    then ctx
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then ctx
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    if b56
                                                                    then ctx
                                                                    else 
                                                                    if b57
                                                                    then ctx
                                                                    else 
                                                                    if b58
                                                                    then ctx
                                                                    else 
                                                                    if b59
                                                                    then ctx
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then ctx
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    if b64
                                                                    then 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then ctx
                                                                    else 
                                                                    if b67
                                                                    then ctx
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then ctx
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then ctx
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then ctx
                                                                    else 
                                                                    if b75
                                                                    then ctx
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then ctx
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    { env_stack =
                                                                    ctx.env_stack;
                                                                    math_mode =
                                                                    ctx.math_mode;
                                                                    current_line =
                                                                    ctx.current_line;
                                                                    packages_loaded =
                                                                    (('u'::('n'::('k'::('n'::('o'::('w'::('n'::('_'::('p'::('a'::('c'::('k'::('a'::('g'::('e'::[])))))))))))))))::ctx.packages_loaded);
                                                                    labels_defined =
                                                                    ctx.labels_defined;
                                                                    refs_used =
                                                                    ctx.refs_used;
                                                                    figures_count =
                                                                    ctx.figures_count;
                                                                    tables_count =
                                                                    ctx.tables_count;
                                                                    equations_count =
                                                                    ctx.equations_count }
                                                                    | _::_ ->
                                                                    ctx)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a8)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a7)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a6)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a5)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a4)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a3)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a2)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a1)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                         else ctx
                                                    else ctx)
                                                    a0)
                                     else ctx
                                else ctx
                           else if b4
                                then if b5
                                     then if b6
                                          then ctx
                                          else (match s0 with
                                                | [] -> ctx
                                                | a0::s1 ->
                                                  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                    (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                    if b7
                                                    then ctx
                                                    else if b8
                                                         then if b9
                                                              then if b10
                                                                   then 
                                                                    if b11
                                                                    then ctx
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then ctx
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then ctx
                                                                    else 
                                                                    if b16
                                                                    then ctx
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then ctx
                                                                    else 
                                                                    if b19
                                                                    then ctx
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then ctx
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    (match ctx.env_stack with
                                                                    | [] ->
                                                                    ctx
                                                                    | e::rest ->
                                                                    (match e with
                                                                    | EnvBegin (
                                                                    _, _) ->
                                                                    { env_stack =
                                                                    rest;
                                                                    math_mode =
                                                                    ctx.math_mode;
                                                                    current_line =
                                                                    ctx.current_line;
                                                                    packages_loaded =
                                                                    ctx.packages_loaded;
                                                                    labels_defined =
                                                                    ctx.labels_defined;
                                                                    refs_used =
                                                                    ctx.refs_used;
                                                                    figures_count =
                                                                    ctx.figures_count;
                                                                    tables_count =
                                                                    ctx.tables_count;
                                                                    equations_count =
                                                                    ctx.equations_count }
                                                                    | EnvEnd (
                                                                    _, _) ->
                                                                    ctx))
                                                                    | _::_ ->
                                                                    ctx)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a1)
                                                                    else ctx
                                                                    else ctx
                                                                   else ctx
                                                              else ctx
                                                         else ctx)
                                                    a0)
                                     else ctx
                                else ctx
                 else ctx
       else if b0
            then if b1
                 then ctx
                 else if b2
                      then ctx
                      else if b3
                           then ctx
                           else if b4
                                then if b5
                                     then if b6
                                          then ctx
                                          else (match s0 with
                                                | [] -> ctx
                                                | a0::s1 ->
                                                  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                    (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                    if b7
                                                    then if b8
                                                         then ctx
                                                         else if b9
                                                              then if b10
                                                                   then ctx
                                                                   else 
                                                                    if b11
                                                                    then ctx
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then ctx
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then ctx
                                                                    else 
                                                                    if b19
                                                                    then ctx
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then ctx
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then ctx
                                                                    else 
                                                                    if b25
                                                                    then ctx
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then ctx
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then ctx
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    ctx
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then ctx
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then ctx
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then ctx
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    { env_stack =
                                                                    ((EnvBegin
                                                                    (('u'::('n'::('k'::('n'::('o'::('w'::('n'::[]))))))),
                                                                    ctx.current_line))::ctx.env_stack);
                                                                    math_mode =
                                                                    ctx.math_mode;
                                                                    current_line =
                                                                    ctx.current_line;
                                                                    packages_loaded =
                                                                    ctx.packages_loaded;
                                                                    labels_defined =
                                                                    ctx.labels_defined;
                                                                    refs_used =
                                                                    ctx.refs_used;
                                                                    figures_count =
                                                                    ctx.figures_count;
                                                                    tables_count =
                                                                    ctx.tables_count;
                                                                    equations_count =
                                                                    ctx.equations_count }
                                                                    | _::_ ->
                                                                    ctx)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a3)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a2)
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx
                                                                    else ctx)
                                                                    a1)
                                                                    else ctx
                                                                    else ctx
                                                              else ctx
                                                    else ctx)
                                                    a0)
                                     else ctx
                                else ctx
            else ctx)
       a)
| TText s ->
  if string_contains_substring s ('\\'::('n'::[]))
  then { env_stack = ctx.env_stack; math_mode = ctx.math_mode; current_line =
         (succ ctx.current_line); packages_loaded = ctx.packages_loaded;
         labels_defined = ctx.labels_defined; refs_used = ctx.refs_used;
         figures_count = ctx.figures_count; tables_count = ctx.tables_count;
         equations_count = ctx.equations_count }
  else ctx
| _ -> ctx

(** val build_context :
    latex_token list -> semantic_context -> semantic_context **)

let rec build_context tokens0 ctx =
  match tokens0 with
  | [] -> ctx
  | tok::rest -> build_context rest (update_context ctx tok)

(** val check_brace_balance : latex_token list -> int -> bool **)

let rec check_brace_balance tokens0 depth =
  match tokens0 with
  | [] -> negb ((=) depth 0)
  | l::rest ->
    (match l with
     | TBeginGroup -> check_brace_balance rest (succ depth)
     | TEndGroup ->
       if (=) depth 0 then true else check_brace_balance rest (Nat.pred depth)
     | _ -> check_brace_balance rest depth)

(** val delim_001_validator_real : document_state -> validation_issue list **)

let delim_001_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       if check_brace_balance expanded 0
       then { rule_id =
              ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('1'::[])))))))));
              issue_severity = Error; message =
              ('U'::('n'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::(' '::('{'::(' '::('}'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('m'::('a'::('c'::('r'::('o'::(' '::('e'::('x'::('p'::('a'::('n'::('s'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))));
              loc = None; suggested_fix = (Some
              ('b'::('a'::('l'::('a'::('n'::('c'::('e'::('_'::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::[])))))))))))))))))));
              rule_owner =
              ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::[]
       else []
  else []

(** val check_extra_closing : latex_token list -> int -> bool **)

let rec check_extra_closing tokens0 depth =
  match tokens0 with
  | [] -> false
  | l::rest ->
    (match l with
     | TBeginGroup -> check_extra_closing rest (succ depth)
     | TEndGroup ->
       if (=) depth 0 then true else check_extra_closing rest (Nat.pred depth)
     | _ -> check_extra_closing rest depth)

(** val delim_002_validator_real : document_state -> validation_issue list **)

let delim_002_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       if check_extra_closing expanded 0
       then { rule_id =
              ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('2'::[])))))))));
              issue_severity = Error; message =
              ('E'::('x'::('t'::('r'::('a'::(' '::('c'::('l'::('o'::('s'::('i'::('n'::('g'::(' '::('}'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('i'::('n'::(' '::('e'::('x'::('p'::('a'::('n'::('d'::('e'::('d'::(' '::('t'::('o'::('k'::('e'::('n'::('s'::[])))))))))))))))))))))))))))))))))))))))))));
              loc = None; suggested_fix = (Some
              ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('x'::('t'::('r'::('a'::('_'::('b'::('r'::('a'::('c'::('e'::[])))))))))))))))))));
              rule_owner =
              ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::[]
       else []
  else []

(** val check_left_right_pairs : latex_token list -> int -> bool **)

let rec check_left_right_pairs tokens0 left_count =
  match tokens0 with
  | [] -> negb ((=) left_count 0)
  | l::rest ->
    (match l with
     | TCommand s ->
       (match s with
        | [] -> check_left_right_pairs rest left_count
        | a::s0 ->
          (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
            (fun b b0 b1 b2 b3 b4 b5 b6 ->
            if b
            then check_left_right_pairs rest left_count
            else if b0
                 then if b1
                      then check_left_right_pairs rest left_count
                      else if b2
                           then check_left_right_pairs rest left_count
                           else if b3
                                then if b4
                                     then if b5
                                          then if b6
                                               then check_left_right_pairs
                                                      rest left_count
                                               else (match s0 with
                                                     | [] ->
                                                       check_left_right_pairs
                                                         rest left_count
                                                     | a0::s1 ->
                                                       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                         (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                         if b7
                                                         then if b8
                                                              then check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                              else if b9
                                                                   then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                   else 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    if 
                                                                    (=)
                                                                    left_count
                                                                    0
                                                                    then true
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    (Nat.pred
                                                                    left_count)
                                                                    | _::_ ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count)
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count)
                                                                    a3)
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count)
                                                                    a2)
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count)
                                                                    a1)
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                         else check_left_right_pairs
                                                                rest
                                                                left_count)
                                                         a0)
                                          else check_left_right_pairs rest
                                                 left_count
                                     else check_left_right_pairs rest
                                            left_count
                                else check_left_right_pairs rest left_count
                 else if b1
                      then if b2
                           then if b3
                                then check_left_right_pairs rest left_count
                                else if b4
                                     then if b5
                                          then if b6
                                               then check_left_right_pairs
                                                      rest left_count
                                               else (match s0 with
                                                     | [] ->
                                                       check_left_right_pairs
                                                         rest left_count
                                                     | a0::s1 ->
                                                       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                         (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                         if b7
                                                         then if b8
                                                              then check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                              else if b9
                                                                   then 
                                                                    if b10
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    (succ
                                                                    left_count)
                                                                    | _::_ ->
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count)
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count)
                                                                    a2)
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count)
                                                                    a1)
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                                   else 
                                                                    check_left_right_pairs
                                                                    rest
                                                                    left_count
                                                         else check_left_right_pairs
                                                                rest
                                                                left_count)
                                                         a0)
                                          else check_left_right_pairs rest
                                                 left_count
                                     else check_left_right_pairs rest
                                            left_count
                           else check_left_right_pairs rest left_count
                      else check_left_right_pairs rest left_count)
            a)
     | _ -> check_left_right_pairs rest left_count)

(** val delim_003_validator_real : document_state -> validation_issue list **)

let delim_003_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       if check_left_right_pairs expanded 0
       then { rule_id =
              ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('3'::[])))))))));
              issue_severity = Error; message =
              ('U'::('n'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('\\'::('\\'::('l'::('e'::('f'::('t'::(' '::('w'::('i'::('t'::('h'::('o'::('u'::('t'::(' '::('c'::('o'::('r'::('r'::('e'::('s'::('p'::('o'::('n'::('d'::('i'::('n'::('g'::(' '::('\\'::('\\'::('r'::('i'::('g'::('h'::('t'::(' '::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))));
              loc = None; suggested_fix = (Some
              ('a'::('d'::('d'::('_'::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))));
              rule_owner =
              ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::[]
       else []
  else []

(** val check_math_commands_misplaced :
    latex_token list -> bool -> char list list -> validation_issue list **)

let rec check_math_commands_misplaced tokens0 in_math math_cmds =
  match tokens0 with
  | [] -> []
  | l::rest ->
    (match l with
     | TCommand cmd ->
       if (&&) (existsb (eqb cmd) math_cmds) (negb in_math)
       then { rule_id =
              ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('9'::[]))))))));
              issue_severity = Warning; message =
              (append
                ('M'::('a'::('t'::('h'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('\\'::('\\'::[])))))))))))))))
                (append cmd
                  (' '::('u'::('s'::('e'::('d'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('m'::('a'::('t'::('h'::(' '::('m'::('o'::('d'::('e'::[])))))))))))))))))))))))));
              loc = None; suggested_fix = (Some
              ('w'::('r'::('a'::('p'::('_'::('i'::('n'::('_'::('m'::('a'::('t'::('h'::('_'::('m'::('o'::('d'::('e'::[]))))))))))))))))));
              rule_owner =
              ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
              (check_math_commands_misplaced rest in_math math_cmds)
       else check_math_commands_misplaced rest in_math math_cmds
     | TMathShift ->
       check_math_commands_misplaced rest (negb in_math) math_cmds
     | _ -> check_math_commands_misplaced rest in_math math_cmds)

(** val math_009_validator_real : document_state -> validation_issue list **)

let math_009_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let math_commands =
         ('f'::('r'::('a'::('c'::[]))))::(('s'::('q'::('r'::('t'::[]))))::(('s'::('u'::('m'::[])))::(('p'::('r'::('o'::('d'::[]))))::(('i'::('n'::('t'::[])))::(('l'::('i'::('m'::[])))::(('i'::('n'::('f'::('t'::('y'::[])))))::(('a'::('l'::('p'::('h'::('a'::[])))))::(('b'::('e'::('t'::('a'::[]))))::(('g'::('a'::('m'::('m'::('a'::[])))))::(('t'::('h'::('e'::('t'::('a'::[])))))::(('c'::('d'::('o'::('t'::[]))))::[])))))))))))
       in
       check_math_commands_misplaced expanded false math_commands
  else []

(** val extract_ref_labels : latex_token list -> char list list **)

let rec extract_ref_labels = function
| [] -> []
| l::rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> extract_ref_labels rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then if b0
               then extract_ref_labels rest
               else if b1
                    then if b2
                         then extract_ref_labels rest
                         else if b3
                              then extract_ref_labels rest
                              else if b4
                                   then if b5
                                        then if b6
                                             then extract_ref_labels rest
                                             else (match s0 with
                                                   | [] ->
                                                     extract_ref_labels rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then extract_ref_labels
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   extract_ref_labels
                                                                    rest
                                                                 else 
                                                                   if b10
                                                                   then 
                                                                    extract_ref_labels
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    (match rest with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | l0::l1 ->
                                                                    (match l0 with
                                                                    | TBeginGroup ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | l2::l3 ->
                                                                    (match l2 with
                                                                    | TText label ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | l4::rest0 ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    label::
                                                                    (extract_ref_labels
                                                                    rest0)
                                                                    | _ ->
                                                                    extract_ref_labels
                                                                    rest))
                                                                    | _ ->
                                                                    extract_ref_labels
                                                                    rest))
                                                                    | _ ->
                                                                    extract_ref_labels
                                                                    rest))
                                                                    | _::_ ->
                                                                    extract_ref_labels
                                                                    rest)
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                       else extract_ref_labels
                                                              rest)
                                                       a0)
                                        else extract_ref_labels rest
                                   else extract_ref_labels rest
                    else extract_ref_labels rest
          else if b0
               then if b1
                    then extract_ref_labels rest
                    else if b2
                         then extract_ref_labels rest
                         else if b3
                              then if b4
                                   then if b5
                                        then if b6
                                             then extract_ref_labels rest
                                             else (match s0 with
                                                   | [] ->
                                                     extract_ref_labels rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then extract_ref_labels
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   if b10
                                                                   then 
                                                                    extract_ref_labels
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    (match rest with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | l0::l1 ->
                                                                    (match l0 with
                                                                    | TBeginGroup ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | l2::l3 ->
                                                                    (match l2 with
                                                                    | TText label ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    extract_ref_labels
                                                                    rest
                                                                    | l4::rest0 ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    label::
                                                                    (extract_ref_labels
                                                                    rest0)
                                                                    | _ ->
                                                                    extract_ref_labels
                                                                    rest))
                                                                    | _ ->
                                                                    extract_ref_labels
                                                                    rest))
                                                                    | _ ->
                                                                    extract_ref_labels
                                                                    rest))
                                                                    | _::_ ->
                                                                    extract_ref_labels
                                                                    rest)
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                    else 
                                                                    extract_ref_labels
                                                                    rest
                                                                 else 
                                                                   extract_ref_labels
                                                                    rest
                                                       else extract_ref_labels
                                                              rest)
                                                       a0)
                                        else extract_ref_labels rest
                                   else extract_ref_labels rest
                              else extract_ref_labels rest
               else extract_ref_labels rest)
          a)
   | _ -> extract_ref_labels rest)

(** val ref_001_validator_real : document_state -> validation_issue list **)

let ref_001_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let ctx = build_context expanded init_context in
       let referenced_labels = extract_ref_labels expanded in
       flat_map (fun ref_label ->
         if existsb (fun def_label -> eqb ref_label def_label)
              ctx.labels_defined
         then []
         else { rule_id =
                ('R'::('E'::('F'::('-'::('0'::('0'::('1'::[])))))));
                issue_severity = Error; message =
                (append
                  ('U'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('\\'::('\\'::('r'::('e'::('f'::('/'::('\\'::('\\'::('e'::('q'::('r'::('e'::('f'::(' '::('l'::('a'::('b'::('e'::('l'::(':'::(' '::[])))))))))))))))))))))))))))))))
                  ref_label); loc = None; suggested_fix = (Some
                ('d'::('e'::('f'::('i'::('n'::('e'::('_'::('m'::('i'::('s'::('s'::('i'::('n'::('g'::('_'::('l'::('a'::('b'::('e'::('l'::[])))))))))))))))))))));
                rule_owner =
                ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::[])
         referenced_labels
  else []

(** val check_subscripts : latex_token list -> validation_issue list **)

let rec check_subscripts = function
| [] -> []
| l::rest ->
  (match l with
   | TSubscript ->
     (match rest with
      | [] -> check_subscripts rest
      | l0::rest0 ->
        (match l0 with
         | TText sub ->
           if Nat.ltb (succ 0) (length sub)
           then { rule_id =
                  ('S'::('C'::('R'::('I'::('P'::('T'::('-'::('0'::('0'::('1'::[]))))))))));
                  issue_severity = Warning; message =
                  (append
                    (append
                      (append
                        (append
                          ('M'::('u'::('l'::('t'::('i'::('-'::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::(' '::('s'::('u'::('b'::('s'::('c'::('r'::('i'::('p'::('t'::(' '::('\''::[])))))))))))))))))))))))))))
                          sub)
                        ('\''::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('i'::('n'::(' '::('b'::('r'::('a'::('c'::('e'::('s'::(':'::(' '::('_'::('{'::[]))))))))))))))))))))))))))
                      sub) ('}'::[])); loc = None; suggested_fix = (Some
                  ('w'::('r'::('a'::('p'::('_'::('s'::('u'::('b'::('s'::('c'::('r'::('i'::('p'::('t'::('_'::('i'::('n'::('_'::('b'::('r'::('a'::('c'::('e'::('s'::[])))))))))))))))))))))))));
                  rule_owner =
                  ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
                  (check_subscripts rest0)
           else check_subscripts rest0
         | _ -> check_subscripts rest))
   | _ -> check_subscripts rest)

(** val script_001_validator_real :
    document_state -> validation_issue list **)

let script_001_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in check_subscripts expanded
  else []

(** val cmd_001_validator_real : document_state -> validation_issue list **)

let cmd_001_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let obsolete_commands = (('b'::('f'::[])),
         ('t'::('e'::('x'::('t'::('b'::('f'::[])))))))::((('i'::('t'::[])),
         ('t'::('e'::('x'::('t'::('i'::('t'::[])))))))::((('r'::('m'::[])),
         ('t'::('e'::('x'::('t'::('r'::('m'::[])))))))::((('s'::('f'::[])),
         ('t'::('e'::('x'::('t'::('s'::('f'::[])))))))::((('t'::('t'::[])),
         ('t'::('e'::('x'::('t'::('t'::('t'::[])))))))::((('s'::('c'::[])),
         ('t'::('e'::('x'::('t'::('s'::('c'::[])))))))::((('e'::('m'::[])),
         ('e'::('m'::('p'::('h'::[])))))::((('c'::('a'::('l'::[]))),
         ('m'::('a'::('t'::('h'::('c'::('a'::('l'::[]))))))))::((('c'::('e'::('n'::('t'::('e'::('r'::('l'::('i'::('n'::('e'::[])))))))))),
         ('c'::('e'::('n'::('t'::('e'::('r'::('i'::('n'::('g'::[]))))))))))::((('o'::('v'::('e'::('r'::[])))),
         ('f'::('r'::('a'::('c'::[])))))::[])))))))))
       in
       flat_map (fun tok ->
         match tok with
         | TCommand cmd ->
           (match find (fun pair -> eqb (fst pair) cmd) obsolete_commands with
            | Some p ->
              let (obs, repl) = p in
              { rule_id =
              ('C'::('M'::('D'::('-'::('0'::('0'::('1'::[])))))));
              issue_severity = Info; message =
              (append
                (append
                  (append
                    (append
                      ('O'::('b'::('s'::('o'::('l'::('e'::('t'::('e'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('\\'::('\\'::[])))))))))))))))))))
                      obs)
                    (' '::('-'::(' '::('u'::('s'::('e'::(' '::('\\'::('\\'::[]))))))))))
                  repl)
                (' '::('i'::('n'::('s'::('t'::('e'::('a'::('d'::[])))))))));
              loc = None; suggested_fix = (Some
              (append ('u'::('s'::('e'::('_'::[])))) repl)); rule_owner =
              ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::[]
            | None -> [])
         | _ -> []) expanded
  else []

(** val math_010_validator_real : document_state -> validation_issue list **)

let math_010_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let check_division_symbol = fun tok ->
         match tok with
         | TCommand _ -> []
         | TBeginGroup -> []
         | TEndGroup -> []
         | TMathShift -> []
         | TAlignment -> []
         | TParameter -> []
         | TSuperscript -> []
         | TSubscript -> []
         | TText s ->
           if string_contains_substring s ('\194'::('\183'::[]))
           then { rule_id =
                  ('M'::('A'::('T'::('H'::('-'::('0'::('1'::('0'::[]))))))));
                  issue_severity = Warning; message =
                  ('D'::('i'::('v'::('i'::('s'::('i'::('o'::('n'::(' '::('s'::('y'::('m'::('b'::('o'::('l'::(' '::('\194'::('\183'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('-'::(' '::('u'::('s'::('e'::(' '::('\\'::('\\'::('f'::('r'::('a'::('c'::('{'::('a'::('}'::('{'::('b'::('}'::(' '::('o'::('r'::(' '::('/'::(' '::('i'::('n'::('s'::('t'::('e'::('a'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
                  loc = None; suggested_fix = (Some
                  ('u'::('s'::('e'::('_'::('c'::('d'::('o'::('t'::('_'::('c'::('o'::('m'::('m'::('a'::('n'::('d'::[])))))))))))))))));
                  rule_owner =
                  ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::[]
           else []
         | _ -> []
       in
       flat_map check_division_symbol expanded
  else []

(** val check_multi_letter_functions :
    latex_token list -> char list list -> validation_issue list **)

let rec check_multi_letter_functions tokens0 multi_letter_functions =
  match tokens0 with
  | [] -> []
  | l::rest ->
    (match l with
     | TText s ->
       if existsb (fun fname -> eqb s fname) multi_letter_functions
       then { rule_id =
              ('M'::('A'::('T'::('H'::('-'::('0'::('1'::('2'::[]))))))));
              issue_severity = Warning; message =
              (append
                (append
                  (append
                    (append
                      ('M'::('u'::('l'::('t'::('i'::('-'::('l'::('e'::('t'::('t'::('e'::('r'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('\''::[])))))))))))))))))))))))
                      s)
                    ('\''::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('u'::('s'::('e'::(' '::('\\'::('\\'::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('n'::('a'::('m'::('e'::('{'::[])))))))))))))))))))))))))))))
                  s) ('}'::[])); loc = None; suggested_fix = (Some
              ('w'::('r'::('a'::('p'::('_'::('i'::('n'::('_'::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('n'::('a'::('m'::('e'::[])))))))))))))))))))));
              rule_owner =
              ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
              (check_multi_letter_functions rest multi_letter_functions)
       else check_multi_letter_functions rest multi_letter_functions
     | _ -> check_multi_letter_functions rest multi_letter_functions)

(** val math_012_validator_real : document_state -> validation_issue list **)

let math_012_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let multi_letter_functions =
         ('s'::('i'::('n'::[])))::(('c'::('o'::('s'::[])))::(('t'::('a'::('n'::[])))::(('l'::('o'::('g'::[])))::(('e'::('x'::('p'::[])))::(('m'::('a'::('x'::[])))::(('m'::('i'::('n'::[])))::(('d'::('e'::('t'::[])))::(('t'::('r'::[]))::(('d'::('i'::('m'::[])))::[])))))))))
       in
       check_multi_letter_functions expanded multi_letter_functions
  else []

(** val math_015_validator_real : document_state -> validation_issue list **)

let math_015_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let check_stackrel = fun tok ->
         match tok with
         | TCommand s ->
           (match s with
            | [] -> []
            | a::s0 ->
              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                (fun b b0 b1 b2 b3 b4 b5 b6 ->
                if b
                then if b0
                     then if b1
                          then []
                          else if b2
                               then []
                               else if b3
                                    then if b4
                                         then if b5
                                              then if b6
                                                   then []
                                                   else (match s0 with
                                                         | [] -> []
                                                         | a0::s1 ->
                                                           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                             (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                             if b7
                                                             then []
                                                             else if b8
                                                                  then []
                                                                  else 
                                                                    if b9
                                                                    then 
                                                                    if b10
                                                                    then []
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then []
                                                                    else 
                                                                    (match s1 with
                                                                    | [] -> []
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then []
                                                                    else 
                                                                    if b17
                                                                    then []
                                                                    else 
                                                                    if b18
                                                                    then []
                                                                    else 
                                                                    if b19
                                                                    then []
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then []
                                                                    else 
                                                                    (match s2 with
                                                                    | [] -> []
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then []
                                                                    else 
                                                                    if b26
                                                                    then []
                                                                    else 
                                                                    if b27
                                                                    then []
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then []
                                                                    else 
                                                                    (match s3 with
                                                                    | [] -> []
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    if b33
                                                                    then []
                                                                    else 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then []
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then []
                                                                    else 
                                                                    (match s4 with
                                                                    | [] -> []
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then []
                                                                    else 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then []
                                                                    else 
                                                                    if b42
                                                                    then []
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then []
                                                                    else 
                                                                    (match s5 with
                                                                    | [] -> []
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then []
                                                                    else 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then []
                                                                    else 
                                                                    if b51
                                                                    then []
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then []
                                                                    else 
                                                                    (match s6 with
                                                                    | [] -> []
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then []
                                                                    else 
                                                                    if b56
                                                                    then []
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then 
                                                                    if b59
                                                                    then []
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then []
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    { rule_id =
                                                                    ('M'::('A'::('T'::('H'::('-'::('0'::('1'::('5'::[]))))))));
                                                                    issue_severity =
                                                                    Warning;
                                                                    message =
                                                                    ('\\'::('\\'::('s'::('t'::('a'::('c'::('k'::('r'::('e'::('l'::(' '::('i'::('s'::(' '::('o'::('b'::('s'::('o'::('l'::('e'::('t'::('e'::(' '::('-'::(' '::('u'::('s'::('e'::(' '::('\\'::('\\'::('o'::('v'::('e'::('r'::('s'::('e'::('t'::('{'::('a'::('b'::('o'::('v'::('e'::('}'::('{'::('b'::('a'::('s'::('e'::('}'::[])))))))))))))))))))))))))))))))))))))))))))))))))));
                                                                    loc =
                                                                    None;
                                                                    suggested_fix =
                                                                    (Some
                                                                    ('r'::('e'::('p'::('l'::('a'::('c'::('e'::('_'::('w'::('i'::('t'::('h'::('_'::('o'::('v'::('e'::('r'::('s'::('e'::('t'::[])))))))))))))))))))));
                                                                    rule_owner =
                                                                    ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) }::[]
                                                                    | _::_ ->
                                                                    [])
                                                                    else []
                                                                    else []
                                                                    else []
                                                                    else [])
                                                                    a6)
                                                                    else []
                                                                    else []
                                                                    else []
                                                                    else [])
                                                                    a5)
                                                                    else []
                                                                    else []
                                                                    else []
                                                                    else [])
                                                                    a4)
                                                                    else []
                                                                    else []
                                                                    else []
                                                                    else []
                                                                    else [])
                                                                    a3)
                                                                    else []
                                                                    else []
                                                                    else []
                                                                    else [])
                                                                    a2)
                                                                    else []
                                                                    else []
                                                                    else [])
                                                                    a1)
                                                                    else []
                                                                    else []
                                                                    else []
                                                                    else [])
                                                             a0)
                                              else []
                                         else []
                                    else []
                     else []
                else [])
                a)
         | _ -> []
       in
       flat_map check_stackrel expanded
  else []

(** val check_nested_subscripts :
    latex_token list -> validation_issue list **)

let rec check_nested_subscripts = function
| [] -> []
| l::rest ->
  (match l with
   | TText s ->
     (match s with
      | [] -> check_nested_subscripts rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then if b0
               then if b1
                    then if b2
                         then if b3
                              then if b4
                                   then check_nested_subscripts rest
                                   else if b5
                                        then if b6
                                             then check_nested_subscripts rest
                                             else (match s0 with
                                                   | [] ->
                                                     (match rest with
                                                      | [] ->
                                                        check_nested_subscripts
                                                          rest
                                                      | l0::l1 ->
                                                        (match l0 with
                                                         | TText sub1 ->
                                                           (match l1 with
                                                            | [] ->
                                                              check_nested_subscripts
                                                                rest
                                                            | l2::l3 ->
                                                              (match l2 with
                                                               | TText s1 ->
                                                                 (match s1 with
                                                                  | [] ->
                                                                    check_nested_subscripts
                                                                    rest
                                                                  | a0::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                                    if b7
                                                                    then 
                                                                    if b8
                                                                    then 
                                                                    if b9
                                                                    then 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    check_nested_subscripts
                                                                    rest
                                                                    else 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_nested_subscripts
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    check_nested_subscripts
                                                                    rest
                                                                    | l4::rest0 ->
                                                                    (match l4 with
                                                                    | TText sub2 ->
                                                                    { rule_id =
                                                                    ('M'::('A'::('T'::('H'::('-'::('0'::('1'::('6'::[]))))))));
                                                                    issue_severity =
                                                                    Warning;
                                                                    message =
                                                                    (append
                                                                    (append
                                                                    (append
                                                                    (append
                                                                    ('N'::('e'::('s'::('t'::('e'::('d'::(' '::('s'::('u'::('b'::('s'::('c'::('r'::('i'::('p'::('t'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('-'::(' '::('u'::('s'::('e'::(' '::('b'::('r'::('a'::('c'::('e'::('s'::(':'::(' '::('_'::('{'::[])))))))))))))))))))))))))))))))))))))))))))
                                                                    sub1)
                                                                    ('_'::('{'::[])))
                                                                    sub2)
                                                                    ('}'::('}'::[])));
                                                                    loc =
                                                                    None;
                                                                    suggested_fix =
                                                                    (Some
                                                                    ('b'::('r'::('a'::('c'::('e'::('_'::('n'::('e'::('s'::('t'::('e'::('d'::('_'::('s'::('u'::('b'::('s'::('c'::('r'::('i'::('p'::('t'::('s'::[]))))))))))))))))))))))));
                                                                    rule_owner =
                                                                    ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) }::
                                                                    (check_nested_subscripts
                                                                    rest0)
                                                                    | _ ->
                                                                    check_nested_subscripts
                                                                    rest))
                                                                    | _::_ ->
                                                                    check_nested_subscripts
                                                                    rest)
                                                                    else 
                                                                    check_nested_subscripts
                                                                    rest
                                                                    else 
                                                                    check_nested_subscripts
                                                                    rest
                                                                    else 
                                                                    check_nested_subscripts
                                                                    rest
                                                                    else 
                                                                    check_nested_subscripts
                                                                    rest
                                                                    else 
                                                                    check_nested_subscripts
                                                                    rest
                                                                    else 
                                                                    check_nested_subscripts
                                                                    rest)
                                                                    a0)
                                                               | _ ->
                                                                 check_nested_subscripts
                                                                   rest))
                                                         | _ ->
                                                           check_nested_subscripts
                                                             rest))
                                                   | _::_ ->
                                                     check_nested_subscripts
                                                       rest)
                                        else check_nested_subscripts rest
                              else check_nested_subscripts rest
                         else check_nested_subscripts rest
                    else check_nested_subscripts rest
               else check_nested_subscripts rest
          else check_nested_subscripts rest)
          a)
   | _ -> check_nested_subscripts rest)

(** val math_016_validator_real : document_state -> validation_issue list **)

let math_016_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       check_nested_subscripts expanded
  else []

(** val math_018_validator_real : document_state -> validation_issue list **)

let math_018_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let check_pi_constant = fun tok ->
         match tok with
         | TCommand _ -> []
         | TBeginGroup -> []
         | TEndGroup -> []
         | TMathShift -> []
         | TAlignment -> []
         | TParameter -> []
         | TSuperscript -> []
         | TSubscript -> []
         | TText s ->
           if string_contains_substring s ('3'::('.'::('1'::('4'::[]))))
           then { rule_id =
                  ('M'::('A'::('T'::('H'::('-'::('0'::('1'::('8'::[]))))))));
                  issue_severity = Info; message =
                  ('P'::('i'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::('a'::('s'::(' '::('d'::('e'::('c'::('i'::('m'::('a'::('l'::(' '::('3'::('.'::('1'::('4'::('.'::('.'::('.'::(' '::('-'::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('\\'::('\\'::('p'::('i'::[]))))))))))))))))))))))))))))))))))))))))))))))))))));
                  loc = None; suggested_fix = (Some
                  ('u'::('s'::('e'::('_'::('p'::('i'::('_'::('s'::('y'::('m'::('b'::('o'::('l'::[]))))))))))))));
                  rule_owner =
                  ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) }::[]
           else []
         | _ -> []
       in
       flat_map check_pi_constant expanded
  else []

(** val extract_labels : latex_token list -> char list list **)

let rec extract_labels = function
| [] -> []
| l::rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> extract_labels rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then extract_labels rest
          else if b0
               then extract_labels rest
               else if b1
                    then if b2
                         then if b3
                              then extract_labels rest
                              else if b4
                                   then if b5
                                        then if b6
                                             then extract_labels rest
                                             else (match s0 with
                                                   | [] -> extract_labels rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then extract_labels
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   extract_labels
                                                                    rest
                                                                 else 
                                                                   if b10
                                                                   then 
                                                                    extract_labels
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    extract_labels
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    extract_labels
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    extract_labels
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    (match rest with
                                                                    | [] ->
                                                                    extract_labels
                                                                    rest
                                                                    | l0::l1 ->
                                                                    (match l0 with
                                                                    | TBeginGroup ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    extract_labels
                                                                    rest
                                                                    | l2::l3 ->
                                                                    (match l2 with
                                                                    | TText label ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    extract_labels
                                                                    rest
                                                                    | l4::rest0 ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    label::
                                                                    (extract_labels
                                                                    rest0)
                                                                    | _ ->
                                                                    extract_labels
                                                                    rest))
                                                                    | _ ->
                                                                    extract_labels
                                                                    rest))
                                                                    | _ ->
                                                                    extract_labels
                                                                    rest))
                                                                    | _::_ ->
                                                                    extract_labels
                                                                    rest)
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                                    else 
                                                                    extract_labels
                                                                    rest
                                                       else extract_labels
                                                              rest)
                                                       a0)
                                        else extract_labels rest
                                   else extract_labels rest
                         else extract_labels rest
                    else extract_labels rest)
          a)
   | _ -> extract_labels rest)

(** val find_duplicates :
    char list list -> char list list -> validation_issue list **)

let rec find_duplicates labels seen =
  match labels with
  | [] -> []
  | lbl::rest ->
    if existsb (fun seen_lbl -> eqb lbl seen_lbl) seen
    then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('2'::[])))))));
           issue_severity = Error; message =
           (append
             ('D'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('n'::('a'::('m'::('e'::(':'::(' '::[]))))))))))))))))))))))
             lbl); loc = None; suggested_fix = (Some
           ('r'::('e'::('n'::('a'::('m'::('e'::('_'::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::('_'::('l'::('a'::('b'::('e'::('l'::[])))))))))))))))))))))));
           rule_owner =
           ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
           (find_duplicates rest seen)
    else find_duplicates rest (lbl::seen)

(** val ref_002_validator_real : document_state -> validation_issue list **)

let ref_002_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       let all_labels = extract_labels expanded in
       find_duplicates all_labels []
  else []

(** val check_label_format : latex_token list -> validation_issue list **)

let rec check_label_format = function
| [] -> []
| l::rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> check_label_format rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then check_label_format rest
          else if b0
               then check_label_format rest
               else if b1
                    then if b2
                         then if b3
                              then check_label_format rest
                              else if b4
                                   then if b5
                                        then if b6
                                             then check_label_format rest
                                             else (match s0 with
                                                   | [] ->
                                                     check_label_format rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then check_label_format
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   check_label_format
                                                                    rest
                                                                 else 
                                                                   if b10
                                                                   then 
                                                                    check_label_format
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_label_format
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_label_format
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    check_label_format
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    (match rest with
                                                                    | [] ->
                                                                    check_label_format
                                                                    rest
                                                                    | l0::l1 ->
                                                                    (match l0 with
                                                                    | TBeginGroup ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    check_label_format
                                                                    rest
                                                                    | l2::l3 ->
                                                                    (match l2 with
                                                                    | TText label ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    check_label_format
                                                                    rest
                                                                    | l4::rest0 ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    if 
                                                                    string_contains_substring
                                                                    label
                                                                    (' '::[])
                                                                    then 
                                                                    { rule_id =
                                                                    ('R'::('E'::('F'::('-'::('0'::('0'::('3'::[])))))));
                                                                    issue_severity =
                                                                    Warning;
                                                                    message =
                                                                    (append
                                                                    (append
                                                                    ('L'::('a'::('b'::('e'::('l'::(' '::('\''::[])))))))
                                                                    label)
                                                                    ('\''::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::('s'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('-'::(' '::('u'::('s'::('e'::(' '::('h'::('y'::('p'::('h'::('e'::('n'::('s'::(' '::('o'::('r'::(' '::('u'::('n'::('d'::('e'::('r'::('s'::('c'::('o'::('r'::('e'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))));
                                                                    loc =
                                                                    None;
                                                                    suggested_fix =
                                                                    (Some
                                                                    ('r'::('e'::('p'::('l'::('a'::('c'::('e'::('_'::('s'::('p'::('a'::('c'::('e'::('s'::('_'::('i'::('n'::('_'::('l'::('a'::('b'::('e'::('l'::[]))))))))))))))))))))))));
                                                                    rule_owner =
                                                                    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
                                                                    (check_label_format
                                                                    rest0)
                                                                    else 
                                                                    check_label_format
                                                                    rest0
                                                                    | _ ->
                                                                    check_label_format
                                                                    rest))
                                                                    | _ ->
                                                                    check_label_format
                                                                    rest))
                                                                    | _ ->
                                                                    check_label_format
                                                                    rest))
                                                                    | _::_ ->
                                                                    check_label_format
                                                                    rest)
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                                    else 
                                                                    check_label_format
                                                                    rest
                                                       else check_label_format
                                                              rest)
                                                       a0)
                                        else check_label_format rest
                                   else check_label_format rest
                         else check_label_format rest
                    else check_label_format rest)
          a)
   | _ -> check_label_format rest)

(** val ref_003_validator_real : document_state -> validation_issue list **)

let ref_003_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in check_label_format expanded
  else []

(** val check_right_without_left :
    latex_token list -> int -> validation_issue list **)

let rec check_right_without_left tokens0 left_count =
  match tokens0 with
  | [] -> []
  | l::rest ->
    (match l with
     | TCommand s ->
       (match s with
        | [] -> check_right_without_left rest left_count
        | a::s0 ->
          (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
            (fun b b0 b1 b2 b3 b4 b5 b6 ->
            if b
            then check_right_without_left rest left_count
            else if b0
                 then if b1
                      then check_right_without_left rest left_count
                      else if b2
                           then check_right_without_left rest left_count
                           else if b3
                                then if b4
                                     then if b5
                                          then if b6
                                               then check_right_without_left
                                                      rest left_count
                                               else (match s0 with
                                                     | [] ->
                                                       check_right_without_left
                                                         rest left_count
                                                     | a0::s1 ->
                                                       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                         (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                         if b7
                                                         then if b8
                                                              then check_right_without_left
                                                                    rest
                                                                    left_count
                                                              else if b9
                                                                   then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                   else 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    if 
                                                                    (=)
                                                                    left_count
                                                                    0
                                                                    then 
                                                                    { rule_id =
                                                                    ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('4'::[])))))))));
                                                                    issue_severity =
                                                                    Error;
                                                                    message =
                                                                    ('\\'::('\\'::('r'::('i'::('g'::('h'::('t'::(' '::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::(' '::('w'::('i'::('t'::('h'::('o'::('u'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::(' '::('\\'::('\\'::('l'::('e'::('f'::('t'::[])))))))))))))))))))))))))))))))))))))))));
                                                                    loc =
                                                                    None;
                                                                    suggested_fix =
                                                                    (Some
                                                                    ('a'::('d'::('d'::('_'::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))));
                                                                    rule_owner =
                                                                    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
                                                                    (check_right_without_left
                                                                    rest 0)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    (Nat.pred
                                                                    left_count)
                                                                    | _::_ ->
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count)
                                                                    a3)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count)
                                                                    a2)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count)
                                                                    a1)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                         else check_right_without_left
                                                                rest
                                                                left_count)
                                                         a0)
                                          else check_right_without_left rest
                                                 left_count
                                     else check_right_without_left rest
                                            left_count
                                else check_right_without_left rest left_count
                 else if b1
                      then if b2
                           then if b3
                                then check_right_without_left rest left_count
                                else if b4
                                     then if b5
                                          then if b6
                                               then check_right_without_left
                                                      rest left_count
                                               else (match s0 with
                                                     | [] ->
                                                       check_right_without_left
                                                         rest left_count
                                                     | a0::s1 ->
                                                       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                         (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                         if b7
                                                         then if b8
                                                              then check_right_without_left
                                                                    rest
                                                                    left_count
                                                              else if b9
                                                                   then 
                                                                    if b10
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    check_right_without_left
                                                                    rest
                                                                    (succ
                                                                    left_count)
                                                                    | _::_ ->
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count)
                                                                    a2)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count)
                                                                    a1)
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                    else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                                   else 
                                                                    check_right_without_left
                                                                    rest
                                                                    left_count
                                                         else check_right_without_left
                                                                rest
                                                                left_count)
                                                         a0)
                                          else check_right_without_left rest
                                                 left_count
                                     else check_right_without_left rest
                                            left_count
                           else check_right_without_left rest left_count
                      else check_right_without_left rest left_count)
            a)
     | _ -> check_right_without_left rest left_count)

(** val delim_004_validator_real : document_state -> validation_issue list **)

let delim_004_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       check_right_without_left expanded 0
  else []

(** val check_angle_brackets :
    latex_token list -> int -> validation_issue list **)

let rec check_angle_brackets tokens0 langle_count =
  match tokens0 with
  | [] ->
    if Nat.ltb 0 langle_count
    then { rule_id =
           ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('7'::[])))))))));
           issue_severity = Error; message =
           ('U'::('n'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('\\'::('\\'::('l'::('a'::('n'::('g'::('l'::('e'::(' '::('w'::('i'::('t'::('h'::('o'::('u'::('t'::(' '::('\\'::('\\'::('r'::('a'::('n'::('g'::('l'::('e'::[])))))))))))))))))))))))))))))))))));
           loc = None; suggested_fix = (Some
           ('a'::('d'::('d'::('_'::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::('_'::('r'::('a'::('n'::('g'::('l'::('e'::[]))))))))))))))))))));
           rule_owner =
           ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::[]
    else []
  | l::rest ->
    (match l with
     | TCommand s ->
       (match s with
        | [] -> check_angle_brackets rest langle_count
        | a::s0 ->
          (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
            (fun b b0 b1 b2 b3 b4 b5 b6 ->
            if b
            then check_angle_brackets rest langle_count
            else if b0
                 then if b1
                      then check_angle_brackets rest langle_count
                      else if b2
                           then check_angle_brackets rest langle_count
                           else if b3
                                then if b4
                                     then if b5
                                          then if b6
                                               then check_angle_brackets rest
                                                      langle_count
                                               else (match s0 with
                                                     | [] ->
                                                       check_angle_brackets
                                                         rest langle_count
                                                     | a0::s1 ->
                                                       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                         (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                         if b7
                                                         then if b8
                                                              then check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                              else if b9
                                                                   then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                   else 
                                                                    if b10
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    if 
                                                                    (=)
                                                                    langle_count
                                                                    0
                                                                    then 
                                                                    { rule_id =
                                                                    ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('7'::[])))))))));
                                                                    issue_severity =
                                                                    Error;
                                                                    message =
                                                                    ('\\'::('\\'::('r'::('a'::('n'::('g'::('l'::('e'::(' '::('w'::('i'::('t'::('h'::('o'::('u'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::(' '::('\\'::('\\'::('l'::('a'::('n'::('g'::('l'::('e'::[]))))))))))))))))))))))))))))))))));
                                                                    loc =
                                                                    None;
                                                                    suggested_fix =
                                                                    (Some
                                                                    ('a'::('d'::('d'::('_'::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::('_'::('l'::('a'::('n'::('g'::('l'::('e'::[]))))))))))))))))))));
                                                                    rule_owner =
                                                                    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
                                                                    (check_angle_brackets
                                                                    rest 0)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    (Nat.pred
                                                                    langle_count)
                                                                    | _::_ ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a4)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a3)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a2)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a1)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                         else check_angle_brackets
                                                                rest
                                                                langle_count)
                                                         a0)
                                          else check_angle_brackets rest
                                                 langle_count
                                     else check_angle_brackets rest
                                            langle_count
                                else check_angle_brackets rest langle_count
                 else if b1
                      then if b2
                           then if b3
                                then check_angle_brackets rest langle_count
                                else if b4
                                     then if b5
                                          then if b6
                                               then check_angle_brackets rest
                                                      langle_count
                                               else (match s0 with
                                                     | [] ->
                                                       check_angle_brackets
                                                         rest langle_count
                                                     | a0::s1 ->
                                                       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                         (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                         if b7
                                                         then if b8
                                                              then check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                              else if b9
                                                                   then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                   else 
                                                                    if b10
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    (succ
                                                                    langle_count)
                                                                    | _::_ ->
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a4)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a3)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a2)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count)
                                                                    a1)
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                                    else 
                                                                    check_angle_brackets
                                                                    rest
                                                                    langle_count
                                                         else check_angle_brackets
                                                                rest
                                                                langle_count)
                                                         a0)
                                          else check_angle_brackets rest
                                                 langle_count
                                     else check_angle_brackets rest
                                            langle_count
                           else check_angle_brackets rest langle_count
                      else check_angle_brackets rest langle_count)
            a)
     | _ -> check_angle_brackets rest langle_count)

(** val delim_007_validator_real : document_state -> validation_issue list **)

let delim_007_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       check_angle_brackets expanded 0
  else []

(** val check_empty_left_right : latex_token list -> validation_issue list **)

let rec check_empty_left_right = function
| [] -> []
| l::rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> check_empty_left_right rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then check_empty_left_right rest
          else if b0
               then check_empty_left_right rest
               else if b1
                    then if b2
                         then if b3
                              then check_empty_left_right rest
                              else if b4
                                   then if b5
                                        then if b6
                                             then check_empty_left_right rest
                                             else (match s0 with
                                                   | [] ->
                                                     check_empty_left_right
                                                       rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then check_empty_left_right
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   if b10
                                                                   then 
                                                                    check_empty_left_right
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    (match rest with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | l0::rest0 ->
                                                                    (match l0 with
                                                                    | TCommand s4 ->
                                                                    (match s4 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a3::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    if b33
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b34
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a4::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b42
                                                                    then 
                                                                    if b43
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a5::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b51
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a6::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b56
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b58
                                                                    then 
                                                                    if b59
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a7::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b64
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    { rule_id =
                                                                    ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('8'::[])))))))));
                                                                    issue_severity =
                                                                    Info;
                                                                    message =
                                                                    ('E'::('m'::('p'::('t'::('y'::(' '::('\\'::('\\'::('l'::('e'::('f'::('t'::('\\'::('\\'::('r'::('i'::('g'::('h'::('t'::(' '::('p'::('a'::('i'::('r'::(' '::('i'::('s'::(' '::('r'::('e'::('d'::('u'::('n'::('d'::('a'::('n'::('t'::[])))))))))))))))))))))))))))))))))))));
                                                                    loc =
                                                                    None;
                                                                    suggested_fix =
                                                                    (Some
                                                                    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::('_'::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))));
                                                                    rule_owner =
                                                                    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
                                                                    (check_empty_left_right
                                                                    rest0)
                                                                    | _::_ ->
                                                                    check_empty_left_right
                                                                    rest)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a7)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a6)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a5)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a4)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a3)
                                                                    | TText s4 ->
                                                                    (match s4 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a3::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b38
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    (match rest0 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | l1::l2 ->
                                                                    (match l1 with
                                                                    | TCommand s6 ->
                                                                    (match s6 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a4::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b42
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a5::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b49
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b50
                                                                    then 
                                                                    if b51
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a6::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    if b56
                                                                    then 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a7::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b64
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b66
                                                                    then 
                                                                    if b67
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a8::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b72
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    (match l2 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | l3::rest1 ->
                                                                    (match l3 with
                                                                    | TText s12 ->
                                                                    (match s12 with
                                                                    | [] ->
                                                                    check_empty_left_right
                                                                    rest
                                                                    | a9::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    if b86
                                                                    then 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    { rule_id =
                                                                    ('D'::('E'::('L'::('I'::('M'::('-'::('0'::('0'::('8'::[])))))))));
                                                                    issue_severity =
                                                                    Info;
                                                                    message =
                                                                    ('E'::('m'::('p'::('t'::('y'::(' '::('\\'::('\\'::('l'::('e'::('f'::('t'::('.'::(' '::('\\'::('\\'::('r'::('i'::('g'::('h'::('t'::('.'::(' '::('p'::('a'::('i'::('r'::(' '::('i'::('s'::(' '::('r'::('e'::('d'::('u'::('n'::('d'::('a'::('n'::('t'::[]))))))))))))))))))))))))))))))))))))))));
                                                                    loc =
                                                                    None;
                                                                    suggested_fix =
                                                                    (Some
                                                                    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::('_'::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))));
                                                                    rule_owner =
                                                                    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) }::
                                                                    (check_empty_left_right
                                                                    rest1)
                                                                    | _::_ ->
                                                                    check_empty_left_right
                                                                    rest)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a9)
                                                                    | _ ->
                                                                    check_empty_left_right
                                                                    rest))
                                                                    | _::_ ->
                                                                    check_empty_left_right
                                                                    rest)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a8)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a7)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a6)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a5)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a4)
                                                                    | _ ->
                                                                    check_empty_left_right
                                                                    rest))
                                                                    | _::_ ->
                                                                    check_empty_left_right
                                                                    rest)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a3)
                                                                    | _ ->
                                                                    check_empty_left_right
                                                                    rest))
                                                                    | _::_ ->
                                                                    check_empty_left_right
                                                                    rest)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                    else 
                                                                    check_empty_left_right
                                                                    rest
                                                                 else 
                                                                   check_empty_left_right
                                                                    rest
                                                       else check_empty_left_right
                                                              rest)
                                                       a0)
                                        else check_empty_left_right rest
                                   else check_empty_left_right rest
                         else check_empty_left_right rest
                    else check_empty_left_right rest)
          a)
   | _ -> check_empty_left_right rest)

(** val delim_008_validator_real : document_state -> validation_issue list **)

let delim_008_validator_real doc =
  if is_expanded doc
  then let expanded = get_expanded_tokens doc in
       check_empty_left_right expanded
  else []
