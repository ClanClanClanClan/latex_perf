(* b2cmt.ml: the TYPED half of b2static.py (spike H.5 stage 2, review hardening). A test
   instrument, never linked into the model.

   Usage: b2cmt.exe PURE_MODULES TREE_MODULES FILE.cmt ...
   TREE_MODULES lists every module of the extracted tree (comma-separated). PURE_MODULES lists
   those that do not depend, even transitively, on Values (b2static.py computes both with
   ocamldep); they are used only for the REACHABLE lines: the roots are the other modules' code.

   For every use of a realizer of `match` that takes continuation closures (Coq's extraction of
   nat, Z, N, positive and ascii: the applied `fun` whose parameters are named as in
   b2static.py's REALIZERS), and for every continuation closure passed to it, it prints

     SITE <file> <line> <col> <kind> <toplevel> <i> <verdict> <detail>

   For every `fun` written in the source and passed as an argument (kind `lambda`), the same
   line is printed; such a closure is also checked against its CALLEE: unless the callee uses
   that parameter only as one call in tail position (computed from the callee's typed body),
   the callee may keep the closure, and its environment, while it does other work.

   where <verdict> is the first of these that holds:
     DEAD       during every non-leaf call (below) the closure's environment is dead: the call is
                in tail position, or nothing that runs after it inside the closure reads a free
                variable (so ocamlopt keeps nothing of the environment across it);
     STATEFREE  no free variable of the closure has a type that can reach a state (Values.state,
                Values.block, a persistent array, a function, a type variable or an unknown
                type): the environment cannot hold a state;
     LOOP       the only non-leaf calls with the environment live are LOOP calls: the closure may
                hold a state across a data-bounded write loop of the tree (copy_cells,
                put_cells, ...), and retains at most one Diff node per write of that loop, until
                the loop returns. It cannot hold a state across interpreter code;
     HOLDS      otherwise: the closure may hold a state across a RUN call, which can re-enter
                the interpreter. <detail> lists the state-bearing free variables and the calls
                made with the environment live (each tagged RUN or LOOP).
   A call is a LEAF when its callee is a primitive, a library function (outside the tree;
   Parray.set itself is one write) or a LEAF function of the tree (see `compute` below), and
   every function-typed argument it is given performs no Parray.set and runs no code of a
   non-pure module. It is a LOOP call when its callee is a LOOP function of the tree; every
   other call is RUN (a parameter, a local function, a RUN function, a callee given a function
   argument that writes or runs code).

   Why a leaf call cannot make a held state retain a growing amount of memory: an old version
   of a persistent array keeps alive the chain of updates made after it (coq-core's Parray), so
   a state held across a call retains one Diff node per Parray.set performed during that call
   (before B2: 211 M words, because the calls held were the interpreter's own recursion). A leaf
   call performs a bounded number of Parray.set, fixed by the code, and a LOOP call as many as
   its data (cells copied, a list written), so what a closure can retain across either is
   bounded by that call's own writes and freed when the closure returns. Only a RUN call can
   make a held state retain the rest of the run.

   It also prints  CALLGRAPH <qualified name> <leaf|loop|run> <why>, the
   REACHABLE values (see main) and USE lines (see `uses`), for the record and for b2static.py. *)

open Typedtree

let realizers =
  [ ([ "fO"; "fS"; "n" ], "nat", 2); ([ "fO"; "fp"; "fn"; "z" ], "Z", 3);
    ([ "fO"; "fp"; "n" ], "N", 2); ([ "f2p1"; "f2p"; "f1"; "p" ], "positive", 3);
    ([ "f"; "c" ], "ascii", 1) ]

let pure_modules = ref []
let tree_modules = ref []

(* ---------------------------------------------------------------- names *)
let topq : (string, string) Hashtbl.t = Hashtbl.create 997 (* Ident.unique_name -> qualified *)
let modq : (string, string) Hashtbl.t = Hashtbl.create 97

let rec qual = function
  | Path.Pident id -> (
      let u = Ident.unique_name id in
      match Hashtbl.find_opt topq u with
      | Some q -> q
      | None -> ( match Hashtbl.find_opt modq u with Some q -> q | None -> Ident.name id))
  | Path.Pdot (p, s) -> qual p ^ "." ^ s
  | Path.Papply (a, b) -> qual a ^ "(" ^ qual b ^ ")"
  | Path.Pextra_ty (p, _) -> qual p

let head_module q = match String.index_opt q '.' with Some i -> String.sub q 0 i | None -> q
let in_tree q = List.mem (head_module q) !tree_modules
let in_pure q = List.mem (head_module q) !pure_modules

let is_toplevel_path = function
  | Path.Pident id -> Hashtbl.mem topq (Ident.unique_name id)
  | Path.Pdot _ -> true
  | _ -> false

(* ---------------------------------------------------------------- types *)
let typedecls : (string, Types.type_declaration) Hashtbl.t = Hashtbl.create 997

let pure_base =
  [ "int"; "char"; "bool"; "unit"; "string"; "float"; "bytes"; "list"; "option"; "array";
    "Big_int_Z.big_int"; "Z.t"; "Uint63.t"; "Float64.t"; "Stdlib.ref"; "ref" ]

let bearing_roots = [ "Values.state"; "Values.block" ]

(* Some reason when a value of type t can reach a state, None when it cannot. cur: the module
   whose code (or declaration) mentions t, so that a Pident type path means a type of cur. *)
let bearing ~cur t =
  let seen = Hashtbl.create 17 in
  let rec go cur t =
    match Types.get_desc t with
    | Types.Tvar _ | Types.Tunivar _ -> Some "a type variable"
    | Types.Tarrow _ -> Some "a function"
    | Types.Ttuple ts -> first cur ts
    | Types.Tpoly (t, _) -> go cur t
    | Types.Tconstr (p, args, _) -> (
        let q =
          match p with
          | Path.Pident id when not (Hashtbl.mem topq (Ident.unique_name id)) ->
              let n = Ident.name id in
              if List.mem n pure_base then n else cur ^ "." ^ n
          | _ -> qual p
        in
        if List.mem q bearing_roots then Some q
        else if q = "Parray.t" || q = "PArray0.array" then Some ("a persistent array (" ^ q ^ ")")
        else if List.mem q pure_base then first cur args
        else if Hashtbl.mem seen q then first cur args
        else (
          Hashtbl.add seen q ();
          match Hashtbl.find_opt typedecls q with
          | None -> Some ("an unknown type " ^ q)
          | Some d ->
              let comps =
                match d.Types.type_kind with
                | Types.Type_variant (cs, _) ->
                    List.concat_map
                      (fun c ->
                        match c.Types.cd_args with
                        | Types.Cstr_tuple ts -> ts
                        | Types.Cstr_record ls -> List.map (fun l -> l.Types.ld_type) ls)
                      cs
                | Types.Type_record (ls, _) -> List.map (fun l -> l.Types.ld_type) ls
                | Types.Type_abstract _ | Types.Type_open -> (
                    match d.Types.type_manifest with Some m -> [ m ] | None -> [])
              in
              let abstract =
                match (d.Types.type_kind, d.Types.type_manifest) with
                | (Types.Type_abstract _ | Types.Type_open), None -> true
                | _ -> false
              in
              if abstract then Some ("an abstract type " ^ q)
              else
                let dm = String.sub q 0 (String.rindex q '.') in
                let rec firstc = function
                  | [] -> first cur args
                  | c :: r -> ( match go dm c with Some x -> Some (q ^ " -> " ^ x) | None -> firstc r)
                in
                firstc comps))
    | Types.Tobject _ | Types.Tfield _ | Types.Tnil | Types.Tvariant _ | Types.Tpackage _ ->
        Some "an object, variant or package type"
    | Types.Tlink _ | Types.Tsubst _ -> assert false
  and first cur = function
    | [] -> None
    | t :: r -> ( match go cur t with Some x -> Some x | None -> first cur r)
  in
  go cur t

(* ---------------------------------------------------------------- realizers *)
let fun_params e =
  match e.exp_desc with
  | Texp_function (ps, _) -> Some (List.map (fun p -> Ident.name p.fp_param) ps)
  | _ -> None

let realizer_kind e =
  match fun_params e with
  | Some names -> List.find_map (fun (n, k, nk) -> if n = names then Some (k, nk) else None) realizers
  | None -> None

let fun_body e =
  match e.exp_desc with
  | Texp_function (_, Tfunction_body b) -> Some b
  | _ -> None

(* ---------------------------------------------------------------- call graph *)
type fninfo = {
  mutable callees : string list; (* every value of the tree it names *)
  mutable unknown : string list; (* the parameters (or other non-global functions) it calls *)
  mutable hof : string list; (* function arguments it passes to a function outside its module's
                                reach: a lambda, a parameter, or a function of a non-pure module,
                                passed to a function of a pure module or of a library *)
  mutable writes : bool; (* names Parray.set *)
}

let fns : (string, fninfo) Hashtbl.t = Hashtbl.create 997
let is_arrow t = match Types.get_desc t with Types.Tarrow _ -> true | _ -> false

(* names bound by `let` to a function inside a top-level body: calls to them are calls into the
   same body, which the walk covers *)
let collect_info (info : fninfo) body =
  let local_funs = Hashtbl.create 17 in
  let open Tast_iterator in
  (* a lambda is suspicious when its body calls something that is not a primitive, a library
     function other than Parray.set, or a function of a pure module *)
  let suspicious_lambda lam =
    let bad = ref false in
    let it =
      {
        default_iterator with
        expr =
          (fun self e ->
            (match e.exp_desc with
            | Texp_ident (p, _, vd) -> (
                match vd.Types.val_kind with
                | Types.Val_prim _ -> ()
                | _ ->
                    let q = qual p in
                    if q = "Parray.set" then bad := true
                    else if is_toplevel_path p then (if in_tree q && not (in_pure q) then bad := true)
                    else if is_arrow e.exp_type then bad := true)
            | _ -> ());
            default_iterator.expr self e);
      }
    in
    (match lam.exp_desc with
    | Texp_function (_, Tfunction_body b) -> it.expr it b
    | _ -> bad := true);
    !bad
  in
  let note_hof callee_q args =
    if (not (in_tree callee_q)) || in_pure callee_q then
      List.iter
        (fun (_, a) ->
          match a with
          | Some ({ exp_desc = Texp_function _; _ } as l) ->
              if suspicious_lambda l then info.hof <- ("a lambda that calls or writes to " ^ callee_q) :: info.hof
          | Some ({ exp_desc = Texp_ident (pa, _, _); _ } as a) when is_arrow a.exp_type ->
              let qa = qual pa in
              if not (is_toplevel_path pa) then info.hof <- (qa ^ " to " ^ callee_q) :: info.hof
              else if in_tree qa && not (in_pure qa) then info.hof <- (qa ^ " to " ^ callee_q) :: info.hof
          | Some a when is_arrow a.exp_type -> info.hof <- ("a computed function to " ^ callee_q) :: info.hof
          | _ -> ())
        args
  in
  let it =
    {
      default_iterator with
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_let (_, vbs, _) ->
              List.iter
                (fun vb ->
                  match (vb.vb_pat.pat_desc, vb.vb_expr.exp_desc) with
                  | Tpat_var (id, _, _), Texp_function _ -> Hashtbl.replace local_funs (Ident.unique_name id) ()
                  | _ -> ())
                vbs
          | _ -> ());
          match e.exp_desc with
          | Texp_apply (f, args) when realizer_kind f <> None ->
              (* the realizer's own body calls its continuation parameters: known *)
              List.iter (function _, Some a -> self.expr self a | _ -> ()) args
          | Texp_ident (p, _, vd) -> (
              match vd.Types.val_kind with
              | Types.Val_prim _ -> ()
              | _ ->
                  if qual p = "Parray.set" then info.writes <- true;
                  if is_toplevel_path p && in_tree (qual p) then info.callees <- qual p :: info.callees)
          | Texp_apply ({ exp_desc = Texp_ident (p, _, vd); _ }, args) ->
              (match vd.Types.val_kind with
              | Types.Val_prim _ -> ()
              | _ ->
                  let q = qual p in
                  if q = "Parray.set" then info.writes <- true;
                  if is_toplevel_path p then begin
                    if in_tree q then info.callees <- q :: info.callees;
                    note_hof q args
                  end
                  else
                    match p with
                    | Path.Pident id when Hashtbl.mem local_funs (Ident.unique_name id) -> ()
                    | _ -> info.unknown <- q :: info.unknown);
              List.iter (function _, Some a -> self.expr self a | _ -> ()) args
          | _ -> default_iterator.expr self e);
    }
  in
  it.expr it body

(* WRITES: names Parray.set, or calls a function that does (least fixpoint).
   RUN (Some why): may run code it was given, so a call to it can re-enter the interpreter:
     - a function of a non-pure module that calls a parameter, or passes a lambda that calls or
       writes, a parameter or a non-pure function to a function of a pure module or a library
       (a pure module's code cannot see a state; its own parameter calls are judged here, at
       its non-pure callers);
     - a function that calls a RUN function, or one not in the analysed .cmt files.
   LOOP (Some why), when not RUN: a recursive writer (it writes and lies on a cycle of the call
   graph), or a function that calls one: its number of Parray.set depends on its data.
   Every other function of the tree is a LEAF: a call to it performs a bounded number of
   Parray.set, fixed by the code. *)
let writes : (string, unit) Hashtbl.t = Hashtbl.create 997
let run : (string, string) Hashtbl.t = Hashtbl.create 997
let loop : (string, string) Hashtbl.t = Hashtbl.create 997
let computed = ref false

let on_cycle q =
  let seen = Hashtbl.create 97 in
  let rec go c =
    if c = q then true
    else if Hashtbl.mem seen c then false
    else begin
      Hashtbl.replace seen c ();
      match Hashtbl.find_opt fns c with Some i -> List.exists go i.callees | None -> false
    end
  in
  match Hashtbl.find_opt fns q with Some i -> List.exists go (List.sort_uniq compare i.callees) | None -> false

let short w = if String.length w > 160 then String.sub w 0 160 ^ "..." else w

let propagate tbl ~missing =
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter
      (fun q i ->
        if not (Hashtbl.mem tbl q) then
          match
            List.find_opt (fun c -> Hashtbl.mem tbl c || (missing && not (Hashtbl.mem fns c))) (List.sort_uniq compare i.callees)
          with
          | Some c ->
              let why =
                match Hashtbl.find_opt tbl c with
                | Some w -> "calls " ^ c ^ " (" ^ short w ^ ")"
                | None -> "calls " ^ c ^ ", which is not in the analysed .cmt files"
              in
              Hashtbl.replace tbl q why;
              changed := true
          | None -> ())
      fns
  done

let compute () =
  Hashtbl.iter (fun q i -> if i.writes then Hashtbl.replace writes q ()) fns;
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter
      (fun q i ->
        if (not (Hashtbl.mem writes q)) && List.exists (fun c -> Hashtbl.mem writes c) i.callees then begin
          Hashtbl.replace writes q ();
          changed := true
        end)
      fns
  done;
  Hashtbl.iter
    (fun q i ->
      if (not (in_pure q)) && i.unknown <> [] then
        Hashtbl.replace run q ("calls a parameter: " ^ String.concat "," (List.sort_uniq compare i.unknown))
      else if (not (in_pure q)) && i.hof <> [] then
        Hashtbl.replace run q ("passes " ^ String.concat ", " (List.sort_uniq compare i.hof)))
    fns;
  propagate run ~missing:true;
  Hashtbl.iter
    (fun q _ -> if Hashtbl.mem writes q && on_cycle q && not (Hashtbl.mem run q) then Hashtbl.replace loop q "a recursive writer")
    fns;
  propagate loop ~missing:false;
  Hashtbl.filter_map_inplace (fun q w -> if Hashtbl.mem run q then None else Some w) loop;
  computed := true

type cls = Leaf | Loop of string | Run of string

let classify q =
  assert !computed;
  if not (Hashtbl.mem fns q) then Run "not in the analysed .cmt files"
  else
    match Hashtbl.find_opt run q with
    | Some w -> Run w
    | None -> ( match Hashtbl.find_opt loop q with Some w -> Loop w | None -> Leaf)

(* a function value passed to a callee that may call it any number of times: a leaf only if it
   performs no Parray.set at all and runs no code it was not given here *)
let rec writefree_arg a =
  match a.exp_desc with
  | Texp_ident (pa, _, _) ->
      is_toplevel_path pa
      && ((not (in_tree (qual pa)) && qual pa <> "Parray.set")
         || (classify (qual pa) = Leaf && not (Hashtbl.mem writes (qual pa))))
  | Texp_function _ -> (
      match fun_body a with
      | None -> false
      | Some b ->
          let ok = ref true in
          let open Tast_iterator in
          let it =
            {
              default_iterator with
              expr =
                (fun self e ->
                  (match e.exp_desc with
                  | Texp_apply (({ exp_desc = Texp_ident (_, _, { Types.val_kind = Types.Val_prim _; _ }); _ }), _) -> ()
                  | Texp_apply (({ exp_desc = Texp_ident _; _ } as f), args) ->
                      if not (writefree_arg f) then ok := false;
                      List.iter
                        (fun (_, a) -> match a with Some a when is_arrow a.exp_type && not (writefree_arg a) -> ok := false | _ -> ())
                        args
                  | Texp_apply (f, _) when realizer_kind f = None -> (
                      match f.exp_desc with Texp_function _ -> () | _ -> ok := false)
                  | _ -> ());
                  default_iterator.expr self e);
            }
          in
          it.expr it b;
          !ok)
  | _ -> false

(* ---------------------------------------------------------------- site analysis *)
(* the free variables of the closure being classified (Ident.unique_name), and whether an
   expression reads one of them (a nested `fun` that captures one reads it when it is built) *)
let cur_fv : (string, unit) Hashtbl.t = Hashtbl.create 17

let reads e =
  let hit = ref false in
  let open Tast_iterator in
  let it =
    {
      default_iterator with
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_ident (Path.Pident id, _, _) when Hashtbl.mem cur_fv (Ident.unique_name id) -> hit := true
          | _ -> ());
          if not !hit then default_iterator.expr self e);
    }
  in
  it.expr it e;
  !hit

let reads_any es = List.exists reads es

let rec lambda_nonleaf_calls e =
  (* a lambda passed as an argument: the non-leaf calls its body can make, wherever *)
  match fun_body e with Some b -> scan ~after:true b | None -> [ "RUN a function value that is not a plain `fun`" ]

(* The non-leaf calls of e during which the closure's environment is LIVE: after:true when some
   code that runs after e, inside the closure, reads a free variable. A call in tail position
   has after:false. OCaml's argument order is unspecified, so siblings count as "after". *)
and scan ~after e : string list =
  let others xs x = List.filter (fun y -> y != x) xs in
  match e.exp_desc with
  | Texp_apply (f, args) when realizer_kind f <> None ->
      (* the realizer calls exactly one continuation, in tail position, after leaf arithmetic *)
      let _, nk = Option.get (realizer_kind f) in
      let args = List.filter_map (fun (_, a) -> a) args in
      let conts = List.filteri (fun i _ -> i < nk) args in
      let rest = List.filteri (fun i _ -> i >= nk) args in
      let bodies = List.filter_map fun_body conts in
      (if List.length bodies <> nk then [ "RUN a non-`fun` continuation" ] else [])
      @ List.concat_map (scan ~after) bodies
      @ List.concat_map (fun r -> scan ~after:(after || reads_any bodies || reads_any (others rest r)) r) rest
  | Texp_apply (({ exp_desc = Texp_function (ps, Tfunction_body b); _ } as f), args)
    when List.length ps = List.length args && List.for_all (fun (_, a) -> a <> None) args ->
      (* a beta-redex `(fun x -> b) a` (extraction prints constructors of positive this way):
         the arguments are evaluated, then b runs in the redex's own position *)
      ignore f;
      let args = List.filter_map snd args in
      List.concat_map (fun a -> scan ~after:(after || reads b || reads_any (others args a)) a) args @ scan ~after b
  | Texp_apply (f, args) ->
      let args = List.filter_map (fun (_, a) -> a) args in
      let in_args =
        List.concat_map
          (fun a ->
            match a.exp_desc with
            | Texp_function _ -> []
            | _ -> scan ~after:(after || reads f || reads_any (others args a)) a)
          args
      in
      let leaf, name =
        match f.exp_desc with
        | Texp_ident (p, _, vd) -> (
            let q = qual p in
            match vd.Types.val_kind with
            | Types.Val_prim _ -> (true, q)
            | _ ->
                let fargs =
                  List.filter_map
                    (fun a ->
                      if is_arrow a.exp_type && not (writefree_arg a) then
                        Some (match a.exp_desc with Texp_ident (pa, _, _) -> qual pa | _ -> "a lambda that writes or calls")
                      else None)
                    args
                in
                if not (is_toplevel_path p) then (false, "RUN " ^ q ^ " (a local function or parameter)")
                else if fargs <> [] then (false, "RUN " ^ q ^ " (with function arguments " ^ String.concat "," fargs ^ ")")
                else if not (in_tree q) then (true, q)
                else (
                  match classify q with
                  | Leaf -> (true, q)
                  | Loop w -> (false, "LOOP " ^ q ^ " (" ^ w ^ ")")
                  | Run w -> (false, "RUN " ^ q ^ " (" ^ w ^ ")")))
        | Texp_function _ -> (false, "RUN an applied lambda")
        | _ -> (false, "RUN a computed callee")
      in
      let fcalls =
        match f.exp_desc with
        | Texp_ident _ -> []
        | Texp_function _ -> lambda_nonleaf_calls f
        | _ -> scan ~after:true f
      in
      let here = if leaf || not after then [] else [ name ] in
      here @ in_args @ fcalls
  | Texp_match (sc, cases, _) ->
      let later = List.exists (fun c -> reads c.c_rhs || match c.c_guard with Some g -> reads g | None -> false) cases in
      scan ~after:(after || later) sc
      @ List.concat_map
          (fun c -> (match c.c_guard with Some g -> scan ~after:true g | None -> []) @ scan ~after c.c_rhs)
          cases
  | Texp_ifthenelse (c, a, b) ->
      let later = reads a || match b with Some b -> reads b | None -> false in
      scan ~after:(after || later) c @ scan ~after a @ (match b with Some b -> scan ~after b | None -> [])
  | Texp_let (_, vbs, body) ->
      let es = List.map (fun vb -> vb.vb_expr) vbs in
      List.concat_map
        (fun x -> match x.exp_desc with Texp_function _ -> [] | _ -> scan ~after:(after || reads body || reads_any (others es x)) x)
        es
      @ scan ~after body
  | Texp_sequence (a, b) -> scan ~after:(after || reads b) a @ scan ~after b
  | Texp_try (b, hs) ->
      scan ~after:(after || List.exists (fun c -> reads c.c_rhs) hs) b @ List.concat_map (fun c -> scan ~after c.c_rhs) hs
  | Texp_open (_, b) -> scan ~after b
  | Texp_function _ -> [] (* an allocation: its body runs when it is called *)
  | Texp_ident _ | Texp_constant _ -> []
  | _ ->
      (* constructors, tuples, records, fields: the children are evaluated, in some order, before
         e's own value is built; conservatively, each child's siblings count as "after" *)
      let acc = ref [] in
      let open Tast_iterator in
      let it = { default_iterator with expr = (fun _ e' -> acc := !acc @ scan ~after:(after || reads e) e') } in
      default_iterator.expr it e;
      !acc

(* Which parameters of each top-level function are used ONLY as the callee of one call in tail
   position (and nowhere else, not even inside a nested `fun`): a closure passed there is not
   held by the function while its body runs. *)
let tail_only : (string, int list) Hashtbl.t = Hashtbl.create 997

let param_tail_only body pid =
  let ok = ref true in
  let mentions e =
    let hit = ref false in
    let open Tast_iterator in
    let it =
      {
        default_iterator with
        expr =
          (fun self e ->
            (match e.exp_desc with
            | Texp_ident (Path.Pident id, _, _) when Ident.same id pid -> hit := true
            | _ -> ());
            default_iterator.expr self e);
      }
    in
    it.expr it e;
    !hit
  in
  let rec go ~tail e =
    match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (Path.Pident id, _, _); _ }, args) when Ident.same id pid ->
        if not tail then ok := false;
        List.iter (fun (_, a) -> match a with Some a when mentions a -> ok := false | _ -> ()) args
    | Texp_ident (Path.Pident id, _, _) when Ident.same id pid -> ok := false
    | Texp_match (sc, cases, _) ->
        go ~tail:false sc;
        List.iter (fun c -> (match c.c_guard with Some g -> go ~tail:false g | None -> ()); go ~tail c.c_rhs) cases
    | Texp_ifthenelse (c, a, b) ->
        go ~tail:false c;
        go ~tail a;
        Option.iter (go ~tail) b
    | Texp_let (_, vbs, b) ->
        List.iter (fun vb -> go ~tail:false vb.vb_expr) vbs;
        go ~tail b
    | Texp_sequence (a, b) ->
        go ~tail:false a;
        go ~tail b
    | Texp_open (_, b) -> go ~tail b
    | _ -> if mentions e then ok := false
  in
  go ~tail:true body;
  !ok

let compute_tail_only (str : structure) =
  let rec items str =
    List.iter
      (fun si ->
        match si.str_desc with
        | Tstr_value (_, vbs) ->
            List.iter
              (fun vb ->
                match (vb.vb_pat.pat_desc, vb.vb_expr.exp_desc) with
                | Tpat_var (id, _, _), Texp_function (ps, Tfunction_body body) ->
                    let idx =
                      List.concat (List.mapi (fun i p -> if param_tail_only body p.fp_param then [ i ] else []) ps)
                    in
                    Hashtbl.replace tail_only (qual (Path.Pident id)) idx
                | _ -> ())
              vbs
        | Tstr_module { mb_expr = { mod_desc = Tmod_structure s; _ }; _ } -> items s
        | _ -> ())
      str.str_items
  in
  items str

let free_vars cont =
  let used = Hashtbl.create 17 and bound = Hashtbl.create 17 in
  let open Tast_iterator in
  let it =
    {
      default_iterator with
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_ident ((Path.Pident id as p), _, _) when not (is_toplevel_path p) ->
              Hashtbl.replace used (Ident.unique_name id) (Ident.name id, e.exp_type)
          | Texp_function (ps, _) -> List.iter (fun p -> Hashtbl.replace bound (Ident.unique_name p.fp_param) ()) ps
          | Texp_for (id, _, _, _, _, _) -> Hashtbl.replace bound (Ident.unique_name id) ()
          | _ -> ());
          default_iterator.expr self e);
      pat =
        (fun (type k) self (p : k general_pattern) ->
          (match p.pat_desc with
          | Tpat_var (id, _, _) -> Hashtbl.replace bound (Ident.unique_name id) ()
          | Tpat_alias (_, id, _, _) -> Hashtbl.replace bound (Ident.unique_name id) ()
          | _ -> ());
          default_iterator.pat self p);
    }
  in
  it.expr it cont;
  Hashtbl.fold (fun u (n, t) acc -> if Hashtbl.mem bound u then acc else (u, n, t) :: acc) used []
  |> List.sort compare

let sites = ref []

(* held: Some why when the closure is passed to a callee that may keep it while doing other work
   (anything but one call of it in tail position) *)
let classify_closure ?held modname c =
  let bodies =
    match c.exp_desc with
    | Texp_function (_, Tfunction_body b) -> Some [ b ]
    | Texp_function (_, Tfunction_cases { cases; _ }) -> Some (List.map (fun cs -> cs.c_rhs) cases)
    | _ -> None
  in
  let fv = free_vars c in
  let bear =
    List.filter_map (fun (_, n, t) -> match bearing ~cur:modname t with Some w -> Some (n ^ ":" ^ w) | None -> None) fv
  in
  Hashtbl.reset cur_fv;
  List.iter (fun (u, _, _) -> Hashtbl.replace cur_fv u ()) fv;
  match bodies with
  | None -> ("HOLDS", "the closure is not a `fun`")
  | Some bs -> (
      let nl = List.sort_uniq compare (List.concat_map (scan ~after:false) bs) in
      let nl =
        match held with
        | Some (why, callee_nonleaf) when bear <> [] ->
            (* the callee keeps the whole environment while it runs: every non-leaf call the
               closure makes, anywhere, and the callee's own work, happen with it held *)
            let all = List.concat_map (scan ~after:true) bs in
            if callee_nonleaf || all <> [] then
              List.sort_uniq compare ((if callee_nonleaf then [ why ] else []) @ nl @ all)
            else nl
        | _ -> nl
      in
      if nl = [] then ("DEAD", "")
      else if bear = [] then ("STATEFREE", "non-tail calls " ^ String.concat "; " nl)
      else if List.for_all (fun c -> String.length c > 5 && String.sub c 0 5 = "LOOP ") nl then
        ( "LOOP",
          "state-bearing free variables [" ^ String.concat "; " bear ^ "] across non-tail calls [" ^ String.concat "; " nl ^ "]" )
      else
        ( "HOLDS",
          "state-bearing free variables [" ^ String.concat "; " bear ^ "] across non-tail calls [" ^ String.concat "; " nl ^ "]" ))

let analyse_structure file modname str =
  let open Tast_iterator in
  let top = ref "?" in
  let it =
    {
      default_iterator with
      structure_item =
        (fun self si ->
          match si.str_desc with
          | Tstr_value (_, vbs) ->
              List.iter
                (fun vb ->
                  (match vb.vb_pat.pat_desc with
                  | Tpat_var (id, _, _) -> top := qual (Path.Pident id)
                  | _ -> ());
                  self.value_binding self vb)
                vbs
          | _ -> default_iterator.structure_item self si);
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_apply (f, args) -> (
              match realizer_kind f with
              | Some (k, nk) ->
                  let pos = f.exp_loc.Location.loc_start in
                  let line = pos.Lexing.pos_lnum and col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
                  let conts = List.filteri (fun i _ -> i < nk) (List.filter_map snd args) in
                  if List.length conts <> nk then
                    sites := Printf.sprintf "SITE %s %d %d %s %s 0 HOLDS fewer continuation arguments than the realizer takes" file line col k !top :: !sites
                  else
                    List.iteri
                      (fun i c ->
                        let verdict, detail = classify_closure modname c in
                        sites :=
                          Printf.sprintf "SITE %s %d %d %s %s %d %s %s" file line col k !top i verdict
                            (String.map (fun ch -> if ch = '\n' || ch = '\t' then ' ' else ch) detail)
                          :: !sites)
                      conts
              | None -> (
                  (* a `fun` written in the source and passed as an argument (not a realizer's
                     branch, not a beta-redex's own function): the same question *)
                  match f.exp_desc with
                  | Texp_function _ -> ()
                  | _ ->
                      List.iteri
                        (fun i (_, a) ->
                          match a with
                          | Some ({ exp_desc = Texp_function _; _ } as c) ->
                              let pos = c.exp_loc.Location.loc_start in
                              let held =
                                match f.exp_desc with
                                | Texp_ident (p, _, vd) when is_toplevel_path p -> (
                                    let q = qual p in
                                    match Hashtbl.find_opt tail_only q with
                                    | Some idx when List.mem i idx -> None
                                    | _ ->
                                        let cls =
                                          match vd.Types.val_kind with
                                          | Types.Val_prim _ -> "LEAF"
                                          | _ when not (in_tree q) -> "LEAF"
                                          | _ -> ( match classify q with Leaf -> "LEAF" | Loop _ -> "LOOP" | Run _ -> "RUN")
                                        in
                                        Some (cls ^ " " ^ q ^ " (the callee, which may keep the closure)", cls <> "LEAF"))
                                | _ -> Some ("RUN an unknown callee, which may keep the closure", true)
                              in
                              let verdict, detail = classify_closure ?held modname c in
                              sites :=
                                Printf.sprintf "SITE %s %d %d lambda %s %d %s %s" file pos.Lexing.pos_lnum
                                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) !top i verdict
                                  (String.map (fun ch -> if ch = '\n' || ch = '\t' then ' ' else ch) detail)
                                :: !sites
                          | _ -> ())
                        args))
          | _ -> ());
          default_iterator.expr self e);
    }
  in
  it.structure it str

(* USE lines: every use of a function that has a HOLDS site, outside its own definition. A
   polymorphic library function holds a value of a type variable; it holds a state only if some
   use instantiates that variable at a state-bearing type, or passes it a closure. *)
let rec bearing_inst ~cur t =
  match Types.get_desc t with
  | Types.Tarrow (_, a, b, _) -> (
      match bearing_inst ~cur a with Some w -> Some w | None -> bearing_inst ~cur b)
  | _ -> bearing ~cur t

let uses targets file modname str =
  let open Tast_iterator in
  let top = ref "?" in
  let as_callee = Hashtbl.create 17 in
  let out = ref [] in
  let it =
    {
      default_iterator with
      structure_item =
        (fun self si ->
          match si.str_desc with
          | Tstr_value (_, vbs) ->
              List.iter
                (fun vb ->
                  (match vb.vb_pat.pat_desc with Tpat_var (id, _, _) -> top := qual (Path.Pident id) | _ -> ());
                  self.value_binding self vb)
                vbs
          | _ -> default_iterator.structure_item self si);
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_apply (({ exp_desc = Texp_ident (p, _, _); _ } as f), args)
            when is_toplevel_path p && List.mem (qual p) targets ->
              let q = qual p in
              Hashtbl.replace as_callee f.exp_loc ();
              if q <> !top then begin
                let pos = f.exp_loc.Location.loc_start in
                let inst = match bearing_inst ~cur:modname f.exp_type with Some w -> "bearing " ^ w | None -> "state-free" in
                let fargs =
                  List.filter_map
                    (fun (_, a) ->
                      match a with
                      | Some ({ exp_desc = Texp_ident (pa, _, _); _ } as a) when is_arrow a.exp_type ->
                          if is_toplevel_path pa then None else Some (qual pa)
                      | Some a when is_arrow a.exp_type -> Some "a closure"
                      | _ -> None)
                    args
                in
                out :=
                  Printf.sprintf "USE %s %s:%d %s %s" q file pos.Lexing.pos_lnum inst
                    (if fargs = [] then "global-function-arguments" else "closure-arguments:" ^ String.concat "," fargs)
                  :: !out
              end
          | Texp_ident (p, _, _) when is_toplevel_path p && List.mem (qual p) targets ->
              if (not (Hashtbl.mem as_callee e.exp_loc)) && qual p <> !top then
                out := Printf.sprintf "USE %s %s:%d escapes (named, not applied)" (qual p) file e.exp_loc.Location.loc_start.Lexing.pos_lnum :: !out
          | _ -> ());
          default_iterator.expr self e);
    }
  in
  it.structure it str;
  List.rev !out

(* first pass: qualified names of every top-level value and module, type declarations,
   call-graph facts *)
let rec register prefix str =
  List.iter
    (fun si ->
      match si.str_desc with
      | Tstr_value (_, vbs) ->
          List.iter
            (fun vb ->
              match vb.vb_pat.pat_desc with
              | Tpat_var (id, _, _) -> Hashtbl.replace topq (Ident.unique_name id) (prefix ^ "." ^ Ident.name id)
              | _ -> ())
            vbs
      | Tstr_type (_, tds) ->
          List.iter (fun td -> Hashtbl.replace typedecls (prefix ^ "." ^ Ident.name td.typ_id) td.typ_type) tds
      | Tstr_module { mb_id = Some id; mb_expr; _ } -> (
          let q = prefix ^ "." ^ Ident.name id in
          Hashtbl.replace modq (Ident.unique_name id) q;
          let rec strip m =
            match m.mod_desc with
            | Tmod_structure s -> Some s
            | Tmod_constraint (m, _, _, _) -> strip m
            | _ -> None
          in
          match strip mb_expr with Some s -> register q s | None -> ())
      | _ -> ())
    str.str_items

let rec callgraph prefix str =
  List.iter
    (fun si ->
      match si.str_desc with
      | Tstr_value (rf, vbs) ->
          let names =
            List.filter_map
              (fun vb -> match vb.vb_pat.pat_desc with Tpat_var (id, _, _) -> Some (qual (Path.Pident id)) | _ -> None)
              vbs
          in
          List.iter
            (fun vb ->
              match vb.vb_pat.pat_desc with
              | Tpat_var (id, _, _) ->
                  let info = { callees = []; unknown = []; hof = []; writes = false } in
                  collect_info info vb.vb_expr;
                  ignore rf;
                  ignore names;
                  Hashtbl.replace fns (qual (Path.Pident id)) info
              | _ -> ())
            vbs
      | Tstr_module { mb_id = Some id; mb_expr; _ } -> (
          let q = prefix ^ "." ^ Ident.name id in
          let rec strip m =
            match m.mod_desc with
            | Tmod_structure s -> Some s
            | Tmod_constraint (m, _, _, _) -> strip m
            | _ -> None
          in
          match strip mb_expr with Some s -> callgraph q s | None -> ())
      | _ -> ())
    str.str_items

let () =
  let argv = Array.to_list Sys.argv in
  match argv with
  | _ :: pure :: tree :: files ->
      pure_modules := String.split_on_char ',' pure;
      tree_modules := String.split_on_char ',' tree;
      let loaded =
        List.map
          (fun f ->
            let c = Cmt_format.read_cmt f in
            match c.Cmt_format.cmt_annots with
            | Cmt_format.Implementation s -> (Filename.basename f, c.Cmt_format.cmt_modname, s)
            | _ -> failwith (f ^ ": not an implementation"))
          files
      in
      List.iter (fun (_, m, s) -> register m s) loaded;
      List.iter (fun (_, m, s) -> callgraph m s) loaded;
      compute ();
      List.iter (fun (_, _, s) -> compute_tail_only s) loaded;
      List.iter (fun (f, m, s) -> analyse_structure (Filename.chop_suffix f ".cmt" ^ ".ml") m s) loaded;
      Hashtbl.fold (fun q _ acc -> q :: acc) fns []
      |> List.sort compare
      |> List.iter (fun q ->
             match classify q with
             | Leaf -> Printf.printf "CALLGRAPH %s leaf %s\n" q (if Hashtbl.mem writes q then "(writes)" else "(write-free)")
             | Loop w -> Printf.printf "CALLGRAPH %s loop %s\n" q w
             | Run w -> Printf.printf "CALLGRAPH %s run %s\n" q w);
      (* REACHABLE: every value named, transitively, by the code of a module that can see a
         state (a non-pure module): a polymorphic library function that is not reachable can
         never be instantiated at a state *)
      let reach = Hashtbl.create 997 in
      let rec visit q =
        if not (Hashtbl.mem reach q) then begin
          Hashtbl.replace reach q ();
          match Hashtbl.find_opt fns q with Some i -> List.iter visit i.callees | None -> ()
        end
      in
      Hashtbl.iter (fun q _ -> if not (in_pure q) then visit q) fns;
      Hashtbl.fold (fun q _ acc -> q :: acc) reach []
      |> List.sort compare
      |> List.iter (Printf.printf "REACHABLE %s\n");
      List.iter print_endline (List.rev !sites);
      let targets =
        List.sort_uniq compare
          (List.filter_map
             (fun l ->
               match String.split_on_char ' ' l with
               | "SITE" :: _ :: _ :: _ :: _ :: top :: _ :: "HOLDS" :: _ -> Some top
               | _ -> None)
             !sites)
      in
      List.iter
        (fun (f, m, s) -> List.iter print_endline (uses targets (Filename.chop_suffix f ".cmt" ^ ".ml") m s))
        loaded
  | _ ->
      prerr_endline "usage: b2cmt.exe PURE_MODULES TREE_MODULES FILE.cmt ...";
      exit 2
