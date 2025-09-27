(* Minimal brace-aware expander for two controls: \textbf{...}, \emph{...}
   Non-nested, best-effort. Returns expanded string by stripping the control and
   braces. *)

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let take_ident s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && is_letter s.[!j] do
    incr j
  done;
  !j

let find_brace_block s i =
  let n = String.length s in
  if i >= n || s.[i] <> '{' then None
  else
    let j = ref (i + 1) in
    let depth = ref 1 in
    while !j < n && !depth > 0 do
      (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
      incr j
    done;
    if !depth = 0 then Some (i + 1, !j - i - 2) else None

let expand_once_with cfg s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if s.[!i] = '\\' then (
      let j = take_ident s (!i + 1) in
      let name =
        if j > !i + 1 then String.sub s (!i + 1) (j - (!i + 1)) else ""
      in
      match name with
      | _
        when try
               let p = List.assoc name cfg.Catalogue_loader.controls in
               p.Catalogue_loader.arity >= 1
             with Not_found ->
               List.mem name cfg.Catalogue_loader.strip_controls ->
          (* Consume 'arity' brace blocks and concatenate their contents *)
          let arity =
            try
              (snd
                 (List.find
                    (fun (n, _) -> n = name)
                    cfg.Catalogue_loader.controls))
                .arity
            with Not_found -> 1
          in
          let rec collect k idx =
            if k = 0 then (Buffer.contents b, idx)
            else
              match find_brace_block s idx with
              | Some (off, len) ->
                  Buffer.add_substring b s off len;
                  collect (k - 1) (idx + len + 2)
              | None -> (Buffer.contents b, idx)
          in
          let start_len = Buffer.length b in
          let _, idx' = collect arity j in
          if Buffer.length b = start_len then (
            Buffer.add_char b s.[!i];
            incr i)
          else i := idx'
      | "bfseries" when cfg.Catalogue_loader.bfseries_until_brace ->
          (* Copy until next closing brace or end. *)
          let n = String.length s in
          let k = ref j in
          while !k < n && s.[!k] <> '}' do
            incr k
          done;
          Buffer.add_substring b s j (!k - j);
          i := if !k < n then !k + 1 else !k
      | _ ->
          Buffer.add_char b s.[!i];
          incr i)
    else (
      Buffer.add_char b s.[!i];
      incr i)
  done;
  Buffer.contents b

let rec expand_fix s =
  let s' = expand_once_with Catalogue_loader.default s in
  if String.equal s s' then s else expand_fix s'

let rec expand_fix_with cfg s =
  let s' = expand_once_with cfg s in
  if String.equal s s' then s else expand_fix_with cfg s'
