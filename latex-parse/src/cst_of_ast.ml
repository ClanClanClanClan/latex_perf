(** See [cst_of_ast.mli]. *)

let span_of_loc ~start_offset ~end_offset =
  (* End may legitimately equal start (zero-length markers, Error nodes). Guard
     against pathological values just in case. *)
  let s = max 0 start_offset in
  let e = max s end_offset in
  Stable_spans.make ~start_offset:s ~end_offset:e

let substring_of_span src (span : Stable_spans.t) : string =
  let len = Stable_spans.length span in
  if len = 0 then ""
  else
    let src_len = String.length src in
    let s = span.start_offset in
    if s < 0 || s + len > src_len then "" else String.sub src s len

let span_of_ln (ln : Parser_l2.located_node) : Stable_spans.t =
  span_of_loc ~start_offset:ln.loc.offset ~end_offset:ln.loc.end_offset

let convert_node src (ln : Parser_l2.located_node) : Cst.t =
  let span = span_of_ln ln in
  let text = substring_of_span src span in
  match ln.node with
  | Parser_l2.Word _ -> Cst.CToken { kind = Cst.Word; text; span }
  | Parser_l2.Whitespace _ -> Cst.CTrivia { kind = Cst.Whitespace; text; span }
  | Parser_l2.Newline -> Cst.CTrivia { kind = Cst.Whitespace; text; span }
  | Parser_l2.Comment _ -> Cst.CTrivia { kind = Cst.Comment; text; span }
  | Parser_l2.MathInline _ -> Cst.CMathInline { text; span }
  | Parser_l2.MathDisplay _ -> Cst.CMathDisplay { text; span }
  | Parser_l2.Verbatim { env_name; _ } -> Cst.CVerbatim { env_name; text; span }
  | Parser_l2.Environment { env_name; _ } ->
      (* Body bytes between \begin{env}...\end{env}. Byte-lossless iff the
         source actually contains the closing tag; on unclosed environments the
         parser still emits an Environment node but there is no \end{env} in the
         source, and reconstructing one would lose bytes. In that case we fall
         back to CUnparsed so serialize returns the raw source verbatim. *)
      let opening = "\\begin{" ^ env_name ^ "}" in
      let closing = "\\end{" ^ env_name ^ "}" in
      let olen = String.length opening in
      let clen = String.length closing in
      let full_len = Stable_spans.length span in
      let has_closing =
        full_len >= olen + clen
        &&
        let start = span.start_offset + full_len - clen in
        start >= 0
        && start + clen <= String.length src
        && String.sub src start clen = closing
      in
      if has_closing then
        let body_len = full_len - olen - clen in
        let body_text =
          if body_len <= 0 then ""
          else String.sub src (span.start_offset + olen) body_len
        in
        Cst.CEnvironment { env_name; body_text; span }
      else Cst.CUnparsed { text; span }
  | Parser_l2.Cmd _ | Parser_l2.Group _ | Parser_l2.Error _ ->
      (* v26.2: these constructs lose structural info at AST construction (Cmd
         args are strings, Group body drops locs, Error carries only a
         position). Emit as byte-lossless Unparsed. PR B3 may revisit. *)
      Cst.CUnparsed { text; span }

let rec fill_nodes src prev_end acc = function
  | [] ->
      let src_len = String.length src in
      if prev_end < src_len then
        let span = span_of_loc ~start_offset:prev_end ~end_offset:src_len in
        let text = substring_of_span src span in
        Cst.CUnparsed { text; span } :: acc
      else acc
  | ln :: rest ->
      let span = span_of_ln ln in
      let acc =
        if span.start_offset > prev_end then
          let gap =
            span_of_loc ~start_offset:prev_end ~end_offset:span.start_offset
          in
          let text = substring_of_span src gap in
          Cst.CUnparsed { text; span = gap } :: acc
        else acc
      in
      let cst_node = convert_node src ln in
      let next_end = max prev_end span.end_offset in
      fill_nodes src next_end (cst_node :: acc) rest

let of_located (src : string) (nodes : Parser_l2.located_node list) : Cst.t list
    =
  List.rev (fill_nodes src 0 [] nodes)

let of_source (src : string) : Cst.t list =
  let nodes, _errors = Parser_l2.parse_located src in
  of_located src nodes
