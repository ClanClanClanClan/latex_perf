(** See [rewrite_engine.mli]. *)

type conflict = [ `Overlap of Cst_edit.t * Cst_edit.t ]

let apply ~source ~edits = Cst_edit.apply_all source edits

let apply_and_reparse ~source ~edits =
  match apply ~source ~edits with
  | Error _ as e -> e
  | Ok rewritten ->
      let cst = Cst_of_ast.of_source rewritten in
      Ok (rewritten, cst)
