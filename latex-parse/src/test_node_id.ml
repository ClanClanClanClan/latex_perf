(** PR #241 (memo §6 E3): verify [Node_id.of_located] produces stable
    content_ids under the invariants proved in [proofs/StableNodeIds.v]. *)

open Latex_parse_lib
open Test_helpers

let mk_loc offset = { Parser_l2.line = 0; col = 0; offset; end_offset = offset }

let () =
  (* 1. Same inputs produce equal node_ids. *)
  run "of_located determinism" (fun tag ->
      let a =
        Node_id.of_located ~node_length:10 ~command_hash:42 (mk_loc 100)
      in
      let b =
        Node_id.of_located ~node_length:10 ~command_hash:42 (mk_loc 100)
      in
      expect (Node_id.equal a b) (tag ^ ": equal inputs ⇒ equal ids"));

  (* 2. content_id is stable across offset changes (the hash64 changes but
     content_id pair does not). *)
  run "content_id invariant under offset shift" (fun tag ->
      let a = Node_id.of_located ~node_length:7 ~command_hash:13 (mk_loc 50) in
      let b = Node_id.of_located ~node_length:7 ~command_hash:13 (mk_loc 120) in
      expect
        (Node_id.content_id a = Node_id.content_id b)
        (tag ^ ": content_id stable under offset shift");
      expect
        (not (Node_id.equal a b))
        (tag ^ ": full node_id differs when offset differs"));

  (* 3. content_id distinguishes nodes with different length OR command. *)
  run "content_id distinguishes content" (fun tag ->
      let a = Node_id.of_located ~node_length:7 ~command_hash:13 (mk_loc 50) in
      let b = Node_id.of_located ~node_length:8 ~command_hash:13 (mk_loc 50) in
      let c = Node_id.of_located ~node_length:7 ~command_hash:14 (mk_loc 50) in
      expect
        (Node_id.content_id a <> Node_id.content_id b)
        (tag ^ ": different length ⇒ different content_id");
      expect
        (Node_id.content_id a <> Node_id.content_id c)
        (tag ^ ": different command_hash ⇒ different content_id"));

  (* 4. hash64 is deterministic. *)
  run "hash64 determinism" (fun tag ->
      let a = Node_id.of_located ~node_length:5 ~command_hash:99 (mk_loc 1) in
      let b = Node_id.of_located ~node_length:5 ~command_hash:99 (mk_loc 1) in
      expect
        (Node_id.hash64 a = Node_id.hash64 b)
        (tag ^ ": same inputs ⇒ same hash64"));

  finalise "node_id"
