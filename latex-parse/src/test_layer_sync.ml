(** Tests for Layer_sync — cross-layer consistency protocol. *)

open Test_helpers

let () =
  let open Latex_parse_lib.Layer_sync in
  (* Test 1: Initial version *)
  run "initial version" (fun tag ->
      expect (initial_version.gen = 0) (tag ^ ": gen=0");
      expect (initial_version.parent_gen = 0) (tag ^ ": parent_gen=0"));

  (* Test 2: accepts_delta — matching *)
  run "accepts_delta matching" (fun tag ->
      let parent = mk_version ~gen:5 ~parent_gen:3 in
      let child = mk_version ~gen:6 ~parent_gen:5 in
      expect
        (accepts_delta parent child)
        (tag ^ ": child.parent_gen = parent.gen"));

  (* Test 3: accepts_delta — mismatch *)
  run "accepts_delta mismatch" (fun tag ->
      let parent = mk_version ~gen:5 ~parent_gen:3 in
      let child = mk_version ~gen:6 ~parent_gen:4 in
      expect (not (accepts_delta parent child)) (tag ^ ": mismatch"));

  (* Test 4: advance *)
  run "advance creates new gen" (fun tag ->
      let parent = mk_version ~gen:0 ~parent_gen:0 in
      let child = advance parent in
      expect (child.parent_gen = parent.gen) (tag ^ ": parent_gen matches");
      expect (child.gen >= 0) (tag ^ ": gen assigned");
      let child2 = advance child in
      expect (child2.gen > child.gen) (tag ^ ": gen increments"));

  (* Test 5: Consistent snapshot *)
  run "consistent snapshot" (fun tag ->
      let s0 =
        { layer = L0; version = mk_version ~gen:1 ~parent_gen:0; data = "l0" }
      in
      let s1 =
        { layer = L1; version = mk_version ~gen:2 ~parent_gen:1; data = "l1" }
      in
      let snap = create_snapshot [ s0; s1 ] in
      expect (is_consistent snap) (tag ^ ": consistent"));

  (* Test 6: Inconsistent snapshot *)
  run "inconsistent snapshot" (fun tag ->
      let s0 =
        { layer = L0; version = mk_version ~gen:1 ~parent_gen:0; data = "l0" }
      in
      let s1 =
        { layer = L1; version = mk_version ~gen:2 ~parent_gen:99; data = "l1" }
      in
      let snap = create_snapshot [ s0; s1 ] in
      expect (not (is_consistent snap)) (tag ^ ": inconsistent"));

  (* Test 7: Rollback *)
  run "rollback child" (fun tag ->
      let s0 =
        { layer = L0; version = mk_version ~gen:1 ~parent_gen:0; data = "l0" }
      in
      let s1 =
        { layer = L1; version = mk_version ~gen:2 ~parent_gen:1; data = "l1" }
      in
      let snap = create_snapshot [ s0; s1 ] in
      let snap', result = rollback_child snap L1 in
      expect (result = Rolled_back) (tag ^ ": rolled back");
      expect (List.length snap'.states = 1) (tag ^ ": only L0 remains"));

  (* Test 8: Layer lookup *)
  run "layer of snapshot" (fun tag ->
      let s0 = { layer = L0; version = initial_version; data = "lexer" } in
      let snap = create_snapshot [ s0 ] in
      match layer_of_snapshot snap L0 with
      | Some s -> expect (s.data = "lexer") (tag ^ ": found L0")
      | None -> expect false (tag ^ ": L0 not found"));

  (* Test 9: Empty snapshot is consistent *)
  run "empty snapshot consistent" (fun tag ->
      let snap = create_snapshot [] in
      expect (is_consistent snap) (tag ^ ": empty consistent"));

  (* Test 10: Generation counter increments *)
  run "generation counter" (fun tag ->
      let g1 = current_gen () in
      let _ = next_gen () in
      let g2 = current_gen () in
      expect (g2 > g1) (tag ^ ": increments"));

  finalise "layer_sync"
