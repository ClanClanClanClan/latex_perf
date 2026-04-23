(** Tests for [Cst_edit]. *)

open Latex_parse_lib
open Test_helpers

let () =
  run "insert at position" (fun tag ->
      let e = Cst_edit.insert ~at:5 "X" in
      let out = Cst_edit.apply_single "hello world" e in
      expect (out = "helloX world") (tag ^ ": 'helloX world'"));

  run "delete range" (fun tag ->
      let e = Cst_edit.delete ~start_offset:5 ~end_offset:11 in
      let out = Cst_edit.apply_single "hello world" e in
      expect (out = "hello") (tag ^ ": deletes trailing' world'"));

  run "replace range" (fun tag ->
      let e = Cst_edit.replace ~start_offset:6 ~end_offset:11 "LaTeX" in
      let out = Cst_edit.apply_single "hello world" e in
      expect (out = "hello LaTeX") (tag ^ ": replaced"));

  run "make rejects negative start" (fun tag ->
      let raised =
        try
          let _ =
            Cst_edit.make ~start_offset:(-1) ~end_offset:0 ~replacement:""
          in
          false
        with Invalid_argument _ -> true
      in
      expect raised (tag ^ ": Invalid_argument"));

  run "make rejects end < start" (fun tag ->
      let raised =
        try
          let _ = Cst_edit.make ~start_offset:5 ~end_offset:2 ~replacement:"" in
          false
        with Invalid_argument _ -> true
      in
      expect raised (tag ^ ": Invalid_argument"));

  run "delta is length change" (fun tag ->
      let e = Cst_edit.replace ~start_offset:0 ~end_offset:5 "hi" in
      expect (Cst_edit.delta e = -3) (tag ^ ": -3 bytes"));

  run "insertions at same offset don't conflict" (fun tag ->
      let a = Cst_edit.insert ~at:5 "X" in
      let b = Cst_edit.insert ~at:5 "Y" in
      expect (not (Cst_edit.conflicts a b)) (tag ^ ": same-point inserts OK"));

  run "insertion strictly inside replacement conflicts" (fun tag ->
      let a = Cst_edit.insert ~at:5 "Z" in
      let b = Cst_edit.replace ~start_offset:3 ~end_offset:8 "xxx" in
      expect (Cst_edit.conflicts a b) (tag ^ ": insert strictly inside range"));

  run "insertion at boundary does not conflict" (fun tag ->
      let a = Cst_edit.insert ~at:3 "Z" in
      let b = Cst_edit.replace ~start_offset:3 ~end_offset:8 "xxx" in
      expect
        (not (Cst_edit.conflicts a b))
        (tag ^ ": insert at left edge allowed"));

  run "overlapping replacements conflict" (fun tag ->
      let a = Cst_edit.replace ~start_offset:2 ~end_offset:6 "A" in
      let b = Cst_edit.replace ~start_offset:4 ~end_offset:9 "B" in
      expect (Cst_edit.conflicts a b) (tag ^ ": overlap detected"));

  run "disjoint replacements don't conflict" (fun tag ->
      let a = Cst_edit.replace ~start_offset:2 ~end_offset:5 "A" in
      let b = Cst_edit.replace ~start_offset:5 ~end_offset:9 "B" in
      expect
        (not (Cst_edit.conflicts a b))
        (tag ^ ": touching at boundary = no overlap"));

  run "validate_non_overlapping ok" (fun tag ->
      let es =
        [
          Cst_edit.replace ~start_offset:0 ~end_offset:2 "X";
          Cst_edit.replace ~start_offset:5 ~end_offset:7 "Y";
          Cst_edit.insert ~at:10 "Z";
        ]
      in
      expect
        (Cst_edit.validate_non_overlapping es = Ok ())
        (tag ^ ": no conflicts"));

  run "validate_non_overlapping error" (fun tag ->
      let a = Cst_edit.replace ~start_offset:0 ~end_offset:4 "X" in
      let b = Cst_edit.replace ~start_offset:3 ~end_offset:6 "Y" in
      match Cst_edit.validate_non_overlapping [ a; b ] with
      | Error (e, f) ->
          expect
            (Cst_edit.equal e a && Cst_edit.equal f b)
            (tag ^ ": reports the conflicting pair")
      | Ok () -> expect false (tag ^ ": missed overlap"));

  run "apply_all multiple edits" (fun tag ->
      let src = "abcdefghij" in
      let es =
        [
          Cst_edit.replace ~start_offset:0 ~end_offset:2 "XX";
          Cst_edit.insert ~at:5 "_";
          Cst_edit.delete ~start_offset:8 ~end_offset:10;
        ]
      in
      match Cst_edit.apply_all src es with
      | Ok out -> expect (out = "XXcde_fgh") (tag ^ ": '" ^ out ^ "'")
      | Error _ -> expect false (tag ^ ": should succeed"));

  run "apply_all unsorted" (fun tag ->
      let src = "abcdefghij" in
      let es =
        [
          Cst_edit.replace ~start_offset:5 ~end_offset:7 "YY";
          Cst_edit.replace ~start_offset:0 ~end_offset:2 "XX";
        ]
      in
      match Cst_edit.apply_all src es with
      | Ok out -> expect (out = "XXcdeYYhij") (tag ^ ": sorted internally")
      | Error _ -> expect false (tag ^ ": should succeed"));

  run "apply_all rejects overlap" (fun tag ->
      let src = "abcdefghij" in
      let a = Cst_edit.replace ~start_offset:0 ~end_offset:5 "X" in
      let b = Cst_edit.replace ~start_offset:3 ~end_offset:7 "Y" in
      match Cst_edit.apply_all src [ a; b ] with
      | Error (`Overlap (x, y)) ->
          expect
            (Cst_edit.equal x a && Cst_edit.equal y b)
            (tag ^ ": reports the conflicting pair")
      | Ok _ -> expect false (tag ^ ": should reject"));

  run "shift_after moves edit forward" (fun tag ->
      let e = Cst_edit.replace ~start_offset:10 ~end_offset:15 "" in
      let e' = Cst_edit.shift_after ~by:3 ~at_or_after:5 e in
      expect (e'.start_offset = 13 && e'.end_offset = 18) (tag ^ ": shifted"));

  run "shift_after leaves earlier edit untouched" (fun tag ->
      let e = Cst_edit.replace ~start_offset:2 ~end_offset:4 "" in
      let e' = Cst_edit.shift_after ~by:10 ~at_or_after:20 e in
      expect (Cst_edit.equal e e') (tag ^ ": unchanged"));

  finalise "cst-edit"
