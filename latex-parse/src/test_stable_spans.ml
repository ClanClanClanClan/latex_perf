(** Tests for [Stable_spans]. *)

open Latex_parse_lib
open Test_helpers

let () =
  run "make basic" (fun tag ->
      let s = Stable_spans.make ~start_offset:5 ~end_offset:10 in
      expect (Stable_spans.length s = 5) (tag ^ ": length = 5"));

  run "zero-length span" (fun tag ->
      let s = Stable_spans.zero 7 in
      expect (Stable_spans.is_empty s) (tag ^ ": is_empty");
      expect (Stable_spans.length s = 0) (tag ^ ": length 0"));

  run "make rejects negative start" (fun tag ->
      let raised =
        try
          let _ = Stable_spans.make ~start_offset:(-1) ~end_offset:0 in
          false
        with Invalid_argument _ -> true
      in
      expect raised (tag ^ ": Invalid_argument raised"));

  run "make rejects start > end" (fun tag ->
      let raised =
        try
          let _ = Stable_spans.make ~start_offset:10 ~end_offset:5 in
          false
        with Invalid_argument _ -> true
      in
      expect raised (tag ^ ": Invalid_argument raised"));

  run "contains" (fun tag ->
      let s = Stable_spans.make ~start_offset:5 ~end_offset:10 in
      expect (Stable_spans.contains s 5) (tag ^ ": 5 in [5,10)");
      expect (Stable_spans.contains s 9) (tag ^ ": 9 in [5,10)");
      expect (not (Stable_spans.contains s 10)) (tag ^ ": 10 not in [5,10)");
      expect (not (Stable_spans.contains s 4)) (tag ^ ": 4 not in [5,10)"));

  run "disjoint" (fun tag ->
      let a = Stable_spans.make ~start_offset:0 ~end_offset:5 in
      let b = Stable_spans.make ~start_offset:5 ~end_offset:10 in
      let c = Stable_spans.make ~start_offset:3 ~end_offset:8 in
      expect (Stable_spans.disjoint a b) (tag ^ ": touching = disjoint");
      expect
        (not (Stable_spans.disjoint a c))
        (tag ^ ": overlapping = not disjoint"));

  run "substring" (fun tag ->
      let src = "hello world" in
      let s = Stable_spans.make ~start_offset:6 ~end_offset:11 in
      expect
        (Stable_spans.substring src s = "world")
        (tag ^ ": substring = 'world'"));

  run "shift_after moves span following edit" (fun tag ->
      let s = Stable_spans.make ~start_offset:10 ~end_offset:15 in
      let e =
        Stable_spans.
          { edit_offset = 0; edit_old_length = 3; edit_new_length = 5 }
      in
      let s' = Stable_spans.shift_after e s in
      expect
        (s'.start_offset = 12 && s'.end_offset = 17)
        (tag ^ ": shifted by +2"));

  run "shift_after leaves earlier span untouched" (fun tag ->
      let s = Stable_spans.make ~start_offset:2 ~end_offset:5 in
      let e =
        Stable_spans.
          { edit_offset = 10; edit_old_length = 1; edit_new_length = 5 }
      in
      let s' = Stable_spans.shift_after e s in
      expect (Stable_spans.equal s s') (tag ^ ": unchanged"));

  run "damaged_by detects overlap" (fun tag ->
      let s = Stable_spans.make ~start_offset:10 ~end_offset:20 in
      let e_overlap =
        Stable_spans.
          { edit_offset = 15; edit_old_length = 3; edit_new_length = 1 }
      in
      let e_before =
        Stable_spans.
          { edit_offset = 5; edit_old_length = 2; edit_new_length = 0 }
      in
      expect (Stable_spans.damaged_by e_overlap s) (tag ^ ": overlap damages");
      expect
        (not (Stable_spans.damaged_by e_before s))
        (tag ^ ": earlier edit does not damage"));

  run "of_located uses offset+end_offset" (fun tag ->
      let ln : Parser_l2.located_node =
        {
          node = Parser_l2.Word "hi";
          loc = { line = 1; col = 0; offset = 3; end_offset = 5 };
        }
      in
      let s = Stable_spans.of_located ln in
      expect
        (s.start_offset = 3 && s.end_offset = 5)
        (tag ^ ": span matches loc"));

  finalise "stable-spans"
