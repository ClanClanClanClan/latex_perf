(** Tests for invalidation engine: minimal chunk invalidation set. *)

open Latex_parse_lib
open Test_helpers

(* Pad paragraphs to > 128 bytes to prevent chunk merging *)
let pad s =
  let n = String.length s in
  if n >= 128 then s else s ^ String.make (128 - n) ' '

let mk_snap texts =
  Chunk_store.create_snapshot (String.concat "\n\n" (List.map pad texts))

let () =
  run "edit chunk without labels/refs: only that chunk" (fun tag ->
      let old_snap =
        mk_snap [ "Hello world."; "\\label{x} stuff."; "\\ref{x} more." ]
      in
      let new_snap =
        mk_snap [ "Hello CHANGED."; "\\label{x} stuff."; "\\ref{x} more." ]
      in
      let affected = Invalidation.compute ~old_snap ~new_snap in
      expect (List.mem 0 affected) (tag ^ ": chunk 0 affected");
      expect (not (List.mem 1 affected)) (tag ^ ": chunk 1 not affected");
      expect (not (List.mem 2 affected)) (tag ^ ": chunk 2 not affected"));

  run "edit chunk with label: ref chunk also affected" (fun tag ->
      let old_snap =
        mk_snap
          [
            "intro text here";
            "\\label{eq:1} equation content";
            "See \\ref{eq:1} for details.";
          ]
      in
      let new_snap =
        mk_snap
          [
            "intro text here";
            "\\label{eq:1} CHANGED equation content";
            "See \\ref{eq:1} for details.";
          ]
      in
      let affected = Invalidation.compute ~old_snap ~new_snap in
      expect (List.mem 1 affected) (tag ^ ": label chunk affected");
      expect (List.mem 2 affected) (tag ^ ": ref chunk affected"));

  run "add new label: no extra invalidation" (fun tag ->
      let old_snap = mk_snap [ "text only"; "more text" ] in
      let new_snap = mk_snap [ "\\label{new} text"; "more text" ] in
      let affected = Invalidation.compute ~old_snap ~new_snap in
      expect (List.mem 0 affected) (tag ^ ": changed chunk");
      expect (not (List.mem 1 affected)) (tag ^ ": unchanged chunk not affected"));

  run "structural change: all chunks" (fun tag ->
      let old_snap = mk_snap [ "one"; "two" ] in
      let new_snap = mk_snap [ "one"; "two"; "three" ] in
      let affected = Invalidation.compute ~old_snap ~new_snap in
      expect
        (List.length affected >= 3)
        (tag ^ ": all chunks on structural change"));

  run "no change: empty affected set" (fun tag ->
      let snap = mk_snap [ "hello"; "world" ] in
      let affected = Invalidation.compute ~old_snap:snap ~new_snap:snap in
      expect (affected = []) (tag ^ ": no changes"));

  run "macro def change propagates to use" (fun tag ->
      let old_snap =
        mk_snap
          [ "\\newcommand{\\myop}{old}"; "Use \\myop here."; "No macros." ]
      in
      let new_snap =
        mk_snap
          [ "\\newcommand{\\myop}{NEW}"; "Use \\myop here."; "No macros." ]
      in
      let affected = Invalidation.compute ~old_snap ~new_snap in
      expect (List.mem 0 affected) (tag ^ ": def chunk");
      expect (List.mem 1 affected) (tag ^ ": use chunk");
      expect (not (List.mem 2 affected)) (tag ^ ": unrelated chunk not affected"));

  run "multiple labels in one chunk" (fun tag ->
      let old_snap =
        mk_snap
          [
            "\\label{a} \\label{b} content";
            "\\ref{a} stuff";
            "\\ref{b} stuff";
            "no refs";
          ]
      in
      let new_snap =
        mk_snap
          [
            "\\label{a} \\label{b} CHANGED";
            "\\ref{a} stuff";
            "\\ref{b} stuff";
            "no refs";
          ]
      in
      let affected = Invalidation.compute ~old_snap ~new_snap in
      expect (List.mem 0 affected) (tag ^ ": label chunk");
      expect (List.mem 1 affected) (tag ^ ": ref-a chunk");
      expect (List.mem 2 affected) (tag ^ ": ref-b chunk");
      expect (not (List.mem 3 affected)) (tag ^ ": unrelated chunk not affected"));

  run "invalidation set smaller than full set" (fun tag ->
      let old_snap =
        mk_snap
          [
            "para one";
            "para two";
            "para three CHANGE";
            "para four";
            "para five";
          ]
      in
      let new_snap =
        mk_snap
          [
            "para one";
            "para two";
            "para three CHANGED";
            "para four";
            "para five";
          ]
      in
      let affected = Invalidation.compute ~old_snap ~new_snap in
      let total = Array.length new_snap.chunks in
      expect (List.length affected < total) (tag ^ ": fewer than all chunks"))

let () = finalise "invalidation"
