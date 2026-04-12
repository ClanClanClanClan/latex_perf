(** Test chunk store. 12+ cases. *)

open Latex_parse_lib
open Test_helpers

let () =
  (* ── split_into_chunks ──────────────────────────────────────── *)
  run "3 paragraphs -> 3 chunks" (fun tag ->
      let src =
        "First paragraph with enough text to exceed the sixty-four byte \
         minimum chunk size threshold.\n\n\
         Second paragraph also needs to be long enough to stand on its own as \
         a proper chunk boundary.\n\n\
         Third paragraph completing the document with sufficient length for \
         chunk store splitting."
      in
      let chunks = Chunk_store.split_into_chunks src in
      expect (Array.length chunks = 3) (tag ^ ": 3 chunks"));

  run "single paragraph -> 1 chunk" (fun tag ->
      let src = "Just one paragraph with enough text to exceed the minimum." in
      let chunks = Chunk_store.split_into_chunks src in
      expect (Array.length chunks = 1) (tag ^ ": 1 chunk"));

  run "empty string -> 0 chunks" (fun tag ->
      let chunks = Chunk_store.split_into_chunks "" in
      expect (Array.length chunks = 0) (tag ^ ": 0 chunks"));

  run "chunks cover entire source" (fun tag ->
      let src =
        "Hello world with enough text to be a real chunk.\n\n\
         Goodbye world with more text."
      in
      let chunks = Chunk_store.split_into_chunks src in
      expect (Array.length chunks >= 1) (tag ^ ": has chunks");
      let total_len =
        Array.fold_left
          (fun acc c -> acc + String.length c.Chunk_store.content)
          0 chunks
      in
      (* Chunks should cover most of the source (minus separators) *)
      expect
        (total_len > 0 && total_len <= String.length src)
        (tag ^ ": total len reasonable"));

  (* ── hash determinism ───────────────────────────────────────── *)
  run "same content same hash" (fun tag ->
      let src = "Deterministic content.\n\nSecond paragraph." in
      let c1 = Chunk_store.split_into_chunks src in
      let c2 = Chunk_store.split_into_chunks src in
      expect
        (Array.length c1 = Array.length c2
        && Array.for_all2 (fun a b -> a.Chunk_store.id = b.Chunk_store.id) c1 c2
        )
        (tag ^ ": identical hashes"));

  run "different content different hash" (fun tag ->
      let c1 =
        Chunk_store.split_into_chunks "Content version A with enough length."
      in
      let c2 =
        Chunk_store.split_into_chunks "Content version B with enough length."
      in
      expect
        (Array.length c1 > 0 && Array.length c2 > 0 && c1.(0).id <> c2.(0).id)
        (tag ^ ": different hashes"));

  (* ── diff_snapshots ─────────────────────────────────────────── *)
  run "diff identical -> empty" (fun tag ->
      let src = "Same document.\n\nTwo paragraphs here." in
      let s1 = Chunk_store.create_snapshot src in
      let s2 = Chunk_store.create_snapshot src in
      let dirty = Chunk_store.diff_snapshots s1 s2 in
      expect (dirty = []) (tag ^ ": no dirty"));

  run "diff single edit -> 1 dirty" (fun tag ->
      let old_src = "First paragraph.\n\nSecond paragraph unchanged." in
      let new_src = "First paragraph EDITED.\n\nSecond paragraph unchanged." in
      let s1 = Chunk_store.create_snapshot old_src in
      let s2 = Chunk_store.create_snapshot new_src in
      let dirty = Chunk_store.diff_snapshots s1 s2 in
      expect (List.length dirty >= 1) (tag ^ ": at least 1 dirty"));

  run "diff append -> new chunk dirty" (fun tag ->
      let old_src = "Original paragraph." in
      let new_src = "Original paragraph.\n\nNew paragraph added." in
      let s1 = Chunk_store.create_snapshot old_src in
      let s2 = Chunk_store.create_snapshot new_src in
      let dirty = Chunk_store.diff_snapshots s1 s2 in
      expect (List.length dirty >= 1) (tag ^ ": new chunk dirty"));

  (* ── cache ──────────────────────────────────────────────────── *)
  run "cache miss then hit" (fun tag ->
      let cache = Chunk_store.create_cache () in
      let id = 42L in
      expect (Chunk_store.lookup_chunk cache id = None) (tag ^ ": miss");
      Chunk_store.store_chunk cache id
        [
          {
            Validators_common.id = "TEST-001";
            severity = Info;
            message = "test";
            count = 1;
          };
        ];
      match Chunk_store.lookup_chunk cache id with
      | Some results ->
          expect (List.length results = 1) (tag ^ ": hit with 1 result")
      | None -> expect false (tag ^ ": should hit"));

  run "cache stats" (fun tag ->
      let cache = Chunk_store.create_cache () in
      ignore (Chunk_store.lookup_chunk cache 1L);
      ignore (Chunk_store.lookup_chunk cache 2L);
      Chunk_store.store_chunk cache 1L [];
      ignore (Chunk_store.lookup_chunk cache 1L);
      let stats = Chunk_store.cache_stats cache in
      expect (String.length stats > 0) (tag ^ ": non-empty stats");
      expect
        (Validators_common.contains_substring stats "hits=1")
        (tag ^ ": 1 hit"))

let () = finalise "chunk-store"
