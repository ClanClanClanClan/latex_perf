(** Unit tests for Alloc_guard hot-path allocation checker. *)

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[alloc-guard] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. enabled starts false *)
  run "enabled default" (fun tag -> expect (not !Alloc_guard.enabled) tag);

  (* 2. with_no_alloc returns result (disabled) *)
  run "passthrough disabled" (fun tag ->
      let r = Alloc_guard.with_no_alloc (fun () -> 42) in
      expect (r = 42) tag);

  (* 3. with_no_alloc returns result (enabled) *)
  run "passthrough enabled" (fun tag ->
      Alloc_guard.enabled := true;
      let r = Alloc_guard.with_no_alloc (fun () -> "hello") in
      expect (r = "hello") tag;
      Alloc_guard.enabled := false);

  (* 4. words() returns non-negative float *)
  run "words non-negative" (fun tag ->
      (* Force some allocation so the counter is non-zero *)
      let _ = Array.make 1000 0 in
      expect (Alloc_guard.words () >= 0.0) tag);

  (* 5. words() non-decreasing across allocation *)
  run "words monotonic" (fun tag ->
      let w0 = Alloc_guard.words () in
      let _ = Array.make 10000 0 in
      let w1 = Alloc_guard.words () in
      expect (w1 >= w0) tag);

  (* 6. Allocating function with enabled=true → no crash *)
  run "alloc with enabled" (fun tag ->
      Alloc_guard.enabled := true;
      let r = Alloc_guard.with_no_alloc (fun () -> Array.make 100 0) in
      expect (Array.length r = 100) tag;
      Alloc_guard.enabled := false);

  (* 7. Non-allocating function with enabled=true *)
  run "no-alloc with enabled" (fun tag ->
      Alloc_guard.enabled := true;
      let r = Alloc_guard.with_no_alloc (fun () -> 1 + 1) in
      expect (r = 2) tag;
      Alloc_guard.enabled := false);

  if !fails > 0 then (
    Printf.eprintf "[alloc-guard] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[alloc-guard] PASS %d cases\n%!" !cases
