(** Unit tests for Percentiles computation. *)

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[percentiles] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let feq a b = Float.abs (a -. b) < 0.001

let () =
  (* 1. Single element *)
  run "single element p50" (fun tag ->
      expect (feq (Percentiles.exact [| 5.0 |] 0.5) 5.0) tag);

  run "single element p99" (fun tag ->
      expect (feq (Percentiles.exact [| 5.0 |] 0.99) 5.0) tag);

  (* 2. Sorted array 1..100 *)
  run "p50 of 1..100" (fun tag ->
      let a = Array.init 100 (fun i -> float (i + 1)) in
      expect (feq (Percentiles.exact a 0.50) 50.0) tag);

  run "p99 of 1..100" (fun tag ->
      let a = Array.init 100 (fun i -> float (i + 1)) in
      expect (feq (Percentiles.exact a 0.99) 99.0) tag);

  run "p100 of 1..100" (fun tag ->
      let a = Array.init 100 (fun i -> float (i + 1)) in
      expect (feq (Percentiles.exact a 1.0) 100.0) tag);

  (* 3. Reverse-sorted → same results *)
  run "reverse-sorted" (fun tag ->
      let a = Array.init 100 (fun i -> float (100 - i)) in
      expect (feq (Percentiles.exact a 0.50) 50.0) tag);

  (* 4. Duplicates *)
  run "duplicates" (fun tag ->
      let a = [| 1.0; 1.0; 1.0; 2.0; 2.0; 2.0 |] in
      expect (feq (Percentiles.exact a 0.5) 1.0) tag);

  (* 5. Does not mutate original array *)
  run "non-destructive" (fun tag ->
      let a = [| 3.0; 1.0; 2.0 |] in
      let _ = Percentiles.exact a 0.5 in
      expect (feq a.(0) 3.0) (tag ^ ": a[0] unchanged");
      expect (feq a.(1) 1.0) (tag ^ ": a[1] unchanged");
      expect (feq a.(2) 2.0) (tag ^ ": a[2] unchanged"));

  (* --- keep_slowest --- *)
  run "keep_slowest top-2" (fun tag ->
      let xs : Percentiles.tail_trace =
        [ (10.0, "a"); (5.0, "b"); (20.0, "c") ]
      in
      let got = Percentiles.keep_slowest 2 xs in
      expect (List.length got = 2) (tag ^ ": length");
      expect (feq (fst (List.hd got)) 20.0) (tag ^ ": first=20");
      expect (snd (List.hd got) = "c") (tag ^ ": first meta=c");
      expect (feq (fst (List.nth got 1)) 10.0) (tag ^ ": second=10"));

  run "keep_slowest 0" (fun tag ->
      let xs : Percentiles.tail_trace = [ (1.0, "a") ] in
      expect (Percentiles.keep_slowest 0 xs = []) tag);

  run "keep_slowest n > length" (fun tag ->
      let xs : Percentiles.tail_trace = [ (1.0, "a"); (2.0, "b") ] in
      let got = Percentiles.keep_slowest 10 xs in
      expect (List.length got = 2) tag);

  run "keep_slowest empty" (fun tag ->
      expect (Percentiles.keep_slowest 5 [] = []) tag);

  if !fails > 0 then (
    Printf.eprintf "[percentiles] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[percentiles] PASS %d cases\n%!" !cases
