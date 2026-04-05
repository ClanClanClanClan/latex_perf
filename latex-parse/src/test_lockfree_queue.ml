(** Tests for Lockfree_queue — MPMC ring buffer (spec W63). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_lockfree_queue]\n%!";

  (* Test 1: basic push/pop *)
  let q = Latex_parse_lib.Lockfree_queue.create 16 in
  check "capacity is 16" (Latex_parse_lib.Lockfree_queue.capacity q = 16);
  check "initially empty" (Latex_parse_lib.Lockfree_queue.is_empty q);
  let ok = Latex_parse_lib.Lockfree_queue.try_push q 42 in
  check "push succeeds" ok;
  check "not empty after push" (not (Latex_parse_lib.Lockfree_queue.is_empty q));
  let v = Latex_parse_lib.Lockfree_queue.try_pop q in
  check "pop returns 42" (v = Some 42);
  check "empty after pop" (Latex_parse_lib.Lockfree_queue.is_empty q);

  (* Test 2: FIFO order *)
  let q2 = Latex_parse_lib.Lockfree_queue.create 8 in
  for i = 1 to 5 do
    ignore (Latex_parse_lib.Lockfree_queue.try_push q2 i)
  done;
  check "length is 5" (Latex_parse_lib.Lockfree_queue.length q2 = 5);
  for i = 1 to 5 do
    let v = Latex_parse_lib.Lockfree_queue.try_pop q2 in
    check (Printf.sprintf "FIFO order %d" i) (v = Some i)
  done;

  (* Test 3: full queue *)
  let q3 = Latex_parse_lib.Lockfree_queue.create 4 in
  for i = 1 to 4 do
    ignore (Latex_parse_lib.Lockfree_queue.try_push q3 i)
  done;
  let full_push = Latex_parse_lib.Lockfree_queue.try_push q3 99 in
  check "push to full fails" (not full_push);

  (* Test 4: empty queue pop *)
  let q4 = Latex_parse_lib.Lockfree_queue.create 4 in
  let empty_pop = Latex_parse_lib.Lockfree_queue.try_pop q4 in
  check "pop from empty returns None" (empty_pop = None);

  (* Test 5: round up to power of 2 *)
  let q5 = Latex_parse_lib.Lockfree_queue.create 5 in
  check "capacity rounded to 8" (Latex_parse_lib.Lockfree_queue.capacity q5 = 8);

  (* Test 6: wrap-around *)
  let q6 = Latex_parse_lib.Lockfree_queue.create 4 in
  (* Fill and drain twice to exercise wrap-around *)
  for _ = 1 to 2 do
    for i = 1 to 4 do
      ignore (Latex_parse_lib.Lockfree_queue.try_push q6 i)
    done;
    for i = 1 to 4 do
      let v = Latex_parse_lib.Lockfree_queue.try_pop q6 in
      check (Printf.sprintf "wrap-around %d" i) (v = Some i)
    done
  done;

  (* Test 7: concurrent producer/consumer *)
  let q7 = Latex_parse_lib.Lockfree_queue.create 1024 in
  let n = 10000 in
  let producer () =
    for i = 1 to n do
      Latex_parse_lib.Lockfree_queue.push q7 i
    done
  in
  let sum = Atomic.make 0 in
  let consumer () =
    for _ = 1 to n do
      let v = Latex_parse_lib.Lockfree_queue.pop q7 in
      ignore (Atomic.fetch_and_add sum v)
    done
  in
  let d1 = Domain.spawn producer in
  let d2 = Domain.spawn consumer in
  Domain.join d1;
  Domain.join d2;
  let expected = n * (n + 1) / 2 in
  check "concurrent sum correct" (Atomic.get sum = expected);

  (* Test 8: multi-producer with concurrent consumer *)
  let q8 = Latex_parse_lib.Lockfree_queue.create 4096 in
  let count = 5000 in
  let consumed = Atomic.make 0 in
  let p1 =
    Domain.spawn (fun () ->
        for i = 1 to count do
          Latex_parse_lib.Lockfree_queue.push q8 i
        done)
  in
  let p2 =
    Domain.spawn (fun () ->
        for i = 1 to count do
          Latex_parse_lib.Lockfree_queue.push q8 (i + count)
        done)
  in
  (* Consumer runs concurrently *)
  let c1 =
    Domain.spawn (fun () ->
        for _ = 1 to count * 2 do
          let _v = Latex_parse_lib.Lockfree_queue.pop q8 in
          ignore (Atomic.fetch_and_add consumed 1)
        done)
  in
  Domain.join p1;
  Domain.join p2;
  Domain.join c1;
  check "multi-producer all consumed" (Atomic.get consumed = count * 2);

  Printf.printf "[test_lockfree_queue] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_lockfree_queue] %d failures\n%!" !fails;
    exit 1)
