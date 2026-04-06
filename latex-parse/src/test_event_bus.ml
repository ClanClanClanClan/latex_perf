(** Tests for event_bus — pub/sub semantic deltas (spec W62). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_event_bus]\n%!";

  (* Test 1: create bus starts with 0 events *)
  let bus = Latex_parse_lib.Event_bus.create () in
  check "initial event_count = 0" (Latex_parse_lib.Event_bus.event_count bus = 0);

  (* Test 2: subscribe + publish → handler called *)
  let received = ref 0 in
  Latex_parse_lib.Event_bus.subscribe bus "counter" (fun _ -> incr received);
  Latex_parse_lib.Event_bus.publish bus
    (Latex_parse_lib.Event_bus.LabelDefined { key = "eq:1"; position = 10 });
  check "handler called once" (!received = 1);
  check "event_count = 1" (Latex_parse_lib.Event_bus.event_count bus = 1);

  (* Test 3: multiple publishes *)
  Latex_parse_lib.Event_bus.publish bus
    (Latex_parse_lib.Event_bus.RefUsed
       { key = "eq:1"; position = 20; command = "ref" });
  check "handler called twice" (!received = 2);

  (* Test 4: unsubscribe → handler not called *)
  Latex_parse_lib.Event_bus.unsubscribe bus "counter";
  Latex_parse_lib.Event_bus.publish bus
    (Latex_parse_lib.Event_bus.DocumentBegin 0);
  check "unsubscribed: not called" (!received = 2);
  check "event_count still increments"
    (Latex_parse_lib.Event_bus.event_count bus = 3);

  (* Test 5: multiple subscribers *)
  let bus2 = Latex_parse_lib.Event_bus.create () in
  let a = ref 0 in
  let b = ref 0 in
  Latex_parse_lib.Event_bus.subscribe bus2 "a" (fun _ -> incr a);
  Latex_parse_lib.Event_bus.subscribe bus2 "b" (fun _ -> incr b);
  Latex_parse_lib.Event_bus.publish bus2
    (Latex_parse_lib.Event_bus.SectionStarted
       { level = 1; title = "Intro"; position = 0 });
  check "subscriber a called" (!a = 1);
  check "subscriber b called" (!b = 1);

  (* Test 6: publish to bus with no subscribers → no crash *)
  let bus3 = Latex_parse_lib.Event_bus.create () in
  Latex_parse_lib.Event_bus.publish bus3
    (Latex_parse_lib.Event_bus.EnvironmentOpened
       { name = "figure"; position = 0 });
  check "no subscribers: no crash"
    (Latex_parse_lib.Event_bus.event_count bus3 = 1);

  (* Test 7: scan_and_publish parses LaTeX *)
  let bus4 = Latex_parse_lib.Event_bus.create () in
  let events = ref [] in
  Latex_parse_lib.Event_bus.subscribe bus4 "collector" (fun e ->
      events := e :: !events);
  Latex_parse_lib.Event_bus.scan_and_publish bus4
    {|\label{eq:1} \ref{fig:a} \section{Intro} \begin{figure}|};
  check "scan produced events" (List.length !events > 0);

  (* Test 8: global bus singleton *)
  let g1 = Latex_parse_lib.Event_bus.global () in
  let g2 = Latex_parse_lib.Event_bus.global () in
  check "global is singleton" (g1 == g2);

  Printf.printf "[test_event_bus] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_event_bus] %d failures\n%!" !fails;
    exit 1)
