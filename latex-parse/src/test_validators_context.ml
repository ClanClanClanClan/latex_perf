(** Unit tests for Validators_context per-thread storage. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[val-ctx] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. Fresh thread: empty *)
  run "fresh empty" (fun tag ->
      (* Clear first in case prior tests left state *)
      Validators_context.clear ();
      let cmds = Validators_context.get_post_commands () in
      expect (cmds = []) tag);

  (* 2. Set then get roundtrip *)
  run "set-get roundtrip" (fun tag ->
      let open Validators_context in
      let xs =
        [
          { name = "a"; s = 0; e = 1 };
          { name = "b"; s = 2; e = 3 };
          { name = "c"; s = 4; e = 5 };
        ]
      in
      set_post_commands xs;
      let got = get_post_commands () in
      expect (List.length got = 3) (tag ^ ": length");
      expect ((List.hd got).name = "a") (tag ^ ": first name");
      clear ());

  (* 3. Clear removes state *)
  run "clear" (fun tag ->
      let open Validators_context in
      set_post_commands [ { name = "x"; s = 0; e = 1 } ];
      clear ();
      let got = get_post_commands () in
      expect (got = []) tag);

  (* 4. Overwrite *)
  run "overwrite" (fun tag ->
      let open Validators_context in
      set_post_commands [ { name = "old"; s = 0; e = 1 } ];
      set_post_commands [ { name = "new"; s = 2; e = 3 } ];
      let got = get_post_commands () in
      expect (List.length got = 1) (tag ^ ": length");
      expect ((List.hd got).name = "new") (tag ^ ": name");
      clear ());

  (* 5. Thread isolation: spawned thread sees empty *)
  run "thread isolation" (fun tag ->
      let open Validators_context in
      set_post_commands [ { name = "main"; s = 0; e = 1 } ];
      let child_saw = ref [] in
      let t = Thread.create (fun () -> child_saw := get_post_commands ()) () in
      Thread.join t;
      expect (!child_saw = []) (tag ^ ": child should see empty");
      clear ());

  (* 6. Two threads with independent state *)
  run "concurrent isolation" (fun tag ->
      let open Validators_context in
      let b1 = Barrier.create () in
      let b2 = Barrier.create () in
      let a_saw = ref "" in
      let b_saw = ref "" in
      let ta =
        Thread.create
          (fun () ->
            set_post_commands [ { name = "thread_a"; s = 0; e = 1 } ];
            Barrier.release b1;
            Barrier.wait b2;
            let got = get_post_commands () in
            (a_saw := match got with [ x ] -> x.name | _ -> "WRONG_LENGTH");
            clear ())
          ()
      in
      let tb =
        Thread.create
          (fun () ->
            set_post_commands [ { name = "thread_b"; s = 0; e = 1 } ];
            Barrier.release b1;
            Barrier.wait b2;
            let got = get_post_commands () in
            (b_saw := match got with [ x ] -> x.name | _ -> "WRONG_LENGTH");
            clear ())
          ()
      in
      (* Wait for both threads to have set their state *)
      Barrier.wait b1;
      Barrier.wait b1;
      (* Release both to read *)
      Barrier.release b2;
      Thread.join ta;
      Thread.join tb;
      expect (!a_saw = "thread_a") (tag ^ ": a saw " ^ !a_saw);
      expect (!b_saw = "thread_b") (tag ^ ": b saw " ^ !b_saw));

  (* 7. Clear is idempotent *)
  run "clear idempotent" (fun tag ->
      Validators_context.clear ();
      Validators_context.clear ();
      let got = Validators_context.get_post_commands () in
      expect (got = []) tag);

  if !fails > 0 then (
    Printf.eprintf "[val-ctx] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[val-ctx] PASS %d cases\n%!" !cases
