(** Tests for float_tracking — figure/table distance (spec W58). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_float_tracking]\n%!";

  (* Test 1: extract floats *)
  let floats =
    Latex_parse_lib.Float_tracking.extract_floats
      {|\begin{figure}\caption{A}\label{fig:a}\end{figure}
\begin{table}\caption{B}\label{tbl:b}\end{table}|}
  in
  check "extract 2 floats" (List.length floats = 2);

  (* Test 2: extract refs *)
  let refs =
    Latex_parse_lib.Float_tracking.extract_refs
      {|See \ref{fig:a} and \ref{tbl:b} for details.|}
  in
  check "extract 2 refs" (List.length refs = 2);

  (* Test 3: no floats *)
  let no_floats =
    Latex_parse_lib.Float_tracking.extract_floats "Hello world."
  in
  check "no floats" (no_floats = []);

  (* Test 4: compute distances *)
  let doc =
    {|\begin{figure}\caption{A}\label{fig:a}\end{figure}
Some text here in the middle of the document.
See \ref{fig:a} for the figure.|}
  in
  let dist = Latex_parse_lib.Float_tracking.compute_distances doc in
  check "distances computed" (dist.entries <> []);
  check "max_distance >= 0" (dist.max_distance >= 0);

  (* Test 5: empty document *)
  let dist2 = Latex_parse_lib.Float_tracking.compute_distances "" in
  check "empty: no entries" (dist2.entries = []);

  (* Test 6: float without ref *)
  let dist3 =
    Latex_parse_lib.Float_tracking.compute_distances
      {|\begin{figure}\label{fig:orphan}\end{figure}|}
  in
  check "orphan float: before_first_ref" (dist3.before_first_ref <> []);

  Printf.printf "[test_float_tracking] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_float_tracking] %d failures\n%!" !fails;
    exit 1)
