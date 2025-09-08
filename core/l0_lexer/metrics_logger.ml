(* Tail latency forensics - Enhanced metrics logging for SIMD.md integration *)

open Printf

type row = {
  ms_total      : float;
  t_in_start    : int64;
  t_in_done     : int64;
  t_proc_start  : int64;
  t_hedge_fire  : int64;
  t_first_reply : int64;
  t_reply_ready : int64;
  hedged        : bool;
  origin        : string;  (* "P" primary, "H" hedge *)
}

type t = {
  mutable slowest : (float * row) list;  (* keep top-N by ms_total *)
  keep            : int;
  mutable hedged  : int;
  mutable hedged_wins : int;
  mutable rotations   : int;
}

let create ~keep = { slowest=[]; keep; hedged=0; hedged_wins=0; rotations=0 }

let keep_slowest n xs =
  xs |> List.sort (fun (a,_) (b,_) -> compare b a) |> fun s ->
  let rec take k = function [] -> [] | _ when k=0 -> [] | x::xs -> x::take (k-1) xs in
  take n s

let note p row =
  p.slowest <- keep_slowest p.keep ((row.ms_total, row) :: p.slowest)

let bump_hedge p ~win =
  p.hedged <- p.hedged + 1; if win then p.hedged_wins <- p.hedged_wins + 1

let set_rotations p n = p.rotations <- n

let dump_csv p path =
  try
    let oc = open_out path in
    fprintf oc "ms_total,t_in_start,t_in_done,t_proc_start,t_hedge_fire,t_first_reply,t_reply_ready,hedged,origin\n";
    p.slowest |> List.iter (fun (_, row) ->
      fprintf oc "%.6f,%Ld,%Ld,%Ld,%Ld,%Ld,%Ld,%b,%s\n"
        row.ms_total row.t_in_start row.t_in_done row.t_proc_start
        row.t_hedge_fire row.t_first_reply row.t_reply_ready row.hedged row.origin
    );
    close_out oc;
    eprintf "[Metrics] CSV dumped to %s (%d rows)\n%!" path (List.length p.slowest)
  with e ->
    eprintf "[Metrics] CSV dump failed: %s\n%!" (Printexc.to_string e)

let print_summary p =
  let hedge_rate = if p.hedged = 0 then 0.0 else (float p.hedged_wins) /. (float p.hedged) *. 100.0 in
  printf "\n=== Tail Metrics Summary ===\n";
  printf "Hedges: %d (win rate: %.1f%%)\n" p.hedged hedge_rate;
  printf "Rotations: %d\n" p.rotations;
  printf "Slowest samples kept: %d\n" (List.length p.slowest);
  if p.slowest <> [] then begin
    let worst_ms = fst (List.hd p.slowest) in
    printf "Worst latency: %.3fms\n" worst_ms
  end