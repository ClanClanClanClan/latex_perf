(* SINGLE-PASS VALIDATOR - ULTRA-OPTIMIZED FOR <1ms *)
(* Target: <1ms for 276K tokens (validators should add ~0 overhead) *)

open Bigarray

(* Pre-allocated global buffers to avoid allocation *)
let global_issue_buffer = Array1.create int32 c_layout 65536
let global_issue_count = ref 0

(* Token kinds - dense 0..19 *)
let kind_other = 12
let kind_space = 10
let kind_letter = 11
let kind_begin_group = 1
let kind_end_group = 2

(* Inline everything critical *)
let[@inline always] check_quote code issues pos =
  if code = 34 then begin
    Array1.unsafe_set issues !global_issue_count (Int32.of_int pos);
    incr global_issue_count
  end

let[@inline always] check_hyphen kinds codes i n issues =
  if i + 1 < n && 
     Array1.unsafe_get codes i = 45l &&
     Array1.unsafe_get codes (i+1) = 45l then begin
    Array1.unsafe_set issues !global_issue_count (Int32.of_int i);
    incr global_issue_count
  end

(* ULTRA-FAST MAIN LOOP - Everything inlined *)
let validate_soa kinds codes n =
  global_issue_count := 0;
  
  (* Single pass, no function calls *)
  let i = ref 0 in
  while !i < n do
    let k = Int32.to_int (Array1.unsafe_get kinds !i) in
    let c = Int32.to_int (Array1.unsafe_get codes !i) in
    
    (* Direct checks, no dispatch *)
    if k = kind_other then begin
      (* Quote check *)
      if c = 34 then begin
        Array1.unsafe_set global_issue_buffer !global_issue_count (Int32.of_int !i);
        incr global_issue_count
      end;
      (* Hyphen check *)
      if c = 45 && !i + 1 < n then begin
        let next_c = Int32.to_int (Array1.unsafe_get codes (!i + 1)) in
        if next_c = 45 then begin
          Array1.unsafe_set global_issue_buffer !global_issue_count (Int32.of_int !i);
          incr global_issue_count
        end
      end
    end;
    
    incr i
  done;
  
  !global_issue_count

(* Benchmark function *)
let bench_ultra tokens_array =
  let n = Array.length tokens_array in
  
  (* Pre-allocate SoA arrays *)
  let kinds = Array1.create int32 c_layout n in
  let codes = Array1.create int32 c_layout n in
  
  (* Convert tokens to SoA (this is one-time cost) *)
  for i = 0 to n - 1 do
    let tok = tokens_array.(i) in
    let (k, c) = match tok.Validator_core_fixed.token with
      | TChar (uc, Other) -> (kind_other, Uchar.to_int uc)
      | TChar (uc, Space) -> (kind_space, Uchar.to_int uc)
      | TChar (uc, Letter) -> (kind_letter, Uchar.to_int uc)
      | TChar (uc, BeginGroup) -> (kind_begin_group, Uchar.to_int uc)
      | TChar (uc, EndGroup) -> (kind_end_group, Uchar.to_int uc)
      | _ -> (0, 0)
    in
    Array1.unsafe_set kinds i (Int32.of_int k);
    Array1.unsafe_set codes i (Int32.of_int c)
  done;
  
  (* Warm up *)
  for _ = 1 to 10 do
    ignore (validate_soa kinds codes n)
  done;
  
  (* Benchmark *)
  let times = ref [] in
  for _ = 1 to 100 do
    let t0 = Unix.gettimeofday () in
    let issues = validate_soa kinds codes n in
    let t1 = Unix.gettimeofday () in
    times := (t1 -. t0) *. 1000.0 :: !times
  done;
  
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted 98 in
  let p95 = List.nth sorted 94 in
  let p50 = List.nth sorted 49 in
  let mean = (List.fold_left (+.) 0.0 sorted) /. 100.0 in
  
  Printf.printf "Ultra-optimized validator benchmark (%d tokens):\n" n;
  Printf.printf "  Mean: %.3fms\n" mean;
  Printf.printf "  P50:  %.3fms\n" p50;
  Printf.printf "  P95:  %.3fms\n" p95;
  Printf.printf "  P99:  %.3fms\n" p99;
  Printf.printf "  Issues found: %d\n" !global_issue_count;
  
  (* Estimate for 276K *)
  let scale = 276000.0 /. float n in
  Printf.printf "\nEstimated for 276K tokens:\n";
  Printf.printf "  P99: %.3fms\n" (p99 *. scale);
  
  if p99 *. scale < 1.0 then
    Printf.printf "✅ ULTRA-FAST: <1ms validator overhead!\n"
  else
    Printf.printf "⚠️ Still too slow: %.1fx over 1ms target\n" (p99 *. scale);
  
  p99 *. scale