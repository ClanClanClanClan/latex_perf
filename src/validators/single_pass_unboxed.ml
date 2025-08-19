(* SINGLE-PASS VALIDATOR - UNBOXED VERSION *)
(* Following expert advice: int8_unsigned for zero boxing overhead *)

open Bigarray

(* Token kinds - fits in int8 *)
let kind_other = 12
let kind_space = 10  
let kind_letter = 11
let kind_begin_group = 1
let kind_end_group = 2

(* Unboxed SoA using int8_unsigned - returns immediate ints! *)
module SoA_Unboxed = struct
  type t = {
    kind_u8: (int, int8_unsigned_elt, c_layout) Array1.t;
    ascii_interest: (int, int8_unsigned_elt, c_layout) Array1.t; (* 0=skip, else ASCII code *)
    len: int;
  }
  
  let create ~capacity = {
    kind_u8 = Array1.create int8_unsigned c_layout capacity;
    ascii_interest = Array1.create int8_unsigned c_layout capacity;
    len = 0;
  }
end

(* Pre-allocated issue buffer - use int not int32! *)
let global_issue_buffer = Array1.create int c_layout 65536
let global_issue_count = ref 0

(* TRACK 1: Unboxed validator with int8 *)
let validate_unboxed_2load kind_u8 ascii_u8 n =
  global_issue_count := 0;
  let n1 = n - 1 in
  
  for i = 0 to n1 do
    (* These return immediate ints - NO BOXING! *)
    let k = Array1.unsafe_get kind_u8 i in
    if k = kind_other then begin
      let a = Array1.unsafe_get ascii_u8 i in
      if a < 128 then begin
        (* ASCII quote check *)
        if a = 34 then begin
          Array1.unsafe_set global_issue_buffer !global_issue_count i;
          incr global_issue_count
        end;
        (* ASCII hyphen check *)
        if a = 45 && i < n1 then begin
          let a1 = Array1.unsafe_get ascii_u8 (i + 1) in
          if a1 = 45 then begin
            Array1.unsafe_set global_issue_buffer !global_issue_count i;
            incr global_issue_count
          end
        end;
        (* Period/ellipsis check *)
        if a = 46 && i + 2 <= n1 then begin
          let a1 = Array1.unsafe_get ascii_u8 (i + 1) in
          let a2 = Array1.unsafe_get ascii_u8 (i + 2) in
          if a1 = 46 && a2 = 46 then begin
            Array1.unsafe_set global_issue_buffer !global_issue_count i;
            incr global_issue_count
          end
        end
      end
    end
  done;
  !global_issue_count

(* TRACK 2: Single-load version using ascii_interest *)
let[@inline] validate_1load ascii_interest n =
  global_issue_count := 0;
  let n1 = n - 1 in
  
  for i = 0 to n1 do
    (* Single load - ascii_interest encodes both kind and value *)
    let b = Array1.unsafe_get ascii_interest i in
    if b <> 0 then begin (* 0 means "not interesting" *)
      (* Quote *)
      if b = 34 then begin
        Array1.unsafe_set global_issue_buffer !global_issue_count i;
        incr global_issue_count
      end;
      (* Hyphen -> check for double *)
      if b = 45 && i < n1 then begin
        let b1 = Array1.unsafe_get ascii_interest (i + 1) in
        if b1 = 45 then begin
          Array1.unsafe_set global_issue_buffer !global_issue_count i;
          incr global_issue_count
        end
      end;
      (* Period -> check for triple (ellipsis) *)
      if b = 46 && i + 2 <= n1 then begin
        let b1 = Array1.unsafe_get ascii_interest (i + 1) in
        let b2 = Array1.unsafe_get ascii_interest (i + 2) in
        if b1 = 46 && b2 = 46 then begin
          Array1.unsafe_set global_issue_buffer !global_issue_count i;
          incr global_issue_count
        end
      end;
      (* Tab character *)
      if b = 9 then begin
        Array1.unsafe_set global_issue_buffer !global_issue_count i;
        incr global_issue_count
      end
    end
  done;
  !global_issue_count

(* Convert existing tokens to unboxed SoA *)
let tokens_to_unboxed_soa tokens =
  let n = List.length tokens in
  let soa = SoA_Unboxed.create ~capacity:n in
  
  List.iteri (fun i tok ->
    let open Validator_core_fixed in
    let (kind, ascii_val) = match tok.token with
      | TChar (uc, Other) -> 
          let code = Uchar.to_int uc in
          if code < 128 then (kind_other, code)
          else (kind_other, 255)  (* Non-ASCII marked as 255 *)
      | TChar (uc, Space) -> 
          let code = Uchar.to_int uc in
          if code < 128 then (kind_space, code) else (kind_space, 255)
      | TChar (uc, Letter) ->
          let code = Uchar.to_int uc in
          if code < 128 then (kind_letter, code) else (kind_letter, 255)
      | TChar (uc, BeginGroup) -> (kind_begin_group, 123)
      | TChar (uc, EndGroup) -> (kind_end_group, 125)
      | _ -> (0, 0)
    in
    Array1.unsafe_set soa.kind_u8 i kind;
    
    (* ascii_interest: 0 for uninteresting, ASCII code for OTHER/SPACE kinds *)
    let interest = 
      if kind = kind_other && ascii_val < 128 then ascii_val
      else if kind = kind_space && ascii_val < 128 then ascii_val
      else 0
    in
    Array1.unsafe_set soa.ascii_interest i interest
  ) tokens;
  
  { soa with len = n }

(* Benchmark harness *)
let bench_unboxed tokens_list =
  let soa = tokens_to_unboxed_soa tokens_list in
  let n = soa.len in
  
  (* Warm up *)
  for _ = 1 to 10 do
    ignore (validate_1load soa.ascii_interest n)
  done;
  
  (* Benchmark *)
  let times = ref [] in
  for _ = 1 to 100 do
    let t0 = Unix.gettimeofday () in
    let issues = validate_1load soa.ascii_interest n in
    let t1 = Unix.gettimeofday () in
    times := (t1 -. t0) *. 1000.0 :: !times
  done;
  
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted 98 in
  let p95 = List.nth sorted 94 in
  let p50 = List.nth sorted 49 in
  let mean = (List.fold_left (+.) 0.0 sorted) /. 100.0 in
  
  Printf.printf "Unboxed single-load validator (%d tokens):\n" n;
  Printf.printf "  Mean: %.3fms\n" mean;
  Printf.printf "  P50:  %.3fms\n" p50;
  Printf.printf "  P95:  %.3fms\n" p95;
  Printf.printf "  P99:  %.3fms\n" p99;
  Printf.printf "  Issues found: %d\n" !global_issue_count;
  
  let scale = 276000.0 /. float n in
  Printf.printf "\nEstimated for 276K tokens:\n";
  Printf.printf "  P99: %.3fms\n" (p99 *. scale);
  
  if p99 *. scale < 2.0 then
    Printf.printf "✅ SUCCESS: Major improvement from unboxing!\n"
  else
    Printf.printf "⚠️ Next step: Fuse into L0 or use C microkernel\n";
  
  p99 *. scale