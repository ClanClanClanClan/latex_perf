(* ══════════════════════════════════════════════════════════════════════
   Suffix_array — O(n log n) construction, O(log n) search (spec W46)

   Used for dirty-region detection: given old and new source, find the minimal
   changed regions using suffix array binary search.
   ══════════════════════════════════════════════════════════════════════ *)

type t = { text : string; sa : int array (* sorted suffix indices *) }

(* ── Construction (O(n log² n) simple approach) ─────────────── *)

let build (text : string) : t =
  let n = String.length text in
  if n = 0 then { text; sa = [||] }
  else
    let sa = Array.init n (fun i -> i) in
    (* Sort suffixes lexicographically *)
    Array.sort
      (fun i j ->
        let li = n - i and lj = n - j in
        let len = min li lj in
        let rec cmp k =
          if k >= len then compare li lj
          else
            let ci = Char.code (String.unsafe_get text (i + k)) in
            let cj = Char.code (String.unsafe_get text (j + k)) in
            if ci <> cj then compare ci cj else cmp (k + 1)
        in
        cmp 0)
      sa;
    { text; sa }

(* ── Binary search: O(log n) ────────────────────────────────── *)

let search (arr : t) (pattern : string) : int list =
  let n = Array.length arr.sa in
  let plen = String.length pattern in
  if n = 0 || plen = 0 then []
  else
    (* Binary search for first occurrence *)
    let compare_at idx =
      let suffix_start = arr.sa.(idx) in
      let suffix_len = String.length arr.text - suffix_start in
      let cmp_len = min plen suffix_len in
      let rec cmp k =
        if k >= cmp_len then if plen <= suffix_len then 0 else 1
        else
          let cp = Char.code (String.unsafe_get pattern k) in
          let cs = Char.code (String.unsafe_get arr.text (suffix_start + k)) in
          if cp < cs then -1 else if cp > cs then 1 else cmp (k + 1)
      in
      cmp 0
    in
    (* Find lower bound *)
    let lo = ref 0 and hi = ref (n - 1) in
    while !lo < !hi do
      let mid = !lo + ((!hi - !lo) / 2) in
      if compare_at mid < 0 then lo := mid + 1 else hi := mid
    done;
    let first = !lo in
    if first >= n || compare_at first <> 0 then []
    else
      (* Find upper bound *)
      let hi = ref (n - 1) in
      while !lo < !hi do
        let mid = !lo + ((!hi - !lo + 1) / 2) in
        if compare_at mid <= 0 then lo := mid else hi := mid - 1
      done;
      let last = !lo in
      let results = ref [] in
      for i = first to last do
        results := arr.sa.(i) :: !results
      done;
      List.rev !results

(* ── Dirty region detection ─────────────────────────────────── *)

type dirty_region = { start_pos : int; end_pos : int }

let find_dirty_regions (old_text : string) (new_text : string) :
    dirty_region list =
  let old_len = String.length old_text in
  let new_len = String.length new_text in
  let min_len = min old_len new_len in
  (* Find first difference *)
  let start = ref 0 in
  while !start < min_len && old_text.[!start] = new_text.[!start] do
    incr start
  done;
  if !start = old_len && old_len = new_len then [] (* identical *)
  else
    (* Find last difference from end *)
    let old_end = ref (old_len - 1) in
    let new_end = ref (new_len - 1) in
    while
      !old_end > !start
      && !new_end > !start
      && old_text.[!old_end] = new_text.[!new_end]
    do
      decr old_end;
      decr new_end
    done;
    [ { start_pos = !start; end_pos = !new_end + 1 } ]
