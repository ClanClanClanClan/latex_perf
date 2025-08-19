(* PRODUCTION VALIDATOR TYPES - Core types and interfaces *)

open Bigarray

(* 8-bit interest mask type for maximum performance *)
type interest_mask = (int, int8_unsigned_elt, c_layout) Array1.t

(* Issue storage - off-heap for zero GC impact *)
type issue_buffer = {
  positions: (int32, int32_elt, c_layout) Array1.t;  (* Token indices *)
  rule_codes: (int, int16_unsigned_elt, c_layout) Array1.t;  (* Rule IDs *)
  mutable count: int;
}

(* Rule codes - following specs/rules_v3.yaml *)
module Rules = struct
  let quote = 1         (* TYPO-001: ASCII quotes *)
  let endash = 2        (* TYPO-002: Double hyphen → en-dash *)
  let emdash = 3        (* TYPO-003: Triple hyphen → em-dash *)
  let ellipsis = 5      (* TYPO-005: Triple period → ellipsis *)
  let tab = 6           (* STYLE-001: Tab characters *)
  let unmatched_close = 7   (* DELIM-001: Unmatched closing brace *)
  let unclosed_open = 8     (* DELIM-002: Unclosed opening brace *)
end

(* Interest mask bit layout for L0 integration *)
module InterestBits = struct
  let quote = 1      (* " *)
  let hyphen = 2     (* - *)
  let period = 4     (* . *)
  let tab = 8        (* \t *)
  let left_brace = 16    (* { *)
  let right_brace = 32   (* } *)
end

(* Validator state for stateful processing *)
type validator_state = {
  issues: issue_buffer;
  
  (* Run tracking for sequences *)
  mutable hyphen_start: int;
  mutable hyphen_count: int;
  mutable period_start: int;
  mutable period_count: int;
  
  (* Brace balance tracking *)
  brace_stack: int array;
  mutable brace_sp: int;
}

(* Performance statistics *)
type perf_stats = {
  validation_time_ms: float;
  tokens_processed: int;
  issues_found: int;
  early_exit_rate: float;  (* Percentage of positions with mask=0 *)
}

(* Create optimized issue buffer *)
let create_issue_buffer capacity = {
  positions = Array1.create int32 c_layout capacity;
  rule_codes = Array1.create int16_unsigned c_layout capacity;
  count = 0;
}

(* Create validator state *)
let create_validator_state capacity = {
  issues = create_issue_buffer capacity;
  hyphen_start = -1;
  hyphen_count = 0;
  period_start = -1;
  period_count = 0;
  brace_stack = Array.make 65536 0;
  brace_sp = 0;
}

(* Interest mask lookup table for L0 integration *)
let create_interest_lookup_table () =
  let lut = Bytes.create 256 in
  Bytes.fill lut 0 256 '\000';
  
  (* Set bits for characters of interest *)
  Bytes.set lut 34 (Char.chr InterestBits.quote);      (* " *)
  Bytes.set lut 45 (Char.chr InterestBits.hyphen);     (* - *)
  Bytes.set lut 46 (Char.chr InterestBits.period);     (* . *)
  Bytes.set lut 9  (Char.chr InterestBits.tab);        (* \t *)
  Bytes.set lut 123 (Char.chr InterestBits.left_brace);  (* { *)
  Bytes.set lut 125 (Char.chr InterestBits.right_brace); (* } *)
  
  lut

(* Global lookup table - initialized once *)
let interest_lookup_table = create_interest_lookup_table ()

(* Compute interest mask for L0 integration *)
let[@inline] compute_interest_mask ~is_ascii_char ~ascii_code =
  if is_ascii_char && ascii_code < 128 then
    Char.code (Bytes.unsafe_get interest_lookup_table ascii_code)
  else
    0