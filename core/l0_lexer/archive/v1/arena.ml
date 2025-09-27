open Bigarray

type token_soa = {
  kinds : (int, int8_unsigned_elt, c_layout) Array1.t;
  starts : (int32, int32_elt, c_layout) Array1.t;
  ends : (int32, int32_elt, c_layout) Array1.t;
  mutable count : int;
}

let create_token_soa cap =
  {
    kinds = Array1.create int8_unsigned c_layout cap;
    starts = Array1.create int32 c_layout cap;
    ends = Array1.create int32 c_layout cap;
    count = 0;
  }

let add_token soa kind start_pos end_pos =
  if soa.count < Array1.dim soa.kinds then (
    Array1.unsafe_set soa.kinds soa.count kind;
    Array1.unsafe_set soa.starts soa.count (Int32.of_int start_pos);
    Array1.unsafe_set soa.ends soa.count (Int32.of_int end_pos);
    soa.count <- soa.count + 1)

let clear_soa soa = soa.count <- 0

type arena = {
  primary : token_soa;
  secondary : token_soa;
  mutable active : [ `Primary | `Secondary ];
}

let create_arena () =
  let cap = Config.arenas_tokens_cap in
  {
    primary = create_token_soa cap;
    secondary = create_token_soa cap;
    active = `Primary;
  }

let get_active_soa arena =
  match arena.active with
  | `Primary -> arena.primary
  | `Secondary -> arena.secondary

let get_inactive_soa arena =
  match arena.active with
  | `Primary -> arena.secondary
  | `Secondary -> arena.primary

let swap_arenas arena =
  arena.active <-
    (match arena.active with `Primary -> `Secondary | `Secondary -> `Primary)
