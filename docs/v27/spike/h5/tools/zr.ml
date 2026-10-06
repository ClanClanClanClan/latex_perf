(* PROFILING EXPERIMENT (spike H.5 stage 1): zarith's Z, outside the extracted modules that
   shadow the name Z (BinInt.Z) *)
let u63_to_z (i : Uint63.t) : Z.t = Z.of_int64 (Uint63.to_int64 i)
let s63_to_z (i : Uint63.t) : Z.t = Z.signed_extract (Z.of_int64 (Uint63.to_int64 i)) 0 63
let z_to_u63 (z : Z.t) : Uint63.t = Uint63.of_int64 (Z.to_int64 (Z.extract z 0 63))
let eq = Z.equal
(* T2 (spike H.5 stage 1 experiment): the Coq Z functions that ExtrOcamlZBigInt does not
   realize, which the extracted program then computes bit by bit with a division per bit *)
let land_ = Z.logand
let lor_ = Z.logor
let lxor_ = Z.logxor
(* Coq: Z.testbit a n = false for n < 0; zarith's testbit takes an OCaml int *)
let testbit a n = if Z.sign n < 0 then false else if Z.fits_int n then Z.testbit a (Z.to_int n) else Z.sign a < 0
(* Coq: Z.quotrem a 0 = (0, a); otherwise truncated division, as zarith's div_rem *)
let quotrem a b = if Z.sign b = 0 then (Z.zero, a) else Z.div_rem a b
let of_nat (n : int) = Z.of_int n
let eqb (a : bool) b = a = b
let eqp (a, b) (c, d) = Z.equal a c && Z.equal b d
let check = Sys.getenv_opt "PS_T1CHECK" <> None
let fail what = prerr_endline ("T1CHECK mismatch in " ^ what); exit 5
