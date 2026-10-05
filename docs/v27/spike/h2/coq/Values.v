(* PS values, storage and C conversions (spike H.2, ADR-015).

   Every choice below is C's (C11 as gcc implements it on the two targets), restricted
   to DEFINED behaviour. Where C is undefined, or implementation-defined in a way the
   two targets may answer differently, or not modelled yet, the operation is Stuck:
   the document is then outside the tier (H.1 report 5.4, the proposed PS rule). *)

From Coq Require Import ZArith List Bool String PArray Uint63 Sint63 Floats.
Local Open Scope string_scope.
From PS Require Import Syntax.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------- cells and values *)

(* a location: block, cell offset, optional slice (byte offset, width, kind) of a word *)
Record loc : Set := mkloc { lb : Z; lo : Z; lsl : option (Z * Z * slk) }.

Inductive cell : Type :=
| KUndef                              (* never written (malloc'd or automatic storage) *)
| KInt (z : Z)                        (* an integer, already converted to the cell's C type *)
| KDbl (f : float)
| KPtr (b o : Z) | KNull
| KWord (bits mask : Z)               (* a union word: little-endian bytes; mask: defined bytes *)
| KFile (h : Z)                       (* a FILE* or gzFile, owned by the boundary *)
| KLoc (l : loc).                     (* a var parameter's target *)

Inductive val : Type :=
| VI (t : ty) (z : Z)                 (* t is TI32 or TI64 *)
| VF (f : float)
| VP (b o : Z) | VN
| VW (nb bits mask : Z)               (* a word value of nb bytes *)
| VFile (h : Z).

Definition val_name (v : val) : string :=
  match v with VI TI64 _ => "long" | VI _ _ => "int" | VF _ => "double" | VP _ _ => "pointer" | VN => "NULL"
          | VW _ _ _ => "word" | VFile _ => "file" end.

(* ---------------------------------------------------------------- stuck reasons *)
Inductive stuck : Type :=
| StOverflow | StDivZero | StConv (what : string) | StUninit | StBounds (what : string)
| StType (what : string) | StExternal (name : string) | StFuel | StGoto (n : Z)
| StCharSign | StNaNBits | StOther (what : string)
| StIn (proc : Z) (s : stuck).        (* diagnostic: the procedure the stuck step was in *)

Definition ct_name (c : ct) : string :=
  match c with CU8 => "u8" | CS8 => "s8" | CS16 => "s16" | CU16 => "u16" | CI32 => "i32" | CI64 => "i64"
          | CC8 => "c8" | CF64 => "f64" | CPTR => "ptr" | CFILE => "file" | CW8 => "w8" | CW4 => "w4"
          | CAGG => "agg" end.

(* ---------------------------------------------------------------- integer ranges *)
Definition two32 := 4294967296.
Definition in_range (lo hi z : Z) : bool := (lo <=? z) && (z <=? hi).
Definition in_i32 := in_range (-2147483648) 2147483647.
Definition in_i64 := in_range (-9223372036854775808) 9223372036854775807.
Definition fits (t : ty) (z : Z) : bool :=
  match t with TI64 => in_i64 z | _ => in_i32 z end.

(* ---------------------------------------------------------------- IEEE-754 binary64 *)
Definition fshift : Z := 2101.   (* FloatOps.shift: ldshiftexp f e = f * 2^(e - 2101) *)
Definition p52 : Z := 4503599627370496.

(* the double whose bit pattern is z (0 <= z < 2^64); NaN payloads are not kept *)
Definition float_of_bits (z : Z) : float :=
  let s := Z.testbit z 63 in
  let e := Z.land (Z.shiftr z 52) 2047 in
  let m := Z.land z (p52 - 1) in
  let a :=
    if e =? 2047 then (if m =? 0 then infinity else nan)
    else if e =? 0 then ldshiftexp (of_uint63 (Uint63.of_Z m)) (Uint63.of_Z (-1074 + fshift))
    else ldshiftexp (of_uint63 (Uint63.of_Z (p52 + m))) (Uint63.of_Z (e - 1075 + fshift)) in
  if s then PrimFloat.opp a else a.

(* the bit pattern of f; a NaN's pattern is architecture-defined (sign and payload), so None *)
Definition bits_of_float (f : float) : option Z :=
  match classify f with
  | PZero => Some 0 | NZero => Some (Z.shiftl 1 63)
  | PInf => Some (Z.shiftl 2047 52) | NInf => Some (Z.shiftl 1 63 + Z.shiftl 2047 52)
  | NaN => None
  | _ =>
    let neg := match classify f with NNormal | NSubn => true | _ => false end in
    let (fr, e) := frshiftexp (PrimFloat.abs f) in
    let m53 := Uint63.to_Z (normfr_mantissa fr) in        (* in [2^52, 2^53) *)
    let bexp := Uint63.to_Z e - fshift + 1022 in           (* biased exponent if normal *)
    let body :=
      if 0 <? bexp then Z.shiftl bexp 52 + (m53 - p52)
      else Z.shiftr m53 (1 - bexp) in                      (* subnormal: exact *)
    Some (if neg then Z.shiftl 1 63 + body else body)
  end.

(* C's conversion of a finite double to an integer: truncation toward zero *)
Definition float_trunc (f : float) : option Z :=
  match classify f with
  | PZero | NZero => Some 0
  | NaN | PInf | NInf => None
  | _ =>
    let neg := match classify f with NNormal | NSubn => true | _ => false end in
    let (fr, e) := frshiftexp (PrimFloat.abs f) in
    let m53 := Uint63.to_Z (normfr_mantissa fr) in
    let k := Uint63.to_Z e - fshift - 53 in
    let a := if 0 <=? k then Z.shiftl m53 k else Z.shiftr m53 (- k) in
    Some (if neg then - a else a)
  end.

(* C's conversion of an integer to double: exact below 2^53; beyond, not modelled *)
Definition float_of_int (z : Z) : option float :=
  if Z.abs z <=? 9007199254740992 then
    let a := of_uint63 (Uint63.of_Z (Z.abs z)) in
    Some (if z <? 0 then PrimFloat.opp a else a)
  else None.

(* ---------------------------------------------------------------- blocks and the heap *)
(* A block is a chunked array of cells (PArray's length is bounded by 2^22 - 1, and TeX's
   mem is larger). Chunks are fresh copies, so updates stay O(1) in linear use. *)
Definition chunk_bits : Z := 12.
Definition chunk : Z := 4096.

Record block : Type := mkblock { bsize : Z; bdata : array (array cell) }.

Definition empty_block : block := mkblock 0 (PArray.make 1 (PArray.make 1 KUndef)).

Fixpoint fill_chunks (n : nat) (i : Z) (d : cell) (a : array (array cell)) : array (array cell) :=
  match n with
  | O => a
  | S n' => fill_chunks n' (i + 1) d (PArray.set a (Uint63.of_Z i) (PArray.make (Uint63.of_Z chunk) d))
  end.

(* a block of at most one chunk is one array of exactly its size (frames, strings) *)
(* The chunk of a small block is stored with PArray.set, not as PArray.make's default: a
   persistent array keeps its default for ever, and a default that is the chunk's first
   version would keep, through the version chain, every write ever made to the block
   (spike H.3: every scalar global is such a block; the meaning dump exhausted memory) *)
Definition new_block (n : Z) (d : cell) : block :=
  if n <=? chunk then
    mkblock n (PArray.set (PArray.make 1 (PArray.make 1 KUndef)) 0%uint63
                          (PArray.make (Uint63.of_Z (Z.max 1 n)) d))
  else
  let nch := (n + chunk - 1) / chunk in
  mkblock n (fill_chunks (Z.to_nat nch) 0 d (PArray.make (Uint63.of_Z nch) (PArray.make 1 KUndef))).

Definition bget (b : block) (i : Z) : option cell :=
  if (0 <=? i) && (i <? bsize b) then
    Some (PArray.get (PArray.get (bdata b) (Uint63.of_Z (Z.shiftr i chunk_bits)))
                     (Uint63.of_Z (Z.land i (chunk - 1))))
  else None.

Definition bset (b : block) (i : Z) (c : cell) : option block :=
  if (0 <=? i) && (i <? bsize b) then
    let ci := Uint63.of_Z (Z.shiftr i chunk_bits) in
    let ch := PArray.get (bdata b) ci in
    Some (mkblock (bsize b) (PArray.set (bdata b) ci (PArray.set ch (Uint63.of_Z (Z.land i (chunk - 1))) c)))
  else None.

(* the heap: block ids [0, nglob) globals, then string literals, then malloc'd blocks
   (growing from hp), and procedure frames (a stack from frame_base) *)
Definition heap_cap : Z := 1048576.
Definition frame_base : Z := 524288.

Record io : Type := mkio {
  io_out : list (Z * list Z);            (* per file handle: bytes written, most recent first *)
  io_stdin : list Z;                     (* the bytes of stdin not yet read *)
  io_argv : list (list Z);               (* the command line after the program name *)
  io_char_signed : bool;                 (* plain char: signed (x86_64) or unsigned (aarch64) *)
  io_files : list (Z * list Z);          (* open input files: handle, remaining bytes *)
  io_next_handle : Z;
  io_fs : list (list Z * list Z);        (* the file-system snapshot: name, contents *)
  io_env : list (list Z * list Z);       (* the process environment, as getenv(3) sees it:
                                            name, value bytes (no parsing here; Boundary.v
                                            applies C's own parsing: STREQ, strtoull, atoi) *)
  io_kpse : list (list Z * list Z);      (* what kpse_var_value(name) returns in the pinned
                                            image for this run's environment (kpathsea looks at
                                            the environment first, then texmf.cnf, then expands
                                            the value): name, value bytes; absent = NULL *)
  io_kpsefind : list (Z * Z * list Z * list Z);
                                         (* kpse_find_file(name, format, must_exist) in the
                                            pinned image for this run: (format number,
                                            must_exist 0/1, name, result path; an empty path
                                            is NULL). A query not in the table is Stuck *)
  io_in : list (Z * list Z);             (* an open input stream: handle, the bytes not yet read *)
  io_gz : list (list Z * list Z);        (* for a file opened through zlib (gzdopen: the
                                            format file), the bytes gzread returns: path, the
                                            decompressed stream. Decompression is outside the
                                            model (TB-7): the driver is given the stream *)
  io_clock : list (Z * Z);               (* the gettimeofday(2) readings not yet consumed, in
                                            call order: (tv_sec, tv_usec). The real clock is a
                                            nondeterministic input, so it is an explicit part of
                                            the run's identity; none left = Stuck *)
  io_cstate : list (Z * Z)               (* C-internal variables of the boundary, by number:
                                            one-shot flags and the like (Boundary.v names them) *)
}.

(* functional updates of one field of io (positional mkio calls are error-prone) *)
Definition io_set_out (x : io) (o : list (Z * list Z)) : io :=
  mkio o (io_stdin x) (io_argv x) (io_char_signed x) (io_files x) (io_next_handle x) (io_fs x) (io_env x) (io_kpse x) (io_kpsefind x) (io_in x) (io_gz x) (io_clock x) (io_cstate x).
Definition io_set_stdin (x : io) (b : list Z) : io :=
  mkio (io_out x) b (io_argv x) (io_char_signed x) (io_files x) (io_next_handle x) (io_fs x) (io_env x) (io_kpse x) (io_kpsefind x) (io_in x) (io_gz x) (io_clock x) (io_cstate x).
Definition io_set_files (x : io) (fs : list (Z * list Z)) (nh : Z) : io :=
  mkio (io_out x) (io_stdin x) (io_argv x) (io_char_signed x) fs nh (io_fs x) (io_env x) (io_kpse x) (io_kpsefind x) (io_in x) (io_gz x) (io_clock x) (io_cstate x).
Definition io_set_in (x : io) (i : list (Z * list Z)) : io :=
  mkio (io_out x) (io_stdin x) (io_argv x) (io_char_signed x) (io_files x) (io_next_handle x) (io_fs x) (io_env x) (io_kpse x) (io_kpsefind x) i (io_gz x) (io_clock x) (io_cstate x).
Definition io_set_clock (x : io) (c : list (Z * Z)) : io :=
  mkio (io_out x) (io_stdin x) (io_argv x) (io_char_signed x) (io_files x) (io_next_handle x) (io_fs x) (io_env x) (io_kpse x) (io_kpsefind x) (io_in x) (io_gz x) c (io_cstate x).
Definition io_set_cstate (x : io) (c : list (Z * Z)) : io :=
  mkio (io_out x) (io_stdin x) (io_argv x) (io_char_signed x) (io_files x) (io_next_handle x) (io_fs x) (io_env x) (io_kpse x) (io_kpsefind x) (io_in x) (io_gz x) (io_clock x) c.

Record state : Type := mkst {
  heap : array block; hp : Z; fp : Z; fsp : Z; st_io : io }.

Definition hget (st : state) (b : Z) : block := PArray.get (heap st) (Uint63.of_Z b).
Definition hput (st : state) (b : Z) (blk : block) : state :=
  mkst (PArray.set (heap st) (Uint63.of_Z b) blk) (hp st) (fp st) (fsp st) (st_io st).
Definition set_io (st : state) (x : io) : state := mkst (heap st) (hp st) (fp st) (fsp st) x.

Definition cell_at (st : state) (b o : Z) : option cell := bget (hget st b) o.
Definition put_cell (st : state) (b o : Z) (c : cell) : option state :=
  match bset (hget st b) o c with Some blk => Some (hput st b blk) | None => None end.

(* ---------------------------------------------------------------- C conversions on store *)
Inductive conv_res : Type := COk (c : cell) | CStuck (s : stuck).

Definition store_conv (char_signed : bool) (c : ct) (v : val) : conv_res :=
  match c, v with
  | CU8, VI _ z => COk (KInt (Z.modulo z 256))                 (* to unsigned: modulo *)
  | CU16, VI _ z => COk (KInt (Z.modulo z 65536))
  | CS8, VI _ z => if in_range (-128) 127 z then COk (KInt z) else CStuck (StConv "to schar")
  | CS16, VI _ z => if in_range (-32768) 32767 z then COk (KInt z) else CStuck (StConv "to short")
  | CI32, VI _ z => if in_i32 z then COk (KInt z) else CStuck (StConv "to int")
  | CI64, VI _ z => if in_i64 z then COk (KInt z) else CStuck (StConv "to long")
  | CC8, VI _ z =>                                             (* plain char: kept as its byte *)
      if char_signed then (if in_range (-128) 127 z then COk (KInt (Z.modulo z 256)) else CStuck StCharSign)
      else COk (KInt (Z.modulo z 256))
  | CF64, VF f => COk (KDbl f)
  | CF64, VI _ z => match float_of_int z with Some f => COk (KDbl f) | None => CStuck (StConv "int to double") end
  (* C11 6.3.1.4: a double converted to an integer type is truncated toward zero; the
     behaviour is undefined when the truncated value is outside the type's range (and for
     NaN and infinities): Stuck. Plain char takes the architecture's range. *)
  | (CU8 | CU16 | CS8 | CS16 | CI32 | CI64 | CC8), VF f =>
    match float_trunc f with
    | None => CStuck (StConv "double to integer of NaN or inf")
    | Some z =>
      let ok := match c with
                | CU8 => in_range 0 255 z | CU16 => in_range 0 65535 z
                | CS8 => in_range (-128) 127 z | CS16 => in_range (-32768) 32767 z
                | CI32 => in_i32 z | CI64 => in_i64 z
                | _ => if char_signed then in_range (-128) 127 z else in_range 0 255 z end in
      (* plain char cells keep the byte (as the CC8 integer case above does) *)
      if ok then COk (KInt (match c with CC8 => Z.modulo z 256 | _ => z end))
      else CStuck (StConv "double to integer out of range")
    end
  | CPTR, VP b o => COk (KPtr b o)
  | CPTR, VN => COk KNull
  | CFILE, VFile h => COk (KFile h)
  | CFILE, VN => COk KNull
  | CW8, VW 8 bits mask => COk (KWord bits mask)
  | CW4, VW 4 bits mask => COk (KWord bits mask)
  | _, _ => CStuck (StType ("store of a " ++ val_name v ++ " into " ++ ct_name c))
  end.

(* read a whole cell at a location of C type c, promoting (t is the promoted type) *)
Inductive ld_res : Type := LdOk (v : val) | LdStuck (s : stuck).

Definition load_cell (char_signed : bool) (t : ty) (k : cell) : ld_res :=
  match t, k with
  | _, KUndef => LdStuck StUninit
  | TC8, KInt z => LdOk (VI TI32 (if char_signed && (128 <=? z) then z - 256 else z))
  | (TI32 | TI64), KInt z => LdOk (VI t z)
  | TF64, KDbl f => LdOk (VF f)
  | TPTR, KPtr b o => LdOk (VP b o)
  | TPTR, KNull => LdOk VN
  | TFILE, KFile h => LdOk (VFile h)
  | TFILE, KNull => LdOk VN
  | TW8, KWord bits mask => LdOk (VW 8 bits mask)
  | TW4, KWord bits mask => LdOk (VW 4 bits mask)
  | _, _ => LdStuck (StType "load")
  end.

(* a whole word cell read as a word; a never-written word is all-undefined bytes *)
Definition word_of (k : cell) : option (Z * Z) :=
  match k with KWord b m => Some (b, m) | KUndef => Some (0, 0) | _ => None end.

Definition bytes_mask (boff nb : Z) : Z := Z.shiftl (Z.ones (8 * nb)) (8 * boff).
Definition byte_flags (boff nb : Z) : Z := Z.shiftl (Z.ones nb) boff.

(* read a slice of a word *)
Definition load_slice (boff nb : Z) (k : slk) (bits mask : Z) : ld_res :=
  let f := Z.land (Z.shiftr bits (8 * boff)) (Z.ones (8 * nb)) in
  let fm := Z.land (Z.shiftr mask boff) (Z.ones nb) in
  match k with
  | SkW => LdOk (VW nb f fm)
  | _ =>
    if negb (fm =? Z.ones nb) then LdStuck StUninit
    else match k with
         | SkS => let v := if Z.testbit f (8 * nb - 1) then f - Z.shiftl 1 (8 * nb) else f in
                  LdOk (VI TI32 v)
         | SkU => LdOk (VI TI32 f)
         | SkF => LdOk (VF (float_of_bits f))
         | SkW => LdOk (VW nb f fm)
         end
  end.

(* encode a value into a slice's bytes: (field bits, field byte-mask) *)
Definition slice_bits (nb : Z) (k : slk) (v : val) : option (Z * Z) :=
  match k, v with
  | SkS, VI _ z =>
      if in_range (- Z.shiftl 1 (8 * nb - 1)) (Z.shiftl 1 (8 * nb - 1) - 1) z
      then Some (Z.modulo z (Z.shiftl 1 (8 * nb)), Z.ones nb) else None
  | SkU, VI _ z => Some (Z.modulo z (Z.shiftl 1 (8 * nb)), Z.ones nb)   (* unsigned: modulo *)
  | SkF, VF f => match bits_of_float f with Some b => Some (b, Z.ones nb) | None => None end
  | SkW, VW n b m => if n =? nb then Some (b, m) else None
  | _, _ => None
  end.

Definition store_slice (boff nb : Z) (bits mask fb fm : Z) : Z * Z :=
  let cb := Z.lxor (Z.ones 64) (bytes_mask boff nb) in
  let cm := Z.lxor (Z.ones 8) (byte_flags boff nb) in
  (Z.lor (Z.land bits cb) (Z.shiftl fb (8 * boff)),
   Z.lor (Z.land mask cm) (Z.shiftl fm boff)).

(* ---------------------------------------------------------------- arithmetic *)
Inductive ar_res : Type := AOk (v : val) | AStuck (s : stuck).

Definition int_of (v : val) : option Z := match v with VI _ z => Some z | _ => None end.

Definition arith (op : binop) (t : ty) (a b : val) : ar_res :=
  match t with
  | TF64 =>
    match a, b with
    | VF x, VF y =>
      AOk (VF (match op with OAdd => PrimFloat.add x y | OSub => PrimFloat.sub x y
                        | OMul => PrimFloat.mul x y | _ => PrimFloat.div x y end))
    | _, _ => AStuck (StType "double operands")
    end
  | TI32 | TI64 =>
    match a, b with
    | VI _ x, VI _ y =>
      let r := match op with
               | OAdd => Some (x + y) | OSub => Some (x - y) | OMul => Some (x * y)
               | ODiv => if y =? 0 then None else Some (Z.quot x y)
               | OMod => if y =? 0 then None else Some (Z.rem x y)
               | OFDiv => None end in
      match r with
      | None => AStuck (match op with OFDiv => StType "fdiv on integers" | _ => StDivZero end)
      | Some z =>
        (* the quotient overflows only for MIN / -1; C also makes MIN % -1 undefined *)
        if negb (fits t z) || ((match op with OMod => true | _ => false end) && negb (fits t (Z.quot x y)))
        then AStuck StOverflow else AOk (VI t z)
      end
    | _, _ => AStuck (StType "integer operands")
    end
  | _ => AStuck (StType "arith type")
  end.

Definition compare (op : cmpop) (t : ty) (a b : val) : option bool :=
  match a, b with
  | VI _ x, VI _ y =>
    Some (match op with CEq => x =? y | CNe => negb (x =? y) | CLt => x <? y
                   | CGt => y <? x | CLe => x <=? y | CGe => y <=? x end)
  | VF x, VF y =>
    Some (match op with CEq => PrimFloat.eqb x y | CNe => negb (PrimFloat.eqb x y)
                   | CLt => PrimFloat.ltb x y | CGt => PrimFloat.ltb y x
                   | CLe => PrimFloat.leb x y | CGe => PrimFloat.leb y x end)
  | _, _ => None
  end.

(* C's conversions between the arithmetic types of expressions *)
Definition convert (t : ty) (v : val) : ar_res :=
  match t, v with
  | (TI32 | TI64), VI _ z => if fits t z then AOk (VI t z) else AStuck (StConv "narrowing")
  | TF64, VI _ z => match float_of_int z with Some f => AOk (VF f) | None => AStuck (StConv "int to double") end
  | TF64, VF f => AOk (VF f)
  | (TI32 | TI64), VF f =>
    match float_trunc f with
    | Some z => if fits t z then AOk (VI t z) else AStuck (StConv "double to int out of range")
    | None => AStuck (StConv "double to int of NaN or inf")
    end
  | _, _ => AStuck (StType "convert")
  end.

Definition truthy (v : val) : option bool :=
  match v with VI _ z => Some (negb (z =? 0)) | VF f => Some (negb (PrimFloat.eqb f 0%float))
          | VP _ _ => Some true | VN => Some false | _ => None end.
