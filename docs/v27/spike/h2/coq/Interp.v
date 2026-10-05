(* PS as a fuelled interpreter (spike H.2, ADR-015).

   One big-step machine for the IR of Syntax.v. It is parameterised by the program
   (the procedure table, the string-literal base) and by the C boundary model `ext`,
   which may call back into the program (`loadpoolstrings` calls `makestring`).
   Fuel decreases at every node, so every run ends: in a result, a halt (the C exit
   status), or Stuck (outside the tier), fuel exhaustion included.

   Choices C leaves open and PS fixes, all recorded in the H.2 report:
   - operands, arguments and the two sides of an assignment are evaluated left to right,
     the target of an assignment first; C leaves this unspecified, so the translator must
     show each such site order-independent (open at checkpoint 2);
   - && and || short-circuit (C's rule).  *)

From Coq Require Import ZArith List Bool String PArray Uint63 Sint63 Floats.
From PS Require Import Syntax Values.
Import ListNotations.
Local Open Scope Z_scope.

Inductive eres : Type :=
| EOk (v : val) (st : state) | EHalt (code : Z) (st : state) | EStk (s : stuck) (st : state).
Inductive lres : Type :=
| LOk (l : loc) (st : state) | LHalt (code : Z) (st : state) | LStk (s : stuck) (st : state).
Inductive sres : Type :=
| SNorm (st : state) | SGo (n : Z) (st : state) | SRet (st : state)
| SHalt (code : Z) (st : state) | SStk (s : stuck) (st : state).
(* an actual parameter as it lands in the callee's frame *)
Inductive bres : Type :=
| BOk (cells : list cell) (st : state) | BHalt (code : Z) (st : state) | BStk (s : stuck) (st : state).
(* an external's argument *)
Inductive xarg : Type := XLoc (l : loc) (c : ct) (n : Z) | XVal (v : val) | XType (tid : Z).
Inductive xres : Type :=
| XOk (xs : list xarg) (st : state) | XHalt (code : Z) (st : state) | XStk (s : stuck) (st : state).

(* ---------------------------------------------------------------- memory access *)
Definition read_loc (st : state) (t : ty) (l : loc) : ld_res :=
  match cell_at st (lb l) (lo l) with
  | None => LdStuck (StBounds "read")
  | Some k =>
    match lsl l with
    | None => load_cell (io_char_signed (st_io st)) t k
    | Some (boff, nb, sk) =>
      match word_of k with
      | Some (bits, mask) => load_slice boff nb sk bits mask
      | None => LdStuck (StType "slice of a non-word")
      end
    end
  end.

Inductive wr_res : Type := WOk (st : state) | WStk (s : stuck).

Definition write_loc (st : state) (c : ct) (l : loc) (v : val) : wr_res :=
  match lsl l with
  | None =>
    match store_conv (io_char_signed (st_io st)) c v with
    | COk k => match put_cell st (lb l) (lo l) k with Some st' => WOk st' | None => WStk (StBounds "write") end
    | CStuck s => WStk s
    end
  | Some (boff, nb, sk) =>
    match cell_at st (lb l) (lo l) with
    | None => WStk (StBounds "write")
    | Some k =>
      match word_of k, slice_bits nb sk v with
      | Some (bits, mask), Some (fb, fm) =>
        let (b', m') := store_slice boff nb bits mask fb fm in
        match put_cell st (lb l) (lo l) (KWord b' m') with Some st' => WOk st' | None => WStk (StBounds "write") end
      | None, _ => WStk (StType "slice of a non-word")
      | _, None => WStk (StConv "slice")
      end
    end
  end.

Fixpoint copy_cells (n : nat) (sb so db dofs : Z) (st : state) : option state :=
  match n with
  | O => Some st
  | S n' =>
    match cell_at st sb so with
    | None => None
    | Some k => match put_cell st db dofs k with
                | Some st' => copy_cells n' sb (so + 1) db (dofs + 1) st'
                | None => None end
    end
  end.

Fixpoint read_cells (n : nat) (b o : Z) (st : state) : option (list cell) :=
  match n with
  | O => Some []
  | S n' => match cell_at st b o, read_cells n' b (o + 1) st with
            | Some k, Some ks => Some (k :: ks) | _, _ => None end
  end.

Fixpoint put_cells (ks : list cell) (b o : Z) (st : state) : option state :=
  match ks with
  | [] => Some st
  | k :: ks' => match put_cell st b o k with Some st' => put_cells ks' b (o + 1) st' | None => None end
  end.

(* ---------------------------------------------------------------- output *)
Fixpoint out_append (h : Z) (bytes : list Z) (outs : list (Z * list Z)) : list (Z * list Z) :=
  match outs with
  | [] => [(h, rev_append bytes [])]
  | (h', bs) :: rest => if h =? h' then (h', rev_append bytes bs) :: rest else (h', bs) :: out_append h bytes rest
  end.

Definition emit (h : Z) (bytes : list Z) (st : state) : state :=
  let x := st_io st in
  set_io st (io_set_out x (out_append h bytes (io_out x))).

Fixpoint digits_rev (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S f => if n <? 10 then [48 + n] else (48 + Z.rem n 10) :: digits_rev f (Z.quot n 10)
  end.
(* printf's %ld *)
Definition decimal (z : Z) : list Z :=
  let d := rev (digits_rev 25 (Z.abs z)) in if z <? 0 then 45 :: d else d.

(* the bytes of the NUL-terminated C string at (b, o) *)
Fixpoint cstring (fuel : nat) (b o : Z) (st : state) : option (list Z) :=
  match fuel with
  | O => None
  | S f => match cell_at st b o with
           | Some (KInt 0) => Some []
           | Some (KInt c) => match cstring f b (o + 1) st with Some r => Some (Z.modulo c 256 :: r) | None => None end
           | _ => None
           end
  end.

(* ---------------------------------------------------------------- goto continuations *)
Fixpoint has_label (n : Z) (s : stmt) : bool :=
  match s with
  | SLabel m => n =? zi m
  | SSeq ss => existsb (has_label n) ss
  | SIf _ a b => has_label n a || has_label n b
  | SWhile _ b => has_label n b
  | SRepeat b _ => has_label n b
  | SFor _ _ _ _ _ b => has_label n b
  | SCase _ arms d => existsb (fun a => has_label n (snd a)) arms ||
                      match d with Some x => has_label n x | None => false end
  | _ => false
  end.

(* the statement that continues execution of s from label n inside it (C goto semantics
   for jumps into an if branch, a case arm, a loop body or a sequence) *)
Fixpoint resume (n : Z) (s : stmt) : option stmt :=
  match s with
  | SLabel m => if n =? zi m then Some SSkip else None
  | SSeq ss =>
    (fix go (l : list stmt) : option stmt :=
       match l with
       | [] => None
       | x :: rest => if has_label n x then
                        match resume n x with Some x' => Some (SSeq (x' :: rest)) | None => None end
                      else go rest
       end) ss
  | SIf _ a b => if has_label n a then resume n a else resume n b
  | SWhile c b => match resume n b with Some b' => Some (SSeq [b'; SWhile c b]) | None => None end
  | SRepeat b c => match resume n b with
                   | Some b' => Some (SSeq [b'; SIf c SSkip (SRepeat b c)]) | None => None end
  | SCase _ arms d =>
    (fix go (l : list (list int * stmt)) : option stmt :=
       match l with
       | [] => match d with Some x => resume n x | None => None end
       | a :: rest => if has_label n (snd a) then resume n (snd a) else go rest
       end) arms
  | _ => None   (* a for body: web2c's bound lives in a hidden temporary *)
  end.

(* ---------------------------------------------------------------- the interpreter *)
Section Interp.
Variable procs : array proc.
Variable strings_base : Z.
(* the C boundary: externals by number, with a callback into the program *)
Variable ext : (Z -> list cell -> state -> eres) -> Z -> list xarg -> state -> eres.

Definition truth_or (v : val) (st : state) (k : bool -> eres) : eres :=
  match truthy v with Some b => k b | None => EStk (StType "condition") st end.

Fixpoint evale (fuel : nat) (e : expr) (st : state) {struct fuel} : eres :=
  match fuel with
  | O => EStk StFuel st
  | S f =>
  match e with
  | EInt t z => EOk (VI t (zi z)) st
  | EDbl bits => EOk (VF (float_of_bits bits)) st
  | EStr sid => EOk (VP (strings_base + zi sid) 0) st
  | ENull => EOk VN st
  | ELoad t l =>
    match evall f l st with
    | LOk lc st1 => match read_loc st1 t lc with LdOk v => EOk v st1 | LdStuck s => EStk s st1 end
    | LHalt c st1 => EHalt c st1 | LStk s st1 => EStk s st1
    end
  | ENeg t a =>
    match evale f a st with
    | EOk (VI _ z) st1 => if fits t (- z) then EOk (VI t (- z)) st1 else EStk StOverflow st1
    | EOk (VF x) st1 => EOk (VF (PrimFloat.opp x)) st1
    | EOk _ st1 => EStk (StType "negation") st1
    | r => r
    end
  | EBin op t a b =>
    match evale f a st with
    | EOk va st1 =>
      match evale f b st1 with
      | EOk vb st2 => match arith op t va vb with AOk v => EOk v st2 | AStuck s => EStk s st2 end
      | r => r
      end
    | r => r
    end
  | ECmp op t a b =>
    match evale f a st with
    | EOk va st1 =>
      match evale f b st1 with
      | EOk vb st2 => match compare op t va vb with
                      | Some r => EOk (VI TI32 (if r then 1 else 0)) st2
                      | None => EStk (StType "comparison") st2 end
      | r => r
      end
    | r => r
    end
  | EPCmp eq a b =>
    match evale f a st with
    | EOk va st1 =>
      match evale f b st1 with
      | EOk vb st2 =>
        let same := match va, vb with
                    | VP b1 o1, VP b2 o2 => Some ((b1 =? b2) && (o1 =? o2))
                    | VN, VN => Some true | VP _ _, VN => Some false | VN, VP _ _ => Some false
                    | VFile h1, VFile h2 => Some (h1 =? h2)
                    | VFile _, VN => Some false | VN, VFile _ => Some false
                    | _, _ => None end in
        match same with
        | Some r => EOk (VI TI32 (if Bool.eqb r eq then 1 else 0)) st2
        | None => EStk (StType "pointer comparison") st2
        end
      | r => r
      end
    | r => r
    end
  | EAnd a b =>
    match evale f a st with
    | EOk va st1 => truth_or va st1 (fun x => if x then
                      match evale f b st1 with
                      | EOk vb st2 => truth_or vb st2 (fun y => EOk (VI TI32 (if y then 1 else 0)) st2)
                      | r => r end
                    else EOk (VI TI32 0) st1)
    | r => r
    end
  | EOr a b =>
    match evale f a st with
    | EOk va st1 => truth_or va st1 (fun x => if x then EOk (VI TI32 1) st1 else
                      match evale f b st1 with
                      | EOk vb st2 => truth_or vb st2 (fun y => EOk (VI TI32 (if y then 1 else 0)) st2)
                      | r => r end)
    | r => r
    end
  | ENot a =>
    match evale f a st with
    | EOk va st1 => truth_or va st1 (fun x => EOk (VI TI32 (if x then 0 else 1)) st1)
    | r => r
    end
  | EConv t a =>
    match evale f a st with
    | EOk v st1 => match convert t v with AOk v' => EOk v' st1 | AStuck s => EStk s st1 end
    | r => r
    end
  | ECall p args =>
    match evalargs f (p_params (PArray.get procs p)) args st with
    | BOk cells st1 => callp f (zi p) cells st1
    | BHalt c st1 => EHalt c st1 | BStk s st1 => EStk s st1
    end
  | EExt x args =>
    match evalx f args st with
    | XOk xs st1 => ext (fun p cs st' => callp f p cs st') (zi x) xs st1
    | XHalt c st1 => EHalt c st1 | XStk s st1 => EStk s st1
    end
  | EAddr l =>
    match evall f l st with
    | LOk lc st1 => match lsl lc with None => EOk (VP (lb lc) (lo lc)) st1
                                    | Some _ => EStk (StType "address of a slice") st1 end
    | LHalt c st1 => EHalt c st1 | LStk s st1 => EStk s st1
    end
  | EPAdd p esz neg i =>
    match evale f p st with
    | EOk (VP b o) st1 =>
      match evale f i st1 with
      | EOk (VI _ z) st2 =>
        (* ISO C makes a pointer outside [0, size] of its object undefined, and web2c's
           idiom `hash = yhash - hashoffset` forms one on every run. PS follows the
           binary: plain address arithmetic, bounds checked at every access instead.
           That gcc compiled each of these sites as plain address arithmetic is a claim
           about the binary, to be checked site by site (H.2 report, open items). *)
        EOk (VP b (if neg then o - z * zi esz else o + z * zi esz)) st2
      | EOk _ st2 => EStk (StType "pointer offset") st2
      | r => r
      end
    | EOk _ st1 => EStk (StType "pointer arithmetic on a non-pointer") st1
    | r => r
    end
  | EAbs a =>
    match evale f a st with
    | EOk (VI t z) st1 => if fits TI32 (Z.abs z) then EOk (VI TI32 (Z.abs z)) st1 else EStk StOverflow st1
    | EOk _ st1 => EStk (StType "abs") st1
    | r => r
    end
  | EOdd t a =>
    match evale f a st with
    | EOk (VI _ z) st1 => EOk (VI t (Z.land z 1)) st1
    | EOk _ st1 => EStk (StType "odd") st1
    | r => r
    end
  | EUnseq _ => EStk (StOther "unspecified evaluation order") st
  | EAlloc esz c n =>
    match evale f n st with
    | EOk (VI _ z) st1 =>
      (* xmallocarray(type, n) = xmalloc((n + 1) * sizeof(type)); n + 1 is an int sum *)
      if negb (fits TI32 (z + 1)) || (z + 1 <=? 0) then EStk (StConv "allocation size") st1
      else if heap_cap <=? hp st1 + 1 then EStk (StOther "heap blocks exhausted") st1
      else let b := hp st1 in
           let st2 := hput (mkst (heap st1) (b + 1) (fp st1) (fsp st1) (st_io st1)) b
                            (new_block ((z + 1) * zi esz) KUndef) in
           EOk (VP b 0) st2
    | EOk _ st1 => EStk (StType "allocation size") st1
    | r => r
    end
  | ERealloc esz c p n =>
    match evale f p st with
    | EOk (VP ob 0) st1 =>
      match evale f n st1 with
      | EOk (VI _ z) st2 =>
        if negb (fits TI32 (z + 1)) || (z + 1 <=? 0) then EStk (StConv "allocation size") st2
        else let b := hp st2 in
             let size := (z + 1) * zi esz in
             let osize := bsize (hget st2 ob) in   (* read before st2's heap is superseded *)
             let st3 := hput (mkst (heap st2) (b + 1) (fp st2) (fsp st2) (st_io st2)) b (new_block size KUndef) in
             match copy_cells (Z.to_nat (Z.min size osize)) ob 0 b 0 st3 with
             | Some st4 => EOk (VP b 0) (hput st4 ob empty_block)
             | None => EStk (StBounds "realloc copy") st3
             end
      | EOk _ st2 => EStk (StType "allocation size") st2
      | r => r
      end
    | EOk _ st1 => EStk (StType "realloc of a non-block") st1
    | r => r
    end
  end
  end

with evall (fuel : nat) (l : lexp) (st : state) {struct fuel} : lres :=
  match fuel with
  | O => LStk StFuel st
  | S f =>
  match l with
  | LGlob g => LOk (mkloc (zi g) 0 None) st
  | LLoc k => LOk (mkloc (fp st) (zi k) None) st
  | LRef k => match cell_at st (fp st) (zi k) with
              | Some (KLoc lc) => LOk lc st
              | _ => LStk (StType "var parameter") st end
  | LIdx a i lo0 hi0 esz =>
    match evall f a st with
    | LOk lc st1 =>
      match evale f i st1 with
      | EOk (VI _ z) st2 =>
        if in_range (zi lo0) (zi hi0) z then LOk (mkloc (lb lc) (Values.lo lc + (z - zi lo0) * zi esz) None) st2
        else LStk (StBounds "array index") st2
      | EOk _ st2 => LStk (StType "index") st2
      | EHalt c st2 => LHalt c st2 | EStk s st2 => LStk s st2
      end
    | r => r
    end
  | LPIdx p i esz =>
    match evale f p st with
    | EOk (VP b o) st1 =>
      match evale f i st1 with
      | EOk (VI _ z) st2 => LOk (mkloc b (o + z * zi esz) None) st2
      | EOk _ st2 => LStk (StType "index") st2
      | EHalt c st2 => LHalt c st2 | EStk s st2 => LStk s st2
      end
    | EOk VN st1 => LStk (StBounds "NULL pointer") st1
    | EOk _ st1 => LStk (StType "indexing a non-pointer") st1
    | EHalt c st1 => LHalt c st1 | EStk s st1 => LStk s st1
    end
  | LFld a off =>
    match evall f a st with
    | LOk lc st1 => LOk (mkloc (lb lc) (Values.lo lc + zi off) None) st1
    | r => r
    end
  | LSl a boff nb k =>
    match evall f a st with
    | LOk lc st1 => LOk (mkloc (lb lc) (Values.lo lc) (Some (zi boff, zi nb, k))) st1
    | r => r
    end
  end
  end

(* actual parameters of a Pascal call, evaluated left to right into frame cells *)
with evalargs (fuel : nat) (ks : list pkind) (args : list arg) (st : state) {struct fuel} : bres :=
  match fuel with
  | O => BStk StFuel st
  | S f =>
  match ks, args with
  | [], [] => BOk [] st
  | PVal c :: ks', AVal _ e :: args' =>
    match evale f e st with
    | EOk v st1 =>
      match store_conv (io_char_signed (st_io st1)) c v with
      | COk k => match evalargs f ks' args' st1 with
                 | BOk cs st2 => BOk (k :: cs) st2 | r => r end
      | CStuck s => BStk s st1
      end
    | EHalt c st1 => BHalt c st1 | EStk s st1 => BStk s st1
    end
  | PRef :: ks', ARef l :: args' =>
    match evall f l st with
    | LOk lc st1 => match evalargs f ks' args' st1 with
                    | BOk cs st2 => BOk (KLoc lc :: cs) st2 | r => r end
    | LHalt c st1 => BHalt c st1 | LStk s st1 => BStk s st1
    end
  | PCopy n :: ks', ACopy l _ :: args' =>
    match evall f l st with
    | LOk lc st1 =>
      match read_cells (Z.to_nat (zi n)) (lb lc) (Values.lo lc) st1 with
      | Some cells => match evalargs f ks' args' st1 with
                      | BOk cs st2 => BOk (cells ++ cs) st2 | r => r end
      | None => BStk (StBounds "record argument") st1
      end
    | LHalt c st1 => BHalt c st1 | LStk s st1 => BStk s st1
    end
  | _, _ => BStk (StType "arguments") st
  end
  end

(* an external's arguments, left to right *)
with evalx (fuel : nat) (args : list arg) (st : state) {struct fuel} : xres :=
  match fuel with
  | O => XStk StFuel st
  | S f =>
  match args with
  | [] => XOk [] st
  | ALv l c n :: rest =>
    match evall f l st with
    | LOk lc st1 => match evalx f rest st1 with XOk xs st2 => XOk (XLoc lc c (zi n) :: xs) st2 | r => r end
    | LHalt c0 st1 => XHalt c0 st1 | LStk s st1 => XStk s st1
    end
  | AExp _ e :: rest =>
    match evale f e st with
    | EOk v st1 => match evalx f rest st1 with XOk xs st2 => XOk (XVal v :: xs) st2 | r => r end
    | EHalt c st1 => XHalt c st1 | EStk s st1 => XStk s st1
    end
  | AType tid :: rest => match evalx f rest st with XOk xs st1 => XOk (XType (zi tid) :: xs) st1 | r => r end
  | _ :: _ => XStk (StType "external argument") st
  end
  end

(* call procedure p with its parameter cells; a function returns its result cell's value *)
with callp (fuel : nat) (p : Z) (cells : list cell) (st : state) {struct fuel} : eres :=
  match fuel with
  | O => EStk StFuel st
  | S f =>
    let pr := PArray.get procs (Uint63.of_Z p) in
    let fb := fsp st in
    if heap_cap <=? fb + 1 then EStk (StOther "frame stack exhausted") st else
    let st1 := hput (mkst (heap st) (hp st) fb (fb + 1) (st_io st)) fb (new_block (Z.max 1 (zi (p_frame pr))) KUndef) in
    match put_cells cells fb 0 st1 with
    | None => EStk (StBounds "parameters") st1
    | Some st2 =>
      (* the caller's frame pointer, taken now: a closure that referred to the caller's
         state `st` would keep that state's persistent heap alive for the whole call, and
         with it a record of every write the callee makes (spike H.3: the meaning dump
         exhausted 24 GB of memory and swap) *)
      let caller_fp := fp st in
      let finish (st3 : state) : eres :=
        let res := match p_result pr with
                   | None => LdOk VN
                   | Some (off, c) =>
                     let t := match c with CI64 => TI64 | CF64 => TF64 | CPTR => TPTR | CW8 => TW8
                                        | CW4 => TW4 | CFILE => TFILE | CC8 => TC8 | _ => TI32 end in
                     read_loc st3 t (mkloc fb (zi off) None)
                   end in
        let st4 := hput (mkst (heap st3) (hp st3) caller_fp fb (st_io st3)) fb empty_block in
        match res with LdOk v => EOk v st4 | LdStuck s => EStk (StIn p s) st4 end in
      match exec f (p_body pr) st2 with
      | SNorm st3 => finish st3
      | SRet st3 => finish st3
      | SGo n st3 => EStk (StIn p (StGoto n)) st3
      | SHalt c st3 => EHalt c st3
      | SStk s st3 => EStk (StIn p s) st3
      end
    end
  end

with exec (fuel : nat) (s : stmt) (st : state) {struct fuel} : sres :=
  match fuel with
  | O => SStk StFuel st
  | S f =>
  match s with
  | SSkip => SNorm st
  | SLabel _ => SNorm st
  | SGoto n => SGo (zi n) st
  | SReturn => SRet st
  | SUnseq _ => SStk (StOther "unspecified evaluation order") st
  | SAsg l c e =>
    match evall f l st with
    | LOk lc st1 =>
      match evale f e st1 with
      | EOk v st2 => match write_loc st2 c lc v with WOk st3 => SNorm st3 | WStk s0 => SStk s0 st2 end
      | EHalt c0 st2 => SHalt c0 st2 | EStk s0 st2 => SStk s0 st2
      end
    | LHalt c0 st1 => SHalt c0 st1 | LStk s0 st1 => SStk s0 st1
    end
  | SCopy d src n =>
    match evall f d st with
    | LOk ld st1 =>
      match evall f src st1 with
      | LOk ls st2 => match copy_cells (Z.to_nat (zi n)) (lb ls) (Values.lo ls) (lb ld) (Values.lo ld) st2 with
                      | Some st3 => SNorm st3 | None => SStk (StBounds "copy") st2 end
      | LHalt c0 st2 => SHalt c0 st2 | LStk s0 st2 => SStk s0 st2
      end
    | LHalt c0 st1 => SHalt c0 st1 | LStk s0 st1 => SStk s0 st1
    end
  | SPCall p args =>
    match evalargs f (p_params (PArray.get procs p)) args st with
    | BOk cells st1 => match callp f (zi p) cells st1 with
                       | EOk _ st2 => SNorm st2 | EHalt c0 st2 => SHalt c0 st2 | EStk s0 st2 => SStk s0 st2 end
    | BHalt c0 st1 => SHalt c0 st1 | BStk s0 st1 => SStk s0 st1
    end
  | SExt x args =>
    match evalx f args st with
    | XOk xs st1 => match ext (fun p cs st' => callp f p cs st') (zi x) xs st1 with
                    | EOk _ st2 => SNorm st2 | EHalt c0 st2 => SHalt c0 st2 | EStk s0 st2 => SStk s0 st2 end
    | XHalt c0 st1 => SHalt c0 st1 | XStk s0 st1 => SStk s0 st1
    end
  | SSeq ss => exec_list f ss ss st
  | SIf c a b =>
    match evale f c st with
    | EOk v st1 => match truthy v with
                   | Some true => exec f a st1 | Some false => exec f b st1
                   | None => SStk (StType "condition") st1 end
    | EHalt c0 st1 => SHalt c0 st1 | EStk s0 st1 => SStk s0 st1
    end
  | SWhile c b =>
    match evale f c st with
    | EOk v st1 => match truthy v with
                   | Some true => match exec f b st1 with
                                  | SNorm st2 => exec f (SWhile c b) st2
                                  | r => r end
                   | Some false => SNorm st1
                   | None => SStk (StType "condition") st1 end
    | EHalt c0 st1 => SHalt c0 st1 | EStk s0 st1 => SStk s0 st1
    end
  | SRepeat b c =>                       (* web2c: do { b } while (!(c)) *)
    match exec f b st with
    | SNorm st1 =>
      match evale f c st1 with
      | EOk v st2 => match truthy v with
                     | Some true => SNorm st2 | Some false => exec f (SRepeat b c) st2
                     | None => SStk (StType "condition") st2 end
      | EHalt c0 st2 => SHalt c0 st2 | EStk s0 st2 => SStk s0 st2
      end
    | r => r
    end
  | SFor l c up a b body =>
    (* web2c: { register integer for_end; v = a; for_end = b;
                if (v <= for_end) do body while (v++ < for_end); }   (>=, v-- > for downto) *)
    match evall f l st with
    | LOk lc st1 =>
      match evale f a st1 with
      | EOk va st2 =>
        match write_loc st2 c lc va with
        | WStk s0 => SStk s0 st2
        | WOk st3 =>
          match evale f b st3 with
          | EOk vb st4 =>
            match store_conv false CI32 vb with
            | CStuck s0 => SStk s0 st4
            | COk (KInt fe) =>
              let t := match c with CI64 => TI64 | CC8 => TC8 | _ => TI32 end in
              match read_loc st4 t lc with
              | LdOk (VI _ v0) =>
                if (if up then v0 <=? fe else fe <=? v0) then for_loop f lc c t up fe body st4 else SNorm st4
              | LdOk _ => SStk (StType "for variable") st4
              | LdStuck s0 => SStk s0 st4
              end
            | COk _ => SStk (StType "for bound") st4
            end
          | EHalt c0 st4 => SHalt c0 st4 | EStk s0 st4 => SStk s0 st4
          end
        end
      | EHalt c0 st2 => SHalt c0 st2 | EStk s0 st2 => SStk s0 st2
      end
    | LHalt c0 st1 => SHalt c0 st1 | LStk s0 st1 => SStk s0 st1
    end
  | SCase e arms d =>
    match evale f e st with
    | EOk (VI _ z) st1 =>
      match find (fun a => existsb (fun m => Z.eqb z (zi m)) (fst a)) arms with
      | Some (_, body) => exec f body st1
      | None => match d with Some x => exec f x st1 | None => SNorm st1 end
      end
    | EOk _ st1 => SStk (StType "case selector") st1
    | EHalt c0 st1 => SHalt c0 st1 | EStk s0 st1 => SStk s0 st1
    end
  | SIncr l c d =>                       (* ++(x) / --(x) in the variable's C type *)
    match evall f l st with
    | LOk lc st1 =>
      let t := match c with CI64 => TI64 | CC8 => TC8 | _ => TI32 end in
      match read_loc st1 t lc with
      | LdOk (VI t' z) =>
        (* the increment is done in the promoted type; int overflow is undefined *)
        if negb (fits (match t' with TI64 => TI64 | _ => TI32 end) (z + zi d)) then SStk StOverflow st1 else
        match write_loc st1 c lc (VI t' (z + zi d)) with WOk st2 => SNorm st2 | WStk s0 => SStk s0 st1 end
      | LdOk _ => SStk (StType "increment") st1
      | LdStuck s0 => SStk s0 st1
      end
    | LHalt c0 st1 => SHalt c0 st1 | LStk s0 st1 => SStk s0 st1
    end
  | SWrite fe items nl =>
    match evale f fe st with
    | EOk (VFile h) st1 => write_items f h items nl st1
    | EOk _ st1 => SStk (StType "write to a non-file") st1
    | EHalt c0 st1 => SHalt c0 st1 | EStk s0 st1 => SStk s0 st1
    end
  end
  end

with for_loop (fuel : nat) (lc : loc) (c : ct) (t : ty) (up : bool) (fe : Z) (body : stmt) (st : state)
  {struct fuel} : sres :=
  match fuel with
  | O => SStk StFuel st
  | S f =>
    match exec f body st with
    | SNorm st1 =>
      match read_loc st1 t lc with
      | LdOk (VI t' v) =>
        let v' := if up then v + 1 else v - 1 in
        if negb (fits (match t' with TI64 => TI64 | _ => TI32 end) v') then SStk StOverflow st1 else
        match write_loc st1 c lc (VI t' v') with
        | WStk s0 => SStk s0 st1
        | WOk st2 => if (if up then v <? fe else fe <? v) then for_loop f lc c t up fe body st2 else SNorm st2
        end
      | LdOk _ => SStk (StType "for variable") st1
      | LdStuck s0 => SStk s0 st1
      end
    | r => r
    end
  end

with exec_list (fuel : nat) (all rest : list stmt) (st : state) {struct fuel} : sres :=
  match fuel with
  | O => SStk StFuel st
  | S f =>
    match rest with
    | [] => SNorm st
    | s :: tl =>
      match exec f s st with
      | SNorm st1 => exec_list f all tl st1
      | SGo n st1 => goto_in f n all all st1
      | r => r
      end
    end
  end

(* a goto reaching this statement list: find the element that is, or contains, label n *)
with goto_in (fuel : nat) (n : Z) (all scan : list stmt) (st : state) {struct fuel} : sres :=
  match fuel with
  | O => SStk StFuel st
  | S f =>
    match scan with
    | [] => SGo n st                     (* not here: propagate outward *)
    | SLabel m :: tl => if n =? zi m then exec_list f all tl st else goto_in f n all tl st
    | x :: tl =>
      if has_label n x then
        match resume n x with
        | Some x' => match exec f x' st with
                     | SNorm st1 => exec_list f all tl st1
                     | SGo n' st1 => goto_in f n' all all st1
                     | r => r end
        | None => SStk (StGoto n) st
        end
      else goto_in f n all tl st
    end
  end

with write_items (fuel : nat) (h : Z) (items : list witem) (nl : bool) (st : state) {struct fuel} : sres :=
  match fuel with
  | O => SStk StFuel st
  | S f =>
    match items with
    | [] => SNorm (if nl then emit h [10] st else st)
    | it :: rest =>
      let e := match it with WC e | WS e | WLd e => e end in
      match evale f e st with
      | EOk v st1 =>
        let bytes := match it, v with
                     | WC _, VI _ z => Some [Z.modulo z 256]            (* putc: unsigned char *)
                     | WLd _, VI _ z => Some (decimal z)                (* %ld of (long) *)
                     | WS _, VP b o => cstring 100000 b o st1           (* %s *)
                     | _, _ => None end in
        match bytes with
        | Some bs => write_items f h rest nl (emit h bs st1)
        | None => SStk (StType "write item") st1
        end
      | EHalt c0 st1 => SHalt c0 st1 | EStk s0 st1 => SStk s0 st1
      end
    end
  end.

End Interp.
