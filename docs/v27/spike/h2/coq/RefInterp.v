(* The interpreter's mutual block as it was before B2 (spike H.5 stage 2): lines 169-707 of
   git 9c3315be:docs/v27/spike/h2/coq/Interp.v (sha256 1ef36d75...), verbatim below this header.
   It shares Interp.v's types and helpers (Interp.v keeps lines 1-178 of that file unchanged),
   so B2Equiv.v can state each new member equal to its counterpart here. Not extracted: no
   model code depends on this file. Checked by h5/tools/b2gen.py --check. *)

From Coq Require Import ZArith List Bool String PArray Uint63 Sint63 Floats.
From PS Require Import Syntax Values Interp.
Import ListNotations.
Local Open Scope Z_scope.

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
