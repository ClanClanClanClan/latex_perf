(* PS syntax: the IR that translate/lower.py emits for web2c's Pascal (spike H.2, ADR-015).

   The translator resolves names, lays out storage and gives every operation its C
   type, so this syntax is already "what web2c's C does", made explicit. The
   semantics (Semantics.v) is a uniform machine over it; its C-dependent choices
   are listed there. Identifiers are numbers: globals, local frame offsets,
   procedures, externals and string literals each have their own table. *)

From Coq Require Import ZArith List Uint63 Sint63.

(* C storage types of a location. CC8 is plain `char` (signedness is the
   architecture's, H.1 report 5.4). CW8/CW4 are the union words of texmfmem.h. *)
Inductive ct : Set := CU8 | CS8 | CS16 | CU16 | CI32 | CI64 | CC8 | CF64 | CPTR | CFILE | CW8 | CW4
                      | CAGG.

(* arithmetic types of C expressions after the integer promotions *)
Inductive ty : Set := TI32 | TI64 | TF64 | TPTR | TW8 | TW4 | TFILE
                      | TC8.   (* only in ELoad: promote a plain char (architecture-dependent) *)

(* a slice of a union word: signed int, unsigned int, double, or a sub-word *)
Inductive slk : Set := SkS | SkU | SkF | SkW.

Inductive binop : Set := OAdd | OSub | OMul | ODiv | OMod | OFDiv.
Inductive cmpop : Set := CEq | CNe | CLt | CGt | CLe | CGe.

Inductive lexp : Set :=
| LGlob (g : int)                              (* a global variable (its own block) *)
| LLoc (k : int)                               (* cell k of the current frame *)
| LRef (k : int)                               (* the location held in frame cell k (var param) *)
| LIdx (a : lexp) (i : expr) (lo hi esz : int) (* static array element; lo..hi checked *)
| LPIdx (p : expr) (i : expr) (esz : int)      (* C pointer p + i, element of esz cells *)
| LFld (a : lexp) (off : int)                  (* record field at cell offset off *)
| LSl (a : lexp) (boff nb : int) (k : slk)     (* bytes boff..boff+nb-1 of a union word *)
with expr : Set :=
| EInt (t : ty) (z : int)
| EDbl (bits : Z)                            (* IEEE binary64 bit pattern of the literal *)
| EStr (sid : int)                             (* a C string literal: pointer to its static array *)
| ENull
| ELoad (t : ty) (l : lexp)                  (* read, then promote to t *)
| ENeg (t : ty) (e : expr)
| EBin (op : binop) (t : ty) (a b : expr)
| ECmp (op : cmpop) (t : ty) (a b : expr)
| EPCmp (eq : bool) (a b : expr)             (* pointer == / != *)
| EAnd (a b : expr) | EOr (a b : expr) | ENot (e : expr)   (* C && || ! *)
| EConv (t : ty) (e : expr)
| ECall (f : int) (args : list arg)
| EExt (x : int) (args : list arg)
| EAddr (l : lexp)
| EPAdd (p : expr) (esz : int) (neg : bool) (i : expr)
| EAbs (e : expr)                            (* cpascal.h abs on integer *)
| EOdd (t : ty) (e : expr)                   (* (x) & 1 *)
| EAlloc (esz : int) (c : ct) (n : expr)       (* xmallocarray: (n+1)*esz cells *)
| EUnseq (e : expr)                          (* C leaves the order of e's parts unspecified and
                                                translate/evalorder.py could not show it
                                                irrelevant: Stuck when reached *)
| ERealloc (esz : int) (c : ct) (p n : expr)
with arg : Set :=
| AVal (c : ct) (e : expr)                   (* by value, converted to c *)
| ARef (l : lexp)                            (* var parameter *)
| ACopy (l : lexp) (n : int)                   (* record by value *)
| ALv (l : lexp) (c : ct) (n : int)            (* external's argument that is a variable *)
| AExp (t : ty) (e : expr)                   (* external's argument that is an expression *)
| AType (tid : int).                           (* a type name given to a C macro *)

Inductive witem : Set := WC (e : expr) | WS (e : expr) | WLd (e : expr).

Inductive stmt : Set :=
| SSkip
| SAsg (l : lexp) (c : ct) (e : expr)
| SCopy (d s : lexp) (n : int)
| SPCall (p : int) (args : list arg)
| SExt (x : int) (args : list arg)
| SSeq (ss : list stmt)
| SLabel (n : int)
| SIf (c : expr) (a b : stmt)
| SWhile (c : expr) (s : stmt)
| SRepeat (s : stmt) (c : expr)
| SFor (l : lexp) (c : ct) (up : bool) (a b : expr) (s : stmt)
| SCase (e : expr) (arms : list (list int * stmt)) (dflt : option stmt)
| SGoto (n : int)
| SReturn                                    (* web2c: goto 10 in TeX mode is `return` *)
| SUnseq (s : stmt)                          (* as EUnseq, for a statement *)
| SIncr (l : lexp) (c : ct) (d : int)
| SWrite (f : expr) (items : list witem) (nl : bool).

(* how an actual parameter lands in the callee's frame *)
Inductive pkind : Set := PVal (c : ct) | PRef | PCopy (n : int).

Record proc : Set := mkproc {
  p_params : list pkind;
  p_frame : int;                               (* frame size in cells *)
  p_result : option (int * ct);                (* result cell and its C type *)
  p_body : stmt }.

(* a global's storage: runs of (count, cell type), zero-initialised (C static storage) *)
Definition gshape := list (int * ct).

(* AST numbers are primitive 63-bit ints read as signed; this keeps the extracted program
   small (a Z literal extracts to a chain of big-integer operations) *)
Definition zi (x : int) : Z := Sint63.to_Z x.
