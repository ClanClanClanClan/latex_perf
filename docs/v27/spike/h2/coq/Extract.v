(* Extraction of the whole program to OCaml (spike H.2). Z is extracted to zarith's
   Big_int_Z, nat (fuel) to OCaml int, and the primitive ints, floats and persistent
   arrays to coq-core's kernel implementations (the same code Coq's own kernel runs). *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatInt ExtrOCamlInt63
                        ExtrOCamlFloats ExtrOcamlString.
From Coq Require Import PArray.
(* Coq 8.18's ExtrOCamlPArray, minus its `Extraction Inline PArray.array`: with that
   inline, extraction prints a nested array type as `cell 'a Parray.t 'a Parray.t`, which
   OCaml rejects (H.2 checkpoint 2 repaired it with a textual sed patch of the extracted
   code). Without the inline the type is `cell array array`, with PArray's extracted module
   defining `type 'a array = 'a Parray.t`: the same realizers, and no patch. *)
Extract Constant PArray.array "'a" => "'a Parray.t".
Extract Constant PArray.make => "Parray.make".
Extract Constant PArray.get => "Parray.get".
Extract Constant PArray.default => "Parray.default".
Extract Constant PArray.set => "Parray.set".
Extract Constant PArray.length => "Parray.length".
Extract Constant PArray.copy => "Parray.copy".
From PS Require Import Syntax Values Interp Kpse Boundary Main.
(* the byte constants of Kpse.v's loops over file contents: computed once (a Z literal is
   extracted as big-integer arithmetic evaluated at every use) *)
Extraction NoInline Kpse.C_NUL Kpse.C_TAB Kpse.C_LF Kpse.C_CR Kpse.C_SP Kpse.C_BANG Kpse.C_DOLLAR
  Kpse.C_PCT Kpse.C_PLUS Kpse.C_MINUS Kpse.C_DOT Kpse.SL Kpse.C_D0 Kpse.C_D9 Kpse.C_COLON Kpse.C_SEMI
  Kpse.C_AT Kpse.C_UA Kpse.C_UZ Kpse.C_US Kpse.C_LA Kpse.C_LC Kpse.C_LZ Kpse.C_LBRACE Kpse.C_RBRACE
  Kpse.C_TILDE Kpse.db_size.
Set Extraction Output Directory ".".
(* the kernel's own OCaml modules must not be shadowed by extracted Coq modules of the
   same name *)
Extraction Blacklist Uint63 Sint63 PArray PrimFloat PrimInt63 PrimArray Parray Float64 Main.
(* one OCaml module per Coq module: the procedure files compile separately *)
Separate Extraction run initial_state.
