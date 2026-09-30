(* Extraction of the whole program to OCaml (spike H.2). Z is extracted to zarith's
   Big_int_Z, nat (fuel) to OCaml int, and the primitive ints, floats and persistent
   arrays to coq-core's kernel implementations (the same code Coq's own kernel runs). *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatInt ExtrOCamlInt63
                        ExtrOCamlFloats ExtrOCamlPArray ExtrOcamlString.
From PS Require Import Syntax Values Interp Boundary Main.
Set Extraction Output Directory ".".
(* the kernel's own OCaml modules must not be shadowed by extracted Coq modules of the
   same name *)
Extraction Blacklist Uint63 Sint63 PArray PrimFloat PrimInt63 PrimArray Parray Float64 Main.
(* one OCaml module per Coq module: the procedure files compile separately *)
Separate Extraction run initial_state.
