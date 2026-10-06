(* Spike H.5, stage-1 correction (H5-heap-design.md §3.4): what one `Z` operation on a small value costs
   against a native 63-bit int operation WITH an overflow check, on this machine and compiler.
   Build (the model's switch and flags: l0-testing, OCaml 5.2.0 with flambda, no -O):
     ocamlfind ocamlopt -package zarith -linkpkg zbench.ml -o zbench.exe
   Each loop does N operations whose results feed the next iteration (nothing is dead code), and
   prints ns per operation (CPU time, Sys.time). Small values: |x| < 2^31, the range of C's int,
   which is where the model's arithmetic lives (zarith keeps them unboxed). *)
let n = 100_000_000
let time name f =
  let t0 = Sys.time () in
  let r = f () in
  let t = Sys.time () -. t0 in
  Printf.printf "%-34s %6.2f ns/op   (check %d)\n%!" name (t *. 1e9 /. float n) r
exception Overflow
(* add with the overflow test a proved int63 realizer would carry (C's int is 32-bit, so the
   model's real test is a range check against 2^31; both are shown) *)
let add_ovf a b = let s = a + b in if (a lxor s) land (b lxor s) < 0 then raise Overflow else s
let add_i32 a b = let s = a + b in if s < -0x8000_0000 || s > 0x7fff_ffff then raise Overflow else s
let () =
  time "Z.add (small)" (fun () ->
      let a = ref (Z.of_int 12345) and k = Z.of_int 7 and m = Z.of_int 0xffff in
      for _ = 1 to n do a := Z.logand (Z.add !a k) m done; Z.to_int !a);
  time "  ... of which Z.logand alone" (fun () ->
      let a = ref (Z.of_int 12345) and m = Z.of_int 0xffff and k = Z.of_int 1 in
      for i = 1 to n do a := Z.logand (if i land 1 = 0 then !a else Z.of_int i) m done; ignore k; Z.to_int !a);
  time "Z.compare + Z.sub (small)" (fun () ->
      let a = ref (Z.of_int 1_000_000) and one = Z.one and c = ref 0 in
      for _ = 1 to n do if Z.compare !a Z.zero > 0 then a := Z.sub !a one else a := Z.of_int 1_000_000; incr c done; !c + Z.to_int !a);
  time "Z.div/Z.rem (small)" (fun () ->
      let a = ref (Z.of_int 987654) and acc = ref Z.zero and d = Z.of_int 10 in
      for i = 1 to n do acc := Z.add (Z.rem !a d) !acc; a := if i land 7 = 0 then Z.of_int (987654 + i land 1023) else Z.div !a d done;
      Z.to_int !acc);
  time "int add + land (overflow-checked, 63)" (fun () ->
      let a = ref 12345 in for _ = 1 to n do a := (add_ovf !a 7) land 0xffff done; !a);
  time "int add + land (range-checked, i32)" (fun () ->
      let a = ref 12345 in for _ = 1 to n do a := (add_i32 !a 7) land 0xffff done; !a);
  time "int compare + sub" (fun () ->
      let a = ref 1_000_000 and c = ref 0 in
      for _ = 1 to n do if !a > 0 then a := !a - 1 else a := 1_000_000; incr c done; !c + !a);
  time "int div/rem" (fun () ->
      let a = ref 987654 and acc = ref 0 in
      for i = 1 to n do acc := !a mod 10 + !acc; a := if i land 7 = 0 then 987654 + i land 1023 else !a / 10 done; !acc)
