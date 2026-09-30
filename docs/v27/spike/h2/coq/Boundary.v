(* The C boundary model, as far as spike H.2 needs it (ADR-015, ADR-014 draft 2.5).

   Each external the translated program calls is either modelled here, from the C
   source of the pinned revision (the file and function are named per case), or
   Stuck (StExternal name): an unmodelled external puts the run outside the tier.
   This is hand-written C semantics, the part of the trusted base that ADR-015 says
   gets the most scrutiny; every case below is a claim to be attested (H.6). *)

From Coq Require Import ZArith List Bool String Ascii PArray Uint63 Sint63 Floats.
From PS Require Import Syntax Values Interp ProgGlobals PoolData.
Import ListNotations.
Local Open Scope Z_scope.

(* handles of the three standard streams (C's stdin, stdout, stderr) *)
Definition H_stdin : Z := 0.
Definition H_stdout : Z := 1.
Definition H_stderr : Z := 2.

Definition xint (st : state) (a : xarg) : option Z :=
  match a with
  | XVal (VI _ z) => Some z
  | XLoc l _ _ => match read_loc st TI64 l with LdOk (VI _ z) => Some z | _ =>
                  match read_loc st TI32 l with LdOk (VI _ z) => Some z | _ => None end end
  | _ => None
  end.

Definition xptr (st : state) (a : xarg) : option val :=
  match a with
  | XVal (VP b o) => Some (VP b o)
  | XVal VN => Some VN
  | XLoc l _ _ => match read_loc st TPTR l with LdOk v => Some v | _ => None end
  | _ => None
  end.

Definition xstring (st : state) (a : xarg) : option (list Z) :=
  match xptr st a with Some (VP b o) => cstring 100000 b o st | _ => None end.

Fixpoint lookup_env (name : list Z) (env : list (list Z * Z)) : option Z :=
  match env with
  | [] => None
  | (n, v) :: rest => if list_eq_dec Z.eq_dec n name then Some v else lookup_env name rest
  end.

Definition ext_name (x : Z) : string := nth (Z.to_nat x) ext_names "?"%string.

Definition stuck_ext (x : Z) (st : state) : eres := EStk (StExternal (ext_name x)) st.

Definition ok (st : state) : eres := EOk (VI TI32 0) st.

(* ---------------------------------------------------------------- helpers *)
Definition gint (st : state) (g : Z) : option Z :=
  match cell_at st g 0 with Some (KInt z) => Some z | _ => None end.
Definition gput (st : state) (g : Z) (k : cell) : option state := put_cell st g 0 k.
Definition gptr (st : state) (g : Z) : option (Z * Z) :=
  match cell_at st g 0 with Some (KPtr b o) => Some (b, o) | _ => None end.

Definition with_stdin (st : state) (bytes : list Z) : state :=
  let x := st_io st in
  set_io st (mkio (io_out x) bytes (io_argv x) (io_char_signed x) (io_files x) (io_next_handle x) (io_fs x) (io_env x) (io_cstate x)).

Fixpoint cget (k : Z) (l : list (Z * Z)) : Z :=
  match l with [] => 0 | (k', v) :: r => if k =? k' then v else cget k r end.
Definition cstate (st : state) (k : Z) : Z := cget k (io_cstate (st_io st)).
Definition set_cstate (st : state) (k v : Z) : state :=
  let x := st_io st in
  set_io st (mkio (io_out x) (io_stdin x) (io_argv x) (io_char_signed x) (io_files x) (io_next_handle x)
                  (io_fs x) (io_env x) ((k, v) :: io_cstate x)).
(* C-internal variables (static storage, 0 at start) *)
Definition CS_synctex_option_read : Z := 1.       (* synctex.c synctex_ctxt.flags.option_read *)
Definition CS_pdftexbanner_init : Z := 2.         (* utils.c makepdftexbanner's static flag *)

(* constants compiled into the binary, measured by gdb on the reference build *)
Definition ptexbanner : list Z :=                 (* "This is pdfTeX, Version 3.141592653-2.6-1.40.29" *)
  map (fun c => Z.of_nat (Ascii.nat_of_ascii c)) (list_ascii_of_string "This is pdfTeX, Version 3.141592653-2.6-1.40.29").
Definition kpathsea_version_string : list Z :=
  map (fun c => Z.of_nat (Ascii.nat_of_ascii c)) (list_ascii_of_string "kpathsea version 6.4.2").

Definition env_int (st : state) (name : string) : option Z :=
  lookup_env (map (fun c => Z.of_nat (Ascii.nat_of_ascii c)) (list_ascii_of_string name)) (io_env (st_io st)).

(* gmtime's calendar (proleptic Gregorian, UTC): days since 1970-01-01 -> (y, m, d),
   H. Hinnant's civil_from_days *)
Definition civil_from_days (z : Z) : Z * Z * Z :=
  let z := z + 719468 in
  let era := Z.div z 146097 in
  let doe := z - era * 146097 in
  let yoe := Z.div (doe - Z.div doe 1460 + Z.div doe 36524 - Z.div doe 146096) 365 in
  let y := yoe + era * 400 in
  let doy := doe - (365 * yoe + Z.div yoe 4 - Z.div yoe 100) in
  let mp := Z.div (5 * doy + 2) 153 in
  let d := doy - Z.div (153 * mp + 2) 5 + 1 in
  let m := if mp <? 10 then mp + 3 else mp - 9 in
  ((if m <=? 2 then y + 1 else y), m, d).

(* texmfmp.c input_line (FILE *f), for a byte stream: bytes go to buffer[first..] until
   LF, CR or EOF (or bufsize), trailing spaces are trimmed, a CR LF counts as one
   terminator, and buffer[first..last] is mapped through xord *)
Fixpoint read_into (n : nat) (bytes : list Z) (bb bo last bufsize : Z) (st : state)
  : option (state * Z * Z * list Z) :=      (* state, last, i (-1 = EOF), rest *)
  match n with
  | O => None
  | S n' =>
    if bufsize <=? last then Some (st, last, -2, bytes)   (* stopped by the size test: i unchanged *)
    else match bytes with
         | [] => Some (st, last, -1, [])
         | c :: rest =>
           if (c =? 10) || (c =? 13) then Some (st, last, c, rest)
           else match put_cell st bb (bo + last) (KInt c) with
                | Some st' => read_into n' rest bb bo (last + 1) bufsize st'
                | None => None end
         end
  end.

Fixpoint trim_spaces (n : nat) (bb bo first last : Z) (st : state) : Z :=
  match n with
  | O => last
  | S n' => if (first <? last) && match cell_at st bb (bo + last - 1) with Some (KInt 32) => true | _ => false end
            then trim_spaces n' bb bo first (last - 1) st else last
  end.

Fixpoint map_xord (n : nat) (bb bo i xg : Z) (st : state) : option state :=
  match n with
  | O => Some st
  | S n' => match cell_at st bb (bo + i) with
            | Some (KInt c) => match cell_at st xg c with
                               | Some k => match put_cell st bb (bo + i) k with
                                           | Some st' => map_xord n' bb bo (i + 1) xg st' | None => None end
                               | None => None end
            | _ => None end
  end.

Definition input_line_stdin (st : state) : eres :=
  match gint st G_first, gint st G_bufsize, gptr st G_buffer, gint st G_maxbufstack with
  | Some first, Some bufsize, Some (bb, bo), Some mbs =>
    match read_into (Z.to_nat (bufsize - first + 2)) (io_stdin (st_io st)) bb bo first bufsize st with
    | None => EStk (StBounds "input_line") st
    | Some (st1, last, i, rest) =>
      if (i =? -1) && (last =? first) then EOk (VI TI32 0) (with_stdin st1 rest)
      else if i =? -2 then EStk (StExternal "input_line: buffer full (stderr message, uexit(1)) not modelled") st1
      else
        match put_cell st1 bb (bo + last) (KInt 32) with
        | None => EStk (StBounds "input_line") st1
        | Some st2 =>
          let st3 := if mbs <=? last then match gput st2 G_maxbufstack (KInt last) with Some s => s | None => st2 end else st2 in
          let rest' := if i =? 13 then match rest with 10 :: r => r | _ => rest end else rest in
          let last' := trim_spaces (Z.to_nat (last - first)) bb bo first last st3 in
          match map_xord (Z.to_nat (last' - first + 1)) bb bo first G_xord st3 with
          | None => EStk (StBounds "input_line xord") st3
          | Some st4 => match gput st4 G_last (KInt last') with
                        | Some st5 => EOk (VI TI32 1) (with_stdin st5 rest')
                        | None => EStk (StBounds "input_line") st4 end
          end
        end
    end
  | _, _, _, _ => EStk (StType "input_line globals") st
  end.

(* pdftex-pool.c loadpoolstrings (integer spare_size), generated by makecpool from
   pdftex.pool: each string's bytes go to strpool[poolptr++] and makestring() is called;
   0 if the running total of lengths reaches spare_size *)
Fixpoint load_pool (callp : Z -> list cell -> state -> eres) (ss : list (list int)) (i spare g : Z) (st : state) : eres :=
  match ss with
  | [] => EOk (VI TI32 g) st
  | s :: rest =>
    let l := Z.of_nat (List.length s) in
    if spare <=? i + l then EOk (VI TI32 0) st else
    match gptr st G_strpool, gint st G_poolptr with
    | Some (pb, po), Some pp =>
      match put_cells (map (fun c => KInt (zi c)) s) pb (po + pp) st with
      | None => EStk (StBounds "loadpoolstrings") st
      | Some st1 =>
        match gput st1 G_poolptr (KInt (pp + l)) with
        | None => EStk (StBounds "loadpoolstrings") st1
        | Some st2 =>
          match callp P_makestring [] st2 with
          | EOk (VI _ g') st3 => load_pool callp rest (i + l) spare g' st3
          | EOk _ st3 => EStk (StType "makestring result") st3
          | r => r
          end
        end
      end
    | _, _ => EStk (StType "loadpoolstrings globals") st
    end
  end.

(* utils.c maketexstring (const char *s): "" -> getnullstr(); check_buf(poolptr + l,
   poolsize) (pdftex_fail beyond: not modelled); the bytes to strpool[poolptr++];
   last_tex_string = makestring() (last_tex_string is read only by tex_printf, not kept) *)
Definition maketexstring (callp : Z -> list cell -> state -> eres) (bytes : list Z) (st : state) : eres :=
  match bytes with
  | [] => callp P_getnullstr [] st
  | _ =>
    let l := Z.of_nat (List.length bytes) in
    match gptr st G_strpool, gint st G_poolptr, gint st G_poolsize with
    | Some (pb, po), Some pp, Some ps =>
      if ps <? pp + l then EStk (StExternal "maketexstring: pdftex_fail on pool overflow") st else
      match put_cells (map KInt bytes) pb (po + pp) st with
      | Some st1 => match gput st1 G_poolptr (KInt (pp + l)) with
                    | Some st2 => callp P_makestring [] st2
                    | None => EStk (StBounds "maketexstring") st1 end
      | None => EStk (StBounds "maketexstring") st
      end
    | _, _, _ => EStk (StType "maketexstring globals") st
    end
  end.

Definition put_int_at (st : state) (a : xarg) (z : Z) : option state :=
  match a with
  | XLoc l _ _ => match write_loc st CI32 l (VI TI32 z) with WOk st' => Some st' | WStk _ => None end
  | _ => None
  end.

(* the first heap block id after the globals and the string literals *)
Definition nglobals_strings_end : Z := Z.of_nat (List.length globals + List.length strings).

(* the model; callp calls back into the translated program *)
Definition ext (callp : Z -> list cell -> state -> eres) (x : Z) (args : list xarg) (st : state) : eres :=
  (* lib/setupvar.c setupboundvariable (integer *var, const_string var_name, integer dflt):
     *var = dflt; if kpse_var_value(var_name) is set: atoi; if (conf_val < 0 ||
     (conf_val == 0 && dflt > 0)) warn on stderr and keep dflt, else *var = conf_val *)
  if x =? X_setupboundvariable then
    match args with
    | [pa; na; da] =>
      match xptr st pa, xstring st na, xint st da with
      | Some (VP b o), Some name, Some dflt =>
        let v := match lookup_env name (io_env (st_io st)) with
                 | Some c => if (c <? 0) || ((c =? 0) && (0 <? dflt)) then dflt else c
                 | None => dflt end in
        match lookup_env name (io_env (st_io st)) with
        | Some c => if (c <? 0) || ((c =? 0) && (0 <? dflt))
                    then EStk (StExternal "setupboundvariable: bad value warning not modelled") st
                    else match put_cell st b o (KInt v) with Some st' => ok st' | None => EStk (StBounds "setupboundvariable") st end
        | None => match put_cell st b o (KInt v) with Some st' => ok st' | None => EStk (StBounds "setupboundvariable") st end
        end
      | _, _, _ => EStk (StType "setupboundvariable arguments") st
      end
    | _ => EStk (StType "setupboundvariable arity") st
    end
  (* the standard streams: cpascal.h input/output are stdin/stdout; stderr *)
  else if x =? X_stdout then EOk (VFile H_stdout) st
  else if x =? X_stderr then EOk (VFile H_stderr) st
  else if x =? X_stdin then EOk (VFile H_stdin) st
  (* cpascal.h / C library: fflush(stdout) and friends change no modelled state *)
  else if x =? X_fflush then ok st
  else if x =? X_initstarttime then ok st
  (* texmfmp.c input_line; only the terminal is modelled at checkpoint 2 *)
  else if x =? X_inputln then
    match args with
    | XVal (VFile 0) :: _ => input_line_stdin st
    | _ => EStk (StExternal "inputln on a file (not modelled yet)") st
    end
  (* texmfmp.c topenin: buffer[first] = 0; with no arguments after the options nothing
     else happens (the run is `pdftex -ini`: io_argv holds only the options) *)
  else if x =? X_topenin then
    match gint st G_first, gptr st G_buffer with
    | Some first, Some (bb, bo) =>
      match put_cell st bb (bo + first) (KInt 0) with
      | Some st' => if Nat.eqb (List.length (io_argv (st_io st))) 1 then ok st'
                    else EStk (StExternal "topenin with file arguments (not modelled yet)") st'
      | None => EStk (StBounds "topenin") st
      end
    | _, _ => EStk (StType "topenin globals") st
    end
  else if x =? X_loadpoolstrings then
    match args with
    | [a] => match xint st a with
             | Some spare => load_pool callp PoolData.pool_strings 0 spare 0 st
             | None => EStk (StType "loadpoolstrings argument") st end
    | _ => EStk (StType "loadpoolstrings arity") st
    end
  (* texmfmp.h dateandtime(i,j,k,l) = get_date_and_time(&i,&j,&k,&l); with
     FORCE_SOURCE_DATE=1: gmtime(SOURCE_DATE_EPOCH). The real clock (FORCE_SOURCE_DATE
     unset) is a nondeterministic input (O-5): not modelled, Stuck *)
  else if x =? X_dateandtime then
    match env_int st "FORCE_SOURCE_DATE", env_int st "SOURCE_DATE_EPOCH", args with
    | Some 1, Some e, [a1; a2; a3; a4] =>
      let days := Z.div e 86400 in
      let secs := Z.modulo e 86400 in
      let '(y, m, d) := civil_from_days days in
      match put_int_at st a1 (Z.div secs 60) with
      | Some s1 => match put_int_at s1 a2 d with
                   | Some s2 => match put_int_at s2 a3 m with
                                | Some s3 => match put_int_at s3 a4 y with
                                             | Some s4 => ok s4 | None => EStk (StType "dateandtime") s3 end
                                | None => EStk (StType "dateandtime") s2 end
                   | None => EStk (StType "dateandtime") s1 end
      | None => EStk (StType "dateandtime") st
      end
    | _, _, _ => EStk (StExternal "dateandtime without FORCE_SOURCE_DATE=1 (the real clock, O-5)") st
    end
  (* texmfmp.c get_seconds_and_micros: gettimeofday, the real clock. SPIKE STUB (ADR-014
     draft 9, H.2: "C5 fixed date (spike only)"): SOURCE_DATE_EPOCH seconds, 0 micros *)
  else if x =? X_secondsandmicros then
    match env_int st "SOURCE_DATE_EPOCH", args with
    | Some e, [a1; a2] =>
      match put_int_at st a1 e with
      | Some s1 => match put_int_at s1 a2 0 with Some s2 => ok s2 | None => EStk (StType "secondsandmicros") s1 end
      | None => EStk (StType "secondsandmicros") st
      end
    | _, _ => EStk (StExternal "secondsandmicros: the real clock") st
    end
  (* mapfile.c pdfinitmapfile (const char *map_name): records the default map file in
     mapfile.c's own queue (mitem); nothing the program reads. That queue is C-internal
     state this model does not keep, so every external that consults it (pdfmapfile,
     pdfmapline, font embedding at shipout) is Stuck until it is modelled *)
  else if x =? X_pdfinitmapfile then ok st
  (* synctex.c synctexinitcommand -> _synctex_read_command_line_option: one shot; with
     synctex_options (= synctexoption) == SYNCTEX_NO_OPTION (INT_MAX, set by C main):
     SYNCTEX_VALUE = zeqtb[synctexoffset].cint = 0. Any other option value, and a second
     call (the one-shot flag is C-internal state not kept here), are not modelled *)
  else if x =? X_synctexinitcommand then
    if cstate st CS_synctex_option_read =? 1 then ok st else
    match gint st G_synctexoption, gint st G_synctexoffset, gptr st G_zeqtb with
    | Some 2147483647, Some off, Some (b, o) =>
      match write_loc st CI32 (mkloc b (o + off) (Some (4, 4, SkS))) (VI TI32 0) with
      | WOk st' => ok (set_cstate st' CS_synctex_option_read 1) | WStk s0 => EStk s0 st end
    | _, _, _ => EStk (StExternal "synctexinitcommand with a -synctex option") st
    end
  (* utils.c makepdftexbanner: once (static flag): pdftexbanner =
     maketexstring("%s%s %s" of ptexbanner, versionstring, kpathsea_version_string) *)
  else if x =? X_makepdftexbanner then
    if cstate st CS_pdftexbanner_init =? 1 then ok st else
    match xstring st (XLoc (mkloc G_versionstring 0 None) CPTR 1) with
    | Some vs =>
      match maketexstring callp (ptexbanner ++ vs ++ [32] ++ kpathsea_version_string) st with
      | EOk (VI _ sn) st1 => match gput st1 G_pdftexbanner (KInt sn) with
                             | Some st2 => ok (set_cstate st2 CS_pdftexbanner_init 1)
                             | None => EStk (StBounds "makepdftexbanner") st1 end
      | EOk _ st1 => EStk (StType "makepdftexbanner") st1
      | r => r
      end
    | None => EStk (StType "versionstring") st
    end
  (* texmfmp.c getjobname (strnumber name): c_job_name (-jobname) is NULL for this command
     line, so the argument is returned *)
  else if x =? X_getjobname then
    match args with
    | [a] => match xint st a with Some n => EOk (VI TI32 n) st | None => EStk (StType "getjobname") st end
    | _ => EStk (StType "getjobname arity") st
    end
  (* openclose.c recorder_change_filename: returns at once, the recorder being off
     (no -recorder on the command line) *)
  else if x =? X_recorderchangefilename then ok st
  (* cpascal.h stringcast(x) ((string) (x)): a cast *)
  else if x =? X_stringcast then
    match args with
    | [XVal v] => EOk v st
    | [XLoc l _ _] => match read_loc st TPTR l with LdOk v => EOk v st | LdStuck s0 => EStk s0 st end
    | _ => EStk (StType "stringcast") st
    end
  (* texmfmp.h aopenout(f) = open_out_or_pipe(&f, "w"): a name starting with '|' is a pipe
     (with shell escape; not modelled); otherwise openclose.c open_output: no
     -output-directory on this command line, fopen(nameoffile+1, "w") in the working
     directory. The model's file system accepts every such name, and the file is new and
     empty. fopen's failure modes (permissions, a full disk) are outside the environment
     class *)
  else if x =? X_aopenout then
    match args, gptr st G_nameoffile, gint st G_shellenabledp with
    | [XLoc l _ _], Some (nb, no), Some sh =>
      match cstring 100000 nb (no + 1) st with
      | Some name =>
        if (negb (sh =? 0)) && match name with 124 :: _ => true | _ => false end
        then EStk (StExternal "aopenout of a pipe") st else
        let x0 := st_io st in
        let h := io_next_handle x0 in
        let st1 := set_io st (mkio (io_out x0) (io_stdin x0) (io_argv x0) (io_char_signed x0)
                                   ((h, name) :: io_files x0) (h + 1) (io_fs x0) (io_env x0) (io_cstate x0)) in
        match write_loc st1 CFILE l (VFile h) with
        | WOk st2 => EOk (VI TI32 1) st2
        | WStk s0 => EStk s0 st1
        end
      | None => EStk (StType "aopenout name") st
      end
    | _, _, _ => EStk (StType "aopenout arguments") st
    end
  (* cpascal.h libcfree = free: free(NULL) does nothing; a block allocated by xmalloc is
     released (the model empties it, so a later access is Stuck: use after free); freeing
     anything else is undefined: Stuck *)
  else if x =? X_libcfree then
    match args with
    | [a] => match xptr st a with
             | Some VN => ok st
             | Some (VP b 0) => if (nglobals_strings_end <=? b) && (b <? frame_base) then ok (hput st b empty_block)
                                else EStk (StOther "free of a non-heap object") st
             | _ => EStk (StOther "free of a pointer inside a block") st
             end
    | _ => EStk (StType "libcfree arity") st
    end
  (* cpascal.h ISDIRSEP = IS_DIR_SEP; kpathsea/c-pathch.h on Unix: (ch) == DIR_SEP, '/' *)
  else if x =? X_ISDIRSEP then
    match args with
    | [a] => match xint st a with Some c => EOk (VI TI32 (if c =? 47 then 1 else 0)) st
                                  | None => EStk (StType "ISDIRSEP") st end
    | _ => EStk (StType "ISDIRSEP arity") st
    end
  (* synctex.c synctexterminate (boolean log_opened): with SyncTeX off (SYNCTEX_FILE NULL)
     it only remove()s <log name minus extension>.synctex and .synctex.gz from the
     working directory. The model's file system starts empty and nothing here creates
     such names, so there is nothing to remove; a non-empty file system is not modelled *)
  else if x =? X_synctexterminate then
    match io_fs (st_io st) with [] => ok st | _ => EStk (StExternal "synctexterminate with a file system") st end
  (* texmfmp.h aclose(f) = close_file_or_pipe(f): not a pipe (none was opened), so
     openclose.c close_file: NULL -> nothing; else fclose. The file keeps the bytes written
     to its handle (io_out); an fclose failure (perror) is outside the environment class *)
  else if x =? X_aclose then
    match args with
    | [a] => match xint st a, a with
             | _, XLoc l _ _ => match read_loc st TFILE l with
                                | LdOk VN => ok st
                                | LdOk (VFile _) => ok st
                                | _ => EStk (StType "aclose") st end
             | _, _ => EStk (StType "aclose") st end
    | _ => EStk (StType "aclose arity") st
    end
  else if x =? X_uexit then
    match args with [a] => match xint st a with Some c => EHalt c st | None => EStk (StType "uexit") st end
               | _ => EStk (StType "uexit arity") st end
  else stuck_ext x st.
