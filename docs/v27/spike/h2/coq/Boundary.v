(* The C boundary model, as far as spike H.2 needs it (ADR-015, ADR-014 draft 2.5).

   Each external the translated program calls is either modelled here, from the C
   source of the pinned revision (the file and function are named per case), or
   Stuck (StExternal name): an unmodelled external puts the run outside the tier.
   This is hand-written C semantics, the part of the trusted base that ADR-015 says
   gets the most scrutiny; every case below is a claim to be attested (H.6).

   ENVIRONMENT AUDIT (review A, finding 1; the class, not the instance). Every input of
   a modelled external that is not a function of the program's own state, and how the
   model takes it. Each is either an explicit input that is part of the run's identity
   (Values.io: the driver's SPEC file) or Stuck; none is fixed to a value the real
   function might not produce.
     stdin, stdout, stderr      none (handles)
     setupboundvariable         kpse_var_value: the environment, texmf.cnf, expansion ->
                                io_kpse (explicit, measured in the image); atoi modelled
     topenin                    the command line -> io_argv (explicit; only the measured
                                `-ini`, else Stuck)
     inputln (terminal)         standard input -> io_stdin (explicit)
     loadpoolstrings            none (compiled-in pool)
     makepdftexbanner           none (compiled-in strings; versionstring from C main)
     dateandtime                getenv FORCE_SOURCE_DATE / SOURCE_DATE_EPOCH -> io_env
                                (explicit, C's STREQ and strtoull modelled); time(NULL),
                                localtime and the time zone -> Stuck
     secondsandmicros           gettimeofday -> io_clock (explicit; no reading left: Stuck).
                                Until review A this was a stub returning SOURCE_DATE_EPOCH
                                and 0 microseconds, which gettimeofday never returns:
                                \pdfrandomseed and everything seeded or timed from it gave
                                model outputs the binary never gives (C-107)
     initstarttime              getenv SOURCE_DATE_EPOCH -> io_env (explicit); without it
                                time(NULL): recorded as unknown, any read of it Stuck
     fflush                     none (the model keeps one byte stream per handle and claims
                                no interleaving between them)
     pdfinitmapfile             none (mapfile.c's queue; every reader of it is Stuck)
     synctexinitcommand         the -synctex option (C main, measured command line)
     synctexterminate           the working directory's files (remove()) -> io_fs: the
                                environment class is an empty directory, else Stuck
     getjobname                 the -jobname option: measured command line only, else Stuck
     recorderchangefilename     the -recorder option: measured command line only, else Stuck
     stringcast, aclose, libcfree, ISDIRSEP, uexit
                                none
     aopenout                   the working directory (fopen), -output-directory,
                                $TEXMFOUTPUT on failure, shellenabledp (C main): the
                                environment class is a fresh empty writable directory in
                                which a single new name component opens; any other name,
                                and any other command line, Stuck
   Not inputs of these externals, and not modelled anywhere: the process id, random
   numbers, signals (the environment class delivers none), the locale (pdfTeX never calls
   setlocale, so C's applies). *)

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

Fixpoint lookup_bytes (name : list Z) (env : list (list Z * list Z)) : option (list Z) :=
  match env with
  | [] => None
  | (n, v) :: rest => if list_eq_dec Z.eq_dec n name then Some v else lookup_bytes name rest
  end.

Definition list_eq_dec_bool (a b : list Z) : bool := if list_eq_dec Z.eq_dec a b then true else false.

Definition bytes_of_string (s : string) : list Z :=
  map (fun c => Z.of_nat (Ascii.nat_of_ascii c)) (list_ascii_of_string s).

Definition ext_name (x : Z) : string := nth (Z.to_nat x) ext_names "?"%string.

Definition stuck_ext (x : Z) (st : state) : eres := EStk (StExternal (ext_name x)) st.

Definition ok (st : state) : eres := EOk (VI TI32 0) st.

(* ---------------------------------------------------------------- helpers *)
Definition gint (st : state) (g : Z) : option Z :=
  match cell_at st g 0 with Some (KInt z) => Some z | _ => None end.
Definition gput (st : state) (g : Z) (k : cell) : option state := put_cell st g 0 k.
Definition gptr (st : state) (g : Z) : option (Z * Z) :=
  match cell_at st g 0 with Some (KPtr b o) => Some (b, o) | _ => None end.

Definition with_stdin (st : state) (bytes : list Z) : state := set_io st (io_set_stdin (st_io st) bytes).

Fixpoint cget (k : Z) (l : list (Z * Z)) : Z :=
  match l with [] => 0 | (k', v) :: r => if k =? k' then v else cget k r end.
Definition cstate (st : state) (k : Z) : Z := cget k (io_cstate (st_io st)).
Definition set_cstate (st : state) (k v : Z) : state :=
  set_io st (io_set_cstate (st_io st) ((k, v) :: io_cstate (st_io st))).
(* C-internal variables (static storage, 0 at start) *)
Definition CS_synctex_option_read : Z := 1.       (* synctex.c synctex_ctxt.flags.option_read *)
Definition CS_pdftexbanner_init : Z := 2.         (* utils.c makepdftexbanner's static flag *)
Definition CS_start_time_set : Z := 3.            (* texmfmp.c start_time_set *)
Definition CS_start_time_kind : Z := 4.           (* 1: start_time = SOURCE_DATE_EPOCH (CS_start_time);
                                                     2: start_time = time(NULL), the real clock, whose
                                                     value the model does not have: reading it is Stuck *)
Definition CS_start_time : Z := 5.                (* texmfmp.c start_time, when kind = 1 *)
Definition CS_source_date_epoch_set : Z := 6.     (* texmfmp.c SOURCE_DATE_EPOCH_set *)
Definition CS_force_source_date_set : Z := 7.     (* texmfmp.c FORCE_SOURCE_DATE_set *)

(* constants compiled into the binary, measured by gdb on the reference build *)
Definition ptexbanner : list Z :=                 (* "This is pdfTeX, Version 3.141592653-2.6-1.40.29" *)
  map (fun c => Z.of_nat (Ascii.nat_of_ascii c)) (list_ascii_of_string "This is pdfTeX, Version 3.141592653-2.6-1.40.29").
Definition kpathsea_version_string : list Z :=
  map (fun c => Z.of_nat (Ascii.nat_of_ascii c)) (list_ascii_of_string "kpathsea version 6.4.2").

(* ------------------------------------------------- C's own parsing of environment strings

   The environment and kpathsea's variables are byte strings (Values.io_env, io_kpse); the
   C functions that read them are modelled here, so a value such as FORCE_SOURCE_DATE=01
   or SOURCE_DATE_EPOCH=" 12" means what it means to the binary.
   pdfTeX never calls setlocale (no call in texk/web2c/lib, texk/web2c/pdftexdir or
   texk/kpathsea of r78081), so the C locale's classification applies. *)

(* getenv(3) *)
Definition c_getenv (st : state) (name : string) : option (list Z) :=
  lookup_bytes (bytes_of_string name) (io_env (st_io st)).

(* the C locale's isspace: space, \t \n \v \f \r *)
Definition c_isspace (c : Z) : bool := (c =? 32) || ((9 <=? c) && (c <=? 13)).

Fixpoint skip_space (l : list Z) : list Z :=
  match l with c :: r => if c_isspace c then skip_space r else l | [] => [] end.

(* an optional sign: (negative?, rest) *)
Definition take_sign (l : list Z) : bool * list Z :=
  match l with 45 :: r => (true, r) | 43 :: r => (false, r) | _ => (false, l) end.

(* decimal digits: (value, number of digits, rest) *)
Fixpoint take_digits (l : list Z) (acc : Z) (n : nat) : Z * nat * list Z :=
  match l with
  | c :: r => if (48 <=? c) && (c <=? 57) then take_digits r (acc * 10 + (c - 48)) (S n) else (acc, n, l)
  | [] => (acc, n, [])
  end.

(* glibc strtoull(s, &endptr, 10): (result, the bytes from endptr on, errno = ERANGE).
   No digits: 0, and endptr = s itself. A '-' sign negates in unsigned arithmetic.
   A magnitude above ULLONG_MAX: ULLONG_MAX with ERANGE. *)
Definition two64 : Z := Z.shiftl 1 64.
Definition c_strtoull10 (s : list Z) : Z * list Z * bool :=
  let (neg, t) := take_sign (skip_space s) in
  match take_digits t 0 O with
  | (_, O, _) => (0, s, false)
  | (v, _, rest) => if two64 <=? v then (two64 - 1, rest, true)
                    else ((if neg then Z.modulo (- v) two64 else v), rest, false)
  end.

(* glibc atoi(s) = (int) strtol(s, NULL, 10). A value outside int's range is clamped to
   long's range by strtol and then converted to int (implementation-defined): Stuck, so
   None here means "not modelled" *)
Definition c_atoi (s : list Z) : option Z :=
  let (neg, t) := take_sign (skip_space s) in
  match take_digits t 0 O with
  | (_, O, _) => Some 0
  | (v, _, _) => let z := if neg then - v else v in if in_i32 z then Some z else None
  end.

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

(* The command line C main was measured with (CMain.v, evidence/cmain/): `pdftex -ini`.
   C main's writes, and the externals below that consult the parsed options (topenin's
   optind, getjobname's c_job_name, recorderchangefilename's recorder_enabled,
   open_output's output_directory, synctex's option), are modelled for that command line
   only; any other command line is Stuck at the first of them. *)
Definition argv_measured (st : state) : bool :=
  match io_argv (st_io st) with
  | [a] => if list_eq_dec Z.eq_dec a (bytes_of_string "-ini") then true else false
  | _ => false
  end.

(* texmfmp.c init_start_time: once (start_time_set). SOURCE_DATE_EPOCH set: strtoull,
   FATAL (an error message, exit 1) when *endptr != '\0' or errno != 0 (not modelled:
   Stuck); start_time = epoch (unsigned long long to time_t: implementation-defined above
   LLONG_MAX, Stuck). Unset: start_time = time(NULL), the real clock: the model records
   that start_time is unknown, and whatever reads it is Stuck. The epoch is bounded by
   2^55 so that gmtime's year is far inside int (beyond: not modelled) *)
Definition init_start_time (st : state) : eres :=
  if cstate st CS_start_time_set =? 1 then ok st else
  let st0 := set_cstate st CS_start_time_set 1 in
  match c_getenv st "SOURCE_DATE_EPOCH" with
  | None => ok (set_cstate st0 CS_start_time_kind 2)
  | Some v =>
    match c_strtoull10 v with
    | (u, rest, erange) =>
      if erange || negb (match rest with [] => true | _ => false end)
      then EStk (StExternal "init_start_time: FATAL on an invalid SOURCE_DATE_EPOCH (not modelled)") st0
      else if Z.shiftl 1 63 <=? u then EStk (StConv "SOURCE_DATE_EPOCH to time_t (implementation-defined)") st0
      else if Z.shiftl 1 55 <? u then EStk (StExternal "SOURCE_DATE_EPOCH above 2^55 (not modelled)") st0
      else ok (set_cstate (set_cstate (set_cstate st0 CS_start_time_kind 1) CS_start_time u)
                          CS_source_date_epoch_set 1)
    end
  end.

(* texmfmp.c makepdftime(start_time, start_time_str, utc = true), the string initstarttime
   computes when SOURCE_DATE_EPOCH is set: strftime "D:%Y%m%d%H%M%S" of gmtime (glibc's %Y:
   the year in decimal, unpadded; a gmtime second is never 60), then the offset of local
   time from gmtime, 0 for utc: "Z". Defined for kind 1 (start_time known); for kind 2 the
   string is localtime of the real clock: None (Stuck where it is read) *)
Fixpoint dec_digits (n : nat) (v : Z) (acc : list Z) : list Z :=
  match n with O => acc | S n' => if v <? 10 then (48 + v) :: acc else dec_digits n' (Z.div v 10) ((48 + Z.modulo v 10) :: acc) end.
Definition two_digits (v : Z) : list Z := [48 + Z.div v 10; 48 + Z.modulo v 10].
Definition start_time_str (st : state) : option (list Z) :=
  if negb (cstate st CS_start_time_kind =? 1) then None else
  let e := cstate st CS_start_time in
  let days := Z.div e 86400 in
  let secs := Z.modulo e 86400 in
  let '(y, m, d) := civil_from_days days in
  Some ([68; 58] ++ dec_digits 30 y [] ++ two_digits m ++ two_digits d ++ two_digits (Z.div secs 3600)
        ++ two_digits (Z.modulo (Z.div secs 60) 60) ++ two_digits (Z.modulo secs 60) ++ [90]).

(* gmtime(&t) for 0 <= t <= 2^55, as get_date_and_time stores it *)
Definition put_gmtime (st : state) (e : Z) (a1 a2 a3 a4 : xarg) : eres :=
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
  end.

(* openclose.c open_output, reached through texmfmp.c open_out_or_pipe: fopen(name, "w") in
   the working directory (no -output-directory on the measured command line). The
   environment class is a fresh, empty, writable working directory, in which fopen
   succeeds exactly for a name that is one new path component: non-empty, no '/', not
   "." or "..", at most NAME_MAX = 255 bytes. Any other name (a subdirectory, an absolute
   path, a name opened before) is not modelled: Stuck. (On failure the binary would try
   $TEXMFOUTPUT, a kpathsea variable.) *)
Definition plain_new_name (st : state) (name : list Z) : bool :=
  match name with
  | [] => false
  | _ => negb (existsb (fun c => c =? 47) name)
         && negb (list_eq_dec_bool name [46]) && negb (list_eq_dec_bool name [46; 46])
         && (Z.of_nat (List.length name) <=? 255)
         && negb (existsb (fun hn => list_eq_dec_bool (snd hn) name) (io_files (st_io st)))
         && negb (existsb (fun fc => list_eq_dec_bool (fst fc) name) (io_fs (st_io st)))
  end.


Inductive Stuck_or (A : Type) : Type := Ok (a : A) | Err (s : stuck).
Arguments Ok {A} a. Arguments Err {A} s.

(* ================================================================ spike H.3: the format file

   The externals pdfTeX's format loading and dumping call (tex.ch, texmfmp.h, texmfmp.c,
   openclose.c, writeimg.c, tounicode.c of r78081), modelled from their C source. The
   compressed format is read through zlib (gzdopen/gzread); decompression is outside the
   model (TB-7): the run's identity gives, per path, the decompressed stream (io_gz), and
   what the model dumps is the uncompressed stream gzwrite receives. *)

Definition CS_fullnameoffile : Z := 8.            (* texmfmp.c fullnameoffile: a block id, 0 = NULL *)
Definition CS_image_limit : Z := 9.               (* writeimg.c image_limit (0 in static storage) *)
Definition CS_tounicode_tree : Z := 10.           (* tounicode.c glyph_unicode_tree: 0 = NULL *)

Definition alloc_cells (cs : list cell) (st : state) : option (state * Z) :=
  if heap_cap <=? hp st + 1 then None else
  let b := hp st in
  let st1 := hput (mkst (heap st) (b + 1) (fp st) (fsp st) (st_io st)) b
                  (new_block (Z.max 1 (Z.of_nat (List.length cs))) KUndef) in
  match put_cells cs b 0 st1 with Some st2 => Some (st2, b) | None => None end.

Definition free_block (st : state) (b : Z) : state := hput st b empty_block.

Definition gfile (st : state) (g : Z) : option Z :=
  match cell_at st g 0 with Some (KFile h) => Some h | _ => None end.

Fixpoint lookup_in (h : Z) (l : list (Z * list Z)) : option (list Z) :=
  match l with [] => None | (h', b) :: r => if h =? h' then Some b else lookup_in h r end.
Fixpoint set_in (h : Z) (v : list Z) (l : list (Z * list Z)) : list (Z * list Z) :=
  match l with [] => [(h, v)] | (h', b) :: r => if h =? h' then (h, v) :: r else (h', b) :: set_in h v r end.
Fixpoint drop_in (h : Z) (l : list (Z * list Z)) : list (Z * list Z) :=
  match l with [] => [] | (h', b) :: r => if h =? h' then r else (h', b) :: drop_in h r end.

Fixpoint lookup_find (f m : Z) (name : list Z) (t : list (Z * Z * list Z * list Z)) : option (list Z) :=
  match t with
  | [] => None
  | (f', m', n, r) :: rest => if (f =? f') && (m =? m') && list_eq_dec_bool n name then Some r
                              else lookup_find f m name rest
  end.

(* C's sizeof of an (un)dumped item, by its storage type; texmfmem.h: memoryword and
   twohalves are 8 bytes, fourquarters and fmemoryword 4 *)
Definition item_size (c : ct) : option Z :=
  match c with
  | CU8 | CS8 | CC8 => Some 1 | CU16 | CS16 => Some 2 | CI32 => Some 4
  | CI64 | CW8 | CF64 => Some 8 | CW4 => Some 4 | _ => None
  end.

(* big-endian: the format file's byte order (texmfmp.c do_dump/do_undump swap every item
   on a little-endian host, swap_items) *)
Fixpoint be_value (bs : list Z) (acc : Z) : Z :=
  match bs with [] => acc | b :: r => be_value r (acc * 256 + b) end.
Fixpoint be_bytes (n : nat) (v : Z) (acc : list Z) : list Z :=
  match n with O => acc | S n' => be_bytes n' (Z.shiftr v 8) (Z.land v 255 :: acc) end.

Definition signed_of (bits u : Z) : Z := if Z.testbit u (bits - 1) then u - Z.shiftl 1 bits else u.

(* one undumped item: the cell its bytes make in a cell of storage type c *)
Definition cell_of_bytes (c : ct) (bs : list Z) : option cell :=
  let u := be_value bs 0 in
  match c with
  | CU8 | CC8 | CU16 => Some (KInt u)
  | CS8 => Some (KInt (signed_of 8 u)) | CS16 => Some (KInt (signed_of 16 u))
  | CI32 => Some (KInt (signed_of 32 u)) | CI64 => Some (KInt (signed_of 64 u))
  | CW8 => Some (KWord u 255) | CW4 => Some (KWord u 15)
  | CF64 => (* a NaN's payload is not kept by the model: not modelled *)
            if (Z.land (Z.shiftr u 52) 2047 =? 2047) && negb (Z.land u (Z.ones 52) =? 0) then None
            else Some (KDbl (float_of_bits u))
  | _ => None
  end.

(* one dumped item: its bytes, from a cell of storage type c; an indeterminate byte (a
   never-written cell or word byte) is the binary's garbage: not modelled, None *)
Definition bytes_of_cell (c : ct) (k : cell) : option (list Z) :=
  match item_size c, k with
  | Some n, KInt z => Some (be_bytes (Z.to_nat n) (Z.modulo z (Z.shiftl 1 (8 * n))) [])
  | Some n, KWord bits mask => if mask =? Z.ones n then Some (be_bytes (Z.to_nat n) bits []) else None
  | Some n, KDbl f => match bits_of_float f with Some b => Some (be_bytes (Z.to_nat n) b []) | None => None end
  | _, _ => None
  end.

Fixpoint take (n : nat) (l : list Z) : option (list Z * list Z) :=
  match n with
  | O => Some ([], l)
  | S n' => match l with [] => None | x :: r => match take n' r with Some (a, b) => Some (x :: a, b) | None => None end end
  end.

Fixpoint undump_cells (k : nat) (c : ct) (sz : nat) (bs : list Z) (acc : list cell) : option (list cell * list Z) :=
  match k with
  | O => Some (rev_append acc [], bs)
  | S k' => match take sz bs with
            | Some (item, rest) => match cell_of_bytes c item with
                                   | Some cl => undump_cells k' c sz rest (cl :: acc)
                                   | None => None end
            | None => None
            end
  end.

(* texmfmp.c do_undump(p, sizeof(base), len, fmtfile): gzread of len items, FATAL when
   fewer bytes remain (not modelled: Stuck); swap_items; the items land in consecutive
   cells from base. Returns the new state and the integer values (for the checked forms). *)
Definition do_undump (st : state) (a : xarg) (len : Z) : Stuck_or (state * list cell) :=
  match a, gfile st G_fmtfile with
  | XLoc l c _, Some h =>
    match lsl l, item_size c, lookup_in h (io_in (st_io st)) with
    | None, Some n, Some bs =>
      if (len <? 0) || negb (in_i32 (n * len)) then Err (StConv "undump: item_size * nitems outside int") else
      match undump_cells (Z.to_nat len) c (Z.to_nat n) bs [] with
      | None => Err (StExternal "do_undump: FATAL (short format file) or an item not modelled")
      | Some (cells, rest) =>
        match put_cells cells (lb l) (Values.lo l) st with
        | Some st1 => Ok (set_io st1 (io_set_in (st_io st1) (set_in h rest (io_in (st_io st1)))), cells)
        | None => Err (StBounds "undump")
        end
      end
    | _, _, _ => Err (StType "undump: base or fmtfile")
    end
  | _, _ => Err (StType "undump arguments")
  end.

Definition emit_handle (h : Z) (bytes : list Z) (st : state) : state :=
  set_io st (io_set_out (st_io st) (out_append h bytes (io_out (st_io st)))).

(* texmfmp.c do_dump(p, sizeof(base), len, fmtfile): swap_items, gzwrite (a write failure
   is outside the environment class), swap back *)
Definition do_dump (st : state) (a : xarg) (len : Z) : Stuck_or state :=
  match a, gfile st G_fmtfile with
  | XLoc l c _, Some h =>
    match lsl l, item_size c, read_cells (Z.to_nat len) (lb l) (Values.lo l) st with
    | None, Some n, Some ks =>
      if (len <? 0) || negb (in_i32 (n * len)) then Err (StConv "dump: item_size * nitems outside int") else
      match fold_right (fun k acc => match bytes_of_cell c k, acc with
                                     | Some b, Some r => Some (b ++ r) | _, _ => None end) (Some []) ks with
      | Some bytes => Ok (emit_handle h bytes st)
      | None => Err (StUninit)
      end
    | _, _, None => Err (StBounds "dump")
    | _, _, _ => Err (StType "dump: base")
    end
  | _, _ => Err (StType "dump arguments")
  end.

(* openclose.c open_input(&f, DUMP_FORMAT = kpse_fmt_format, "rb"), then gzdopen: the
   texmfmp.h macro wopenin. *f_ptr = NULL; free(fullnameoffile), = NULL; no
   -output-directory (measured command line); filefmt >= 0, must_exist = 1 (not the tex
   or vf format); fname = kpse_find_file(nameoffile + 1, kpse_fmt_format, 1) (the run's
   table); found: fullnameoffile = xstrdup(fname); a leading "./" is removed unless
   nameoffile + 1 starts with one; xfopen (the run's file system must hold it);
   free(nameoffile); namelength = strlen(fname); nameoffile = xmalloc(namelength + 2) (its
   cell 0 never written); strcpy(nameoffile + 1, fname); recorder off (measured command
   line); gzdopen of the stream. Not found: false, f stays NULL *)
Definition wopenin (st : state) (a : xarg) : eres :=
  if negb (argv_measured st) then EStk (StExternal "wopenin: a command line other than the measured one") st else
  match a, gptr st G_nameoffile with
  | XLoc l CFILE _, Some (nb, 0) =>
    match cstring 100000 nb 1 st with
    | None => EStk (StType "wopenin: nameoffile") st
    | Some name =>
      let fb0 := cstate st CS_fullnameoffile in
      let st0 := set_cstate (if fb0 =? 0 then st else free_block st fb0) CS_fullnameoffile 0 in
      match write_loc st0 CFILE l VN with
      | WStk s0 => EStk s0 st0
      | WOk st1 =>
        match lookup_find 10 1 name (io_kpsefind (st_io st1)) with
        | None => EStk (StExternal "kpse_find_file: a query not in the run's table") st1
        | Some [] => EOk (VI TI32 0) st1
        | Some fname0 =>
          match alloc_cells (map KInt (fname0 ++ [0])) st1 with
          | None => EStk (StOther "heap blocks exhausted") st1
          | Some (st2, fb) =>
            let st3 := set_cstate st2 CS_fullnameoffile fb in
            let fname := match fname0, name with
                         | 46 :: 47 :: _, 46 :: 47 :: _ => fname0
                         | 46 :: 47 :: rest, _ => rest
                         | _, _ => fname0 end in
            match lookup_bytes fname (io_gz (st_io st3)) with
            | None => EStk (StExternal "xfopen: the run's file system does not hold the file kpathsea found") st3
            | Some stream =>
              match alloc_cells (KUndef :: map KInt (fname ++ [0])) (free_block st3 nb) with
              | None => EStk (StOther "heap blocks exhausted") st3
              | Some (st4, nb') =>
                match gput st4 G_nameoffile (KPtr nb' 0) with
                | None => EStk (StBounds "nameoffile") st4
                | Some st5 =>
                  match gput st5 G_namelength (KInt (Z.of_nat (List.length fname))) with
                  | None => EStk (StBounds "namelength") st5
                  | Some st6 =>
                    let x0 := st_io st6 in
                    let h := io_next_handle x0 in
                    let x1 := io_set_files x0 ((h, fname) :: io_files x0) (h + 1) in
                    let st7 := set_io st6 (io_set_in x1 ((h, stream) :: io_in x1)) in
                    match write_loc st7 CFILE l (VFile h) with
                    | WOk st8 => EOk (VI TI32 1) st8
                    | WStk s0 => EStk s0 st7
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  | _, _ => EStk (StType "wopenin arguments") st
  end.

(* texmfmp.h wopenout(f) = open_output(&f, "wb") && gzdopen && gzsetparams(f, 1,
   Z_DEFAULT_STRATEGY) == Z_OK: open_output as for aopenout (the same environment class
   and name restriction); the model keeps the uncompressed stream gzwrite receives *)
Definition wopenout (st : state) (a : xarg) : eres :=
  if negb (argv_measured st) then EStk (StExternal "wopenout: a command line other than the measured one") st else
  match a, gptr st G_nameoffile with
  | XLoc l CFILE _, Some (nb, no) =>
    match cstring 100000 nb (no + 1) st with
    | Some name =>
      if negb (plain_new_name st name) then EStk (StExternal "wopenout: not a new single-component name (not modelled)") st else
      let x0 := st_io st in
      let h := io_next_handle x0 in
      let st1 := set_io st (io_set_files x0 ((h, name) :: io_files x0) (h + 1)) in
      match write_loc st1 CFILE l (VFile h) with
      | WOk st2 => EOk (VI TI32 1) st2
      | WStk s0 => EStk s0 st1
      end
    | None => EStk (StType "wopenout name") st
    end
  | _, _ => EStk (StType "wopenout arguments") st
  end.

Fixpoint all_in_range (lo hi : Z) (ks : list cell) : bool :=
  match ks with
  | [] => true
  | KInt v :: r => (lo <=? v) && (v <=? hi) && all_in_range lo hi r
  | _ :: _ => false
  end.

(* tounicode.c undumptounicode, the records of the glyph-to-unicode AVL tree as the dump has
   them: dumpcharptr(name) (an integer x = strlen + 1, then x bytes, the NUL included);
   generic_dump(code) (an integer); if code = UNI_STRING (-2), dumpcharptr(unicode_seq).
   A NULL name or sequence is pdftex_fail; a name equal to an earlier one fails avl_probe's
   assert: both Stuck. The model keeps the records' bytes and re-dumps them in the order
   dumptounicode's in-order traversal gives, which is the order of strcmp on the names; it
   requires the undumped names to be strictly increasing (then that order is the file's
   order) and every string to have no NUL before its last byte (else strlen would differ),
   and is Stuck otherwise. *)
Definition CS_tounicode_count : Z := 11.
Definition CS_tounicode_len : Z := 12.

Fixpoint lt_bytes (a b : list Z) : bool :=          (* strcmp(a, b) < 0, unsigned bytes *)
  match a, b with
  | [], [] => false | [], _ :: _ => true | _ :: _, [] => false
  | x :: a', y :: b' => if x <? y then true else if y <? x then false else lt_bytes a' b'
  end.

Definition cstring_ok (bs : list Z) : bool :=        (* ends in its only NUL *)
  match rev' bs with 0 :: r => negb (existsb (fun c => c =? 0) r) | _ => false end.

(* one dumpcharptr record: (its bytes, the string, the rest) *)
Definition take_charptr (bs : list Z) : option (list Z * list Z * list Z) :=
  match take 4 bs with
  | Some (b4, r1) =>
    let x := signed_of 32 (be_value b4 0) in
    if (x <=? 0) || (Z.shiftl 1 20 <? x) then None else
    match take (Z.to_nat x) r1 with
    | Some (str, r2) => if cstring_ok str then Some (b4 ++ str, str, r2) else None
    | None => None
    end
  | None => None
  end.

Fixpoint parse_tounicode (n : nat) (bs : list Z) (prev : option (list Z)) (acc : list Z)
  : option (list Z * list Z) :=                       (* (record bytes, reversed), rest *)
  match n with
  | O => Some (acc, bs)
  | S n' =>
    match take_charptr bs with
    | Some (rec1, name, r1) =>
      if match prev with Some p => negb (lt_bytes p name) | None => false end then None else
      match take 4 r1 with
      | Some (cb, r2) =>
        if signed_of 32 (be_value cb 0) =? -2 then
          match take_charptr r2 with
          | Some (rec2, _, r3) => parse_tounicode n' r3 (Some name) (rev_append (rec1 ++ cb ++ rec2) acc)
          | None => None
          end
        else parse_tounicode n' r2 (Some name) (rev_append (rec1 ++ cb) acc)
      | None => None
      end
    | None => None
    end
  end.

Definition undump_result (r : Stuck_or (state * list cell)) (st : state) : eres :=
  match r with Ok (st', _) => ok st' | Err s0 => EStk s0 st end.

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
        let put v := match put_cell st b o (KInt v) with Some st' => ok st' | None => EStk (StBounds "setupboundvariable") st end in
        match lookup_bytes name (io_kpse (st_io st)) with
        | None => put dflt
        | Some e =>
          match c_atoi e with
          | None => EStk (StConv "setupboundvariable: atoi of a value outside int") st
          | Some c => if (c <? 0) || ((c =? 0) && (0 <? dflt))
                      then EStk (StExternal "setupboundvariable: bad value warning not modelled") st
                      else put c
          end
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
  (* texmfmp.c init_start_time, above *)
  else if x =? X_initstarttime then init_start_time st
  (* texmfmp.c input_line; only the terminal is modelled at checkpoint 2 *)
  else if x =? X_inputln then
    match args with
    | XVal (VFile 0) :: _ => input_line_stdin st
    | _ => EStk (StExternal "inputln on a file (not modelled yet)") st
    end
  (* texmfmp.c topenin: buffer[first] = 0; with no arguments after the options
     (optind = argc on the measured command line) the copy loop does not run; then
     `for (last = first; buffer[last]; ++last)` stops at once, the trailing-space loop
     leaves last = first, and the xord loop over [first, last) is empty: last = first *)
  else if x =? X_topenin then
    if negb (argv_measured st) then EStk (StExternal "topenin: a command line other than the measured one") st else
    match gint st G_first, gptr st G_buffer with
    | Some first, Some (bb, bo) =>
      match put_cell st bb (bo + first) (KInt 0) with
      | Some st1 => match gput st1 G_last (KInt first) with
                    | Some st2 => ok st2
                    | None => EStk (StBounds "topenin last") st1 end
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
  (* texmfmp.h dateandtime(i,j,k,l) = get_date_and_time(&i,&j,&k,&l):
     getenv("FORCE_SOURCE_DATE") STREQ "1" (exactly the bytes "1"): init_start_time(),
     gmtime(&start_time), FORCE_SOURCE_DATE_set = true; start_time from time(NULL) (no
     SOURCE_DATE_EPOCH) is the real clock: Stuck. Otherwise localtime(time(NULL)): the real
     clock and the time zone, a nondeterministic input (O-5): Stuck. (It also installs a
     SIGINT handler; the environment class delivers no signals.) *)
  else if x =? X_dateandtime then
    match c_getenv st "FORCE_SOURCE_DATE", args with
    | Some [49], [a1; a2; a3; a4] =>
      match init_start_time st with
      | EOk _ st1 =>
        if cstate st1 CS_start_time_kind =? 1
        then put_gmtime (set_cstate st1 CS_force_source_date_set 1) (cstate st1 CS_start_time) a1 a2 a3 a4
        else EStk (StExternal "dateandtime: FORCE_SOURCE_DATE=1 without SOURCE_DATE_EPOCH: gmtime(time(NULL)), the real clock") st1
      | r => r
      end
    | Some [49], _ => EStk (StType "dateandtime arity") st
    | _, _ => EStk (StExternal "dateandtime: localtime(time(NULL)), the real clock and time zone (O-5)") st
    end
  (* texmfmp.c get_seconds_and_micros: gettimeofday(&tv, NULL); *seconds = tv.tv_sec;
     *micros = tv.tv_usec. The real clock is nondeterministic, so its readings are an
     explicit input of the run (Values.io_clock, consumed in call order) and part of the
     run's identity; with none left the run is Stuck. tv_sec (time_t) to integer is
     implementation-defined outside int (after 2038-01-19): Stuck *)
  else if x =? X_secondsandmicros then
    match io_clock (st_io st), args with
    | (sec, usec) :: rest, [a1; a2] =>
      if negb (in_i32 sec) then EStk (StConv "gettimeofday tv_sec to integer") st
      else if negb (in_range 0 999999 usec) then EStk (StType "a clock reading with tv_usec outside [0, 999999]") st
      else
      let st0 := set_io st (io_set_clock (st_io st) rest) in
      match put_int_at st0 a1 sec with
      | Some s1 => match put_int_at s1 a2 usec with Some s2 => ok s2 | None => EStk (StType "secondsandmicros") s1 end
      | None => EStk (StType "secondsandmicros") st0
      end
    | [], _ => EStk (StExternal "gettimeofday: no clock reading supplied (the clock is an input of the run)") st
    | _, _ => EStk (StType "secondsandmicros arity") st
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
    if negb (argv_measured st) then EStk (StExternal "getjobname: a command line other than the measured one") st else
    match args with
    | [a] => match xint st a with Some n => EOk (VI TI32 n) st | None => EStk (StType "getjobname") st end
    | _ => EStk (StType "getjobname arity") st
    end
  (* openclose.c recorder_change_filename: returns at once, the recorder being off
     (no -recorder on the command line) *)
  else if x =? X_recorderchangefilename then
    if argv_measured st then ok st else EStk (StExternal "recorderchangefilename: a command line other than the measured one") st
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
        if negb (argv_measured st) then EStk (StExternal "aopenout: a command line other than the measured one") st else
        if negb (plain_new_name st name) then EStk (StExternal "aopenout: not a new single-component name (not modelled)") st else
        let x0 := st_io st in
        let h := io_next_handle x0 in
        let st1 := set_io st (io_set_files x0 ((h, name) :: io_files x0) (h + 1)) in
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
  (* cpascal.h ucharcast(x) ((unsigned char) (x)): conversion to unsigned char, modulo 256
     (C11 6.3.1.3), then promoted to int *)
  else if x =? X_ucharcast then
    match args with
    | [a] => match xint st a with Some z => EOk (VI TI32 (Z.modulo z 256)) st
                                | None => EStk (StType "ucharcast") st end
    | _ => EStk (StType "ucharcast arity") st
    end
  (* C strlen(s): the number of bytes before the NUL, as size_t (the translator types it
     as a 64-bit integer) *)
  else if x =? X_strlen then
    match args with
    | [a] => match xstring st a with Some b => EOk (VI TI64 (Z.of_nat (List.length b))) st
                                   | None => EStk (StType "strlen") st end
    | _ => EStk (StType "strlen arity") st
    end
  (* C strcpy(d, s): the bytes of s and its NUL to d's cells; d is returned. Overlapping
     objects are undefined: here, the same block is Stuck *)
  else if x =? X_strcpy then
    match args with
    | [d; s0] => match xptr st d, xstring st s0, xptr st s0 with
                 | Some (VP db dofs), Some b, Some (VP sb _) =>
                   if db =? sb then EStk (StOther "strcpy within one object") st else
                   match put_cells (map KInt (b ++ [0])) db dofs st with
                   | Some st1 => EOk (VP db dofs) st1
                   | None => EStk (StBounds "strcpy") st
                   end
                 | _, _, _ => EStk (StType "strcpy arguments") st
                 end
    | _ => EStk (StType "strcpy arity") st
    end
  (* texmfmp.c getcreationdate: initstarttime() (already run at start-up: a no-op); len =
     strlen(start_time_str); if (unsigned)(poolptr + len) >= (unsigned) poolsize then
     poolptr = poolsize and return; else memcpy into strpool at poolptr, poolptr += len *)
  else if x =? X_getcreationdate then
    if negb (cstate st CS_start_time_set =? 1) then EStk (StExternal "getcreationdate before initstarttime (not modelled)") st else
    match start_time_str st, gptr st G_strpool, gint st G_poolptr, gint st G_poolsize with
    | Some str, Some (pb, po), Some pp, Some ps =>
      let len := Z.of_nat (List.length str) in
      if (pp <? 0) || (ps <? 0) then EStk (StConv "getcreationdate: unsigned comparison of a negative value") st else
      if ps <=? pp + len then
        match gput st G_poolptr (KInt ps) with Some st1 => ok st1 | None => EStk (StBounds "getcreationdate") st end
      else
        match put_cells (map KInt str) pb (po + pp) st with
        | Some st1 => match gput st1 G_poolptr (KInt (pp + len)) with Some st2 => ok st2 | None => EStk (StBounds "getcreationdate") st1 end
        | None => EStk (StBounds "getcreationdate") st
        end
    | None, _, _, _ => EStk (StExternal "getcreationdate: start_time_str of the real clock (localtime)") st
    | _, _, _, _ => EStk (StType "getcreationdate globals") st
    end
  (* ---- spike H.3: the format file (see wopenin and do_undump above) ---- *)
  else if x =? X_wopenin then
    match args with [a] => wopenin st a | _ => EStk (StType "wopenin arity") st end
  else if x =? X_wopenout then
    match args with [a] => wopenout st a | _ => EStk (StType "wopenout arity") st end
  (* texmfmp.h wclose(f) = gzclose(f): a read stream is dropped; a written one keeps its
     bytes; gzclose(NULL) is an error return, no effect *)
  else if x =? X_wclose then
    match args with
    | [XLoc l _ _] => match read_loc st TFILE l with
                      | LdOk (VFile h) => ok (set_io st (io_set_in (st_io st) (drop_in h (io_in (st_io st)))))
                      | LdOk VN => ok st
                      | _ => EStk (StType "wclose") st end
    | _ => EStk (StType "wclose arity") st
    end
  (* texmfmp.h undumpthings(base, len) = do_undump(&base (as a char pointer), sizeof (base), len, fmtfile);
     undumpint = undumphh = generic_undump(x) = undumpthings(x, 1) (REGFIX is not defined) *)
  else if x =? X_undumpthings then
    match args with
    | [b; n] => match xint st n with Some len => undump_result (do_undump st b len) st
                                   | None => EStk (StType "undumpthings length") st end
    | _ => EStk (StType "undumpthings arity") st
    end
  else if (x =? X_undumpint) || (x =? X_undumphh) then
    match args with [b] => undump_result (do_undump st b 1) st | _ => EStk (StType "undump arity") st end
  (* texmfmp.h undumpcheckedthings(low, high, base, len): undumpthings, then FATAL5 if an
     item is < low or > high (not modelled: Stuck); undumpuppercheckthings(high, base, len)
     the same with no lower bound *)
  else if x =? X_undumpcheckedthings then
    match args with
    | [lo; hi; b; n] =>
      match xint st lo, xint st hi, xint st n with
      | Some lo', Some hi', Some len =>
        match do_undump st b len with
        | Ok (st1, ks) => if all_in_range lo' hi' ks then ok st1
                          else EStk (StExternal "undumpcheckedthings: FATAL on an item out of range (not modelled)") st1
        | Err s0 => EStk s0 st
        end
      | _, _, _ => EStk (StType "undumpcheckedthings") st
      end
    | _ => EStk (StType "undumpcheckedthings arity") st
    end
  else if x =? X_undumpuppercheckthings then
    match args with
    | [hi; b; n] =>
      match xint st hi, xint st n with
      | Some hi', Some len =>
        match do_undump st b len with
        | Ok (st1, ks) => if all_in_range (- two64) hi' ks then ok st1
                          else EStk (StExternal "undumpuppercheckthings: FATAL on an item out of range (not modelled)") st1
        | Err s0 => EStk s0 st
        end
      | _, _ => EStk (StType "undumpuppercheckthings") st
      end
    | _ => EStk (StType "undumpuppercheckthings arity") st
    end
  (* texmfmp.h dumpthings(base, len) = do_dump(&base (as a char pointer), sizeof (base), len, fmtfile);
     dumphh = generic_dump(x) = dumpthings(x, 1) *)
  else if x =? X_dumpthings then
    match args with
    | [b; n] => match xint st n with
                | Some len => match do_dump st b len with Ok st1 => ok st1 | Err s0 => EStk s0 st end
                | None => EStk (StType "dumpthings length") st end
    | _ => EStk (StType "dumpthings arity") st
    end
  else if x =? X_dumphh then
    match args with
    | [b] => match do_dump st b 1 with Ok st1 => ok st1 | Err s0 => EStk s0 st end
    | _ => EStk (StType "dumphh arity") st
    end
  (* texmfmp.h dumpint(x): integer x_val = (x); generic_dump(x_val): 4 bytes; a value
     outside int is an implementation-defined conversion: Stuck *)
  else if x =? X_dumpint then
    match args, gfile st G_fmtfile with
    | [a], Some h => match xint st a with
                     | Some z => if in_i32 z then ok (emit_handle h (be_bytes 4 (Z.modulo z two32) []) st)
                                 else EStk (StConv "dumpint: to integer") st
                     | None => EStk (StType "dumpint") st end
    | _, _ => EStk (StType "dumpint arguments") st
    end
  (* writeimg.c undumpimagemeta(major, minor, inclusion level): undumpinteger(image_limit);
     image_array = xtalloc(image_limit, image_entry); undumpinteger(cur_image); then one
     record per image, each re-read from its file: with images, not modelled (Stuck) *)
  else if x =? X_undumpimagemeta then
    match gfile st G_fmtfile with
    | Some h =>
      match lookup_in h (io_in (st_io st)) with
      | Some bs =>
        match take 4 bs with
        | Some (b1, r1) =>
          let lim := signed_of 32 (be_value b1 0) in
          match take 4 r1 with
          | Some (b2, r2) =>
            if negb (be_value b2 0 =? 0) then EStk (StExternal "undumpimagemeta: a format with images (not modelled)") st
            else if (lim <? 0) || (Z.shiftl 1 20 <? lim) then EStk (StExternal "undumpimagemeta: image_limit outside the modelled range") st
            else ok (set_cstate (set_io st (io_set_in (st_io st) (set_in h r2 (io_in (st_io st))))) CS_image_limit lim)
          | None => EStk (StExternal "do_undump: FATAL (short format file, not modelled)") st
          end
        | None => EStk (StExternal "do_undump: FATAL (short format file, not modelled)") st
        end
      | None => EStk (StType "undumpimagemeta stream") st
      end
    | None => EStk (StType "undumpimagemeta fmtfile") st
    end
  (* writeimg.c dumpimagemeta: dumpinteger(image_limit); cur_image = image_ptr - image_array
     (0: no image was ever read, since every external that reads one is Stuck) *)
  else if x =? X_dumpimagemeta then
    match gfile st G_fmtfile with
    | Some h => ok (emit_handle h (be_bytes 4 (Z.modulo (cstate st CS_image_limit) two32) [] ++ [0; 0; 0; 0]) st)
    | None => EStk (StType "dumpimagemeta fmtfile") st
    end
  (* tounicode.c undumptounicode: generic_undump(remaining); 0: return; else an AVL tree
     (not modelled: Stuck) *)
  else if x =? X_undumptounicode then
    match gfile st G_fmtfile with
    | Some h =>
      match lookup_in h (io_in (st_io st)) with
      | Some bs => match take 4 bs with
                   | Some (b1, r1) =>
                     let cnt := signed_of 32 (be_value b1 0) in
                     let st1 := set_io st (io_set_in (st_io st) (set_in h r1 (io_in (st_io st)))) in
                     if cnt =? 0 then ok st1
                     else if (cnt <? 0) || negb (cstate st CS_tounicode_tree =? 0) || (Z.shiftl 1 20 <? cnt)
                     then EStk (StExternal "undumptounicode: a negative count, a second tree, or more than 2^20 records (not modelled)") st
                     else
                     match parse_tounicode (Z.to_nat cnt) r1 None [] with
                     | None => EStk (StExternal "undumptounicode: a record not modelled (NULL string, inner NUL, names not strictly increasing, short file)") st
                     | Some (racc, rest) =>
                       let raw := rev' racc in
                       match alloc_cells (map KInt raw) st with
                       | None => EStk (StOther "heap blocks exhausted") st
                       | Some (st2, b) =>
                         let st3 := set_io st2 (io_set_in (st_io st2) (set_in h rest (io_in (st_io st2)))) in
                         ok (set_cstate (set_cstate (set_cstate st3 CS_tounicode_tree b) CS_tounicode_count cnt)
                                        CS_tounicode_len (Z.of_nat (List.length raw)))
                       end
                     end
                   | None => EStk (StExternal "do_undump: FATAL (short format file, not modelled)") st end
      | None => EStk (StType "undumptounicode stream") st
      end
    | None => EStk (StType "undumptounicode fmtfile") st
    end
  (* tounicode.c dumptounicode: NULL tree: count 0; else avl_count and each record in order
     (the undumped records, kept in that order, see parse_tounicode; no external that adds
     to the tree is modelled) *)
  else if x =? X_dumptounicode then
    match gfile st G_fmtfile with
    | Some h =>
      let b := cstate st CS_tounicode_tree in
      if b =? 0 then ok (emit_handle h [0; 0; 0; 0] st) else
      match read_cells (Z.to_nat (cstate st CS_tounicode_len)) b 0 st with
      | Some ks =>
        match fold_right (fun k acc => match k, acc with KInt v, Some r => Some (v :: r) | _, _ => None end) (Some []) ks with
        | Some raw => ok (emit_handle h (be_bytes 4 (cstate st CS_tounicode_count) [] ++ raw) st)
        | None => EStk (StType "dumptounicode records") st
        end
      | None => EStk (StBounds "dumptounicode") st
      end
    | None => EStk (StType "dumptounicode fmtfile") st
    end
  (* C strcmp(a, b): 0 when the two strings are equal; when they differ glibc returns a
     non-zero value whose magnitude is the library's: not modelled (Stuck) *)
  else if x =? X_strcmp then
    match args with
    | [a; b] => match xstring st a, xstring st b with
                | Some sa, Some sb => if list_eq_dec_bool sa sb then EOk (VI TI32 0) st
                                      else EStk (StExternal "strcmp of different strings (its value is glibc's)") st
                | _, _ => EStk (StType "strcmp arguments") st end
    | _ => EStk (StType "strcmp arity") st
    end
  else stuck_ext x st.
