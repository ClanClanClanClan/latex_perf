(* Driver for the extracted PS program (spike H.2).

   usage: ps.exe FUEL SPEC STDIN

   SPEC is the run's identity besides the program: one item per line,
     argv0 NAME          argv[0], the program name as invoked (required)
     argv ARG            the command line after the program name, in order
     env NAME=VALUE      the process environment as getenv(3) sees it
     kpse NAME=VALUE     what kpse_var_value(NAME) returns in the pinned image for this
                         environment (measured; see evidence/inirun/kpsevars.txt)
     clock SEC USEC      one gettimeofday(2) reading, in call order
     charsigned 0|1      plain char: 0 = unsigned (aarch64), 1 = signed (x86_64)
     cwd PATH            the working directory (a canonical absolute path)
     fsfile PATH=LOCAL   the file-system snapshot (Values.fsent; PATH canonical, without
                         '='): a readable non-directory whose bytes are LOCAL's
     fsexists PATH       a readable non-directory whose bytes the snapshot does not hold
     fslist PATH=N1/N2/...   a directory and its complete listing (without . and ..)
     fsdir PATH          a directory whose listing the snapshot does not hold
     fsabsent PATH       stat fails (ENOENT)
     kfmt F SSO MK SUF ALT PATH   kpse_format_info[F] (Values.kfmt): suffix_search_only
                         SSO and "make_tex would run a program" MK (0/1), the suffix and
                         alt_suffix lists (comma-separated, or - for none), the search path
     gzfile PATH=LOCAL   the file PATH of the run's file system, read through zlib: LOCAL
                         holds the bytes gzread returns (decompressed outside the model, TB-7)
   Values are passed to the model as raw bytes: every C parsing of them (STREQ, strtoull,
   atoi) is in Boundary.v, not here. Any other line is an error (exit 2).
   STDIN is a file whose bytes are the program's standard input, unchanged. *)
let z = Big_int_Z.big_int_of_int
let bytes_of s = Stdlib.List.init (Stdlib.String.length s) (fun i -> z (Stdlib.Char.code (Stdlib.String.get s i)))
let die m = prerr_endline ("ps.exe: " ^ m); exit 2
let dec s = (* a decimal integer, optionally negative; nothing else *)
  let n = Stdlib.String.length s in
  let ok = n > 0 && Stdlib.String.for_all (fun c -> c >= '0' && c <= '9')
             (if Stdlib.String.get s 0 = '-' then Stdlib.String.sub s 1 (n - 1) else s) && s <> "-" in
  if not ok then die ("not a decimal integer: " ^ s);
  Big_int_Z.big_int_of_string s
let () =
  if Stdlib.Array.length Sys.argv <> 4 then die "usage: ps.exe FUEL SPEC STDIN";
  let fuel = match int_of_string_opt Sys.argv.(1) with Some f when f > 0 -> f | _ -> die "FUEL" in
  let argv0 = ref None and argv = ref [] and env = ref [] and kpse = ref [] and clock = ref [] and signed = ref None in
  let gz = ref [] and cwd = ref None and fs = ref [] and kfmt = ref [] in
  let canonical p = (* "/" or "/a/b": no empty, ".", ".." component, no trailing slash, no '=' *)
    p = "/" || (Stdlib.String.length p > 1 && Stdlib.String.get p 0 = '/'
                && not (Stdlib.String.contains p '=')
                && Stdlib.List.for_all (fun c -> c <> "" && c <> "." && c <> "..")
                     (Stdlib.List.tl (Stdlib.String.split_on_char '/' p))) in
  let addfs path e =
    if not (canonical path) then die ("not a canonical path: " ^ path);
    if Stdlib.List.mem_assoc path !fs then die ("two snapshot entries for " ^ path);
    fs := (path, e) :: !fs in
  let pathval rest = match Stdlib.String.index_opt rest '=' with
    | Some i -> (Stdlib.String.sub rest 0 i, Stdlib.String.sub rest (i + 1) (Stdlib.String.length rest - i - 1))
    | None -> die ("no '=' in " ^ rest) in
  let lst s = if s = "-" then [] else Stdlib.List.map bytes_of (Stdlib.String.split_on_char ',' s) in
  let ic = open_in_bin Sys.argv.(2) in
  let kv rest = match Stdlib.String.index_opt rest '=' with
    | Some i -> (bytes_of (Stdlib.String.sub rest 0 i),
                 bytes_of (Stdlib.String.sub rest (i + 1) (Stdlib.String.length rest - i - 1)))
    | None -> die ("no '=' in " ^ rest) in
  (try while true do
     let l = input_line ic in
     match Stdlib.String.index_opt l ' ' with
     | None -> if l <> "" then die ("bad spec line: " ^ l)
     | Some i ->
       let key = Stdlib.String.sub l 0 i and rest = Stdlib.String.sub l (i + 1) (Stdlib.String.length l - i - 1) in
       (match key with
        | "argv0" -> if !argv0 <> None then die "two argv0 lines"; argv0 := Some (bytes_of rest)
        | "argv" -> argv := bytes_of rest :: !argv
        | "env" -> env := kv rest :: !env
        | "kpse" -> kpse := kv rest :: !kpse
        | "clock" -> (match Stdlib.String.split_on_char ' ' rest with
                      | [s; u] -> clock := (dec s, dec u) :: !clock
                      | _ -> die ("bad clock line: " ^ l))
        | "cwd" -> if not (canonical rest) then die ("cwd is not canonical: " ^ rest); cwd := Some rest
        | "fsfile" -> let (pth, local) = pathval rest in
                      addfs pth (KTypes.FsFile (Some (bytes_of (In_channel.with_open_bin local In_channel.input_all))))
        | "fsexists" -> addfs rest (KTypes.FsFile None)
        | "fsdir" -> addfs rest (KTypes.FsDir None)
        | "fslist" -> let (pth, names) = pathval rest in
                      let ns = Stdlib.List.filter (fun n -> n <> "") (Stdlib.String.split_on_char '/' names) in
                      if Stdlib.List.exists (fun n -> n = "." || n = "..") ns then die ("fslist with . or ..: " ^ l);
                      addfs pth (KTypes.FsDir (Some (Stdlib.List.map bytes_of ns)))
        | "fsabsent" -> addfs rest KTypes.FsAbsent
        | "kfmt" -> (match Stdlib.String.split_on_char ' ' rest with
                     | [f; sso; mk; suf; alt; path] ->
                       let b01 x = match x with "0" -> false | "1" -> true | _ -> die ("kfmt: 0 or 1: " ^ l) in
                       let f = dec f in
                       if Stdlib.List.exists (fun (g, _) -> Big_int_Z.eq_big_int g f) !kfmt then die ("two kfmt lines for one format: " ^ l);
                       kfmt := (f, { KTypes.kf_path = bytes_of path; kf_suffix = lst suf; kf_alt = lst alt;
                                     kf_sso = b01 sso; kf_mktex = b01 mk }) :: !kfmt
                     | _ -> die ("bad kfmt line: " ^ l))
        | "gzfile" -> (match Stdlib.String.index_opt rest '=' with
                       | Some i -> let path = Stdlib.String.sub rest 0 i
                                   and local = Stdlib.String.sub rest (i + 1) (Stdlib.String.length rest - i - 1) in
                                   gz := (bytes_of path, bytes_of (In_channel.with_open_bin local In_channel.input_all)) :: !gz
                       | None -> die ("bad gzfile line: " ^ l))
        | "charsigned" -> (match rest with "0" -> signed := Some false | "1" -> signed := Some true
                           | _ -> die "charsigned is 0 or 1")
        | _ -> die ("unknown spec key: " ^ key))
   done with End_of_file -> close_in ic);
  let signed = match !signed with Some b -> b | None -> die "the spec must say charsigned 0 or 1" in
  let stdin_bytes = In_channel.with_open_bin Sys.argv.(3) In_channel.input_all in
  let io = { Values.io_out = []; io_stdin = bytes_of stdin_bytes;
             io_argv0 = (match !argv0 with Some a -> a | None -> die "the spec must give argv0");
             io_argv = Stdlib.List.rev !argv;
             io_char_signed = signed; io_files = []; io_next_handle = z 3;
             io_fs = Stdlib.List.rev_map (fun (p, e) -> (bytes_of p, e)) !fs;
             io_env = Stdlib.List.rev !env; io_kpse = Stdlib.List.rev !kpse;
             io_cwd = (match !cwd with Some c -> bytes_of c | None -> die "the spec must give cwd");
             io_kfmt = Stdlib.List.rev !kfmt; io_kp = { KTypes.kp_db = None; kp_map = None };
             io_in = []; io_eof = []; io_gz = Stdlib.List.rev !gz;
             io_clock = Stdlib.List.rev !clock; io_cstate = [] } in
  let nclock = Stdlib.List.length !clock in
  (match Sys.getenv_opt "PS_COMPACT" with
   | Some k -> let n = ref 0 and k = int_of_string k in
     ignore (Gc.create_alarm (fun () -> incr n; if !n mod k = 0 then Gc.compact ()))
   | None -> ());
  let t0 = Unix.gettimeofday () in
  let r = try Main0.run fuel io with
    | Stack_overflow -> print_endline "RESULT: model resource limit: OCaml stack overflow (no verdict)"; exit 3
    | Out_of_memory -> print_endline "RESULT: model resource limit: out of memory (no verdict)"; exit 3 in
  let t1 = Unix.gettimeofday () in
  let show st =
    (match Sys.getenv_opt "PS_DUMPDIR" with
     | Some d -> Stdlib.List.iter (fun (h, bs) ->
         let oc = open_out_bin (Filename.concat d ("handle-" ^ Big_int_Z.string_of_big_int h)) in
         Stdlib.List.iter (fun b -> output_char oc (Stdlib.Char.chr (Big_int_Z.int_of_big_int b))) (Stdlib.List.rev bs);
         close_out oc) st.Values.st_io.Values.io_out;
       Stdlib.List.iter (fun (h, name) ->
         Printf.printf "--- file handle %s = %s\n" (Big_int_Z.string_of_big_int h)
           (Stdlib.String.concat "" (Stdlib.List.map (fun b -> Stdlib.String.make 1 (Stdlib.Char.chr (Big_int_Z.int_of_big_int b))) name)))
         st.Values.st_io.Values.io_files
     | None -> ());
    Printf.printf "--- stdin bytes not read: %d\n" (Stdlib.List.length st.Values.st_io.Values.io_stdin);
    Printf.printf "--- clock readings used: %d of %d\n" (nclock - Stdlib.List.length st.Values.st_io.Values.io_clock) nclock;
    Stdlib.List.iter (fun (h, bs) ->
      let n = Stdlib.List.length bs in
      Printf.printf "--- handle %s (%d bytes)\n" (Big_int_Z.string_of_big_int h) n;
      if n <= 65536 then begin
        Stdlib.List.iter (fun b -> print_char (Stdlib.Char.chr (Big_int_Z.int_of_big_int b))) (Stdlib.List.rev bs);
        print_newline () end
      else print_endline "(longer than 65536 bytes: not printed; see PS_DUMPDIR)") st.Values.st_io.Values.io_out in
  let str l = Stdlib.String.of_seq (Stdlib.List.to_seq l) in
  (if Sys.getenv_opt "PS_MEMDIAG" <> None then begin
     let st = match r with Interp.EOk (_, s) | Interp.EHalt (_, s) | Interp.EStk (_, s) -> s in
     Gc.compact ();
     let g = Gc.stat () in
     Printf.printf "MEMDIAG live_words %d top_heap_words %d\n" g.Gc.live_words g.Gc.top_heap_words;
     Printf.printf "MEMDIAG reachable_words(state) %d heap %d io %d\n" (Obj.reachable_words (Obj.repr st))
       (Obj.reachable_words (Obj.repr st.Values.heap)) (Obj.reachable_words (Obj.repr st.Values.st_io));
     Printf.printf "MEMDIAG hp %s\n" (Big_int_Z.string_of_big_int st.Values.hp);
     let n = Big_int_Z.int_of_big_int st.Values.hp in
     let sizes = Stdlib.List.init n (fun b ->
       let blk = Values.hget st (Big_int_Z.big_int_of_int b) in
       (Obj.reachable_words (Obj.repr blk), b, Big_int_Z.int_of_big_int blk.Values.bsize)) in
     let sorted = Stdlib.List.sort (fun (a, _, _) (b, _, _) -> compare b a) sizes in
     Stdlib.List.iteri (fun i (w, b, sz) -> if i < 25 then Printf.printf "MEMDIAG block %d size %d words %d\n" b sz w) sorted
   end);
  (match r with
   | Interp.EOk (_, st) -> show st; print_endline "RESULT: returned"
   | Interp.EHalt (c, st) -> show st; Printf.printf "RESULT: exit %s\n" (Big_int_Z.string_of_big_int c)
   | Interp.EStk (s, st) -> show st;
     let names = (try
       let ic = open_in (Sys.getenv "PS_PROCNAMES") in
       let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> Stdlib.List.rev acc in
       Stdlib.Array.of_list (go []) with _ -> [||]) in
     let pname p = let i = Big_int_Z.int_of_big_int p in
       if i < Stdlib.Array.length names then names.(i) else string_of_int i in
     let rec why s = match s with
       | Values.StIn (p, s') -> pname p ^ " > " ^ why s' 
       | Values.StOverflow -> "signed overflow" | Values.StDivZero -> "division by zero"
       | Values.StConv m -> "conversion: " ^ str m | Values.StUninit -> "read of an uninitialised value"
       | Values.StBounds m -> "bounds: " ^ str m | Values.StType m -> "type: " ^ str m
       | Values.StExternal m -> "unmodelled external: " ^ str m | Values.StFuel -> "out of fuel"
       | Values.StGoto n -> "goto " ^ Big_int_Z.string_of_big_int n | Values.StCharSign -> "char signedness"
       | Values.StNaNBits -> "NaN bits" | Values.StOther m -> str m in
     Printf.printf "RESULT: stuck: %s\n" (why s));
  Printf.printf "TIME: %.2f s\n" (t1 -. t0)
