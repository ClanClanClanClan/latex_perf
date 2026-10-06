(* kpathsea's file search, as the pinned binary performs it (ADR-015 boundary step,
   checkpoint 1): kpse_find_file for the tex, tfm and fmt formats, the ls-R database, the
   fontmap, the disk search and its case-folding fallback, each from the C source of
   r78081 (texk/kpathsea/*.c; the file and function are named per definition).

   It is a pure function of the run's explicit inputs (Values.io; the types are KTypes.v): the file-system
   snapshot io_fs (what stat(2), access(2), opendir(3)/readdir(3) and fopen(3) find), the
   working directory io_cwd, the files this run created (io_files), kpathsea's variable
   values io_kpse and its format table io_kfmt. Every question the snapshot does not
   answer, and every C behaviour not modelled here, is Stuck (KStk), never a guess.

   What is modelled, and what is Stuck, and why:
   - absolute names ("/..."), explicitly relative names ("./...", "../..."): modelled as
     kpathsea treats them (absolute_search), EXCEPT that a ".." component is Stuck: the
     kernel resolves ".." after symbolic links, which the snapshot does not record;
   - a "$" in a name (kpathsea_var_expand) or a leading "~" (kpathsea_tilde_expand):
     Stuck (the expansion reads variables and the password database);
   - a path element with "//" (subdirectory expansion, elt-dirs.c do_subdir): modelled
     when its directory does not exist (opendir fails: no directories); Stuck when it
     exists (the result depends on readdir order and st_nlink, which the snapshot does
     not record) -- unless the ls-R database covers the element, which is how kpathsea
     reaches the TeX tree;
   - the case-folding fallback (texmf_casefold_search): modelled when at most one entry
     of the directory matches; Stuck when several do (readdir order decides in C);
   - mktex* (kpse_make_tex runs a shell script): Stuck when kpathsea would run it;
   - alias databases, $TEXMFLOG, an ls-R with no usable entry (a warning on stderr during
     C main), a fontmap warning: Stuck;
   - the kpathsea caches (the element-directory cache, the dir-links table, the
     str_llist_float reordering): not kept, because no result here depends on them: the
     directories the run can see do not change during the run (TeX creates regular files
     only, in the working directory), and every directory list the model forms has at most
     one element (subdirectory expansion is Stuck), so floating reorders nothing;
   - the ls-R database is built in C during C main (cnf.c kpathsea_cnf_get calls
     kpathsea_init_db), before mainbody; the model builds it on first use, from the
     snapshot as it was before the run (written files ignored), which is the same value;
   - name length: a component longer than NAME_MAX (255) or a path of PATH_MAX (4096) bytes
     or more (ENAMETOOLONG, which readable.c handles by truncation): Stuck.
   The hash tables of db.c, fontmap.c and hash.c return, for a key, every value inserted
   under an equal key, in insertion order (hash.c hash_lookup); the bucket function decides
   nothing else, so the model's bucket index (the same recurrence over unsigned bytes) is
   not a claim about C's (which hashes plain char, signed on x86_64). *)

From Coq Require Import ZArith List Bool String PArray Uint63.
From PS Require Import KTypes.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------- results *)
Inductive kr (A : Type) : Type := KOk (a : A) | KStk (m : string).
Arguments KOk {A} a. Arguments KStk {A} m.

(* ---------------------------------------------------------------- bytes *)
(* The byte constants of the loops over file contents (an ls-R is 4.5 MB). Extract.v
   declares them NoInline: Coq extracts a Z literal as a chain of big-integer operations,
   and a match on a Z literal as a chain of divisions, at every use; a named constant is
   computed once. No function below matches on a Z literal. *)
Definition C_NUL : Z := 0.   Definition C_TAB : Z := 9.    Definition C_LF : Z := 10.
Definition C_CR : Z := 13.   Definition C_SP : Z := 32.    Definition C_BANG : Z := 33.
Definition C_DOLLAR : Z := 36. Definition C_PCT : Z := 37. Definition C_PLUS : Z := 43.
Definition C_MINUS : Z := 45. Definition C_DOT : Z := 46.  Definition SL : Z := 47.
Definition C_D0 : Z := 48.   Definition C_D9 : Z := 57.    Definition C_COLON : Z := 58.
Definition C_SEMI : Z := 59. Definition C_AT : Z := 64.    Definition C_UA : Z := 65.
Definition C_UZ : Z := 90.   Definition C_US : Z := 95.    Definition C_LA : Z := 97.
Definition C_LC : Z := 99.   Definition C_LZ : Z := 122.   Definition C_LBRACE : Z := 123.
Definition C_RBRACE : Z := 125. Definition C_TILDE : Z := 126.

Definition hdq (c : Z) (l : list Z) : bool := match l with x :: _ => x =? c | [] => false end.
Fixpoint last_is (c : Z) (l : list Z) : bool := match l with [] => false | [x] => x =? c | _ :: r => last_is c r end.
Definition is_dot (l : list Z) : bool := match l with [x] => x =? C_DOT | _ => false end.
Definition is_dotdot (l : list Z) : bool := match l with [x; y] => (x =? C_DOT) && (y =? C_DOT) | _ => false end.

Fixpoint beq (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && beq a' b'
  | _, _ => false
  end.

Fixpoint bmem (x : list Z) (l : list (list Z)) : bool :=
  match l with [] => false | y :: r => beq x y || bmem x r end.

Fixpoint zs_of (l : list Ascii.ascii) : list Z :=
  match l with [] => [] | c :: r => Z.of_nat (Ascii.nat_of_ascii c) :: zs_of r end.
Definition zs (s : string) : list Z := zs_of (list_ascii_of_string s).

Fixpoint is_prefix (p l : list Z) : bool :=
  match p, l with
  | [], _ => true
  | x :: p', y :: l' => (x =? y) && is_prefix p' l'
  | _ :: _, [] => false
  end.

Definition ends_with (suf l : list Z) : bool :=
  (Z.of_nat (List.length suf) <=? Z.of_nat (List.length l)) && is_prefix (rev' suf) (rev' l).

Definition has_byte (c : Z) (l : list Z) : bool := existsb (fun x => x =? c) l.

(* C locale classification (pdfTeX never calls setlocale) *)
Definition c_isspace (c : Z) : bool := (c =? C_SP) || ((C_TAB <=? c) && (c <=? C_CR)).
Definition c_isalnum (c : Z) : bool := ((C_D0 <=? c) && (c <=? C_D9)) || ((C_UA <=? c) && (c <=? C_UZ)) || ((C_LA <=? c) && (c <=? C_LZ)).
Definition c_tolower (c : Z) : Z := if (C_UA <=? c) && (c <=? C_UZ) then c + C_SP else c.
(* strcasecmp (a, b) == 0 in the C locale *)
Fixpoint casefold_eq (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (c_tolower x =? c_tolower y) && casefold_eq a' b'
  | _, _ => false
  end.

(* the bytes after the last '/' (xbasename.c xbasename, Unix) *)
Fixpoint after_last_slash (l acc : list Z) : list Z :=
  match l with [] => rev' acc | c :: r => if c =? SL then after_last_slash r [] else after_last_slash r (c :: acc) end.
Definition xbasename (l : list Z) : list Z := after_last_slash l [].

(* xdirname.c xdirname (Unix): back over the last component; "." when nothing is left;
   then back over trailing slashes, keeping at least one character *)
Fixpoint drop_while_rev (f : Z -> bool) (l : list Z) : list Z :=
  match l with [] => [] | c :: r => if f c then drop_while_rev f r else l end.
Fixpoint drop_slashes_keep1 (l : list Z) : list Z :=      (* l reversed; keep >= 1 char *)
  match l with
  | c :: (_ :: _) as r => if c =? SL then drop_slashes_keep1 r else l
  | _ => l
  end.
Definition xdirname (l : list Z) : list Z :=
  match drop_while_rev (fun c => negb (c =? SL)) (rev' l) with
  | [] => [C_DOT]
  | r => rev' (drop_slashes_keep1 r)
  end.

(* absolute.c kpathsea_absolute_p (Unix) *)
Definition absolute_p (name : list Z) (relative_ok : bool) : bool :=
  hdq SL name
  || (relative_ok && hdq C_DOT name
      && (hdq SL (tl name) || (hdq C_DOT (tl name) && hdq SL (tl (tl name))))).

(* elt-dirs.c kpathsea_normalize_path (Unix): several leading slashes become one *)
Fixpoint drop_lead_slashes (l : list Z) : list Z :=
  match l with c :: r => if c =? SL then drop_lead_slashes r else l | [] => [] end.
Definition normalize_path (elt : list Z) : list Z :=
  if hdq SL elt then SL :: drop_lead_slashes elt else elt.

(* the bytes before and after the last occurrence of byte b, when there is one *)
Fixpoint split_last_aux (b : Z) (l pre_rev cur_rev : list Z) (seen : bool) : option (list Z * list Z) :=
  match l with
  | [] => if seen then Some (rev' (tl pre_rev), rev' cur_rev) else None    (* pre_rev's head is that b *)
  | c :: r => if c =? b then split_last_aux b r (b :: cur_rev ++ pre_rev) [] true
              else split_last_aux b r pre_rev (c :: cur_rev) seen
  end.
Definition split_last (b : Z) (l : list Z) : option (list Z * list Z) := split_last_aux b l [] [] false.

(* find-suffix.c find_suffix: the bytes after the last '.', if no '/' follows it; here
   (the bytes before that '.', the suffix) *)
Definition find_suffix (l : list Z) : option (list Z * list Z) :=
  match split_last C_DOT l with
  | Some (b, a) => if has_byte SL a then None else Some (b, a)
  | None => None
  end.

(* ---------------------------------------------------------------- the file system *)
Record kenv : Type := mkkenv {
  ke_cwd : list Z; ke_fs : list (list Z * fsent); ke_written : list (list Z);
  ke_vars : list (list Z * list Z); ke_fmts : list (Z * kfmt) }.

Fixpoint split_comps (l cur : list Z) (acc : list (list Z)) : list (list Z) :=
  match l with
  | [] => rev' (rev' cur :: acc)
  | c :: r => if c =? SL then split_comps r [] (rev' cur :: acc) else split_comps r (c :: cur) acc
  end.

(* the components of a path the kernel resolves, the working directory first for a
   relative path; "" and "." components dropped (POSIX path resolution); ".." Stuck *)
Definition canon (env : kenv) (p : list Z) : kr (list (list Z)) :=
  let full := if hdq SL p then p else ke_cwd env ++ [SL] ++ p in
  let cs := filter (fun c => negb (beq c [] || is_dot c)) (split_comps full [] []) in
  if existsb is_dotdot cs then KStk "a path with a '..' component (symbolic links: not modelled)"
  else if existsb (fun c => 255 <? Z.of_nat (List.length c)) cs then KStk "a path component longer than NAME_MAX (ENAMETOOLONG: not modelled)"
  else if 4096 <=? Z.of_nat (List.length full) then KStk "a path of PATH_MAX bytes or more (ENAMETOOLONG: not modelled)"
  else KOk cs.

Fixpoint key_of (cs : list (list Z)) : list Z :=
  match cs with [] => [] | c :: r => SL :: c ++ key_of r end.
Definition key (cs : list (list Z)) : list Z := match cs with [] => [SL] | _ => key_of cs end.

Fixpoint fs_find (k : list Z) (fs : list (list Z * fsent)) : option fsent :=
  match fs with [] => None | (k', e) :: r => if beq k k' then Some e else fs_find k r end.

Inductive fstat : Type :=
| SNone                               (* stat fails *)
| SFile (contents : option (list Z)) (written : bool)
| SDir (listing : option (list (list Z))).

(* the names in the directory with key d: the snapshot's, and for the working directory the
   files this run created (written = false: the snapshot as it was before the run) *)
Definition dir_names (env : kenv) (written : bool) (d : list Z) (l : list (list Z)) : list (list Z) :=
  if written && beq d (ke_cwd env) then l ++ filter (fun w => negb (bmem w l)) (ke_written env) else l.

Definition is_written (env : kenv) (written : bool) (cs : list (list Z)) : bool :=
  written && existsb (fun w => beq (key cs) (ke_cwd env ++ [SL] ++ w)) (ke_written env).

(* decided by an ancestor: (the prefix before component i, component i, the rest) *)
Fixpoint ancestor_absent (env : kenv) (written : bool) (pre : list (list Z)) (rest : list (list Z)) : bool :=
  match rest with
  | [] => false
  | c :: r =>
    let decided := match fs_find (key (rev' pre)) (ke_fs env) with
                   | Some FsAbsent => true                      (* ENOENT *)
                   | Some (FsFile _) => true                    (* ENOTDIR *)
                   | Some (FsDir (Some l)) => negb (bmem c (dir_names env written (key (rev' pre)) l))
                   | _ => false
                   end in
    decided || ancestor_absent env written (c :: pre) r
  end.

Definition fs_stat_cs (env : kenv) (written : bool) (cs : list (list Z)) : kr fstat :=
  if is_written env written cs then KOk (SFile None true) else
  match fs_find (key cs) (ke_fs env) with
  | Some (FsFile c) => KOk (SFile c false)
  | Some (FsDir l) => KOk (SDir (match l with Some l' => Some (dir_names env written (key cs) l') | None => None end))
  | Some FsAbsent => KOk SNone
  | None => if ancestor_absent env written [] cs then KOk SNone
            else KStk (String.append "the file-system snapshot does not decide " (string_of_list_ascii (map (fun z => Ascii.ascii_of_nat (Z.to_nat z)) (key cs))))
  end.

(* stat(2) of a path as C passes it; "" fails (ENOENT); a trailing slash on a file fails
   (ENOTDIR) *)
Definition fs_stat (env : kenv) (written : bool) (p : list Z) : kr fstat :=
  match p with
  | [] => KOk SNone
  | _ => match canon env p with
         | KStk m => KStk m
         | KOk cs => match fs_stat_cs env written cs with
                     | KOk (SFile c w) => if ends_with [SL] p then KOk SNone else KOk (SFile c w)
                     | r => r
                     end
         end
  end.

(* readable.c kpathsea_readable_file: normalize_path, then READABLE (access R_OK, stat,
   not a directory); the (normalized) name, or None *)
Definition readable (env : kenv) (written : bool) (name : list Z) : kr (option (list Z)) :=
  let n := normalize_path name in
  match fs_stat env written n with
  | KOk (SFile _ _) => KOk (Some n)
  | KOk _ => KOk None
  | KStk m => KStk m
  end.

(* dir.c kpathsea_dir_p: stat and S_ISDIR *)
Definition dir_p (env : kenv) (written : bool) (name : list Z) : kr bool :=
  match fs_stat env written name with KOk (SDir _) => KOk true | KOk _ => KOk false | KStk m => KStk m end.

(* opendir(3) and the readdir(3) names; None when opendir fails *)
Definition read_dir (env : kenv) (written : bool) (name : list Z) : kr (option (list (list Z))) :=
  match fs_stat env written name with
  | KOk (SDir (Some l)) => KOk (Some l)
  | KOk (SDir None) => KStk "a directory listing the file-system snapshot does not hold"
  | KOk _ => KOk None
  | KStk m => KStk m
  end.

(* the bytes of a file fopen(3) reads *)
Definition file_bytes (env : kenv) (name : list Z) : kr (list Z) :=
  match fs_stat env true name with
  | KOk (SFile (Some c) false) => KOk c
  | KOk (SFile _ true) => KStk "reading a file this run wrote (not modelled)"
  | KOk (SFile None _) => KStk "a file whose bytes the file-system snapshot does not hold"
  | KOk _ => KStk "fopen of a file that is not readable (xfopen FATAL: not modelled)"
  | KStk m => KStk m
  end.

(* pathsearch.c casefold_readable_file: opendir(xdirname(name)); the first readdir entry
   that strcasecmp-matches xbasename(name) and whose dirname/entry is readable. readdir's
   order is not in the snapshot: decided when at most one entry qualifies, else Stuck *)
Fixpoint readable_all (env : kenv) (written : bool) (dn : list Z) (es : list (list Z)) (acc : list (list Z)) : kr (list (list Z)) :=
  match es with
  | [] => KOk (rev' acc)
  | e :: r => match readable env written (dn ++ [SL] ++ e) with
              | KOk (Some n) => readable_all env written dn r (n :: acc)
              | KOk None => readable_all env written dn r acc
              | KStk m => KStk m
              end
  end.
Definition casefold_readable (env : kenv) (written : bool) (name : list Z) : kr (option (list Z)) :=
  let base := xbasename name in
  let dn := xdirname name in
  match read_dir env written dn with
  | KStk m => KStk m
  | KOk None => KOk None
  | KOk (Some l) =>
    match readable_all env written dn (filter (fun e => casefold_eq e base) l) [] with
    | KStk m => KStk m
    | KOk [] => KOk None
    | KOk [n] => KOk (Some n)
    | KOk _ => KStk "case-folded search with several matches (readdir order: not modelled)"
    end
  end.

(* ---------------------------------------------------------------- path elements *)
(* path-elt.c element (env_p): split at ':' or ';' outside braces *)
Fixpoint path_elts_aux (p : list Z) (lvl : Z) (cur : list Z) : list (list Z) :=
  match p with
  | [] => [rev' cur]
  | c :: r =>
    if (lvl =? 0) && ((c =? C_COLON) || (c =? C_SEMI)) then rev' cur :: path_elts_aux r 0 []
    else path_elts_aux r (if c =? C_LBRACE then lvl + 1 else if c =? C_RBRACE then lvl - 1 else lvl) (c :: cur)
  end.
Definition path_elts (p : list Z) : list (list Z) := path_elts_aux p 0 [].

(* the first "//" at or after the start: (the element up to and including its first '/',
   the rest after all consecutive '/') *)
Fixpoint find_dslash (l : list Z) (acc : list Z) : option (list Z * list Z) :=
  match l with
  | c :: r => if (c =? SL) && hdq SL r then Some (rev' (SL :: acc), drop_lead_slashes r) else find_dslash r (c :: acc)
  | [] => None
  end.

(* elt-dirs.c kpathsea_element_dirs (with expand_elt, do_subdir, checked_dir_list_add) *)
Definition element_dirs (env : kenv) (written : bool) (elt : list Z) : kr (list (list Z)) :=
  match elt with
  | [] => KOk []
  | _ =>
    let e := normalize_path elt in
    match find_dslash e [] with
    | Some (base, _) =>
      match read_dir env written base with
      | KOk None => KOk []
      | KOk (Some _) => KStk "subdirectory expansion (//) of an existing directory (readdir order, st_nlink: not modelled)"
      | KStk m => KStk m
      end
    | None =>
      match dir_p env written e with
      | KOk true => KOk [if ends_with [SL] e then e else e ++ [SL]]
      | KOk false => KOk []
      | KStk m => KStk m
      end
    end
  end.

(* ---------------------------------------------------------------- the ls-R database *)
Definition db_size : Z := 64007.     (* db.c DB_HASH_SIZE *)
Fixpoint hash_aux (l : list Z) (n : Z) : Z := match l with [] => n | c :: r => hash_aux r (Z.modulo (n + n + c) db_size) end.
Definition bucket (k : list Z) : int := Uint63.of_Z (hash_aux k 0).

Definition tab_lookup (t : array (list (list Z * list Z))) (k : list Z) : list (list Z) :=
  map snd (filter (fun kv => beq (fst kv) k) (PArray.get t (bucket k))).
Definition tab_insert (t : array (list (list Z * list Z))) (k v : list Z) : array (list (list Z * list Z)) :=
  let b := bucket k in PArray.set t b (PArray.get t b ++ [(k, v)]).
(* a fresh table per use (a shared constant would be the first version of every table built
   from it, and a persistent array re-roots between versions) *)
Definition tab_new (_ : unit) : array (list (list Z * list Z)) := PArray.make (Uint63.of_Z db_size) [].

(* line.c read_line: lines end at LF, CR or CR LF; NUL bytes are dropped; at end of file a
   partial line is returned when it has a byte *)
Fixpoint read_lines (bs cur : list Z) (acc : list (list Z)) : list (list Z) :=
  match bs with
  | [] => rev' (match cur with [] => acc | _ => rev' cur :: acc end)
  | c :: r =>
    if c =? C_NUL then read_lines r cur acc
    else if c =? C_LF then read_lines r [] (rev' cur :: acc)
    else if c =? C_CR then
      match r with
      | d :: r' => if d =? C_LF then read_lines r' [] (rev' cur :: acc) else read_lines r [] (rev' cur :: acc)
      | [] => read_lines r [] (rev' cur :: acc)
      end
    else read_lines r (c :: cur) acc
  end.

(* db.c ignore_dir_p: a '.' after the first byte, preceded by '/' and followed by a byte
   that is neither NUL nor '/' *)
Fixpoint ignore_aux (prev : Z) (l : list Z) : bool :=
  match l with
  | c :: r => (if c =? C_DOT then match r with d :: _ => (prev =? SL) && negb (d =? SL) | [] => false end else false)
              || ignore_aux c r
  | [] => false
  end.
Definition ignore_dir_p (line : list Z) : bool := match line with c :: r => ignore_aux c r | [] => false end.

(* db.c db_build: the entries (file name, its directory) in ls-R order *)
Fixpoint db_lines (top : list Z) (ls : list (list Z)) (cur : option (list Z)) (acc : list (list Z * list Z)) : list (list Z * list Z) :=
  match ls with
  | [] => rev' acc
  | line :: r =>
    if last_is C_COLON line && absolute_p line true then
      let cur' := if ignore_dir_p line then None else
                  let d := removelast line ++ [SL] in
                  Some (if hdq C_DOT d then top ++ skipn 2 d else d) in
      db_lines top r cur' acc
    else match line, cur with
         | _ :: _, Some d => if is_dot line || is_dotdot line then db_lines top r cur acc
                             else db_lines top r cur ((line, d) :: acc)
         | _, _ => db_lines top r cur acc
         end
  end.

(* ---------------------------------------------------------------- match (db.c) *)
Fixpoint drop_slashes (l : list Z) : list Z := match l with c :: r => if c =? SL then drop_slashes r else l | [] => [] end.
Fixpoint no_slash (l : list Z) : bool := match l with [] => true | c :: r => negb (c =? SL) && no_slash r end.

(* the check after the loop, when the path element is exhausted *)
Definition match_post (atstart : bool) (fprev : Z) (f : list Z) : bool :=
  match f with
  | c :: f' => if c =? SL then no_slash f'                    (* filename[-1] is then '/' *)
               else (atstart || (fprev =? SL)) && no_slash f
  | [] => atstart || (fprev =? SL)
  end.

(* db.c match (filename, path_elt): f the filename from the current position, fprev the
   byte before it (atstart: there is none in this call), p the path element from the
   current position. n bounds the recursion (each level consumes a byte or calls the
   inner loop, whose calls consume one): out of it, None (Stuck) *)
Fixpoint mt (n : nat) (atstart : bool) (fprev : Z) (f p : list Z) : option bool :=
  match n with
  | O => None
  | S n' =>
    match f, p with
    | fc :: f', pc :: p' =>
      if fc =? pc then mt n' false fc f' p'
      else if (pc =? SL) && negb atstart && (fprev =? SL) then
        match drop_slashes p with
        | [] => Some true                                     (* trailing //: matches *)
        | (pc2 :: _) as p2 => mt_inner n' fprev f pc2 p2     (* intermediate // *)
        end
      else Some false                                         (* a non-matching byte: p is not exhausted *)
    | _, _ => Some (match p with [] => match_post atstart fprev f | _ => false end)
    end
  end
with mt_inner (n : nat) (fprev : Z) (f : list Z) (pc2 : Z) (p2 : list Z) : option bool :=
  match n with
  | O => None
  | S n' =>
    match f with
    | [] => Some false
    | fc :: f' =>
      if (fprev =? SL) && (fc =? pc2) then
        match mt n' true 0 f p2 with
        | Some true => Some true
        | Some false => mt_inner n' fc f' pc2 p2
        | None => None
        end
      else mt_inner n' fc f' pc2 p2
    end
  end.

Definition db_match (filename path_elt : list Z) : kr bool :=
  match mt (Nat.add 8 (Nat.mul 4 (List.length filename))) true 0 filename path_elt with
  | Some b => KOk b
  | None => KStk "db.c match: recursion bound (unreachable)"
  end.

(* db.c elt_in_db: db_dir is a (non-empty) prefix of a non-empty path_elt *)
Definition elt_in_db (db_dir elt : list Z) : bool :=
  match db_dir, elt with [], _ | _, [] => false | _, _ => is_prefix db_dir elt end.

(* ---------------------------------------------------------------- searching *)
(* pathsearch.c dir_list_search_list (and dir_list_search, its one-name case): every
   directory, every name that is not absolute or explicitly relative; the first readable
   one when not all *)
Inductive rdf : Type := RdPlain | RdCasefold.
Definition rd (env : kenv) (written : bool) (f : rdf) (n : list Z) : kr (option (list Z)) :=
  match f with RdPlain => readable env written n | RdCasefold => casefold_readable env written n end.

Fixpoint dls_names (env : kenv) (written : bool) (f : rdf) (dir : list Z) (names : list (list Z)) (all : bool) (acc : list (list Z))
  : kr (bool * list (list Z)) :=                 (* (done, found in order) *)
  match names with
  | [] => KOk (false, acc)
  | n :: r =>
    if absolute_p n true then dls_names env written f dir r all acc else
    match rd env written f (dir ++ n) with
    | KStk m => KStk m
    | KOk (Some x) => if all then dls_names env written f dir r all (acc ++ [x]) else KOk (true, acc ++ [x])
    | KOk None => dls_names env written f dir r all acc
    end
  end.
Fixpoint dir_list_search (env : kenv) (written : bool) (f : rdf) (dirs names : list (list Z)) (all : bool) (acc : list (list Z))
  : kr (list (list Z)) :=
  match dirs with
  | [] => KOk acc
  | d :: r => match dls_names env written f d names all acc with
              | KStk m => KStk m
              | KOk (true, acc') => KOk acc'
              | KOk (false, acc') => dir_list_search env written f r names all acc'
              end
  end.

(* db.c kpathsea_db_search_list (and kpathsea_db_search, its one-name case): None when the
   database is absent (buckets NULL) or covers no part of the element. A name with a '/'
   (not first) searches its directory part below the element. Each hit is checked on disk
   (kpathsea_readable_file); without aliases (the model requires none) a hit not on disk is
   skipped. temp_str is freed at the end of every iteration and never reset: a name without
   '/' after one with '/' frees it twice (undefined behaviour): Stuck *)
Fixpoint db_hits (env : kenv) (dirs : list (list Z)) (ctry path : list Z) (all : bool) (acc : list (list Z))
  : kr (bool * list (list Z)) :=
  match dirs with
  | [] => KOk (false, acc)
  | d :: r =>
    let db_file := d ++ ctry in
    match db_match db_file path with
    | KStk m => KStk m
    | KOk false => db_hits env r ctry path all acc
    | KOk true =>
      match readable env true db_file with
      | KStk m => KStk m
      | KOk (Some f) => if all then db_hits env r ctry path all (acc ++ [f]) else KOk (true, acc ++ [f])
      | KOk None => db_hits env r ctry path all acc
      end
    end
  end.

Fixpoint db_names (env : kenv) (t : array (list (list Z * list Z))) (names : list (list Z)) (elt : list Z)
         (all temp : bool) (acc : list (list Z)) : kr (list (list Z)) :=
  match names with
  | [] => KOk acc
  | n :: r =>
    if absolute_p n true then db_names env t r elt all temp acc else
    let '(path, nm, temp') := match split_last SL n with
                              | Some (dpart, base) => (elt ++ [SL] ++ dpart, base, true)
                              | None => (elt, n, false) end in
    if temp && negb temp' then KStk "db.c: temp_str freed twice (undefined behaviour)" else
    match db_hits env (tab_lookup t nm) nm path all acc with
    | KStk m => KStk m
    | KOk (true, acc') => KOk acc'
    | KOk (false, acc') => db_names env t r elt all (temp || temp') acc'
    end
  end.

Definition db_search_list (env : kenv) (db : kdb) (names : list (list Z)) (elt : list Z) (all : bool)
  : kr (option (list (list Z))) :=
  match kdb_tab db with
  | None => KOk None
  | Some t =>
    if negb (existsb (fun d => elt_in_db d elt) (kdb_dirs db)) then KOk None else
    match db_names env t names elt all false [] with
    | KOk l => KOk (Some l)
    | KStk m => KStk m
    end
  end.

(* cnf.c kpse_cnf_p: non-NULL, non-empty, not starting with 'f' or '0' *)
Definition cnf_p (v : option (list Z)) : bool :=
  match v with Some (c :: _) => negb (hdq c (zs "f") || hdq c (zs "0")) | _ => false end.

Fixpoint lookup_var (name : list Z) (vs : list (list Z * list Z)) : option (list Z) :=
  match vs with [] => None | (n, v) :: r => if beq n name then Some v else lookup_var name r end.
Definition var (env : kenv) (name : string) : option (list Z) := lookup_var (zs name) (ke_vars env).

(* pathsearch.c log_search: $TEXMFLOG (read once); when set, every search appends to it *)
Definition log_search_ok (env : kenv) : kr unit :=
  match var env "TEXMFLOG" with
  | None => KOk tt
  | Some _ => KStk "TEXMFLOG is set (search logging: not modelled)"
  end.

(* the loop over the path's elements shared by pathsearch.c path_search and
   kpathsea_path_search_list_generic: "!!" forbids the disk; ls-R first; the disk when
   allowed and the database is not relevant (None), or must_exist and it found nothing;
   then the case-folded disk search when nothing was found and texmf_casefold_search *)
Fixpoint elts_loop (env : kenv) (written : bool) (db : kdb) (elts names : list (list Z)) (must_exist all : bool)
         (acc : list (list Z)) : kr (list (list Z)) :=
  match elts with
  | [] => KOk acc
  | e0 :: r =>
    let '(allow_disk, e1) := if hdq C_BANG e0 && hdq C_BANG (tl e0) then (false, skipn 2 e0) else (true, e0) in
    let elt := normalize_path e1 in
    match db_search_list env db names elt all with
    | KStk m => KStk m
    | KOk found =>
      let need_disk := allow_disk && match found with None => true | Some [] => must_exist | Some _ => false end in
      let found2 :=
        if negb need_disk then KOk found else
        match element_dirs env written elt with
        | KStk m => KStk m
        | KOk [] => KOk found
        | KOk dirs =>
          match dir_list_search env written RdPlain dirs names all [] with
          | KStk m => KStk m
          | KOk [] => if cnf_p (var env "texmf_casefold_search") then
                        match dir_list_search env written RdCasefold dirs names all [] with
                        | KStk m => KStk m
                        | KOk l => KOk (Some l)
                        end
                      else KOk (Some [])
          | KOk l => KOk (Some l)
          end
        end in
      match found2 with
      | KStk m => KStk m
      | KOk (Some ((x :: _) as l)) => if all then elts_loop env written db r names must_exist all (acc ++ l)
                                      else KOk (acc ++ [x])
      | KOk _ => elts_loop env written db r names must_exist all acc
      end
    end
  end.

(* pathsearch.c absolute_search *)
Definition absolute_search (env : kenv) (written : bool) (name : list Z) : kr (list (list Z)) :=
  match readable env written name with
  | KStk m => KStk m
  | KOk (Some f) => KOk [f]
  | KOk None =>
    if cnf_p (var env "texmf_casefold_search") then
      match casefold_readable env written name with
      | KStk m => KStk m | KOk (Some f) => KOk [f] | KOk None => KOk [] end
    else KOk []
  end.

(* str-list.c str_list_uniqify: later duplicates removed (FILESTRCASEEQ is strcmp on Unix) *)
Fixpoint uniq (l acc : list (list Z)) : list (list Z) :=
  match l with [] => rev' acc | x :: r => if bmem x acc then uniq r acc else uniq r (x :: acc) end.

(* pathsearch.c kpathsea_path_search_list_generic. The names are not expanded here (the
   caller, kpathsea_find_file_generic, did it). The first search of the process (for
   texmf.cnf, in C main) sets followup_search; every search here comes after it *)
Fixpoint abs_names (env : kenv) (written : bool) (names : list (list Z)) (all : bool) (acc : list (list Z))
  : kr (bool * bool * list (list Z)) :=                   (* (done, all_absolute, found) *)
  match names with
  | [] => KOk (false, true, acc)
  | n :: r =>
    if absolute_p n true then
      match absolute_search env written n with
      | KStk m => KStk m
      | KOk (f :: _) => if all then abs_names env written r all (acc ++ [f]) else KOk (true, true, acc ++ [f])
      | KOk [] => abs_names env written r all acc
      end
    else match abs_names env written r all acc with
         | KOk (d, _, l) => KOk (d, false, l)
         | k => k
         end
  end.

Definition generic (env : kenv) (written : bool) (db : kdb) (path : list Z) (names : list (list Z)) (must_exist all : bool)
  : kr (list (list Z)) :=
  let res :=
    match abs_names env written names all [] with
    | KStk m => KStk m
    | KOk (true, _, l) => KOk l
    | KOk (false, true, l) => KOk l
    | KOk (false, false, l) => elts_loop env written db (path_elts path) names must_exist all l
    end in
  match res with
  | KStk m => KStk m
  | KOk l => match log_search_ok env with KOk _ => KOk (uniq l []) | KStk m => KStk m end
  end.

(* expand.c kpathsea_expand: $ and a leading ~ (after an optional "!!") are not modelled *)
Definition expand_ok (name : list Z) : kr (list Z) :=
  if has_byte C_DOLLAR name then KStk "a file name with '$' (kpathsea variable expansion: not modelled)" else
  if hdq C_TILDE name || (hdq C_BANG name && hdq C_BANG (tl name) && hdq C_TILDE (tl (tl name)))
  then KStk "a file name with a leading '~' (tilde expansion: not modelled)"
  else KOk name.

(* pathsearch.c search (kpathsea_path_search, kpathsea_all_path_search): one name, expanded;
   absolute: absolute_search; else path_search (the element loop for that name); no
   uniqify *)
Definition search1 (env : kenv) (written : bool) (db : kdb) (path name : list Z) (must_exist all : bool)
  : kr (list (list Z)) :=
  match expand_ok name with
  | KStk m => KStk m
  | KOk n =>
    let res := if absolute_p n true then absolute_search env written n
               else elts_loop env written db (path_elts path) [n] must_exist all [] in
    match res with
    | KStk m => KStk m
    | KOk l => match log_search_ok env with KOk _ => KOk l | KStk m => KStk m end
    end
  end.

Fixpoint lookup_fmt (f : Z) (l : list (Z * kfmt)) : option kfmt :=
  match l with [] => None | (g, k) :: r => if f =? g then Some k else lookup_fmt f r end.

Definition kpse_db_format : Z := 9.
Definition kpse_fontmap_format : Z := 11.

(* db.c kpathsea_init_db, on the snapshot as it was before the run (C main): the ls-R files
   (db_names ls-r, ls-R) along the db format's path, found with no database (buckets
   NULL); consecutive names equal under strcasecmp are the same file when equal byte for
   byte (same_file_p would compare inodes: Stuck otherwise); each read with db_build (a
   file with no usable entry warns on stderr: Stuck); then the alias files, which the
   model requires to be absent *)
Fixpoint dedupe (l : list (list Z)) : kr (list (list Z)) :=
  match l with
  | a :: ((b :: _) as r) =>
    if casefold_eq a b then (if beq a b then dedupe r else KStk "two ls-R names equal under strcasecmp (same_file_p: not modelled)")
    else match dedupe r with KOk r' => KOk (a :: r') | k => k end
  | _ => KOk l
  end.

Fixpoint db_build_all (env : kenv) (files : list (list Z)) (t : array (list (list Z * list Z))) (dirs : list (list Z))
  : kr (array (list (list Z * list Z)) * list (list Z)) :=
  match files with
  | [] => KOk (t, dirs)
  | f :: r =>
    match fs_stat env false f with
    | KStk m => KStk m
    | KOk (SFile (Some bytes) _) =>
      let top := firstn (List.length f - 4) f in            (* strlen (db_filename) - sizeof ("ls-R") + 1: keeps the '/' *)
      let ents := db_lines top (read_lines bytes [] []) None [] in
      match ents with
      | [] => KStk "an ls-R with no usable entries (a warning in C main: not modelled)"
      | _ => db_build_all env r (fold_left (fun t' kv => tab_insert t' (fst kv) (snd kv)) ents t) (dirs ++ [top])
      end
    | KOk (SFile None _) => KStk "an ls-R whose bytes the file-system snapshot does not hold"
    | KOk _ => KStk "an ls-R that is not readable (fopen: not modelled)"
    end
  end.

Definition init_db (env : kenv) : kr kdb :=
  match lookup_fmt kpse_db_format (ke_fmts env) with
  | None => KStk "kpse_format_info of the db format is not an input of this run"
  | Some info =>
    let none := mkkdb [] None in
    match generic env false none (kf_path info) [zs "ls-r"; zs "ls-R"] true true with
    | KStk m => KStk m
    | KOk files =>
      match dedupe files with
      | KStk m => KStk m
      | KOk files' =>
        let built := match files' with
                     | [] => KOk (mkkdb [] None)
                     | _ => match db_build_all env files' (tab_new tt) [] with
                            | KOk (t, dirs) => KOk (mkkdb dirs (Some t))
                            | KStk m => KStk m
                            end
                     end in
        match built with
        | KStk m => KStk m
        | KOk db =>
          match search1 env false db (kf_path info) (zs "aliases") true true with
          | KStk m => KStk m
          | KOk [] => KOk db
          | KOk _ => KStk "an alias database (db.c alias_build: not modelled)"
          end
        end
      end
    end
  end.

(* ---------------------------------------------------------------- the fontmap (fontmap.c) *)
(* token: skip ISSPACE, then the bytes up to the next ISSPACE (never NULL) *)
Fixpoint take_nonspace (l acc : list Z) : list Z * list Z :=
  match l with c :: r => if c_isspace c then (rev' acc, l) else take_nonspace r (c :: acc) | [] => (rev' acc, []) end.
Definition token (l : list Z) : list Z * list Z := take_nonspace (drop_while_rev c_isspace l) [].

(* the comment: from the last '%', else from the first "@c" *)
Fixpoint upto_at_c (l acc : list Z) : list Z :=
  match l with c :: r => if (c =? C_AT) && hdq C_LC r then rev' acc else upto_at_c r (c :: acc) | [] => rev' acc end.
Definition strip_comment (l : list Z) : list Z :=
  match split_last C_PCT l with Some (b, _) => b | None => upto_at_c l [] end.

Fixpoint map_parse (n : nat) (env : kenv) (db : kdb) (path fname : list Z) (t : array (list (list Z * list Z)))
  : kr (array (list (list Z * list Z))) :=
  match n with
  | O => KStk "fontmap include nesting beyond the model's bound"
  | S n' =>
    match file_bytes env fname with
    | KStk m => KStk m
    | KOk bytes =>
      let fix lines (ls : list (list Z)) (t : array (list (list Z * list Z))) : kr (array (list (list Z * list Z))) :=
        match ls with
        | [] => KOk t
        | l0 :: r =>
          let '(filename, rest) := token (strip_comment l0) in
          let '(alias, _) := token rest in
          if beq filename (zs "include") then
            match search1 env true db path alias false false with
            | KStk m => KStk m
            | KOk (inc :: _) => match map_parse n' env db path inc t with KOk t' => lines r t' | k => k end
            | KOk [] => KStk "fontmap: an include file not found (a warning: not modelled)"
            end
          else lines r (tab_insert t alias filename)
        end in
      lines (read_lines bytes [] []) t
    end
  end.

(* fontmap.c read_all_maps: every texfonts.map along the fontmap format's path *)
Definition read_all_maps (env : kenv) (db : kdb) : kr (array (list (list Z * list Z))) :=
  match lookup_fmt kpse_fontmap_format (ke_fmts env) with
  | None => KStk "kpse_format_info of the fontmap format is not an input of this run"
  | Some info =>
    match search1 env true db (kf_path info) (zs "texfonts.map") true true with
    | KStk m => KStk m
    | KOk files =>
      fold_left (fun acc f => match acc with KOk t => map_parse 64 env db (kf_path info) f t | k => k end)
                files (KOk (tab_new tt))
    end
  end.

(* fontmap.c kpathsea_fontmap_lookup: KEY, else KEY without its suffix; every mapped name
   then gets KEY's suffix unless it has one (extend-fname.c extend_filename) *)
Definition fontmap_lookup (t : array (list (list Z * list Z))) (k : list Z) : list (list Z) :=
  let suf := find_suffix k in
  let ret := match tab_lookup t k, suf with
             | [], Some (b, _) => tab_lookup t b
             | r, _ => r end in
  match suf with
  | Some (_, s) => map (fun e => match find_suffix e with None => e ++ [46] ++ s | Some _ => e end) ret
  | None => ret
  end.

(* tex-file.c target_fontmaps: the fontmap's names for a target (none without a fontmap) *)
Definition fm_names (mt0 : option (array (list (list Z * list Z)))) (n : list Z) : list (list Z) :=
  match mt0 with Some t => fontmap_lookup t n | None => [] end.

(* ---------------------------------------------------------------- kpse_find_file *)
(* tex-make.c kpathsea_make_tex: when the format has an enabled program, a base name of
   [A-Za-z0-9+_./-] not starting with '-' runs it (a shell script): Stuck; else NULL *)
Definition make_tex (info : kfmt) (name : list Z) : kr (option (list Z)) :=
  if negb (kf_mktex info) then KOk None else
  if hdq C_MINUS name then KOk None
  else if forallb (fun c => c_isalnum c || (c =? C_MINUS) || (c =? C_PLUS) || (c =? C_US) || (c =? C_DOT) || (c =? SL)) name
  then KStk "kpse_make_tex would run mktex* (a program: not modelled)"
  else KOk None.

Definition use_fontmaps (f : Z) : bool := (f =? 3) || (f =? 0) || (f =? 1) || (f =? 20).

(* the kpathsea state after making sure the database (and, when needed, the fontmap) exist *)
Definition ensure_db (env : kenv) (kp : kpst) : kr (kpst * kdb) :=
  match kp_db kp with
  | Some db => KOk (kp, db)
  | None => match init_db env with KOk db => KOk (mkkpst (Some db) (kp_map kp), db) | KStk m => KStk m end
  end.
Definition ensure_map (env : kenv) (kp : kpst) (db : kdb) : kr (kpst * array (list (list Z * list Z))) :=
  match kp_map kp with
  | Some t => KOk (kp, t)
  | None => match read_all_maps env db with KOk t => KOk (mkkpst (kp_db kp) (Some t), t) | KStk m => KStk m end
  end.

(* tex-file.c kpathsea_find_file_generic (all = false): the name expanded; the suffixed and
   as-is target names (with the fontmap's names for the glyph and metric formats) in the
   order try_std_extension_first gives; the search without, then with, the disk pounding of
   must_exist; then kpse_make_tex. Returns the new kpathsea state and the file found *)
Definition find_file (env : kenv) (kp : kpst) (name0 : list Z) (fmt : Z) (must_exist : bool)
  : kr (kpst * option (list Z)) :=
  match lookup_fmt fmt (ke_fmts env), expand_ok name0, ensure_db env kp with
  | None, _, _ => KStk "kpse_format_info of this format is not an input of this run"
  | _, KStk m, _ | _, _, KStk m => KStk m
  | Some info, KOk name, KOk (kp1, db) =>
    let has_any_suffix := match find_suffix name with Some _ => true | None => false end in
    let hps := existsb (fun s => ends_with s name) (kf_suffix info ++ kf_alt info) in
    let fmr := if use_fontmaps fmt then match ensure_map env kp1 db with
                                         | KOk (k, t) => KOk (k, Some t) | KStk m => KStk m end
               else KOk (kp1, None) in
    match fmr with
    | KStk m => KStk m
    | KOk (kp2, mt0) =>
      let suffixed := if hps then [] else flat_map (fun s => (name ++ s) :: fm_names mt0 (name ++ s)) (kf_suffix info) in
      let asis := if hps || negb (kf_sso info) then name :: fm_names mt0 name else [] in
      let targets := if has_any_suffix && negb (cnf_p (var env "try_std_extension_first"))
                     then asis ++ suffixed else suffixed ++ asis in
      match generic env true db (kf_path info) targets false false with
      | KStk m => KStk m
      | KOk (f :: _) => KOk (kp2, Some f)
      | KOk [] =>
        if negb must_exist then KOk (kp2, None) else
        if negb hps && kf_sso info && match kf_suffix info with [] => true | _ => false end
        then KStk "suffix_search_only with no suffix list (a NULL dereference in C)" else
        let t2 := (if negb hps && kf_sso info then map (fun s => name ++ s) (kf_suffix info) else [])
                  ++ (if hps || negb (kf_sso info) then [name] else []) in
        match generic env true db (kf_path info) t2 true false with
        | KStk m => KStk m
        | KOk (f :: _) => KOk (kp2, Some f)
        | KOk [] => match make_tex info name with
                    | KOk r => KOk (kp2, r)
                    | KStk m => KStk m
                    end
        end
      end
    end
  end.

(* ---------------------------------------------------------------- name checks (tex-file.c) *)
(* kpathsea_name_ok for writing (kpse_out_name_ok: openout_any, default "p", not silent,
   not extended): true, or false with the message C writes on stderr. Reading
   (kpse_in_name_ok) returns true before looking at anything in r78081 *)
Definition abs_fname_ok (fname : list Z) (dir : option (list Z)) : bool :=
  match dir with
  | Some ((_ :: _) as d) => is_prefix d fname && (match skipn (List.length d) fname with [] => true | c :: _ => c =? SL end)
  | _ => false
  end.

Fixpoint dot_bad (prev : option Z) (l : list Z) : bool :=     (* a '.' at the start or after '/', not "./" or "../" *)
  match l with
  | [] => false
  | c :: r => (if c =? C_DOT then
                 match prev with None => true | Some p => p =? SL end
                 && negb (hdq SL r) && negb (hdq C_DOT r && hdq SL (tl r))
               else false) || dot_bad (Some c) r
  end.

Fixpoint dotdot_bad (prev : option Z) (l : list Z) : bool :=  (* "/../" anywhere *)
  match l with
  | c :: r => (if (c =? C_DOT) && hdq C_DOT r && hdq SL (tl r)
               then match prev with Some p => p =? SL | None => false end else false)
              || dotdot_bad (Some c) r
  | [] => false
  end.

Definition out_name_ok (env : kenv) (getenv_outdir : option (list Z)) (fname : list Z) : kr bool :=
  let choice := match var env "openout_any" with Some v => v | None => zs "p" end in
  match choice with
  | c :: _ =>
    if hdq c (zs "a") || hdq c (zs "y") || hdq c (zs "1") then KOk true else
    match expand_ok fname with
    | KStk m => KStk m
    | KOk ex =>
      if dot_bad None fname then KOk false else
      if hdq c (zs "r") || hdq c (zs "n") || hdq c (zs "0") then KOk true else
      if absolute_p ex false && negb (abs_fname_ok ex getenv_outdir) && negb (abs_fname_ok ex (var env "TEXMFOUTPUT"))
      then KOk false
      else if hdq C_DOT fname && hdq C_DOT (tl fname) && hdq SL (tl (tl fname)) then KOk false
      else KOk (negb (dotdot_bad None fname))
    end
  | [] => KStk "openout_any is the empty string (C reads its first byte, NUL: not modelled)"
  end.
