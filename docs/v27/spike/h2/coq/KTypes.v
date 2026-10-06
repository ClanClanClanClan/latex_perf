(* The types of the run's file system and of kpathsea's state (boundary step, ADR-015),
   in a module of their own: Values.io holds them, and Kpse.v, which computes on them, then
   depends on no state (it cannot see the interpreter's heap; H.5's retention check treats it
   as a pure module). *)

From Coq Require Import ZArith List PArray.
Import ListNotations.

(* ---------------------------------------------------------------- the run's file system

   The file-system snapshot (boundary step 1, kpathsea file input): what the run can see of
   the file system, an explicit input that is part of the run's identity, as C-107 made the
   clock. An entry is keyed by a canonical absolute path ("/a/b": no empty, "." or ".."
   component, no trailing slash; "/" is the root) and says what stat(2) and opendir(3)
   find there:
     FsFile c     a file kpathsea's READABLE accepts (access R_OK, stat succeeds, not
                  S_ISDIR); c = its bytes, or None when the snapshot does not hold them
                  (opening it is then Stuck)
     FsDir l      a directory; l = the names readdir(3) returns besides "." and "..", or
                  None when the snapshot does not hold the listing (reading it is Stuck)
     FsAbsent     stat(2) fails with ENOENT
   A path the snapshot does not decide is Stuck where it is asked (Kpse.v fs_stat). *)
Inductive fsent : Type :=
| FsFile (contents : option (list Z))
| FsDir (listing : option (list (list Z)))
| FsAbsent.

(* kpathsea's kpse_format_info[f] after kpse_init_format (tex-file.c), for one format f: the
   search path (after variable, brace and default expansion), the suffix and alt_suffix
   lists, suffix_search_only, and whether kpse_make_tex would run a program (program !=
   NULL and program_enabled_p). An explicit input of the run, read on the reference build
   under gdb, like kpse_var_value's values (io_kpse) *)
Record kfmt : Type := mkkfmt {
  kf_path : list Z; kf_suffix : list (list Z); kf_alt : list (list Z); kf_sso : bool; kf_mktex : bool }.

(* kpathsea's C-internal state the model keeps (Kpse.v): the ls-R database (db.c
   kpathsea_init_db: db_dir_list, and the hash table, None when C's db.buckets is NULL) and
   the fontmap (fontmap.c read_all_maps); None = not computed yet *)
Record kdb : Type := mkkdb { kdb_dirs : list (list Z); kdb_tab : option (array (list (list Z * list Z))) }.
Record kpst : Type := mkkpst { kp_db : option kdb; kp_map : option (array (list (list Z * list Z))) }.

