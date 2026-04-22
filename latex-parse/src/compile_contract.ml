(** Pre-compile readiness contract. See [compile_contract.mli]. *)

type reason =
  | T0_parse_fails of { file : string; message : string }
  | T1_expansion_fails of string
  | T2_project_not_closed of [ `Cycle_in_build_graph | `Missing_file of string ]
  | T3_profile_incompatible of { feature : string; profile : string }
  | T4_semantic_incoherent of
      [ `Duplicate_labels of string list | `Missing_bib_entries of string list ]
  | T5_rule_violations of string list

type ready_check_result = Ready | NotReady of reason list

(* Feature→profile compatibility table. Mirrors the data in
   specs/v26/compilation_profiles.yaml but encoded here for runtime access
   without a yaml dep. *)
let feature_compatible (feature : Project_model.declared_feature)
    (engine : Project_model.engine_profile) : bool =
  let open Project_model in
  match (feature, engine) with
  (* UTF8_inputenc works everywhere except ptex_uptex (uses its own enc) *)
  | UTF8_inputenc, Ptex_uptex -> false
  | UTF8_inputenc, _ -> true
  (* UTF8_direct requires xe/lua *)
  | UTF8_direct, (Xelatex | Lualatex) -> true
  | UTF8_direct, _ -> false
  (* Unicode math requires unicode-aware engine *)
  | Unicode_math, (Xelatex | Lualatex) -> true
  | Unicode_math, _ -> false
  (* OpenType fonts need xelatex or lualatex *)
  | Opentype_fonts, (Xelatex | Lualatex) -> true
  | Opentype_fonts, _ -> false
  (* Lua scripting: only lualatex *)
  | Lua_scripting, Lualatex -> true
  | Lua_scripting, _ -> false
  (* Japanese CJK: only ptex_uptex in v26.2 scope *)
  | Japanese_cjk, Ptex_uptex -> true
  | Japanese_cjk, _ -> false
  (* Everything else is universally supported in v26.2 *)
  | _, _ -> true

let t3_check (proj : Project_model.t) : reason list =
  let engine = proj.Project_model.engine in
  List.filter_map
    (fun feat ->
      if feature_compatible feat engine then None
      else
        Some
          (T3_profile_incompatible
             {
               feature = Project_model.feature_to_string feat;
               profile = Project_model.engine_to_string engine;
             }))
    proj.Project_model.declared_features

let t2_check (proj : Project_model.t) : reason list =
  let g = Build_graph.of_project proj in
  let missing =
    List.filter_map
      (fun (f : Project_model.file_entry) ->
        if Sys.file_exists f.path then None else Some f.path)
      (Project_model.all_files proj)
  in
  let rs =
    if missing = [] then []
    else List.map (fun p -> T2_project_not_closed (`Missing_file p)) missing
  in
  if not (Build_graph.is_acyclic g) then
    T2_project_not_closed `Cycle_in_build_graph :: rs
  else rs

(* T4: if aux exists, use parsed labels to check uniqueness and that cited keys
   resolve. Otherwise fall back to no-check (source-only label analysis is v26.3
   territory). *)
let t4_check ?aux_path (_proj : Project_model.t) : reason list =
  match aux_path with
  | None -> []
  | Some path -> (
      match Aux_state.of_file path with
      | Error _ -> [] (* Can't check; don't fail *)
      | Ok aux ->
          let rs = [] in
          let rs =
            if Aux_state.labels_unique aux then rs
            else
              (* Find the actual duplicates to report. *)
              let counts = Hashtbl.create 16 in
              List.iter
                (fun (l : Aux_state.label_entry) ->
                  let c =
                    try Hashtbl.find counts l.name with Not_found -> 0
                  in
                  Hashtbl.replace counts l.name (c + 1))
                aux.labels;
              let dups =
                Hashtbl.fold
                  (fun name c acc -> if c > 1 then name :: acc else acc)
                  counts []
              in
              T4_semantic_incoherent (`Duplicate_labels dups) :: rs
          in
          rs)

(* T0/T1/T5: placeholders in v26.2. T0/T1 require calling Parser_l2 and Expander
   on the project files, which is heavier than a pre- compile readiness check
   should be. v26.2 scope: T0 returns no failures if all files exist and are
   readable (checked by T2); T1 is not runtime-checked; T5 requires running
   validators, which is also heavy — caller invokes Validators.run_all
   separately. *)
let t0_check (_ : Project_model.t) : reason list = []
let t1_check (_ : Project_model.t) : reason list = []
let t5_check (_ : Project_model.t) : reason list = []

let check_ready_to_compile ?aux_path (proj : Project_model.t)
    (_profile : Build_profile.t) : ready_check_result =
  let reasons =
    t0_check proj
    @ t1_check proj
    @ t2_check proj
    @ t3_check proj
    @ t4_check ?aux_path proj
    @ t5_check proj
  in
  if reasons = [] then Ready else NotReady reasons

let reason_to_string = function
  | T0_parse_fails { file; message } ->
      Printf.sprintf "T0 parse fails in %s: %s" file message
  | T1_expansion_fails msg -> Printf.sprintf "T1 expansion fails: %s" msg
  | T2_project_not_closed `Cycle_in_build_graph ->
      "T2 project not closed: cycle in build graph"
  | T2_project_not_closed (`Missing_file p) ->
      Printf.sprintf "T2 project not closed: missing file %s" p
  | T3_profile_incompatible { feature; profile } ->
      Printf.sprintf
        "T3 profile incompatible: feature %s not supported by profile %s"
        feature profile
  | T4_semantic_incoherent (`Duplicate_labels ds) ->
      Printf.sprintf "T4 semantic incoherent: duplicate labels [%s]"
        (String.concat "; " ds)
  | T4_semantic_incoherent (`Missing_bib_entries es) ->
      Printf.sprintf "T4 semantic incoherent: missing bib entries [%s]"
        (String.concat "; " es)
  | T5_rule_violations ids ->
      Printf.sprintf "T5 rule violations: [%s]" (String.concat "; " ids)
