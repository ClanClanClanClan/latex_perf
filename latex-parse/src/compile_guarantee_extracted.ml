(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the capstone premise-checker
   [CompileGuaranteeBridge.project_wf_dec] and all its dependencies (data model
   + boolean sub-checkers). Regenerate with
   scripts/tools/regen_compile_guarantee_extract.sh from
   proofs/CompileGuaranteeExtract.v.

   [project_wf_dec] here is the PROVEN checker itself (not a hand mirror): the
   Coq lemma [project_wf_dec_sound] (Qed, 0 admits) proves a [true] verdict is
   sufficient for [PdflatexModel.pdflatex_compile_safe]. [Compile_evidence]
   executes this module for the [--compile-check] decision.

   nat is extracted to OCaml int (ExtrOcamlNatInt): label ids are 30-bit hashes,
   for which a Peano representation would be catastrophic. *)

[@@@warning "-a"]

let negb = function true -> false | false -> true
let fst = function x, _ -> x
let snd = function _, y -> y

module Nat = struct
  let ltb n m = Stdlib.Int.succ n <= m
end

let existsb f =
  let rec existsb0 = function [] -> false | a :: l0 -> f a || existsb0 l0 in
  existsb0

let forallb f =
  let rec forallb0 = function [] -> true | a :: l0 -> f a && forallb0 l0 in
  forallb0

type file_id = int
type artefact_kind = Tex | Aux | Bbl | Bib | Pdf | Log

let artefact_kind_eqb a b =
  match a with
  | Tex -> (
      match b with
      | Tex -> true
      | Aux -> false
      | Bbl -> false
      | Bib -> false
      | Pdf -> false
      | Log -> false)
  | Aux -> (
      match b with
      | Tex -> false
      | Aux -> true
      | Bbl -> false
      | Bib -> false
      | Pdf -> false
      | Log -> false)
  | Bbl -> (
      match b with
      | Tex -> false
      | Aux -> false
      | Bbl -> true
      | Bib -> false
      | Pdf -> false
      | Log -> false)
  | Bib -> (
      match b with
      | Tex -> false
      | Aux -> false
      | Bbl -> false
      | Bib -> true
      | Pdf -> false
      | Log -> false)
  | Pdf -> (
      match b with
      | Tex -> false
      | Aux -> false
      | Bbl -> false
      | Bib -> false
      | Pdf -> true
      | Log -> false)
  | Log -> (
      match b with
      | Tex -> false
      | Aux -> false
      | Bbl -> false
      | Bib -> false
      | Pdf -> false
      | Log -> true)

type node = { n_file : file_id; n_kind : artefact_kind }

let node_eqb a b = a.n_file = b.n_file && artefact_kind_eqb a.n_kind b.n_kind

type edge = node * node
type build_graph = { bg_nodes : node list; bg_edges : edge list }

let rec index_of n = function
  | [] -> None
  | x :: xs -> (
      if node_eqb x n then Some 0
      else
        match index_of n xs with
        | Some i -> Some (Stdlib.Int.succ i)
        | None -> None)

type engine = Pdflatex | Xelatex | Lualatex | Ptex_uptex

type feature =
  | UTF8_inputenc
  | UTF8_direct
  | Unicode_math
  | Opentype_fonts
  | Lua_scripting
  | Japanese_cjk
  | Bibtex
  | Biber

let compatible f e =
  match f with
  | UTF8_inputenc -> (
      match e with
      | Pdflatex -> true
      | Xelatex -> true
      | Lualatex -> true
      | Ptex_uptex -> false)
  | UTF8_direct -> (
      match e with
      | Pdflatex -> false
      | Xelatex -> true
      | Lualatex -> true
      | Ptex_uptex -> false)
  | Unicode_math -> (
      match e with
      | Pdflatex -> false
      | Xelatex -> true
      | Lualatex -> true
      | Ptex_uptex -> false)
  | Opentype_fonts -> (
      match e with
      | Pdflatex -> false
      | Xelatex -> true
      | Lualatex -> true
      | Ptex_uptex -> false)
  | Lua_scripting -> (
      match e with
      | Pdflatex -> false
      | Xelatex -> false
      | Lualatex -> true
      | Ptex_uptex -> false)
  | Japanese_cjk -> (
      match e with
      | Pdflatex -> false
      | Xelatex -> false
      | Lualatex -> false
      | Ptex_uptex -> true)
  | Bibtex -> true
  | Biber -> true

let rec all_features_compatible fs e =
  match fs with
  | [] -> true
  | f :: rest -> compatible f e && all_features_compatible rest e

type body_token =
  | BT_text
  | BT_label_def of int
  | BT_label_ref of int
  | BT_needs_feature of feature

let rec body_required_features = function
  | [] -> []
  | b :: rest -> (
      match b with
      | BT_text -> body_required_features rest
      | BT_label_def _ -> body_required_features rest
      | BT_label_ref _ -> body_required_features rest
      | BT_needs_feature f -> f :: body_required_features rest)

let rec body_label_defs = function
  | [] -> []
  | b :: rest -> (
      match b with
      | BT_text -> body_label_defs rest
      | BT_label_def n -> n :: body_label_defs rest
      | BT_label_ref _ -> body_label_defs rest
      | BT_needs_feature _ -> body_label_defs rest)

type pdflatex_project = {
  proj_graph : build_graph;
  proj_body : body_token list;
}

type pdflatex_profile = { prof_engine : engine; prof_features : feature list }

let node_in_b n ns = existsb (fun m -> node_eqb m n) ns

let edges_closed_b g =
  forallb
    (fun e -> node_in_b (fst e) g.bg_nodes && node_in_b (snd e) g.bg_nodes)
    g.bg_edges

let index_lt_b order u v =
  match index_of u order with
  | Some iu -> (
      match index_of v order with Some iv -> Nat.ltb iv iu | None -> false)
  | None -> false

let valid_topo_b g order =
  forallb (fun e -> index_lt_b order (fst e) (snd e)) g.bg_edges

let project_closed_b g order = edges_closed_b g && valid_topo_b g order

let rec mem_nat_b n = function
  | [] -> false
  | x :: xs -> x = n || mem_nat_b n xs

let rec nodup_nat_b = function
  | [] -> true
  | x :: xs -> negb (mem_nat_b x xs) && nodup_nat_b xs

let project_wf_dec p pf order =
  ((project_closed_b p.proj_graph order
   && all_features_compatible pf.prof_features pf.prof_engine)
  && all_features_compatible (body_required_features p.proj_body) pf.prof_engine
  )
  && nodup_nat_b (body_label_defs p.proj_body)
