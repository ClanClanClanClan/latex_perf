(** Extension_registry — WS12 Stage 2: built-in package/tooling contract
    registry and the extension-provides query surface for LP-Extended.

    WS12 Stage 1 ({!Extension_contract}) defines the extension contract type,
    the risk/support ordering, the over-claim check, and the
    {!Extension_contract.evaluate} foreign-contract boundary that folds a set of
    contracts against a base support level. Stage 1's contracts came only from
    an external JSON manifest.

    This module (Stage 2) adds the {b principled built-in catalogue} the spec
    calls "package/tooling contracts for LP-Extended": a small, static registry
    of extension contracts for well-known packages (tikz, minted, mhchem,
    biblatex, listings), each with the risk classification and support level
    that encodes the project's support policy. It also exposes the
    {b extension-provides API} — a stable query surface answering "which
    extension provides this rule-id / feature tag?" and "given a set of active
    extensions, what is the union of provided rule-ids / features?".

    Together these let the system recognise that a feature enters through a
    DECLARED contract (built-in or manifest) rather than as an unknown foreign
    feature, and to compute the effective support of a set of active packages
    via the same Stage-1 {!Extension_contract.evaluate}.

    {b Over-claim safety (structural).} Every built-in contract is constructed
    through {!mk}, which clamps the declared support to
    {!Extension_contract.max_support_for_risk} of its risk. It is therefore
    IMPOSSIBLE for a built-in to declare a guarantee stronger than its risk
    allows — every entry in {!builtin} satisfies
    [Extension_contract.over_claims = false] by construction. This module reuses
    Stage 1; it does not duplicate its logic. *)

module E = Extension_contract

(** Smart constructor for a built-in contract. The declared [support] is CLAMPED
    to the strongest level the [risk] legitimately allows
    ([Extension_contract.support_min support (max_support_for_risk risk)]), so a
    built-in can never over-claim: the resulting contract always satisfies
    [Extension_contract.over_claims = false]. *)
let mk ~name ~provides ~requires ~(risk : E.risk) ~(support : E.support) :
    E.contract =
  {
    E.ext_name = name;
    provides;
    requires;
    risk;
    support = E.support_min support (E.max_support_for_risk risk);
  }

(** The built-in extension contract registry: the project's support policy for
    well-known LP-Extended packages and tooling, encoded as
    {!Extension_contract.contract}s.

    - [tikz] / [pgf] — arbitrary drawing macros; powerful but self-contained.
      Risk [Review], support [Community].
    - [minted] — shells out to an external highlighter (requires shell-escape);
      executes foreign tooling. Risk [Unsafe], support [Foreign].
    - [mhchem] — chemistry markup ([\ce]); well-scoped and stable. Risk [Safe],
      support [Supported].
    - [biblatex] — bibliography backend; stable, first-class. Risk [Safe],
      support [Supported].
    - [listings] — verbatim code listings; benign but interacts with catcodes.
      Risk [Review], support [Community].

    Each entry lists the rule-ids / feature tags it [provides] and the packages
    it [requires]. *)
let builtin : E.contract list =
  [
    mk ~name:"tikz"
      ~provides:[ "tikzpicture"; "pgfplots"; "TIKZ-001" ]
      ~requires:[ "pgf" ] ~risk:E.Review ~support:E.Community;
    mk ~name:"minted"
      ~provides:[ "minted-listing"; "VERB-006" ]
      ~requires:[ "fancyvrb"; "shell-escape" ]
      ~risk:E.Unsafe ~support:E.Foreign;
    mk ~name:"mhchem"
      ~provides:[ "chem-equation"; "CHEM-001" ]
      ~requires:[] ~risk:E.Safe ~support:E.Supported;
    mk ~name:"biblatex"
      ~provides:[ "bibliography"; "BIB-011" ]
      ~requires:[ "biber" ] ~risk:E.Safe ~support:E.Supported;
    mk ~name:"listings"
      ~provides:[ "lstlisting"; "VERB-010" ]
      ~requires:[] ~risk:E.Review ~support:E.Community;
  ]

(** [lookup name] is the built-in contract registered under exactly [name], or
    [None] for an unknown extension. This is the principled catalogue lookup: an
    unknown name returns [None] (it is NOT silently treated as a declared
    contract). *)
let lookup (name : string) : E.contract option =
  List.find_opt (fun (c : E.contract) -> c.E.ext_name = name) builtin

(** [providers_of tag] is the list of built-in contracts whose [provides]
    includes [tag] (a rule-id or feature tag). Empty if no built-in provides it
    — i.e. the feature does not enter through a declared built-in contract. *)
let providers_of (tag : string) : E.contract list =
  List.filter (fun (c : E.contract) -> List.mem tag c.E.provides) builtin

(** [provides_of_names names] is the union of the [provides] lists of every
    KNOWN built-in extension in [names], de-duplicated and sorted. Unknown names
    contribute nothing (they provide no declared feature). This is the set of
    rule-ids / feature tags that legitimately enter through the given active
    extensions. *)
let provides_of_names (names : string list) : string list =
  names
  |> List.filter_map lookup
  |> List.concat_map (fun (c : E.contract) -> c.E.provides)
  |> List.sort_uniq String.compare

(** [contracts_of_names names] partitions [names] into ([known], [unknown]):
    [known] is the built-in contracts for the recognised names (in the order
    they appear in [names]); [unknown] is the names with no built-in contract.
    The caller can feed [known] to {!Extension_contract.evaluate} and treat
    [unknown] as undeclared foreign features. *)
let contracts_of_names (names : string list) : E.contract list * string list =
  List.fold_right
    (fun name (known, unknown) ->
      match lookup name with
      | Some c -> (c :: known, unknown)
      | None -> (known, name :: unknown))
    names ([], [])

(** [evaluate_names ~base names] resolves the recognised built-in extensions in
    [names] and computes the effective support level via the Stage-1
    {!Extension_contract.evaluate} boundary, returning the evaluation result
    alongside the list of UNKNOWN (undeclared) names. Because every built-in is
    over-claim-free by construction, the [Error] branch cannot arise from a
    built-in; it can only surface manifest-style rejections if the registry were
    ever extended with an over-claiming entry (a case the unit tests forbid). *)
let evaluate_names ~(base : E.support) (names : string list) :
    (E.effective, E.rejection list) result * string list =
  let known, unknown = contracts_of_names names in
  (E.evaluate ~base known, unknown)

(** [well_formed ()] is [true] iff EVERY built-in contract passes the Stage-1
    over-claim check ([Extension_contract.over_claims = false]). It holds by
    construction (see {!mk}); it is exposed so callers and tests can assert the
    registry invariant directly. *)
let well_formed () : bool =
  not (List.exists (fun (c : E.contract) -> E.over_claims c) builtin)
