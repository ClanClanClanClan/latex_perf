(** Bounded user-macro subset. See [macro_subset.mli].

    Implementation delegates to [User_macro_registry.classify] and re-packages
    the result so the subset concept is a first-class module independent of the
    registry's parsing machinery (memo §10.4). *)

type status = In_subset | Out_of_subset of string

let classify (def : User_macro_registry.user_macro_def) : status =
  let classified = User_macro_registry.classify def in
  match classified.status with
  | User_macro_registry.Supported -> In_subset
  | User_macro_registry.Unsupported msg -> Out_of_subset msg

let is_in_subset def =
  match classify def with In_subset -> true | Out_of_subset _ -> false

let reason = function In_subset -> None | Out_of_subset msg -> Some msg

let unsupported_features =
  [
    "arity > 9 (TeX-level limit)";
    "\\def inside body (catcode leak)";
    "\\csname…\\endcsname expansion (dynamic name)";
    "catcode mutation (\\catcode, \\let, \\edef)";
    "shell escape or primitive exec";
    "recursive redefinition without termination measure";
  ]
