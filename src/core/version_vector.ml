(* Version Vector - Simple implementation for LaTeX Perfectionist v25 *)
(* Provides version tracking and compatibility management *)

type t = {
  major: int;
  minor: int;
  patch: int;
  revision: string option;
}

let current = {
  major = 25;
  minor = 0;
  patch = 0;
  revision = Some "R0";
}

let create ~major ~minor ~patch ?revision () = 
  { major; minor; patch; revision }

let to_string v =
  match v.revision with
  | Some r -> Printf.sprintf "v%d.%d.%d-%s" v.major v.minor v.patch r
  | None -> Printf.sprintf "v%d.%d.%d" v.major v.minor v.patch

let compare v1 v2 =
  let c = Int.compare v1.major v2.major in
  if c <> 0 then c else
  let c = Int.compare v1.minor v2.minor in
  if c <> 0 then c else
  Int.compare v1.patch v2.patch

let is_compatible ~required ~actual =
  (* Major version must match exactly *)
  required.major = actual.major &&
  (* Minor version of actual must be >= required *)
  (actual.minor > required.minor ||
   (actual.minor = required.minor && actual.patch >= required.patch))

let parse s =
  try
    let s = if String.get s 0 = 'v' then String.sub s 1 (String.length s - 1) else s in
    match String.split_on_char '-' s with
    | [version] ->
        (match String.split_on_char '.' version with
         | [major; minor; patch] ->
             Some { major = int_of_string major;
                    minor = int_of_string minor;
                    patch = int_of_string patch;
                    revision = None }
         | _ -> None)
    | [version; revision] ->
        (match String.split_on_char '.' version with
         | [major; minor; patch] ->
             Some { major = int_of_string major;
                    minor = int_of_string minor;
                    patch = int_of_string patch;
                    revision = Some revision }
         | _ -> None)
    | _ -> None
  with _ -> None