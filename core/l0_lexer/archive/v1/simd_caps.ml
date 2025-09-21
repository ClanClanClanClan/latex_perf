external is_rosetta : unit -> bool = "ocaml_is_rosetta"
external has_neon   : unit -> bool = "ocaml_has_neon"
let simd_available () = (not (is_rosetta())) && has_neon ()
let enforce_in_ci () =
  if Config.require_simd_in_ci && not (simd_available ())
  then failwith "SIMD required in CI but not available (Rosetta or NEON missing)."
