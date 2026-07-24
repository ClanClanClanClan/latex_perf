(* Uncommitted measurement driver: classify each file (paths on stdin) into
   LP-Core / LP-Extended / LP-Foreign and print tier + triggering feature ids. *)
let read_file p =
  let ic = open_in_bin p in
  Fun.protect ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let () =
  try
    while true do
      let path = input_line stdin in
      (try
         let src = read_file path in
         let tier, feats = Latex_parse_lib.Language_profile.classify_source src in
         let ids =
           feats
           |> List.map (fun (f : Latex_parse_lib.Unsupported_feature.t) -> f.id)
           |> List.sort_uniq compare |> String.concat ","
         in
         Printf.printf "%s\t%s\t%b\t%s\n"
           (Latex_parse_lib.Language_profile.tier_to_string tier)
           (if ids = "" then "-" else ids)
           (let needle = "\\documentclass" in
            let n = String.length src and m = String.length needle in
            let rec go i = i + m <= n && (String.sub src i m = needle || go (i+1)) in
            go 0)
           path
       with e -> Printf.printf "ERROR\t%s\t-\t%s\n" (Printexc.to_string e) path)
    done
  with End_of_file -> ()
