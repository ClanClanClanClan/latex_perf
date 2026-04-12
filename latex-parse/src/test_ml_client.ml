(** Test ML client. 5 cases. *)

open Latex_parse_lib
open Test_helpers

let () =
  run "is_available returns false when no server" (fun tag ->
      (* No server running on 8091 *)
      expect (not (Ml_client.is_available ())) (tag ^ ": not available"));

  run "classify_batch empty -> empty" (fun tag ->
      let results = Ml_client.classify_batch [] in
      expect (results = []) (tag ^ ": empty"));

  run "classify_batch when unavailable -> empty" (fun tag ->
      let results =
        Ml_client.classify_batch
          [
            {
              Ml_client.bytes_b64 = "AAAA";
              rule_id = "TYPO-001";
              parser_features = [ 0.0; 0.0; 0.0; 0.0 ];
            };
          ]
      in
      expect (results = []) (tag ^ ": graceful empty"));

  run "classify_batch with bad port -> empty" (fun tag ->
      let results =
        Ml_client.classify_batch ~port:1
          [
            {
              Ml_client.bytes_b64 = "AAAA";
              rule_id = "TYPO-001";
              parser_features = [];
            };
          ]
      in
      expect (results = []) (tag ^ ": bad port graceful"));

  run "is_available caches result" (fun tag ->
      let a1 = Ml_client.is_available () in
      let a2 = Ml_client.is_available () in
      expect (a1 = a2) (tag ^ ": consistent"))

let () = finalise "ml-client"
