(** ML sidecar client — HTTP client for byte_classifier_server.

    Sends batch classification requests to the Python ML sidecar on port 8091.
    Falls back gracefully to empty results if the server is unavailable.
    Availability is cached for 30 seconds. *)

type classify_request = {
  bytes_b64 : string;
  rule_id : string;
  parser_features : float list;
}

type classify_response = { rule_id : string; p_violation : float }

val classify_batch :
  ?host:string -> ?port:int -> classify_request list -> classify_response list

val is_available : unit -> bool
