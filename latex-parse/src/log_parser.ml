(* ══════════════════════════════════════════════════════════════════════
   Log_parser — parse LaTeX compile output (.log files)

   Extracts structured events from LaTeX log files: - Overfull/underfull \hbox
   and \vbox warnings - Page numbers - Float placement warnings - Widow/orphan
   warnings - General LaTeX warnings with line numbers
   ══════════════════════════════════════════════════════════════════════ *)

type box_type = Hbox | Vbox

type log_event =
  | Overfull of {
      box : box_type;
      amount_pt : float;
      line_start : int;
      line_end : int;
    }
  | Underfull of { box : box_type; badness : int; line_start : int }
  | PageNumber of int
  | WidowPenalty of { page : int }
  | ClubPenalty of { page : int }
  | FloatWarning of { message : string; line : int }
  | LatexWarning of { message : string; line : int }

type log_context = {
  events : log_event list;
  overfull_lines : (int * int) list;
  underfull_lines : int list;
  pages : int list;
  max_overfull_pt : float;
  has_widows : bool;
  has_orphans : bool;
}

let empty_context =
  {
    events = [];
    overfull_lines = [];
    underfull_lines = [];
    pages = [];
    max_overfull_pt = 0.0;
    has_widows = false;
    has_orphans = false;
  }

(* ── Regex patterns for log parsing ─────────────────────────────── *)

let re_overfull_hbox =
  Str.regexp
    {|Overfull \\hbox (\([0-9.]+\)pt too wide) in paragraph at lines \([0-9]+\)--\([0-9]+\)|}

let re_overfull_vbox = Str.regexp {|Overfull \\vbox (\([0-9.]+\)pt too high)|}

let re_underfull_hbox =
  Str.regexp
    {|Underfull \\hbox (badness \([0-9]+\)) in paragraph at lines \([0-9]+\)|}

let re_underfull_vbox = Str.regexp {|Underfull \\vbox (badness \([0-9]+\))|}
let re_page_number = Str.regexp {|\[\([0-9]+\)\]|}

let re_float_warning =
  Str.regexp {|LaTeX Warning: Float too large.*input line \([0-9]+\)|}

let _re_latex_warning =
  Str.regexp {|LaTeX Warning: \(.*\) on input line \([0-9]+\)|}

let re_widow = Str.regexp_string "Widow penalty"
let re_club = Str.regexp_string "Club penalty"

(* ── Parser ─────────────────────────────────────────────────────── *)

let parse_log (content : string) : log_context =
  let events = ref [] in
  let lines = String.split_on_char '\n' content in
  List.iter
    (fun line ->
      (* Overfull \hbox *)
      (try
         ignore (Str.search_forward re_overfull_hbox line 0);
         let amt = float_of_string (Str.matched_group 1 line) in
         let ls = int_of_string (Str.matched_group 2 line) in
         let le = int_of_string (Str.matched_group 3 line) in
         events :=
           Overfull
             { box = Hbox; amount_pt = amt; line_start = ls; line_end = le }
           :: !events
       with Not_found | Failure _ -> ());
      (* Overfull \vbox *)
      (try
         ignore (Str.search_forward re_overfull_vbox line 0);
         let amt = float_of_string (Str.matched_group 1 line) in
         events :=
           Overfull
             { box = Vbox; amount_pt = amt; line_start = 0; line_end = 0 }
           :: !events
       with Not_found | Failure _ -> ());
      (* Underfull \hbox *)
      (try
         ignore (Str.search_forward re_underfull_hbox line 0);
         let bad = int_of_string (Str.matched_group 1 line) in
         let ls = int_of_string (Str.matched_group 2 line) in
         events :=
           Underfull { box = Hbox; badness = bad; line_start = ls } :: !events
       with Not_found | Failure _ -> ());
      (* Underfull \vbox *)
      (try
         ignore (Str.search_forward re_underfull_vbox line 0);
         let bad = int_of_string (Str.matched_group 1 line) in
         events :=
           Underfull { box = Vbox; badness = bad; line_start = 0 } :: !events
       with Not_found | Failure _ -> ());
      (* Page numbers *)
      let i = ref 0 in
      (try
         while true do
           ignore (Str.search_forward re_page_number line !i);
           let pg = int_of_string (Str.matched_group 1 line) in
           events := PageNumber pg :: !events;
           i := Str.match_end ()
         done
       with Not_found -> ());
      (* Float warnings *)
      (try
         ignore (Str.search_forward re_float_warning line 0);
         let ln = int_of_string (Str.matched_group 1 line) in
         events := FloatWarning { message = line; line = ln } :: !events
       with Not_found | Failure _ -> ());
      (* Widow/club penalties *)
      (try
         ignore (Str.search_forward re_widow line 0);
         events := WidowPenalty { page = 0 } :: !events
       with Not_found -> ());
      try
        ignore (Str.search_forward re_club line 0);
        events := ClubPenalty { page = 0 } :: !events
      with Not_found -> ())
    lines;
  let events = List.rev !events in
  let overfull_lines =
    List.filter_map
      (function
        | Overfull { box = Hbox; line_start; line_end; _ } ->
            Some (line_start, line_end)
        | _ -> None)
      events
  in
  let underfull_lines =
    List.filter_map
      (function
        | Underfull { line_start; _ } when line_start > 0 -> Some line_start
        | _ -> None)
      events
  in
  let pages =
    List.filter_map (function PageNumber p -> Some p | _ -> None) events
  in
  let max_overfull_pt =
    List.fold_left
      (fun mx -> function
        | Overfull { amount_pt; _ } -> max mx amount_pt
        | _ -> mx)
      0.0 events
  in
  let has_widows =
    List.exists (function WidowPenalty _ -> true | _ -> false) events
  in
  let has_orphans =
    List.exists (function ClubPenalty _ -> true | _ -> false) events
  in
  {
    events;
    overfull_lines;
    underfull_lines;
    pages;
    max_overfull_pt;
    has_widows;
    has_orphans;
  }

(* ── Thread-local log context ───────────────────────────────────── *)

let _log_ctx_tbl : (int, log_context) Hashtbl.t = Hashtbl.create 4

let set_log_context (ctx : log_context) : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.replace _log_ctx_tbl tid ctx

let get_log_context () : log_context option =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.find_opt _log_ctx_tbl tid

let clear_log_context () : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.remove _log_ctx_tbl tid
