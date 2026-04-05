(** Parse LaTeX compile output (.log files) into structured events. *)

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

val empty_context : log_context
val parse_log : string -> log_context

(** Thread-local log context for validators that need compile-log data. *)

val set_log_context : log_context -> unit
val get_log_context : unit -> log_context option
val clear_log_context : unit -> unit
