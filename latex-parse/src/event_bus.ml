(* ══════════════════════════════════════════════════════════════════════
   Event_bus — live event dispatch for semantic deltas (spec W62)

   Validators subscribe to semantic events (label added, ref resolved, section
   started, etc.) and receive deltas as they occur.
   ══════════════════════════════════════════════════════════════════════ *)

type event =
  | LabelDefined of { key : string; position : int }
  | RefUsed of { key : string; position : int; command : string }
  | SectionStarted of { level : int; title : string; position : int }
  | EnvironmentOpened of { name : string; position : int }
  | EnvironmentClosed of { name : string; position : int }
  | DocumentBegin of int
  | DocumentEnd of int
  | TaskScheduled of { task_id : string; deadline : float }
  | TaskCompleted of { task_id : string; elapsed_ms : float }
  | DeadlineMissed of { task_id : string; deadline : float; actual : float }

type handler = event -> unit

type bus = {
  mutable handlers : (string * handler) list;
  mutable event_count : int;
}

let create () : bus = { handlers = []; event_count = 0 }

let subscribe (bus : bus) (name : string) (handler : handler) : unit =
  bus.handlers <- (name, handler) :: bus.handlers

let unsubscribe (bus : bus) (name : string) : unit =
  bus.handlers <- List.filter (fun (n, _) -> n <> name) bus.handlers

let publish (bus : bus) (event : event) : unit =
  bus.event_count <- bus.event_count + 1;
  List.iter (fun (_, handler) -> handler event) bus.handlers

let event_count (bus : bus) : int = bus.event_count

(* ── Global bus instance ────────────────────────────────────── *)

let _global_bus = create ()
let global () : bus = _global_bus
let publish_global (event : event) : unit = publish _global_bus event

let subscribe_global (name : string) (handler : handler) : unit =
  subscribe _global_bus name handler

(* ── Event generation from source scan ──────────────────────── *)

let scan_and_publish (bus : bus) (src : string) : unit =
  let re_label = Str.regexp {|\\label{\([^}]+\)}|} in
  let re_ref = Str.regexp {|\\ref{\([^}]+\)}|} in
  let re_section = Str.regexp {|\\section{\([^}]+\)}|} in
  let re_begin = Str.regexp {|\\begin{\([^}]+\)}|} in
  let re_end = Str.regexp {|\\end{\([^}]+\)}|} in
  let scan re mk_event =
    let i = ref 0 in
    try
      while true do
        let pos = Str.search_forward re src !i in
        let g1 = Str.matched_group 1 src in
        publish bus (mk_event g1 pos);
        i := Str.match_end ()
      done
    with Not_found -> ()
  in
  scan re_label (fun key pos -> LabelDefined { key; position = pos });
  scan re_ref (fun key pos -> RefUsed { key; position = pos; command = "ref" });
  scan re_section (fun title pos ->
      SectionStarted { level = 1; title; position = pos });
  scan re_begin (fun name pos -> EnvironmentOpened { name; position = pos });
  scan re_end (fun name pos -> EnvironmentClosed { name; position = pos })
