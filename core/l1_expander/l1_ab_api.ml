(* Minimal, safe tokenizer for control sequences to exercise the expander. *)

type tok =
  | Control of string
  | Text of string

let tokenize_controls (s:string) : tok list =
  let n = String.length s in
  let rec take_ident i = if i<n && ((s.[i] >= 'a' && s.[i] <= 'z') || (s.[i] >= 'A' && s.[i] <= 'Z')) then take_ident (i+1) else i in
  let rec loop i acc =
    if i >= n then List.rev acc
    else if s.[i] = '\\' then
      let j = take_ident (i+1) in
      if j = i+1 then loop (i+1) (Text "\\" :: acc)
      else let name = String.sub s (i+1) (j - (i+1)) in loop j (Control name :: acc)
    else
      (* accumulate non-control chars as text chunks *)
      let j = ref i in
      while !j < n && s.[!j] <> '\\' do incr j done;
      loop !j (Text (String.sub s i (!j - i)) :: acc)
  in loop 0 []

let summarize (toks:tok list) : (int * int) =
  List.fold_left (fun (c_ctrl, c_text) -> function Control _ -> (c_ctrl+1, c_text) | Text _ -> (c_ctrl, c_text+1)) (0,0) toks

(* Strategies (placeholder: identical for now; ready to diverge). *)
let tokenize_a = tokenize_controls

let tokenize_b (s:string) : tok list =
  (* Variant strategy: treat control names case-insensitively by normalizing
     to lowercase. Text chunks are left intact. *)
  let toks = tokenize_controls s in
  List.map (function
    | Control name -> Control (String.lowercase_ascii name)
    | Text t -> Text t
  ) toks

let equal_toks (a:tok list) (b:tok list) : bool =
  let rec eq = function
    | ([],[]) -> true
    | (Control x::xs, Control y::ys) -> x=y && eq (xs,ys)
    | (Text x::xs, Text y::ys) -> x=y && eq (xs,ys)
    | _ -> false
  in eq (a,b)
