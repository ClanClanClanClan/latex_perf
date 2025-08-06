(* Dlist Module - Double-ended list (deque) *)
(* LaTeX Perfectionist v25 - Referenced in Section 3.1.1 *)

(** Double-ended list for efficient token streaming *)
type 'a t = {
  front: 'a list;  (* Front of the deque *)
  rear: 'a list;   (* Rear of the deque, stored in reverse *)
}

(** Empty deque *)
let empty = { front = []; rear = [] }

(** Check if deque is empty *)
let is_empty d = d.front = [] && d.rear = []

(** Add element to front *)
let cons x d = { d with front = x :: d.front }

(** Add element to rear *)
let snoc d x = { d with rear = x :: d.rear }

(** Remove element from front *)
let uncons = function
  | { front = []; rear = [] } -> None
  | { front = x :: xs; rear } -> Some (x, { front = xs; rear })
  | { front = []; rear } -> 
      (* Move rear to front *)
      let front = List.rev rear in
      begin match front with
      | [] -> None
      | x :: xs -> Some (x, { front = xs; rear = [] })
      end

(** Remove element from rear *)
let unsnoc = function
  | { front = []; rear = [] } -> None
  | { front; rear = x :: xs } -> Some ({ front; rear = xs }, x)
  | { front; rear = [] } ->
      (* Move front to rear *)
      let rear = List.rev front in
      begin match rear with
      | [] -> None
      | x :: xs -> Some ({ front = []; rear = xs }, x)
      end

(** Convert to list *)
let to_list d = d.front @ List.rev d.rear

(** Create from list *)
let of_list lst = { front = lst; rear = [] }

(** Length *)
let length d = List.length d.front + List.length d.rear

(** Append two deques *)
let append d1 d2 =
  { front = d1.front @ List.rev d1.rear @ d2.front; 
    rear = d2.rear }