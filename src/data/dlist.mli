(* Dlist Module Interface - Double-ended list (deque) *)
(* LaTeX Perfectionist v25 - Referenced in Section 3.1.1 *)

(** Double-ended list (deque) - strict deque for token streaming *)
type 'a t

(** Empty deque *)
val empty : 'a t

(** Check if empty *)
val is_empty : 'a t -> bool

(** Add element to front O(1) *)
val cons : 'a -> 'a t -> 'a t

(** Add element to rear O(1) *)
val snoc : 'a t -> 'a -> 'a t

(** Remove from front O(1) amortized *)
val uncons : 'a t -> ('a * 'a t) option

(** Remove from rear O(1) amortized *)
val unsnoc : 'a t -> ('a t * 'a) option

(** Convert to list *)
val to_list : 'a t -> 'a list

(** Create from list *)
val of_list : 'a list -> 'a t

(** Length *)
val length : 'a t -> int

(** Append two deques *)
val append : 'a t -> 'a t -> 'a t