
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val leb : int -> int -> bool **)

let rec leb n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n0

(** val tail_add : int -> int -> int **)

let rec tail_add n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n1 -> tail_add n1 (Stdlib.Int.succ m))
    n0

(** val tail_addmul : int -> int -> int -> int **)

let rec tail_addmul r n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> r)
    (fun n1 -> tail_addmul (tail_add m r) n1 m)
    n0

(** val tail_mul : int -> int -> int **)

let tail_mul n0 m =
  tail_addmul 0 n0 m

(** val of_uint_acc : uint -> int -> int **)

let rec of_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))))

(** val of_uint : uint -> int **)

let of_uint d =
  of_uint_acc d 0

(** val of_hex_uint_acc : uint0 -> int -> int **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)
  | D11 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))
  | D12 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : uint0 -> int **)

let of_hex_uint d =
  of_hex_uint_acc d 0

(** val of_num_uint : uint1 -> int **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

(** val divmod : int -> int -> int -> int -> int * int **)

let rec divmod x y q u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (q, u))
    (fun x' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> divmod x' y (Stdlib.Int.succ q) y)
      (fun u' -> divmod x' y q u')
      u)
    x

(** val div : int -> int -> int **)

let div x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> y)
    (fun y' -> fst (divmod x y' 0 y'))
    y

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    (<=) (Stdlib.Int.succ n0) m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Stdlib.Int.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  (** val to_nat : n -> int **)

  let to_nat = function
  | N0 -> 0
  | Npos p -> Pos.to_nat p

  (** val of_nat : int -> n **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> N0)
      (fun n' -> Npos (Pos.of_succ_nat n'))
      n0
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      match p with
      | XI p' -> shift true (loop n' p')
      | XO p' -> shift false (loop n' p')
      | XH -> one)
      n0
  in loop (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b :: l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t -> app (f x) (flat_map f t)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n1 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n1 l0))
    n0

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val length0 : char list -> int **)

let rec length0 = function
| [] -> 0
| _::s' -> Stdlib.Int.succ (length0 s')

type latex_token =
| TCommand of char list
| TBeginGroup
| TEndGroup
| TMathShift
| TAlignment
| TParameter
| TSuperscript
| TSubscript
| TText of char list
| TSpace
| TComment of char list
| TNewline
| TEOF

type layer =
| L0_Lexer
| L1_Expanded
| L2_Ast
| L3_Semantics
| L4_Style

type severity =
| Error
| Warning
| Info

type maturity =
| Draft
| Stable
| Proven

type bucket =
| TokenKind_Text
| TokenKind_Command
| TokenKind_MathShift
| TokenKind_BeginGroup
| TokenKind_EndGroup
| TokenKind_Other

type location = { line : int; column : int; file : char list option }

type validation_issue = { rule_id : char list; issue_severity : severity;
                          message : char list; loc : location option;
                          suggested_fix : char list option;
                          rule_owner : char list }

type document_state = { tokens : latex_token list;
                        expanded_tokens : latex_token list option;
                        ast : char list option; semantics : char list option;
                        filename : char list; doc_layer : layer }

type soundness_proof =
  char list
  (* singleton inductive, whose constructor was ProofRef *)

type validation_rule = { id : char list; description : char list;
                         precondition : layer; default_severity : severity;
                         rule_maturity : maturity; owner : char list;
                         performance_bucket : bucket;
                         auto_fix : char list option;
                         implementation_file : char list;
                         validator : (document_state -> validation_issue list);
                         rule_sound : soundness_proof option }

(** val rule_applicable : validation_rule -> document_state -> bool **)

let rule_applicable rule doc =
  match rule.precondition with
  | L0_Lexer -> true
  | L1_Expanded -> (match doc.doc_layer with
                    | L0_Lexer -> false
                    | _ -> true)
  | L2_Ast ->
    (match doc.doc_layer with
     | L0_Lexer -> false
     | L1_Expanded -> false
     | _ -> true)
  | L3_Semantics ->
    (match doc.doc_layer with
     | L3_Semantics -> true
     | L4_Style -> true
     | _ -> false)
  | L4_Style -> (match doc.doc_layer with
                 | L4_Style -> true
                 | _ -> false)

(** val execute_rule :
    validation_rule -> document_state -> validation_issue list **)

let execute_rule rule doc =
  if rule_applicable rule doc then rule.validator doc else []

(** val execute_rules :
    validation_rule list -> document_state -> validation_issue list **)

let rec execute_rules rules doc =
  match rules with
  | [] -> []
  | rule :: rest -> app (execute_rule rule doc) (execute_rules rest doc)

(** val bucket_eq : bucket -> bucket -> bool **)

let bucket_eq b1 b2 =
  match b1 with
  | TokenKind_Text -> (match b2 with
                       | TokenKind_Text -> true
                       | _ -> false)
  | TokenKind_Command ->
    (match b2 with
     | TokenKind_Command -> true
     | _ -> false)
  | TokenKind_MathShift ->
    (match b2 with
     | TokenKind_MathShift -> true
     | _ -> false)
  | TokenKind_BeginGroup ->
    (match b2 with
     | TokenKind_BeginGroup -> true
     | _ -> false)
  | TokenKind_EndGroup ->
    (match b2 with
     | TokenKind_EndGroup -> true
     | _ -> false)
  | TokenKind_Other -> (match b2 with
                        | TokenKind_Other -> true
                        | _ -> false)

(** val execute_rules_bucketed :
    validation_rule list -> document_state -> validation_issue list **)

let execute_rules_bucketed rules doc =
  let bucket_map = fun bucket0 ->
    filter (fun rule -> bucket_eq rule.performance_bucket bucket0) rules
  in
  let text_rules = bucket_map TokenKind_Text in
  let command_rules = bucket_map TokenKind_Command in
  let begin_group_rules = bucket_map TokenKind_BeginGroup in
  let end_group_rules = bucket_map TokenKind_EndGroup in
  let math_rules = bucket_map TokenKind_MathShift in
  let other_rules = bucket_map TokenKind_Other in
  app (execute_rules text_rules doc)
    (app (execute_rules command_rules doc)
      (app (execute_rules begin_group_rules doc)
        (app (execute_rules end_group_rules doc)
          (app (execute_rules math_rules doc) (execute_rules other_rules doc)))))

(** val string_contains : char list -> char -> bool **)

let rec string_contains s c =
  match s with
  | [] -> false
  | c'::s' -> if (=) c c' then true else string_contains s' c

(** val string_prefix : char list -> char list -> bool **)

let rec string_prefix prefix s =
  match prefix with
  | [] -> true
  | c1::rest1 ->
    (match s with
     | [] -> false
     | c2::rest2 -> if (=) c1 c2 then string_prefix rest1 rest2 else false)

(** val string_contains_substring : char list -> char list -> bool **)

let rec string_contains_substring haystack needle =
  match haystack with
  | [] -> (match needle with
           | [] -> true
           | _::_ -> false)
  | _::rest ->
    if string_prefix needle haystack
    then true
    else string_contains_substring rest needle

(** val count_char : char list -> char -> int **)

let rec count_char s c =
  match s with
  | [] -> 0
  | c'::rest ->
    if (=) c c'
    then Stdlib.Int.succ (count_char rest c)
    else count_char rest c

(** val string_ends_with_spaces : char list -> bool **)

let rec string_ends_with_spaces = function
| [] -> false
| c::rest ->
  (match rest with
   | [] -> if (=) c ' ' then true else false
   | _::_ -> string_ends_with_spaces rest)

(** val string_eqb : char list -> char list -> bool **)

let string_eqb s1 s2 =
  if string_dec s1 s2 then true else false

(** val typo_001_check : char list -> bool **)

let typo_001_check s =
  string_contains s
    (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))))))))))))))))))))))))))))))

(** val typo_001_validator : document_state -> validation_issue list **)

let typo_001_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_001_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('1'::[]))))))));
             issue_severity = Error; message =
             ('A'::('S'::('C'::('I'::('I'::(' '::('s'::('t'::('r'::('a'::('i'::('g'::('h'::('t'::(' '::('q'::('u'::('o'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('c'::('u'::('r'::('l'::('y'::(' '::('q'::('u'::('o'::('t'::('e'::('s'::[]))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_001_rule : validation_rule **)

let typo_001_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('1'::[]))))))));
    description =
    ('A'::('S'::('C'::('I'::('I'::(' '::('s'::('t'::('r'::('a'::('i'::('g'::('h'::('t'::(' '::('q'::('u'::('o'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('c'::('u'::('r'::('l'::('y'::(' '::('q'::('u'::('o'::('t'::('e'::('s'::[]))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_001_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_002_check : char list -> bool **)

let typo_002_check s =
  string_contains_substring s ('-'::('-'::[]))

(** val typo_002_validator : document_state -> validation_issue list **)

let typo_002_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_002_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('2'::[]))))))));
             issue_severity = Warning; message =
             ('D'::('o'::('u'::('b'::('l'::('e'::(' '::('h'::('y'::('p'::('h'::('e'::('n'::(' '::('-'::('-'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('e'::('n'::('-'::('d'::('a'::('s'::('h'::[]))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_002_rule : validation_rule **)

let typo_002_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('2'::[]))))))));
    description =
    ('D'::('o'::('u'::('b'::('l'::('e'::(' '::('h'::('y'::('p'::('h'::('e'::('n'::(' '::('-'::('-'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('e'::('n'::('-'::('d'::('a'::('s'::('h'::[]))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_002_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_003_check : char list -> bool **)

let typo_003_check s =
  string_contains_substring s ('-'::('-'::('-'::[])))

(** val typo_003_validator : document_state -> validation_issue list **)

let typo_003_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_003_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('3'::[]))))))));
             issue_severity = Warning; message =
             ('T'::('r'::('i'::('p'::('l'::('e'::(' '::('h'::('y'::('p'::('h'::('e'::('n'::(' '::('-'::('-'::('-'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('e'::('m'::('-'::('d'::('a'::('s'::('h'::[])))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_003_rule : validation_rule **)

let typo_003_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('3'::[]))))))));
    description =
    ('T'::('r'::('i'::('p'::('l'::('e'::(' '::('h'::('y'::('p'::('h'::('e'::('n'::(' '::('-'::('-'::('-'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('e'::('m'::('-'::('d'::('a'::('s'::('h'::[])))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_003_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_004_check : char list -> bool **)

let typo_004_check s =
  (||) (string_contains_substring s ('`'::('`'::[])))
    (string_contains_substring s ('\''::('\''::[])))

(** val typo_004_validator : document_state -> validation_issue list **)

let typo_004_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_004_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('4'::[]))))))));
             issue_severity = Warning; message =
             ('T'::('e'::('X'::(' '::('d'::('o'::('u'::('b'::('l'::('e'::(' '::('b'::('a'::('c'::('k'::('-'::('t'::('i'::('c'::('k'::(' '::('n'::('o'::('t'::(' '::('a'::('l'::('l'::('o'::('w'::('e'::('d'::(';'::(' '::('u'::('s'::('e'::(' '::('o'::('p'::('e'::('n'::('i'::('n'::('g'::(' '::('c'::('u'::('r'::('l'::('y'::(' '::('q'::('u'::('o'::('t'::('e'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_004_rule : validation_rule **)

let typo_004_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('4'::[]))))))));
    description =
    ('T'::('e'::('X'::(' '::('d'::('o'::('u'::('b'::('l'::('e'::(' '::('b'::('a'::('c'::('k'::('-'::('t'::('i'::('c'::('k'::(' '::('n'::('o'::('t'::(' '::('a'::('l'::('l'::('o'::('w'::('e'::('d'::(';'::(' '::('u'::('s'::('e'::(' '::('o'::('p'::('e'::('n'::('i'::('n'::('g'::(' '::('c'::('u'::('r'::('l'::('y'::(' '::('q'::('u'::('o'::('t'::('e'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_004_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_005_check : char list -> bool **)

let typo_005_check s =
  string_contains_substring s ('.'::('.'::('.'::[])))

(** val typo_005_validator : document_state -> validation_issue list **)

let typo_005_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_005_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('5'::[]))))))));
             issue_severity = Warning; message =
             ('E'::('l'::('l'::('i'::('p'::('s'::('i'::('s'::(' '::('a'::('s'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('p'::('e'::('r'::('i'::('o'::('d'::('s'::(' '::('.'::('.'::('.'::(';'::(' '::('u'::('s'::('e'::(' '::('\\'::('d'::('o'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_005_rule : validation_rule **)

let typo_005_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('5'::[]))))))));
    description =
    ('E'::('l'::('l'::('i'::('p'::('s'::('i'::('s'::(' '::('a'::('s'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('p'::('e'::('r'::('i'::('o'::('d'::('s'::(' '::('.'::('.'::('.'::(';'::(' '::('u'::('s'::('e'::(' '::('\\'::('d'::('o'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_005_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_006_check : char list -> bool **)

let typo_006_check s =
  string_contains s
    (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))

(** val typo_006_validator : document_state -> validation_issue list **)

let typo_006_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_006_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('6'::[]))))))));
             issue_severity = Error; message =
             ('T'::('a'::('b'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::(' '::('U'::('+'::('0'::('0'::('0'::('9'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::[]))))))))))))))))))))))))))))));
             loc = None; suggested_fix = None; rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_006_rule : validation_rule **)

let typo_006_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('6'::[]))))))));
    description =
    ('T'::('a'::('b'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::(' '::('U'::('+'::('0'::('0'::('0'::('9'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::[]))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = None;
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_006_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('6'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_007_check : char list -> bool **)

let typo_007_check =
  string_ends_with_spaces

(** val typo_007_validator : document_state -> validation_issue list **)

let typo_007_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_007_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('7'::[]))))))));
             issue_severity = Info; message =
             ('T'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('a'::('t'::(' '::('e'::('n'::('d'::(' '::('o'::('f'::(' '::('l'::('i'::('n'::('e'::[]))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('s'::('t'::('r'::('i'::('p'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_007_rule : validation_rule **)

let typo_007_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('7'::[]))))))));
    description =
    ('T'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('a'::('t'::(' '::('e'::('n'::('d'::(' '::('o'::('f'::(' '::('l'::('i'::('n'::('e'::[]))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('s'::('t'::('r'::('i'::('p'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_007_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('7'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_008_check : char list -> bool **)

let typo_008_check s =
  let newline_count =
    count_char s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))
  in
  Nat.ltb (Stdlib.Int.succ (Stdlib.Int.succ 0)) newline_count

(** val typo_008_validator : document_state -> validation_issue list **)

let typo_008_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_008_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('8'::[]))))))));
             issue_severity = Info; message =
             ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('c'::('o'::('n'::('s'::('e'::('c'::('u'::('t'::('i'::('v'::('e'::(' '::('b'::('l'::('a'::('n'::('k'::(' '::('l'::('i'::('n'::('e'::('s'::(' '::('('::('>'::('2'::(')'::(' '::('i'::('n'::(' '::('s'::('o'::('u'::('r'::('c'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('c'::('o'::('l'::('l'::('a'::('p'::('s'::('e'::('_'::('b'::('l'::('a'::('n'::('k'::('_'::('l'::('i'::('n'::('e'::('s'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_008_rule : validation_rule **)

let typo_008_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('8'::[]))))))));
    description =
    ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('c'::('o'::('n'::('s'::('e'::('c'::('u'::('t'::('i'::('v'::('e'::(' '::('b'::('l'::('a'::('n'::('k'::(' '::('l'::('i'::('n'::('e'::('s'::(' '::('('::('>'::('2'::(')'::(' '::('i'::('n'::(' '::('s'::('o'::('u'::('r'::('c'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('c'::('o'::('l'::('l'::('a'::('p'::('s'::('e'::('_'::('b'::('l'::('a'::('n'::('k'::('_'::('l'::('i'::('n'::('e'::('s'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_008_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('8'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_009_check : char list -> bool **)

let typo_009_check s =
  string_prefix ('~'::[]) s

(** val typo_009_validator : document_state -> validation_issue list **)

let typo_009_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_009_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('9'::[]))))))));
             issue_severity = Warning; message =
             ('N'::('o'::('n'::('-'::('b'::('r'::('e'::('a'::('k'::('i'::('n'::('g'::(' '::('s'::('p'::('a'::('c'::('e'::(' '::('~'::(' '::('u'::('s'::('e'::('d'::(' '::('i'::('n'::('c'::('o'::('r'::('r'::('e'::('c'::('t'::('l'::('y'::(' '::('a'::('t'::(' '::('l'::('i'::('n'::('e'::(' '::('s'::('t'::('a'::('r'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = None; rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_009_rule : validation_rule **)

let typo_009_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('0'::('9'::[]))))))));
    description =
    ('N'::('o'::('n'::('-'::('b'::('r'::('e'::('a'::('k'::('i'::('n'::('g'::(' '::('s'::('p'::('a'::('c'::('e'::(' '::('~'::(' '::('u'::('s'::('e'::('d'::(' '::('i'::('n'::('c'::('o'::('r'::('r'::('e'::('c'::('t'::('l'::('y'::(' '::('a'::('t'::(' '::('l'::('i'::('n'::('e'::(' '::('s'::('t'::('a'::('r'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = None;
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_009_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('0'::('9'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_010_check : char list -> bool **)

let typo_010_check s =
  (||) (string_contains_substring s (' '::(','::[])))
    ((||) (string_contains_substring s (' '::('.'::[])))
      ((||) (string_contains_substring s (' '::(';'::[])))
        ((||) (string_contains_substring s (' '::(':'::[])))
          ((||) (string_contains_substring s (' '::('?'::[])))
            (string_contains_substring s (' '::('!'::[])))))))

(** val typo_010_validator : document_state -> validation_issue list **)

let typo_010_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_010_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('0'::[]))))))));
             issue_severity = Info; message =
             ('S'::('p'::('a'::('c'::('e'::(' '::('b'::('e'::('f'::('o'::('r'::('e'::(' '::('p'::('u'::('n'::('c'::('t'::('u'::('a'::('t'::('i'::('o'::('n'::(' '::(','::(' '::('.'::(' '::(';'::(' '::(':'::(' '::('?'::(' '::('!'::[]))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('s'::('p'::('a'::('c'::('e'::[])))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_010_rule : validation_rule **)

let typo_010_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('0'::[]))))))));
    description =
    ('S'::('p'::('a'::('c'::('e'::(' '::('b'::('e'::('f'::('o'::('r'::('e'::(' '::('p'::('u'::('n'::('c'::('t'::('u'::('a'::('t'::('i'::('o'::('n'::(' '::(','::(' '::('.'::(' '::(';'::(' '::(':'::(' '::('?'::(' '::('!'::[]))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('s'::('p'::('a'::('c'::('e'::[])))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_010_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('0'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_011_check : char list -> bool **)

let typo_011_check s =
  string_contains s
    (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))

(** val typo_011_validator : document_state -> validation_issue list **)

let typo_011_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_011_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('1'::[]))))))));
             issue_severity = Warning; message =
             ('A'::('v'::('o'::('i'::('d'::(' '::('s'::('t'::('r'::('a'::('i'::('g'::('h'::('t'::(' '::('A'::('S'::('C'::('I'::('I'::(' '::('a'::('p'::('o'::('s'::('t'::('r'::('o'::('p'::('h'::('e'::(','::(' '::('u'::('s'::('e'::(' '::('c'::('u'::('r'::('l'::('y'::(' '::('a'::('p'::('o'::('s'::('t'::('r'::('o'::('p'::('h'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_011_rule : validation_rule **)

let typo_011_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('1'::[]))))))));
    description =
    ('A'::('v'::('o'::('i'::('d'::(' '::('s'::('t'::('r'::('a'::('i'::('g'::('h'::('t'::(' '::('A'::('S'::('C'::('I'::('I'::(' '::('a'::('p'::('o'::('s'::('t'::('r'::('o'::('p'::('h'::('e'::(','::(' '::('u'::('s'::('e'::(' '::('c'::('u'::('r'::('l'::('y'::(' '::('a'::('p'::('o'::('s'::('t'::('r'::('o'::('p'::('h'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('u'::('t'::('o'::('_'::('r'::('e'::('p'::('l'::('a'::('c'::('e'::[])))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_011_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_012_check : char list -> bool **)

let typo_012_check s =
  string_contains_substring s (' '::(' '::[]))

(** val typo_012_validator : document_state -> validation_issue list **)

let typo_012_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_012_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('2'::[]))))))));
             issue_severity = Info; message =
             ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('b'::('e'::('t'::('w'::('e'::('e'::('n'::(' '::('w'::('o'::('r'::('d'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('s'::('i'::('n'::('g'::('l'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('s'::('p'::('a'::('c'::('e'::('s'::[])))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_012_rule : validation_rule **)

let typo_012_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('2'::[]))))))));
    description =
    ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('b'::('e'::('t'::('w'::('e'::('e'::('n'::(' '::('w'::('o'::('r'::('d'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('s'::('i'::('n'::('g'::('l'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('s'::('p'::('a'::('c'::('e'::('s'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_012_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_013_check : char list -> bool **)

let typo_013_check s =
  (||) (string_contains_substring s ('a'::(' '::[])))
    (string_contains_substring s ('I'::(' '::[])))

(** val typo_013_validator : document_state -> validation_issue list **)

let typo_013_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_013_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('3'::[]))))))));
             issue_severity = Info; message =
             ('C'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('n'::('o'::('n'::('-'::('b'::('r'::('e'::('a'::('k'::('i'::('n'::('g'::(' '::('s'::('p'::('a'::('c'::('e'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('s'::('i'::('n'::('g'::('l'::('e'::('-'::('l'::('e'::('t'::('t'::('e'::('r'::(' '::('w'::('o'::('r'::('d'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('d'::('d'::('_'::('n'::('o'::('n'::('b'::('r'::('e'::('a'::('k'::('i'::('n'::('g'::('_'::('s'::('p'::('a'::('c'::('e'::[]))))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_013_rule : validation_rule **)

let typo_013_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('3'::[]))))))));
    description =
    ('C'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('n'::('o'::('n'::('-'::('b'::('r'::('e'::('a'::('k'::('i'::('n'::('g'::(' '::('s'::('p'::('a'::('c'::('e'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('s'::('i'::('n'::('g'::('l'::('e'::('-'::('l'::('e'::('t'::('t'::('e'::('r'::(' '::('w'::('o'::('r'::('d'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('n'::('o'::('n'::('b'::('r'::('e'::('a'::('k'::('i'::('n'::('g'::('_'::('s'::('p'::('a'::('c'::('e'::[]))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_013_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_014_check : char list -> bool **)

let typo_014_check s =
  let has_straight =
    string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))))))
  in
  let has_curly =
    (||) (string_contains_substring s ('\''::[]))
      (string_contains_substring s ('\''::[]))
  in
  (&&) has_straight has_curly

(** val typo_014_validator : document_state -> validation_issue list **)

let typo_014_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_014_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('4'::[]))))))));
             issue_severity = Warning; message =
             ('I'::('n'::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::(' '::('q'::('u'::('o'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('a'::('r'::('k'::(' '::('s'::('t'::('y'::('l'::('e'::(' '::('w'::('i'::('t'::('h'::('i'::('n'::(' '::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('q'::('u'::('o'::('t'::('e'::('s'::[])))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_014_rule : validation_rule **)

let typo_014_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('4'::[]))))))));
    description =
    ('I'::('n'::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::(' '::('q'::('u'::('o'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('a'::('r'::('k'::(' '::('s'::('t'::('y'::('l'::('e'::(' '::('w'::('i'::('t'::('h'::('i'::('n'::(' '::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('q'::('u'::('o'::('t'::('e'::('s'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_014_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_015_check : char list -> bool **)

let typo_015_check s =
  string_contains_substring s ('\\'::('\\'::(' '::[])))

(** val typo_015_validator : document_state -> validation_issue list **)

let typo_015_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_015_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('5'::[]))))))));
             issue_severity = Info; message =
             ('L'::('a'::('T'::('e'::('X'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('a'::('d'::('j'::('u'::('s'::('t'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('v'::('i'::('e'::('w'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_015_rule : validation_rule **)

let typo_015_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('5'::[]))))))));
    description =
    ('L'::('a'::('T'::('e'::('X'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('a'::('d'::('j'::('u'::('s'::('t'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('v'::('i'::('e'::('w'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_015_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_016_check : char list -> bool **)

let typo_016_check s =
  (||) (string_contains_substring s ('!'::('!'::[])))
    (string_contains_substring s ('!'::('!'::('!'::[]))))

(** val typo_016_validator : document_state -> validation_issue list **)

let typo_016_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_016_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('6'::[]))))))));
             issue_severity = Info; message =
             ('E'::('x'::('c'::('e'::('s'::('s'::('i'::('v'::('e'::(' '::('e'::('x'::('c'::('l'::('a'::('m'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('a'::('r'::('k'::('s'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('m'::('o'::('d'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('d'::('u'::('c'::('e'::('_'::('e'::('x'::('c'::('l'::('a'::('m'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_016_rule : validation_rule **)

let typo_016_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('6'::[]))))))));
    description =
    ('E'::('x'::('c'::('e'::('s'::('s'::('i'::('v'::('e'::(' '::('e'::('x'::('c'::('l'::('a'::('m'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('a'::('r'::('k'::('s'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('m'::('o'::('d'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('d'::('u'::('c'::('e'::('_'::('e'::('x'::('c'::('l'::('a'::('m'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_016_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('6'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_017_check : char list -> bool **)

let typo_017_check s =
  (||) (string_contains_substring s (' '::('?'::[])))
    (string_contains_substring s ('?'::(' '::[])))

(** val typo_017_validator : document_state -> validation_issue list **)

let typo_017_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_017_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('7'::[]))))))));
             issue_severity = Info; message =
             ('Q'::('u'::('e'::('s'::('t'::('i'::('o'::('n'::(' '::('m'::('a'::('r'::('k'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('r'::('e'::('v'::('i'::('e'::('w'::[])))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('d'::('j'::('u'::('s'::('t'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_017_rule : validation_rule **)

let typo_017_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('7'::[]))))))));
    description =
    ('Q'::('u'::('e'::('s'::('t'::('i'::('o'::('n'::(' '::('m'::('a'::('r'::('k'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('r'::('e'::('v'::('i'::('e'::('w'::[])))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('d'::('j'::('u'::('s'::('t'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_017_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('7'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_018_check : char list -> bool **)

let typo_018_check s =
  string_contains_substring s ('.'::(' '::('a'::[])))

(** val typo_018_validator : document_state -> validation_issue list **)

let typo_018_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_018_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('8'::[]))))))));
             issue_severity = Warning; message =
             ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('c'::('a'::('p'::('i'::('t'::('a'::('l'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::('s'::('u'::('e'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('p'::('e'::('r'::('i'::('o'::('d'::[])))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('c'::('h'::('e'::('c'::('k'::('_'::('c'::('a'::('p'::('i'::('t'::('a'::('l'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_018_rule : validation_rule **)

let typo_018_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('8'::[]))))))));
    description =
    ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('c'::('a'::('p'::('i'::('t'::('a'::('l'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::('s'::('u'::('e'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('p'::('e'::('r'::('i'::('o'::('d'::[])))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('c'::('h'::('e'::('c'::('k'::('_'::('c'::('a'::('p'::('i'::('t'::('a'::('l'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_018_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('8'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_019_check : char list -> bool **)

let typo_019_check s =
  (||) (string_contains_substring s ('-'::(' '::[])))
    (string_contains_substring s (' '::('-'::[])))

(** val typo_019_validator : document_state -> validation_issue list **)

let typo_019_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_019_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('9'::[]))))))));
             issue_severity = Info; message =
             ('I'::('m'::('p'::('r'::('o'::('p'::('e'::('r'::(' '::('h'::('y'::('p'::('h'::('e'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('p'::('a'::('t'::('t'::('e'::('r'::('n'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('f'::('i'::('x'::('_'::('h'::('y'::('p'::('h'::('e'::('n'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_019_rule : validation_rule **)

let typo_019_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('1'::('9'::[]))))))));
    description =
    ('I'::('m'::('p'::('r'::('o'::('p'::('e'::('r'::(' '::('h'::('y'::('p'::('h'::('e'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('p'::('a'::('t'::('t'::('e'::('r'::('n'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('f'::('i'::('x'::('_'::('h'::('y'::('p'::('h'::('e'::('n'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_019_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('1'::('9'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_020_check : char list -> bool **)

let typo_020_check s =
  string_contains_substring s (','::(','::[]))

(** val typo_020_validator : document_state -> validation_issue list **)

let typo_020_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_020_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('0'::[]))))))));
             issue_severity = Warning; message =
             ('R'::('e'::('d'::('u'::('n'::('d'::('a'::('n'::('t'::(' '::('c'::('o'::('m'::('m'::('a'::(' '::('u'::('s'::('a'::('g'::('e'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('x'::('t'::('r'::('a'::('_'::('c'::('o'::('m'::('m'::('a'::[])))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_020_rule : validation_rule **)

let typo_020_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('0'::[]))))))));
    description =
    ('R'::('e'::('d'::('u'::('n'::('d'::('a'::('n'::('t'::(' '::('c'::('o'::('m'::('m'::('a'::(' '::('u'::('s'::('a'::('g'::('e'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('x'::('t'::('r'::('a'::('_'::('c'::('o'::('m'::('m'::('a'::[])))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_020_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('2'::('0'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_021_check : char list -> bool **)

let typo_021_check s =
  (||) (string_contains_substring s ('('::(' '::[])))
    (string_contains_substring s (' '::(')'::[])))

(** val typo_021_validator : document_state -> validation_issue list **)

let typo_021_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_021_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('1'::[]))))))));
             issue_severity = Info; message =
             ('P'::('a'::('r'::('e'::('n'::('t'::('h'::('e'::('s'::('e'::('s'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('a'::('d'::('j'::('u'::('s'::('t'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('f'::('i'::('x'::('_'::('p'::('a'::('r'::('e'::('n'::('t'::('h'::('e'::('s'::('e'::('s'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[]))))))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_021_rule : validation_rule **)

let typo_021_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('1'::[]))))))));
    description =
    ('P'::('a'::('r'::('e'::('n'::('t'::('h'::('e'::('s'::('e'::('s'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('a'::('d'::('j'::('u'::('s'::('t'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('f'::('i'::('x'::('_'::('p'::('a'::('r'::('e'::('n'::('t'::('h'::('e'::('s'::('e'::('s'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[]))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_021_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('2'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_022_check : char list -> bool **)

let typo_022_check s =
  string_contains_substring s (' '::('a'::('n'::('d'::(' '::[])))))

(** val typo_022_validator : document_state -> validation_issue list **)

let typo_022_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_022_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('2'::[]))))))));
             issue_severity = Info; message =
             ('C'::('h'::('e'::('c'::('k'::(' '::('O'::('x'::('f'::('o'::('r'::('d'::(' '::('c'::('o'::('m'::('m'::('a'::(' '::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('c'::('y'::(' '::('i'::('n'::(' '::('l'::('i'::('s'::('t'::('s'::[])))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('v'::('i'::('e'::('w'::('_'::('o'::('x'::('f'::('o'::('r'::('d'::('_'::('c'::('o'::('m'::('m'::('a'::[]))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_022_rule : validation_rule **)

let typo_022_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('2'::[]))))))));
    description =
    ('C'::('h'::('e'::('c'::('k'::(' '::('O'::('x'::('f'::('o'::('r'::('d'::(' '::('c'::('o'::('m'::('m'::('a'::(' '::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('c'::('y'::(' '::('i'::('n'::(' '::('l'::('i'::('s'::('t'::('s'::[])))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('v'::('i'::('e'::('w'::('_'::('o'::('x'::('f'::('o'::('r'::('d'::('_'::('c'::('o'::('m'::('m'::('a'::[]))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_022_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('2'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_023_check : char list -> bool **)

let typo_023_check s =
  (||) (string_contains_substring s (';'::(' '::[])))
    (string_contains_substring s (' '::(';'::[])))

(** val typo_023_validator : document_state -> validation_issue list **)

let typo_023_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_023_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('3'::[]))))))));
             issue_severity = Info; message =
             ('S'::('e'::('m'::('i'::('c'::('o'::('l'::('o'::('n'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('a'::('n'::('d'::(' '::('u'::('s'::('a'::('g'::('e'::(' '::('r'::('e'::('v'::('i'::('e'::('w'::[]))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('v'::('i'::('e'::('w'::('_'::('s'::('e'::('m'::('i'::('c'::('o'::('l'::('o'::('n'::[])))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_023_rule : validation_rule **)

let typo_023_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('3'::[]))))))));
    description =
    ('S'::('e'::('m'::('i'::('c'::('o'::('l'::('o'::('n'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('a'::('n'::('d'::(' '::('u'::('s'::('a'::('g'::('e'::(' '::('r'::('e'::('v'::('i'::('e'::('w'::[]))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('v'::('i'::('e'::('w'::('_'::('s'::('e'::('m'::('i'::('c'::('o'::('l'::('o'::('n'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_023_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('2'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_024_check : char list -> bool **)

let typo_024_check s =
  (||) (string_contains_substring s (':'::(' '::[])))
    (string_contains_substring s (' '::(':'::[])))

(** val typo_024_validator : document_state -> validation_issue list **)

let typo_024_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_024_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('4'::[]))))))));
             issue_severity = Info; message =
             ('C'::('o'::('l'::('o'::('n'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('r'::('e'::('v'::('i'::('e'::('w'::[])))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('d'::('j'::('u'::('s'::('t'::('_'::('c'::('o'::('l'::('o'::('n'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_024_rule : validation_rule **)

let typo_024_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('4'::[]))))))));
    description =
    ('C'::('o'::('l'::('o'::('n'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('r'::('e'::('v'::('i'::('e'::('w'::[])))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('d'::('j'::('u'::('s'::('t'::('_'::('c'::('o'::('l'::('o'::('n'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_024_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('2'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val typo_025_check : char list -> bool **)

let typo_025_check s =
  let italic_count =
    count_char s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))))))))))))))
  in
  let bold_count =
    count_char s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  (||)
    ((=) (Nat.modulo italic_count (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      (Stdlib.Int.succ 0))
    ((=) (Nat.modulo bold_count (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      (Stdlib.Int.succ 0))

(** val typo_025_validator : document_state -> validation_issue list **)

let typo_025_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if typo_025_check s
      then { rule_id =
             ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('5'::[]))))))));
             issue_severity = Warning; message =
             ('T'::('e'::('x'::('t'::(' '::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::(' '::('m'::('a'::('r'::('k'::('e'::('r'::('s'::(' '::('m'::('a'::('y'::(' '::('b'::('e'::(' '::('u'::('n'::('b'::('a'::('l'::('a'::('n'::('c'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('b'::('a'::('l'::('a'::('n'::('c'::('e'::('_'::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::[])))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val typo_025_rule : validation_rule **)

let typo_025_rule =
  { id = ('T'::('Y'::('P'::('O'::('-'::('0'::('2'::('5'::[]))))))));
    description =
    ('T'::('e'::('x'::('t'::(' '::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::(' '::('m'::('a'::('r'::('k'::('e'::('r'::('s'::(' '::('m'::('a'::('y'::(' '::('b'::('e'::(' '::('u'::('n'::('b'::('a'::('l'::('a'::('n'::('c'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('b'::('a'::('l'::('a'::('n'::('c'::('e'::('_'::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = typo_025_validator; rule_sound = (Some
    ('t'::('y'::('p'::('o'::('_'::('0'::('2'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val enc_001_check : char list -> bool **)

let enc_001_check s =
  string_contains s
    (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val enc_001_validator : document_state -> validation_issue list **)

let enc_001_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if enc_001_check s
      then { rule_id = ('E'::('N'::('C'::('-'::('0'::('0'::('1'::[])))))));
             issue_severity = Error; message =
             ('N'::('o'::('n'::('-'::('U'::('T'::('F'::('-'::('8'::(' '::('b'::('y'::('t'::('e'::(' '::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = None; rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val enc_001_rule : validation_rule **)

let enc_001_rule =
  { id = ('E'::('N'::('C'::('-'::('0'::('0'::('1'::[]))))))); description =
    ('N'::('o'::('n'::('-'::('U'::('T'::('F'::('-'::('8'::(' '::('b'::('y'::('t'::('e'::(' '::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = None;
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = enc_001_validator; rule_sound = (Some
    ('e'::('n'::('c'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val enc_002_check : char list -> bool **)

let enc_002_check s =
  string_prefix
    ((ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))::(
    (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))::(
    (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))::[])))
    s

(** val enc_002_validator : document_state -> validation_issue list **)

let enc_002_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if enc_002_check s
      then { rule_id = ('E'::('N'::('C'::('-'::('0'::('0'::('2'::[])))))));
             issue_severity = Warning; message =
             ('U'::('T'::('F'::('-'::('8'::(' '::('B'::('O'::('M'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('t'::(' '::('s'::('t'::('a'::('r'::('t'::(' '::('o'::('f'::(' '::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('b'::('o'::('m'::[])))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val enc_002_rule : validation_rule **)

let enc_002_rule =
  { id = ('E'::('N'::('C'::('-'::('0'::('0'::('2'::[]))))))); description =
    ('U'::('T'::('F'::('-'::('8'::(' '::('B'::('O'::('M'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('t'::(' '::('s'::('t'::('a'::('r'::('t'::(' '::('o'::('f'::(' '::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('b'::('o'::('m'::[])))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = enc_002_validator; rule_sound = (Some
    ('e'::('n'::('c'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val enc_003_check : char list -> bool **)

let enc_003_check s =
  (||)
    (string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val enc_003_validator : document_state -> validation_issue list **)

let enc_003_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if enc_003_check s
      then { rule_id = ('E'::('N'::('C'::('-'::('0'::('0'::('3'::[])))))));
             issue_severity = Warning; message =
             ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('L'::('a'::('t'::('i'::('n'::('-'::('1'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::[])))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('c'::('o'::('n'::('v'::('e'::('r'::('t'::('_'::('t'::('o'::('_'::('u'::('t'::('f'::('8'::[]))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val enc_003_rule : validation_rule **)

let enc_003_rule =
  { id = ('E'::('N'::('C'::('-'::('0'::('0'::('3'::[]))))))); description =
    ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('L'::('a'::('t'::('i'::('n'::('-'::('1'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::[])))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('c'::('o'::('n'::('v'::('e'::('r'::('t'::('_'::('t'::('o'::('_'::('u'::('t'::('f'::('8'::[]))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = enc_003_validator; rule_sound = (Some
    ('e'::('n'::('c'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val enc_004_check : char list -> bool **)

let enc_004_check s =
  (||)
    (string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val enc_004_validator : document_state -> validation_issue list **)

let enc_004_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if enc_004_check s
      then { rule_id = ('E'::('N'::('C'::('-'::('0'::('0'::('4'::[])))))));
             issue_severity = Warning; message =
             ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('W'::('i'::('n'::('d'::('o'::('w'::('s'::('-'::('1'::('2'::('5'::('2'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('c'::('o'::('n'::('v'::('e'::('r'::('t'::('_'::('t'::('o'::('_'::('u'::('t'::('f'::('8'::[]))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val enc_004_rule : validation_rule **)

let enc_004_rule =
  { id = ('E'::('N'::('C'::('-'::('0'::('0'::('4'::[]))))))); description =
    ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('W'::('i'::('n'::('d'::('o'::('w'::('s'::('-'::('1'::('2'::('5'::('2'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('c'::('o'::('n'::('v'::('e'::('r'::('t'::('_'::('t'::('o'::('_'::('u'::('t'::('f'::('8'::[]))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = enc_004_validator; rule_sound = (Some
    ('e'::('n'::('c'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val enc_005_check : char list -> bool **)

let enc_005_check s =
  let has_ascii =
    count_char s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  let has_high =
    string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  (&&) (Nat.ltb 0 has_ascii) has_high

(** val enc_005_validator : document_state -> validation_issue list **)

let enc_005_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if enc_005_check s
      then { rule_id = ('E'::('N'::('C'::('-'::('0'::('0'::('5'::[])))))));
             issue_severity = Error; message =
             ('M'::('i'::('x'::('e'::('d'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('s'::('t'::('a'::('n'::('d'::('a'::('r'::('d'::('i'::('z'::('e'::('_'::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val enc_005_rule : validation_rule **)

let enc_005_rule =
  { id = ('E'::('N'::('C'::('-'::('0'::('0'::('5'::[]))))))); description =
    ('M'::('i'::('x'::('e'::('d'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('s'::('t'::('a'::('n'::('d'::('a'::('r'::('d'::('i'::('z'::('e'::('_'::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = enc_005_validator; rule_sound = (Some
    ('e'::('n'::('c'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val char_001_check : char list -> bool **)

let char_001_check s =
  (||) (string_contains s (ascii_of_nat 0))
    ((||) (string_contains s (ascii_of_nat (Stdlib.Int.succ 0)))
      (string_contains s
        (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          0))))))))))

(** val char_001_validator : document_state -> validation_issue list **)

let char_001_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if char_001_check s
      then { rule_id =
             ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('1'::[]))))))));
             issue_severity = Error; message =
             ('C'::('o'::('n'::('t'::('r'::('o'::('l'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('U'::('+'::('0'::('0'::('0'::('0'::('\226'::('\128'::('\147'::('0'::('0'::('1'::('F'::(' '::('p'::('r'::('e'::('s'::('e'::('n'::('t'::[]))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = None; rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val char_001_rule : validation_rule **)

let char_001_rule =
  { id = ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('1'::[]))))))));
    description =
    ('C'::('o'::('n'::('t'::('r'::('o'::('l'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('U'::('+'::('0'::('0'::('0'::('0'::('\226'::('\128'::('\147'::('0'::('0'::('1'::('F'::(' '::('p'::('r'::('e'::('s'::('e'::('n'::('t'::[]))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = None;
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = char_001_validator; rule_sound = (Some
    ('c'::('h'::('a'::('r'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val char_002_check : char list -> bool **)

let char_002_check s =
  (||)
    (string_contains s
      (ascii_of_nat (of_num_uint (UIntDecimal (D8 (D2 (D0 (D3 Nil))))))))
    ((||)
      (string_contains s
        (ascii_of_nat (of_num_uint (UIntDecimal (D8 (D2 (D0 (D4 Nil))))))))
      (string_contains s
        (ascii_of_nat (of_num_uint (UIntDecimal (D8 (D2 (D0 (D5 Nil)))))))))

(** val char_002_validator : document_state -> validation_issue list **)

let char_002_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if char_002_check s
      then { rule_id =
             ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('2'::[]))))))));
             issue_severity = Warning; message =
             ('I'::('n'::('v'::('i'::('s'::('i'::('b'::('l'::('e'::(' '::('U'::('n'::('i'::('c'::('o'::('d'::('e'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('i'::('n'::('v'::('i'::('s'::('i'::('b'::('l'::('e'::[])))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val char_002_rule : validation_rule **)

let char_002_rule =
  { id = ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('2'::[]))))))));
    description =
    ('I'::('n'::('v'::('i'::('s'::('i'::('b'::('l'::('e'::(' '::('U'::('n'::('i'::('c'::('o'::('d'::('e'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('i'::('n'::('v'::('i'::('s'::('i'::('b'::('l'::('e'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = char_002_validator; rule_sound = (Some
    ('c'::('h'::('a'::('r'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val char_003_check_chars : char list -> bool **)

let rec char_003_check_chars = function
| [] -> false
| c::rest ->
  if Nat.ltb (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (nat_of_ascii c)
  then true
  else char_003_check_chars rest

(** val char_003_check : char list -> bool **)

let char_003_check =
  char_003_check_chars

(** val char_003_validator : document_state -> validation_issue list **)

let char_003_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if char_003_check s
      then { rule_id =
             ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('3'::[]))))))));
             issue_severity = Info; message =
             ('N'::('o'::('n'::('-'::('A'::('S'::('C'::('I'::('I'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::[]))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('c'::('h'::('e'::('c'::('k'::('_'::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::[])))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val char_003_rule : validation_rule **)

let char_003_rule =
  { id = ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('3'::[]))))))));
    description =
    ('N'::('o'::('n'::('-'::('A'::('S'::('C'::('I'::('I'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::[]))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('c'::('h'::('e'::('c'::('k'::('_'::('e'::('n'::('c'::('o'::('d'::('i'::('n'::('g'::[])))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = char_003_validator; rule_sound = (Some
    ('c'::('h'::('a'::('r'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val char_004_check : char list -> bool **)

let char_004_check s =
  let has_cr =
    string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))
  in
  let has_lf =
    string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))
  in
  let has_crlf =
    string_contains_substring s
      ((ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))::((ascii_of_nat
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))))))))))::[]))
  in
  (||) ((&&) has_cr (negb has_crlf)) ((&&) has_lf has_cr)

(** val char_004_validator : document_state -> validation_issue list **)

let char_004_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if char_004_check s
      then { rule_id =
             ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('4'::[]))))))));
             issue_severity = Info; message =
             ('I'::('n'::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::(' '::('l'::('i'::('n'::('e'::(' '::('e'::('n'::('d'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('l'::('i'::('n'::('e'::('_'::('e'::('n'::('d'::('i'::('n'::('g'::('s'::[])))))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val char_004_rule : validation_rule **)

let char_004_rule =
  { id = ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('4'::[]))))))));
    description =
    ('I'::('n'::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::(' '::('l'::('i'::('n'::('e'::(' '::('e'::('n'::('d'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('l'::('i'::('n'::('e'::('_'::('e'::('n'::('d'::('i'::('n'::('g'::('s'::[])))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = char_004_validator; rule_sound = (Some
    ('c'::('h'::('a'::('r'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val char_005_check : char list -> bool **)

let char_005_check s =
  (||)
    (string_contains s
      (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((||)
      (string_contains s
        (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))
      (string_contains s
        (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))))))))))))))

(** val char_005_validator : document_state -> validation_issue list **)

let char_005_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if char_005_check s
      then { rule_id =
             ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('5'::[]))))))));
             issue_severity = Info; message =
             ('U'::('n'::('u'::('s'::('u'::('a'::('l'::(' '::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val char_005_rule : validation_rule **)

let char_005_rule =
  { id = ('C'::('H'::('A'::('R'::('-'::('0'::('0'::('5'::[]))))))));
    description =
    ('U'::('n'::('u'::('s'::('u'::('a'::('l'::(' '::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = char_005_validator; rule_sound = (Some
    ('c'::('h'::('a'::('r'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val env_001_check_aux : char list -> bool **)

let env_001_check_aux cmd =
  (||) (string_contains_substring cmd ('b'::('e'::('g'::('i'::('n'::[]))))))
    (string_contains_substring cmd ('e'::('n'::('d'::[]))))

(** val env_001_check : latex_token list -> bool **)

let rec env_001_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if env_001_check_aux cmd then true else env_001_check rest
   | _ -> env_001_check rest)

(** val env_001_validator : document_state -> validation_issue list **)

let env_001_validator doc =
  if env_001_check doc.tokens
  then { rule_id = ('E'::('N'::('V'::('-'::('0'::('0'::('1'::[])))))));
         issue_severity = Warning; message =
         ('C'::('h'::('e'::('c'::('k'::(' '::('b'::('e'::('g'::('i'::('n'::('/'::('e'::('n'::('d'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::[]))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('c'::('h'::('e'::('c'::('k'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::('_'::('p'::('a'::('i'::('r'::('s'::[]))))))))))))))))))))))));
         rule_owner =
         ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
  else []

(** val env_001_rule : validation_rule **)

let env_001_rule =
  { id = ('E'::('N'::('V'::('-'::('0'::('0'::('1'::[]))))))); description =
    ('C'::('h'::('e'::('c'::('k'::(' '::('b'::('e'::('g'::('i'::('n'::('/'::('e'::('n'::('d'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::('i'::('n'::('g'::[]))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('c'::('h'::('e'::('c'::('k'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::('_'::('p'::('a'::('i'::('r'::('s'::[]))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = env_001_validator; rule_sound = (Some
    ('e'::('n'::('v'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val env_002_check_aux : char list -> bool **)

let env_002_check_aux cmd =
  (||)
    (string_contains_substring cmd
      ('e'::('q'::('n'::('a'::('r'::('r'::('a'::('y'::[])))))))))
    ((||)
      (string_contains_substring cmd
        ('c'::('e'::('n'::('t'::('e'::('r'::[])))))))
      (string_contains_substring cmd
        ('f'::('l'::('u'::('s'::('h'::('l'::('e'::('f'::('t'::[])))))))))))

(** val env_002_check : latex_token list -> bool **)

let rec env_002_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if env_002_check_aux cmd then true else env_002_check rest
   | _ -> env_002_check rest)

(** val env_002_validator : document_state -> validation_issue list **)

let env_002_validator doc =
  if env_002_check doc.tokens
  then { rule_id = ('E'::('N'::('V'::('-'::('0'::('0'::('2'::[])))))));
         issue_severity = Info; message =
         ('D'::('e'::('p'::('r'::('e'::('c'::('a'::('t'::('e'::('d'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('m'::('o'::('d'::('e'::('r'::('n'::(' '::('a'::('l'::('t'::('e'::('r'::('n'::('a'::('t'::('i'::('v'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('m'::('o'::('d'::('e'::('r'::('n'::('i'::('z'::('e'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::[]))))))))))))))))))))));
         rule_owner =
         ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
  else []

(** val env_002_rule : validation_rule **)

let env_002_rule =
  { id = ('E'::('N'::('V'::('-'::('0'::('0'::('2'::[]))))))); description =
    ('D'::('e'::('p'::('r'::('e'::('c'::('a'::('t'::('e'::('d'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('m'::('o'::('d'::('e'::('r'::('n'::(' '::('a'::('l'::('t'::('e'::('r'::('n'::('a'::('t'::('i'::('v'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('m'::('o'::('d'::('e'::('r'::('n'::('i'::('z'::('e'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::[]))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = env_002_validator; rule_sound = (Some
    ('e'::('n'::('v'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val env_003_check : latex_token list -> bool **)

let rec env_003_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     (match rest with
      | [] -> env_003_check rest
      | l0 :: l1 ->
        (match l0 with
         | TBeginGroup ->
           (match l1 with
            | [] -> env_003_check rest
            | l2 :: l3 ->
              (match l2 with
               | TText _ ->
                 (match l3 with
                  | [] -> env_003_check rest
                  | l4 :: l5 ->
                    (match l4 with
                     | TEndGroup ->
                       (match l5 with
                        | [] -> env_003_check rest
                        | l6 :: rest0 ->
                          (match l6 with
                           | TCommand end_cmd ->
                             if (&&)
                                  (string_contains_substring cmd
                                    ('b'::('e'::('g'::('i'::('n'::[]))))))
                                  (string_contains_substring end_cmd
                                    ('e'::('n'::('d'::[]))))
                             then true
                             else env_003_check rest0
                           | _ -> env_003_check rest))
                     | _ -> env_003_check rest))
               | _ -> env_003_check rest))
         | _ -> env_003_check rest))
   | _ -> env_003_check rest)

(** val env_003_validator : document_state -> validation_issue list **)

let env_003_validator doc =
  if env_003_check doc.tokens
  then { rule_id = ('E'::('N'::('V'::('-'::('0'::('0'::('3'::[])))))));
         issue_severity = Info; message =
         ('E'::('m'::('p'::('t'::('y'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('r'::('e'::('m'::('o'::('v'::('a'::('l'::[]))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))));
         rule_owner =
         ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
  else []

(** val env_003_rule : validation_rule **)

let env_003_rule =
  { id = ('E'::('N'::('V'::('-'::('0'::('0'::('3'::[]))))))); description =
    ('E'::('m'::('p'::('t'::('y'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('r'::('e'::('m'::('o'::('v'::('a'::('l'::[]))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('m'::('p'::('t'::('y'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = env_003_validator; rule_sound = (Some
    ('e'::('n'::('v'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val env_004_count_nesting : latex_token list -> int -> int -> int **)

let rec env_004_count_nesting tokens0 depth max_depth =
  match tokens0 with
  | [] -> max_depth
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_contains_substring cmd ('b'::('e'::('g'::('i'::('n'::[])))))
       then let new_depth = Stdlib.Int.succ depth in
            let new_max =
              if Nat.ltb max_depth new_depth then new_depth else max_depth
            in
            env_004_count_nesting rest new_depth new_max
       else if string_contains_substring cmd ('e'::('n'::('d'::[])))
            then env_004_count_nesting rest
                   (if (=) depth 0 then 0 else pred depth) max_depth
            else env_004_count_nesting rest depth max_depth
     | _ -> env_004_count_nesting rest depth max_depth)

(** val env_004_check : latex_token list -> bool **)

let env_004_check tokens0 =
  let max_depth = env_004_count_nesting tokens0 0 0 in
  Nat.ltb (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) max_depth

(** val env_004_validator : document_state -> validation_issue list **)

let env_004_validator doc =
  if env_004_check doc.tokens
  then { rule_id = ('E'::('N'::('V'::('-'::('0'::('0'::('4'::[])))))));
         issue_severity = Info; message =
         ('D'::('e'::('e'::('p'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('n'::('e'::('s'::('t'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('a'::('f'::('f'::('e'::('c'::('t'::(' '::('r'::('e'::('a'::('d'::('a'::('b'::('i'::('l'::('i'::('t'::('y'::[])))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('r'::('e'::('d'::('u'::('c'::('e'::('_'::('n'::('e'::('s'::('t'::('i'::('n'::('g'::[])))))))))))))));
         rule_owner =
         ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
  else []

(** val env_004_rule : validation_rule **)

let env_004_rule =
  { id = ('E'::('N'::('V'::('-'::('0'::('0'::('4'::[]))))))); description =
    ('D'::('e'::('e'::('p'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('n'::('e'::('s'::('t'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('a'::('f'::('f'::('e'::('c'::('t'::(' '::('r'::('e'::('a'::('d'::('a'::('b'::('i'::('l'::('i'::('t'::('y'::[])))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('r'::('e'::('d'::('u'::('c'::('e'::('_'::('n'::('e'::('s'::('t'::('i'::('n'::('g'::[])))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = env_004_validator; rule_sound = (Some
    ('e'::('n'::('v'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val env_005_check_aux : char list -> bool **)

let env_005_check_aux cmd =
  (||)
    (string_contains_substring cmd
      ('c'::('e'::('n'::('t'::('r'::('e'::[])))))))
    ((||)
      (string_contains_substring cmd
        ('i'::('t'::('e'::('m'::('i'::('s'::('e'::[]))))))))
      (string_contains_substring cmd
        ('t'::('a'::('b'::('u'::('l'::('a'::('r'::[])))))))))

(** val env_005_check : latex_token list -> bool **)

let rec env_005_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if env_005_check_aux cmd then true else env_005_check rest
   | _ -> env_005_check rest)

(** val env_005_validator : document_state -> validation_issue list **)

let env_005_validator doc =
  if env_005_check doc.tokens
  then { rule_id = ('E'::('N'::('V'::('-'::('0'::('0'::('5'::[])))))));
         issue_severity = Warning; message =
         ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('n'::('a'::('m'::('e'::(' '::('t'::('y'::('p'::('o'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('f'::('i'::('x'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::('_'::('n'::('a'::('m'::('e'::[])))))))))))))))))))));
         rule_owner =
         ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[])))))))))) } :: []
  else []

(** val env_005_rule : validation_rule **)

let env_005_rule =
  { id = ('E'::('N'::('V'::('-'::('0'::('0'::('5'::[]))))))); description =
    ('P'::('o'::('t'::('e'::('n'::('t'::('i'::('a'::('l'::(' '::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::(' '::('n'::('a'::('m'::('e'::(' '::('t'::('y'::('p'::('o'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('l'::('i'::('n'::('t'::('-'::('t'::('e'::('a'::('m'::[]))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('f'::('i'::('x'::('_'::('e'::('n'::('v'::('i'::('r'::('o'::('n'::('m'::('e'::('n'::('t'::('_'::('n'::('a'::('m'::('e'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = env_005_validator; rule_sound = (Some
    ('e'::('n'::('v'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val math_001_check : char list -> bool **)

let math_001_check s =
  (||) (string_contains_substring s ('x'::('^'::('2'::[]))))
    ((||) (string_contains_substring s ('a'::('_'::('i'::[]))))
      ((||) (string_contains_substring s ('='::[]))
        (string_contains_substring s ('a'::('l'::('p'::('h'::('a'::[]))))))))

(** val math_001_validator : document_state -> validation_issue list **)

let math_001_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if math_001_check s
      then { rule_id =
             ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('1'::[]))))))));
             issue_severity = Warning; message =
             ('M'::('a'::('t'::('h'::('e'::('m'::('a'::('t'::('i'::('c'::('a'::('l'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('i'::('n'::(' '::('m'::('a'::('t'::('h'::(' '::('m'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('d'::('d'::('_'::('m'::('a'::('t'::('h'::('_'::('m'::('o'::('d'::('e'::[]))))))))))))));
             rule_owner =
             ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val math_001_rule : validation_rule **)

let math_001_rule =
  { id = ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('1'::[]))))))));
    description =
    ('M'::('a'::('t'::('h'::('e'::('m'::('a'::('t'::('i'::('c'::('a'::('l'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('i'::('n'::(' '::('m'::('a'::('t'::('h'::(' '::('m'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('m'::('a'::('t'::('h'::('_'::('m'::('o'::('d'::('e'::[]))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = math_001_validator; rule_sound = (Some
    ('m'::('a'::('t'::('h'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val math_002_count_delimiters : latex_token list -> int -> bool **)

let rec math_002_count_delimiters tokens0 count =
  match tokens0 with
  | [] -> negb ((=) count 0)
  | l :: rest ->
    (match l with
     | TMathShift ->
       math_002_count_delimiters rest
         (if (=) count 0 then Stdlib.Int.succ 0 else 0)
     | _ -> math_002_count_delimiters rest count)

(** val math_002_validator : document_state -> validation_issue list **)

let math_002_validator doc =
  if math_002_count_delimiters doc.tokens 0
  then { rule_id =
         ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('2'::[]))))))));
         issue_severity = Error; message =
         ('U'::('n'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('m'::('a'::('t'::('h'::(' '::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::(' '::('$'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('f'::('i'::('x'::('_'::('m'::('a'::('t'::('h'::('_'::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::[]))))))))))))))))))));
         rule_owner =
         ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) } :: []
  else []

(** val math_002_rule : validation_rule **)

let math_002_rule =
  { id = ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('2'::[]))))))));
    description =
    ('U'::('n'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('m'::('a'::('t'::('h'::(' '::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::(' '::('$'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[])))))))))));
    performance_bucket = TokenKind_Other; auto_fix = (Some
    ('f'::('i'::('x'::('_'::('m'::('a'::('t'::('h'::('_'::('d'::('e'::('l'::('i'::('m'::('i'::('t'::('e'::('r'::('s'::[]))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = math_002_validator; rule_sound = (Some
    ('m'::('a'::('t'::('h'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val math_003_check : char list -> bool **)

let math_003_check s =
  string_contains_substring s ('$'::('$'::[]))

(** val math_003_validator : document_state -> validation_issue list **)

let math_003_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if math_003_check s
      then { rule_id =
             ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('3'::[]))))))));
             issue_severity = Warning; message =
             ('D'::('o'::('u'::('b'::('l'::('e'::(' '::('d'::('o'::('l'::('l'::('a'::('r'::(' '::('$'::('$'::(' '::('d'::('e'::('p'::('r'::('e'::('c'::('a'::('t'::('e'::('d'::(','::(' '::('u'::('s'::('e'::(' '::('\\'::('\\'::('['::(' '::('\\'::('\\'::(']'::(' '::('i'::('n'::('s'::('t'::('e'::('a'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('p'::('l'::('a'::('c'::('e'::('_'::('d'::('i'::('s'::('p'::('l'::('a'::('y'::('_'::('m'::('a'::('t'::('h'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val math_003_rule : validation_rule **)

let math_003_rule =
  { id = ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('3'::[]))))))));
    description =
    ('D'::('o'::('u'::('b'::('l'::('e'::(' '::('d'::('o'::('l'::('l'::('a'::('r'::(' '::('$'::('$'::(' '::('d'::('e'::('p'::('r'::('e'::('c'::('a'::('t'::('e'::('d'::(','::(' '::('u'::('s'::('e'::(' '::('\\'::('\\'::('['::(' '::('\\'::('\\'::(']'::(' '::('i'::('n'::('s'::('t'::('e'::('a'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('p'::('l'::('a'::('c'::('e'::('_'::('d'::('i'::('s'::('p'::('l'::('a'::('y'::('_'::('m'::('a'::('t'::('h'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = math_003_validator; rule_sound = (Some
    ('m'::('a'::('t'::('h'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val math_004_check : char list -> bool **)

let math_004_check s =
  (||) (string_contains_substring s ('\226'::('\136'::('\145'::[]))))
    ((||) (string_contains_substring s ('\226'::('\136'::('\171'::[]))))
      ((||) (string_contains_substring s ('\226'::('\137'::('\164'::[]))))
        ((||) (string_contains_substring s ('\226'::('\137'::('\165'::[]))))
          (string_contains_substring s ('\194'::('\177'::[]))))))

(** val math_004_validator : document_state -> validation_issue list **)

let math_004_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if math_004_check s
      then { rule_id =
             ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('4'::[]))))))));
             issue_severity = Warning; message =
             ('U'::('n'::('i'::('c'::('o'::('d'::('e'::(' '::('m'::('a'::('t'::('h'::(' '::('s'::('y'::('m'::('b'::('o'::('l'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('u'::('s'::('e'::(' '::('L'::('a'::('T'::('e'::('X'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('c'::('o'::('n'::('v'::('e'::('r'::('t'::('_'::('m'::('a'::('t'::('h'::('_'::('s'::('y'::('m'::('b'::('o'::('l'::('s'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val math_004_rule : validation_rule **)

let math_004_rule =
  { id = ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('4'::[]))))))));
    description =
    ('U'::('n'::('i'::('c'::('o'::('d'::('e'::(' '::('m'::('a'::('t'::('h'::(' '::('s'::('y'::('m'::('b'::('o'::('l'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('u'::('s'::('e'::(' '::('L'::('a'::('T'::('e'::('X'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('c'::('o'::('n'::('v'::('e'::('r'::('t'::('_'::('m'::('a'::('t'::('h'::('_'::('s'::('y'::('m'::('b'::('o'::('l'::('s'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = math_004_validator; rule_sound = (Some
    ('m'::('a'::('t'::('h'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val math_005_check : char list -> bool **)

let math_005_check s =
  (||) (string_contains_substring s (' '::('$'::[])))
    (string_contains_substring s ('$'::(' '::[])))

(** val math_005_validator : document_state -> validation_issue list **)

let math_005_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if math_005_check s
      then { rule_id =
             ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('5'::[]))))))));
             issue_severity = Info; message =
             ('M'::('a'::('t'::('h'::(' '::('m'::('o'::('d'::('e'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('a'::('d'::('j'::('u'::('s'::('t'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('a'::('d'::('j'::('u'::('s'::('t'::('_'::('m'::('a'::('t'::('h'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[]))))))))))))))))))));
             rule_owner =
             ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val math_005_rule : validation_rule **)

let math_005_rule =
  { id = ('M'::('A'::('T'::('H'::('-'::('0'::('0'::('5'::[]))))))));
    description =
    ('M'::('a'::('t'::('h'::(' '::('m'::('o'::('d'::('e'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('m'::('a'::('y'::(' '::('n'::('e'::('e'::('d'::(' '::('a'::('d'::('j'::('u'::('s'::('t'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('m'::('a'::('t'::('h'::('-'::('r'::('u'::('l'::('e'::('s'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('a'::('d'::('j'::('u'::('s'::('t'::('_'::('m'::('a'::('t'::('h'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[]))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = math_005_validator; rule_sound = (Some
    ('m'::('a'::('t'::('h'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))) }

(** val struct_001_check_aux : char list -> bool **)

let struct_001_check_aux cmd =
  (||)
    (string_contains_substring cmd
      ('s'::('e'::('c'::('t'::('i'::('o'::('n'::[]))))))))
    ((||)
      (string_contains_substring cmd
        ('c'::('h'::('a'::('p'::('t'::('e'::('r'::[]))))))))
      (string_contains_substring cmd
        ('s'::('u'::('b'::('s'::('e'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))

(** val struct_001_check : latex_token list -> bool **)

let rec struct_001_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd1 ->
     (match rest with
      | [] -> struct_001_check rest
      | l0 :: rest0 ->
        (match l0 with
         | TCommand cmd2 ->
           if (&&) (struct_001_check_aux cmd1) (struct_001_check_aux cmd2)
           then true
           else struct_001_check rest0
         | _ -> struct_001_check rest))
   | _ -> struct_001_check rest)

(** val struct_001_validator : document_state -> validation_issue list **)

let struct_001_validator doc =
  if struct_001_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('1'::[]))))))))));
         issue_severity = Info; message =
         ('E'::('m'::('p'::('t'::('y'::(' '::('s'::('e'::('c'::('t'::('i'::('o'::('n'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('a'::('d'::('d'::('i'::('n'::('g'::(' '::('c'::('o'::('n'::('t'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('s'::('e'::('c'::('t'::('i'::('o'::('n'::('_'::('c'::('o'::('n'::('t'::('e'::('n'::('t'::[]))))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_001_rule : validation_rule **)

let struct_001_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('1'::[]))))))))));
    description =
    ('E'::('m'::('p'::('t'::('y'::(' '::('s'::('e'::('c'::('t'::('i'::('o'::('n'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(','::(' '::('c'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('a'::('d'::('d'::('i'::('n'::('g'::(' '::('c'::('o'::('n'::('t'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('s'::('e'::('c'::('t'::('i'::('o'::('n'::('_'::('c'::('o'::('n'::('t'::('e'::('n'::('t'::[]))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_001_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_002_check : latex_token list -> bool **)

let rec struct_002_check = function
| [] -> true
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if string_contains_substring cmd
          ('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))
     then false
     else struct_002_check rest
   | _ -> struct_002_check rest)

(** val struct_002_validator : document_state -> validation_issue list **)

let struct_002_validator doc =
  if struct_002_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('2'::[]))))))))));
         issue_severity = Error; message =
         ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('\\'::('\\'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[]))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_002_rule : validation_rule **)

let struct_002_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('2'::[]))))))))));
    description =
    ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('\\'::('\\'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[]))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_002_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_003_count_documentclass : latex_token list -> int -> int **)

let rec struct_003_count_documentclass tokens0 count =
  match tokens0 with
  | [] -> count
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_contains_substring cmd
            ('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))
       then struct_003_count_documentclass rest (Stdlib.Int.succ count)
       else struct_003_count_documentclass rest count
     | _ -> struct_003_count_documentclass rest count)

(** val struct_003_check : latex_token list -> bool **)

let struct_003_check tokens0 =
  Nat.ltb (Stdlib.Int.succ 0) (struct_003_count_documentclass tokens0 0)

(** val struct_003_validator : document_state -> validation_issue list **)

let struct_003_validator doc =
  if struct_003_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('3'::[]))))))))));
         issue_severity = Error; message =
         ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('\\'::('\\'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::('s'::(' '::('f'::('o'::('u'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('x'::('t'::('r'::('a'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_003_rule : validation_rule **)

let struct_003_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('3'::[]))))))))));
    description =
    ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('\\'::('\\'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::('s'::(' '::('f'::('o'::('u'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('e'::('x'::('t'::('r'::('a'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_003_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_004_check_order : latex_token list -> bool -> bool **)

let rec struct_004_check_order tokens0 seen_begin =
  match tokens0 with
  | [] -> false
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_contains_substring cmd
            ('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))
       then if seen_begin
            then true
            else struct_004_check_order rest seen_begin
       else if (&&)
                 (string_contains_substring cmd
                   ('b'::('e'::('g'::('i'::('n'::[])))))) (negb seen_begin)
            then struct_004_check_order rest true
            else struct_004_check_order rest seen_begin
     | _ -> struct_004_check_order rest seen_begin)

(** val struct_004_check : latex_token list -> bool **)

let struct_004_check tokens0 =
  struct_004_check_order tokens0 false

(** val struct_004_validator : document_state -> validation_issue list **)

let struct_004_validator doc =
  if struct_004_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('4'::[]))))))))));
         issue_severity = Error; message =
         ('D'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('o'::('r'::('d'::('e'::('r'::(' '::('('::('p'::('r'::('e'::('a'::('m'::('b'::('l'::('e'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('\\'::('\\'::('b'::('e'::('g'::('i'::('n'::('{'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('}'::(')'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('r'::('e'::('o'::('r'::('d'::('e'::('r'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_004_rule : validation_rule **)

let struct_004_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('4'::[]))))))))));
    description =
    ('D'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('o'::('r'::('d'::('e'::('r'::[])))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('r'::('e'::('o'::('r'::('d'::('e'::('r'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_004_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_005_check : latex_token list -> bool **)

let rec struct_005_check = function
| [] -> true
| l :: rest ->
  (match l with
   | TCommand cmd ->
     (match rest with
      | [] -> struct_005_check rest
      | l0 :: l1 ->
        (match l0 with
         | TBeginGroup ->
           (match l1 with
            | [] -> struct_005_check rest
            | l2 :: l3 ->
              (match l2 with
               | TText s ->
                 (match s with
                  | [] -> struct_005_check rest
                  | a::s0 ->
                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                      (fun b b0 b1 b2 b3 b4 b5 b6 ->
                      if b
                      then struct_005_check rest
                      else if b0
                           then struct_005_check rest
                           else if b1
                                then if b2
                                     then struct_005_check rest
                                     else if b3
                                          then struct_005_check rest
                                          else if b4
                                               then if b5
                                                    then if b6
                                                         then struct_005_check
                                                                rest
                                                         else (match s0 with
                                                               | [] ->
                                                                 struct_005_check
                                                                   rest
                                                               | a0::s1 ->
                                                                 (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                   (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                                   if b7
                                                                   then 
                                                                    if b8
                                                                    then 
                                                                    if b9
                                                                    then 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    struct_005_check
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    struct_005_check
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    struct_005_check
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    struct_005_check
                                                                    rest
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    struct_005_check
                                                                    rest
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
                                                                    if b51
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    struct_005_check
                                                                    rest
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b56
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    struct_005_check
                                                                    rest
                                                                    | l4 :: rest0 ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    if 
                                                                    string_contains_substring
                                                                    cmd
                                                                    ('b'::('e'::('g'::('i'::('n'::[])))))
                                                                    then false
                                                                    else 
                                                                    struct_005_check
                                                                    rest0
                                                                    | _ ->
                                                                    struct_005_check
                                                                    rest))
                                                                    | _::_ ->
                                                                    struct_005_check
                                                                    rest)
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest)
                                                                    a6)
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest)
                                                                    a5)
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest)
                                                                    a4)
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                    else 
                                                                    struct_005_check
                                                                    rest
                                                                   else 
                                                                    struct_005_check
                                                                    rest)
                                                                   a0)
                                                    else struct_005_check rest
                                               else struct_005_check rest
                                else struct_005_check rest)
                      a)
               | _ -> struct_005_check rest))
         | _ -> struct_005_check rest))
   | _ -> struct_005_check rest)

(** val struct_005_validator : document_state -> validation_issue list **)

let struct_005_validator doc =
  if struct_005_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('5'::[]))))))))));
         issue_severity = Error; message =
         ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('\\'::('\\'::('b'::('e'::('g'::('i'::('n'::('{'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('}'::[])))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('b'::('e'::('g'::('i'::('n'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_005_rule : validation_rule **)

let struct_005_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('5'::[]))))))))));
    description =
    ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('\\'::('\\'::('b'::('e'::('g'::('i'::('n'::('{'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('}'::[])))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('b'::('e'::('g'::('i'::('n'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_005_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_006_check : latex_token list -> bool **)

let rec struct_006_check = function
| [] -> true
| l :: rest ->
  (match l with
   | TCommand cmd ->
     (match rest with
      | [] -> struct_006_check rest
      | l0 :: l1 ->
        (match l0 with
         | TBeginGroup ->
           (match l1 with
            | [] -> struct_006_check rest
            | l2 :: l3 ->
              (match l2 with
               | TText s ->
                 (match s with
                  | [] -> struct_006_check rest
                  | a::s0 ->
                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                      (fun b b0 b1 b2 b3 b4 b5 b6 ->
                      if b
                      then struct_006_check rest
                      else if b0
                           then struct_006_check rest
                           else if b1
                                then if b2
                                     then struct_006_check rest
                                     else if b3
                                          then struct_006_check rest
                                          else if b4
                                               then if b5
                                                    then if b6
                                                         then struct_006_check
                                                                rest
                                                         else (match s0 with
                                                               | [] ->
                                                                 struct_006_check
                                                                   rest
                                                               | a0::s1 ->
                                                                 (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                   (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                                   if b7
                                                                   then 
                                                                    if b8
                                                                    then 
                                                                    if b9
                                                                    then 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    struct_006_check
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    struct_006_check
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    struct_006_check
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    struct_006_check
                                                                    rest
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    struct_006_check
                                                                    rest
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
                                                                    if b51
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    struct_006_check
                                                                    rest
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b56
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    struct_006_check
                                                                    rest
                                                                    | l4 :: rest0 ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    if 
                                                                    string_contains_substring
                                                                    cmd
                                                                    ('e'::('n'::('d'::[])))
                                                                    then false
                                                                    else 
                                                                    struct_006_check
                                                                    rest0
                                                                    | _ ->
                                                                    struct_006_check
                                                                    rest))
                                                                    | _::_ ->
                                                                    struct_006_check
                                                                    rest)
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest)
                                                                    a6)
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest)
                                                                    a5)
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest)
                                                                    a4)
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                    else 
                                                                    struct_006_check
                                                                    rest
                                                                   else 
                                                                    struct_006_check
                                                                    rest)
                                                                   a0)
                                                    else struct_006_check rest
                                               else struct_006_check rest
                                else struct_006_check rest)
                      a)
               | _ -> struct_006_check rest))
         | _ -> struct_006_check rest))
   | _ -> struct_006_check rest)

(** val struct_006_validator : document_state -> validation_issue list **)

let struct_006_validator doc =
  if struct_006_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('6'::[]))))))))));
         issue_severity = Error; message =
         ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('\\'::('\\'::('e'::('n'::('d'::('{'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('}'::[])))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('e'::('n'::('d'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_006_rule : validation_rule **)

let struct_006_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('6'::[]))))))))));
    description =
    ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('\\'::('\\'::('e'::('n'::('d'::('{'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('}'::[])))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('e'::('n'::('d'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_006_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('6'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_007_check_packages : latex_token list -> bool -> bool **)

let rec struct_007_check_packages tokens0 in_document =
  match tokens0 with
  | [] -> false
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_contains_substring cmd
            ('u'::('s'::('e'::('p'::('a'::('c'::('k'::('a'::('g'::('e'::[]))))))))))
       then if in_document
            then true
            else struct_007_check_packages rest in_document
       else if (&&)
                 (string_contains_substring cmd
                   ('b'::('e'::('g'::('i'::('n'::[])))))) (negb in_document)
            then (match rest with
                  | [] -> struct_007_check_packages rest in_document
                  | l0 :: l1 ->
                    (match l0 with
                     | TBeginGroup ->
                       (match l1 with
                        | [] -> struct_007_check_packages rest in_document
                        | l2 :: l3 ->
                          (match l2 with
                           | TText s ->
                             (match s with
                              | [] ->
                                struct_007_check_packages rest in_document
                              | a::s0 ->
                                (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                  (fun b b0 b1 b2 b3 b4 b5 b6 ->
                                  if b
                                  then struct_007_check_packages rest
                                         in_document
                                  else if b0
                                       then struct_007_check_packages rest
                                              in_document
                                       else if b1
                                            then if b2
                                                 then struct_007_check_packages
                                                        rest in_document
                                                 else if b3
                                                      then struct_007_check_packages
                                                             rest in_document
                                                      else if b4
                                                           then if b5
                                                                then 
                                                                  if b6
                                                                  then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                  else 
                                                                    (match s0 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | a0::s1 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                                    if b7
                                                                    then 
                                                                    if b8
                                                                    then 
                                                                    if b9
                                                                    then 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
                                                                    if b51
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b56
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    | l4 :: rest' ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    struct_007_check_packages
                                                                    rest' true
                                                                    | _ ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document))
                                                                    | _::_ ->
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    a6)
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    a5)
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    a4)
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    a3)
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    a2)
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    a1)
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                                    else 
                                                                    struct_007_check_packages
                                                                    rest
                                                                    in_document)
                                                                    a0)
                                                                else 
                                                                  struct_007_check_packages
                                                                    rest
                                                                    in_document
                                                           else struct_007_check_packages
                                                                  rest
                                                                  in_document
                                            else struct_007_check_packages
                                                   rest in_document)
                                  a)
                           | _ -> struct_007_check_packages rest in_document))
                     | _ -> struct_007_check_packages rest in_document))
            else struct_007_check_packages rest in_document
     | _ -> struct_007_check_packages rest in_document)

(** val struct_007_check : latex_token list -> bool **)

let struct_007_check tokens0 =
  struct_007_check_packages tokens0 false

(** val struct_007_validator : document_state -> validation_issue list **)

let struct_007_validator doc =
  if struct_007_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('7'::[]))))))))));
         issue_severity = Error; message =
         ('P'::('a'::('c'::('k'::('a'::('g'::('e'::(' '::('l'::('o'::('a'::('d'::('e'::('d'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('\\'::('\\'::('b'::('e'::('g'::('i'::('n'::('{'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('}'::[]))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('m'::('o'::('v'::('e'::('_'::('t'::('o'::('_'::('p'::('r'::('e'::('a'::('m'::('b'::('l'::('e'::[])))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_007_rule : validation_rule **)

let struct_007_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('7'::[]))))))))));
    description =
    ('P'::('a'::('c'::('k'::('a'::('g'::('e'::(' '::('l'::('o'::('a'::('d'::('e'::('d'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('\\'::('\\'::('b'::('e'::('g'::('i'::('n'::('{'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('}'::[]))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('m'::('o'::('v'::('e'::('_'::('t'::('o'::('_'::('p'::('r'::('e'::('a'::('m'::('b'::('l'::('e'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_007_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('7'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_008_count_braces :
    latex_token list -> int -> int -> int * int **)

let rec struct_008_count_braces tokens0 open_count close_count =
  match tokens0 with
  | [] -> (open_count, close_count)
  | l :: rest ->
    (match l with
     | TBeginGroup ->
       struct_008_count_braces rest (Stdlib.Int.succ open_count) close_count
     | TEndGroup ->
       struct_008_count_braces rest open_count (Stdlib.Int.succ close_count)
     | _ -> struct_008_count_braces rest open_count close_count)

(** val struct_008_check : latex_token list -> bool **)

let struct_008_check tokens0 =
  let (opens, closes) = struct_008_count_braces tokens0 0 0 in
  negb ((=) opens closes)

(** val struct_008_validator : document_state -> validation_issue list **)

let struct_008_validator doc =
  if struct_008_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('8'::[]))))))))));
         issue_severity = Error; message =
         ('M'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('b'::('r'::('a'::('c'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('b'::('a'::('l'::('a'::('n'::('c'::('e'::('_'::('b'::('r'::('a'::('c'::('e'::('s'::[])))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_008_rule : validation_rule **)

let struct_008_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('8'::[]))))))))));
    description =
    ('M'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('b'::('r'::('a'::('c'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_BeginGroup; auto_fix = (Some
    ('b'::('a'::('l'::('a'::('n'::('c'::('e'::('_'::('b'::('r'::('a'::('c'::('e'::('s'::[])))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_008_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('8'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_009_count_consecutive_newlines :
    latex_token list -> int -> int -> int **)

let rec struct_009_count_consecutive_newlines tokens0 count max =
  match tokens0 with
  | [] -> max
  | l :: rest ->
    (match l with
     | TNewline ->
       let new_count = Stdlib.Int.succ count in
       let new_max = if Nat.ltb max new_count then new_count else max in
       struct_009_count_consecutive_newlines rest new_count new_max
     | _ -> struct_009_count_consecutive_newlines rest 0 max)

(** val struct_009_check : latex_token list -> bool **)

let struct_009_check tokens0 =
  Nat.ltb (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (struct_009_count_consecutive_newlines tokens0 0 0)

(** val struct_009_validator : document_state -> validation_issue list **)

let struct_009_validator doc =
  if struct_009_check doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('9'::[]))))))))));
         issue_severity = Info; message =
         ('E'::('x'::('c'::('e'::('s'::('s'::('i'::('v'::('e'::(' '::('b'::('l'::('a'::('n'::('k'::(' '::('l'::('i'::('n'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('('::('m'::('o'::('r'::('e'::(' '::('t'::('h'::('a'::('n'::(' '::('3'::(')'::[]))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('r'::('e'::('d'::('u'::('c'::('e'::('_'::('b'::('l'::('a'::('n'::('k'::('_'::('l'::('i'::('n'::('e'::('s'::[])))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_009_rule : validation_rule **)

let struct_009_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('0'::('9'::[]))))))))));
    description =
    ('E'::('x'::('c'::('e'::('s'::('s'::('i'::('v'::('e'::(' '::('b'::('l'::('a'::('n'::('k'::(' '::('l'::('i'::('n'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Other; auto_fix = (Some
    ('r'::('e'::('d'::('u'::('c'::('e'::('_'::('b'::('l'::('a'::('n'::('k'::('_'::('l'::('i'::('n'::('e'::('s'::[])))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_009_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('0'::('9'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val struct_010_check_text_before_class : latex_token list -> bool **)

let rec struct_010_check_text_before_class = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if string_contains_substring cmd
          ('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))
     then false
     else struct_010_check_text_before_class rest
   | TText _ -> true
   | _ -> struct_010_check_text_before_class rest)

(** val struct_010_validator : document_state -> validation_issue list **)

let struct_010_validator doc =
  if struct_010_check_text_before_class doc.tokens
  then { rule_id =
         ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('1'::('0'::[]))))))))));
         issue_severity = Warning; message =
         ('T'::('e'::('x'::('t'::(' '::('a'::('p'::('p'::('e'::('a'::('r'::('s'::(' '::('b'::('e'::('f'::('o'::('r'::('e'::(' '::('\\'::('\\'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('m'::('o'::('v'::('e'::('_'::('a'::('f'::('t'::('e'::('r'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))))))) } :: []
  else []

(** val struct_010_rule : validation_rule **)

let struct_010_rule =
  { id =
    ('S'::('T'::('R'::('U'::('C'::('T'::('-'::('0'::('1'::('0'::[]))))))))));
    description =
    ('T'::('e'::('x'::('t'::(' '::('a'::('p'::('p'::('e'::('a'::('r'::('s'::(' '::('b'::('e'::('f'::('o'::('r'::('e'::(' '::('\\'::('\\'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('s'::('t'::('r'::('u'::('c'::('t'::('u'::('r'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('m'::('o'::('v'::('e'::('_'::('a'::('f'::('t'::('e'::('r'::('_'::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::('c'::('l'::('a'::('s'::('s'::[])))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = struct_010_validator; rule_sound = (Some
    ('s'::('t'::('r'::('u'::('c'::('t'::('_'::('0'::('1'::('0'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[]))))))))))))))))))))) }

(** val ref_001_check_aux : char list -> bool **)

let ref_001_check_aux cmd =
  (||) (string_contains_substring cmd ('r'::('e'::('f'::[]))))
    (string_contains_substring cmd
      ('p'::('a'::('g'::('e'::('r'::('e'::('f'::[]))))))))

(** val ref_001_check : latex_token list -> bool **)

let rec ref_001_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if ref_001_check_aux cmd then true else ref_001_check rest
   | _ -> ref_001_check rest)

(** val ref_001_validator : document_state -> validation_issue list **)

let ref_001_validator doc =
  if ref_001_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('1'::[])))))));
         issue_severity = Info; message =
         ('R'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('e'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('-'::(' '::('v'::('e'::('r'::('i'::('f'::('y'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('e'::('x'::('i'::('s'::('t'::('s'::[])))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('v'::('e'::('r'::('i'::('f'::('y'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::[]))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_001_rule : validation_rule **)

let ref_001_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('1'::[]))))))); description =
    ('R'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('e'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('-'::(' '::('v'::('e'::('r'::('i'::('f'::('y'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('e'::('x'::('i'::('s'::('t'::('s'::[])))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('v'::('e'::('r'::('i'::('f'::('y'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::[]))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_001_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_002_check_labels : latex_token list -> bool -> bool **)

let rec ref_002_check_labels tokens0 seen_label =
  match tokens0 with
  | [] -> false
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_contains_substring cmd ('l'::('a'::('b'::('e'::('l'::[])))))
       then if seen_label then true else ref_002_check_labels rest true
       else ref_002_check_labels rest seen_label
     | _ -> ref_002_check_labels rest seen_label)

(** val ref_002_check : latex_token list -> bool **)

let ref_002_check tokens0 =
  ref_002_check_labels tokens0 false

(** val ref_002_validator : document_state -> validation_issue list **)

let ref_002_validator doc =
  if ref_002_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('2'::[])))))));
         issue_severity = Warning; message =
         ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('-'::(' '::('c'::('h'::('e'::('c'::('k'::(' '::('f'::('o'::('r'::(' '::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('c'::('h'::('e'::('c'::('k'::('_'::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::[])))))))))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_002_rule : validation_rule **)

let ref_002_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('2'::[]))))))); description =
    ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('l'::('a'::('b'::('e'::('l'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('-'::(' '::('c'::('h'::('e'::('c'::('k'::(' '::('f'::('o'::('r'::(' '::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('c'::('h'::('e'::('c'::('k'::('_'::('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::('_'::('l'::('a'::('b'::('e'::('l'::('s'::[])))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_002_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_003_has_cite : latex_token list -> bool **)

let rec ref_003_has_cite = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if string_contains_substring cmd ('c'::('i'::('t'::('e'::[]))))
     then true
     else ref_003_has_cite rest
   | _ -> ref_003_has_cite rest)

(** val ref_003_has_bibliography : latex_token list -> bool **)

let rec ref_003_has_bibliography = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if (||)
          (string_contains_substring cmd
            ('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::[])))))))))))))
          (string_contains_substring cmd
            ('t'::('h'::('e'::('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::[]))))))))))))))))
     then true
     else ref_003_has_bibliography rest
   | _ -> ref_003_has_bibliography rest)

(** val ref_003_check : latex_token list -> bool **)

let ref_003_check tokens0 =
  (&&) (ref_003_has_cite tokens0) (negb (ref_003_has_bibliography tokens0))

(** val ref_003_validator : document_state -> validation_issue list **)

let ref_003_validator doc =
  if ref_003_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('3'::[])))))));
         issue_severity = Warning; message =
         ('C'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::('s'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('b'::('u'::('t'::(' '::('n'::('o'::(' '::('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::[])))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_003_rule : validation_rule **)

let ref_003_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('3'::[]))))))); description =
    ('C'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::('s'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('b'::('u'::('t'::(' '::('n'::('o'::(' '::('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_003_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_004_check : latex_token list -> bool **)

let rec ref_004_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     (match rest with
      | [] -> ref_004_check rest
      | l0 :: l1 ->
        (match l0 with
         | TBeginGroup ->
           (match l1 with
            | [] -> ref_004_check rest
            | l2 :: rest0 ->
              (match l2 with
               | TEndGroup ->
                 if string_contains_substring cmd
                      ('c'::('i'::('t'::('e'::[]))))
                 then true
                 else ref_004_check rest0
               | _ -> ref_004_check rest))
         | _ -> ref_004_check rest))
   | _ -> ref_004_check rest)

(** val ref_004_validator : document_state -> validation_issue list **)

let ref_004_validator doc =
  if ref_004_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('4'::[])))))));
         issue_severity = Error; message =
         ('E'::('m'::('p'::('t'::('y'::(' '::('c'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('c'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::('_'::('k'::('e'::('y'::[])))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_004_rule : validation_rule **)

let ref_004_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('4'::[]))))))); description =
    ('E'::('m'::('p'::('t'::('y'::(' '::('c'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Error; rule_maturity = Draft;
    owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('c'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::('_'::('k'::('e'::('y'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_004_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_005_check_aux : char list -> bool **)

let ref_005_check_aux cmd =
  (&&) (string_contains_substring cmd ('c'::('i'::('t'::('e'::[])))))
    (negb
      ((||) (string_eqb cmd ('c'::('i'::('t'::('e'::[])))))
        ((||) (string_eqb cmd ('c'::('i'::('t'::('e'::('p'::[]))))))
          ((||) (string_eqb cmd ('c'::('i'::('t'::('e'::('t'::[]))))))
            ((||)
              (string_eqb cmd
                ('c'::('i'::('t'::('e'::('a'::('u'::('t'::('h'::('o'::('r'::[])))))))))))
              ((||)
                (string_eqb cmd
                  ('c'::('i'::('t'::('e'::('y'::('e'::('a'::('r'::[])))))))))
                (string_eqb cmd ('n'::('o'::('c'::('i'::('t'::('e'::[])))))))))))))

(** val ref_005_check : latex_token list -> bool **)

let rec ref_005_check = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if ref_005_check_aux cmd then true else ref_005_check rest
   | _ -> ref_005_check rest)

(** val ref_005_validator : document_state -> validation_issue list **)

let ref_005_validator doc =
  if ref_005_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('5'::[])))))));
         issue_severity = Info; message =
         ('N'::('o'::('n'::('-'::('s'::('t'::('a'::('n'::('d'::('a'::('r'::('d'::(' '::('c'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('u'::('s'::('e'::('_'::('s'::('t'::('a'::('n'::('d'::('a'::('r'::('d'::('_'::('c'::('i'::('t'::('e'::[]))))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_005_rule : validation_rule **)

let ref_005_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('5'::[]))))))); description =
    ('N'::('o'::('n'::('-'::('s'::('t'::('a'::('n'::('d'::('a'::('r'::('d'::(' '::('c'::('i'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('u'::('s'::('e'::('_'::('s'::('t'::('a'::('n'::('d'::('a'::('r'::('d'::('_'::('c'::('i'::('t'::('e'::[]))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_005_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_006_check_equation_refs : latex_token list -> bool **)

let rec ref_006_check_equation_refs = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     (match rest with
      | [] -> ref_006_check_equation_refs rest
      | l0 :: l1 ->
        (match l0 with
         | TBeginGroup ->
           (match l1 with
            | [] -> ref_006_check_equation_refs rest
            | l2 :: l3 ->
              (match l2 with
               | TText content ->
                 (match l3 with
                  | [] -> ref_006_check_equation_refs rest
                  | l4 :: rest0 ->
                    (match l4 with
                     | TEndGroup ->
                       if (&&)
                            (string_eqb cmd
                              ('e'::('q'::('r'::('e'::('f'::[]))))))
                            (string_contains_substring content ('?'::[]))
                       then true
                       else ref_006_check_equation_refs rest0
                     | _ -> ref_006_check_equation_refs rest))
               | _ -> ref_006_check_equation_refs rest))
         | _ -> ref_006_check_equation_refs rest))
   | _ -> ref_006_check_equation_refs rest)

(** val ref_006_validator : document_state -> validation_issue list **)

let ref_006_validator doc =
  if ref_006_check_equation_refs doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('6'::[])))))));
         issue_severity = Warning; message =
         ('E'::('q'::('u'::('a'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('m'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('e'::('q'::('u'::('a'::('t'::('i'::('o'::('n'::('_'::('l'::('a'::('b'::('e'::('l'::[])))))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_006_rule : validation_rule **)

let ref_006_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('6'::[]))))))); description =
    ('E'::('q'::('u'::('a'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('m'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('e'::('q'::('u'::('a'::('t'::('i'::('o'::('n'::('_'::('l'::('a'::('b'::('e'::('l'::[])))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_006_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('6'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_007_count_ref_styles :
    latex_token list -> int -> int -> int * int **)

let rec ref_007_count_ref_styles tokens0 plain eq =
  match tokens0 with
  | [] -> (plain, eq)
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_eqb cmd ('r'::('e'::('f'::[])))
       then ref_007_count_ref_styles rest (Stdlib.Int.succ plain) eq
       else if string_eqb cmd ('e'::('q'::('r'::('e'::('f'::[])))))
            then ref_007_count_ref_styles rest plain (Stdlib.Int.succ eq)
            else ref_007_count_ref_styles rest plain eq
     | _ -> ref_007_count_ref_styles rest plain eq)

(** val ref_007_check : latex_token list -> bool **)

let ref_007_check tokens0 =
  let (plain, eq) = ref_007_count_ref_styles tokens0 0 0 in
  (&&) (Nat.ltb 0 plain) (Nat.ltb 0 eq)

(** val ref_007_validator : document_state -> validation_issue list **)

let ref_007_validator doc =
  if ref_007_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('7'::[])))))));
         issue_severity = Info; message =
         ('M'::('i'::('x'::('e'::('d'::(' '::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('e'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('('::('\\'::('\\'::('r'::('e'::('f'::(' '::('a'::('n'::('d'::(' '::('\\'::('\\'::('e'::('q'::('r'::('e'::('f'::(')'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('u'::('n'::('i'::('f'::('y'::('_'::('r'::('e'::('f'::('_'::('s'::('t'::('y'::('l'::('e'::[]))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_007_rule : validation_rule **)

let ref_007_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('7'::[]))))))); description =
    ('M'::('i'::('x'::('e'::('d'::(' '::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('e'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('u'::('n'::('i'::('f'::('y'::('_'::('r'::('e'::('f'::('_'::('s'::('t'::('y'::('l'::('e'::[]))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_007_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('7'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_008_check_footnotes : latex_token list -> bool -> bool **)

let rec ref_008_check_footnotes tokens0 in_footnote =
  match tokens0 with
  | [] -> false
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_eqb cmd
            ('f'::('o'::('o'::('t'::('n'::('o'::('t'::('e'::[]))))))))
       then if in_footnote then true else ref_008_check_footnotes rest true
       else if string_contains_substring cmd ('e'::('n'::('d'::[])))
            then ref_008_check_footnotes rest false
            else ref_008_check_footnotes rest in_footnote
     | _ -> ref_008_check_footnotes rest in_footnote)

(** val ref_008_check : latex_token list -> bool **)

let ref_008_check tokens0 =
  ref_008_check_footnotes tokens0 false

(** val ref_008_validator : document_state -> validation_issue list **)

let ref_008_validator doc =
  if ref_008_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('8'::[])))))));
         issue_severity = Warning; message =
         ('N'::('e'::('s'::('t'::('e'::('d'::(' '::('f'::('o'::('o'::('t'::('n'::('o'::('t'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('f'::('l'::('a'::('t'::('t'::('e'::('n'::('_'::('f'::('o'::('o'::('t'::('n'::('o'::('t'::('e'::('s'::[]))))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_008_rule : validation_rule **)

let ref_008_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('8'::[]))))))); description =
    ('N'::('e'::('s'::('t'::('e'::('d'::(' '::('f'::('o'::('o'::('t'::('n'::('o'::('t'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('f'::('l'::('a'::('t'::('t'::('e'::('n'::('_'::('f'::('o'::('o'::('t'::('n'::('o'::('t'::('e'::('s'::[]))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_008_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('8'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_009_has_url : latex_token list -> bool **)

let rec ref_009_has_url = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if (||) (string_eqb cmd ('u'::('r'::('l'::[]))))
          (string_eqb cmd ('h'::('r'::('e'::('f'::[])))))
     then true
     else ref_009_has_url rest
   | _ -> ref_009_has_url rest)

(** val ref_009_has_hyperref : latex_token list -> bool **)

let rec ref_009_has_hyperref = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> ref_009_has_hyperref rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then if b0
               then ref_009_has_hyperref rest
               else if b1
                    then if b2
                         then ref_009_has_hyperref rest
                         else if b3
                              then if b4
                                   then if b5
                                        then if b6
                                             then ref_009_has_hyperref rest
                                             else (match s0 with
                                                   | [] ->
                                                     ref_009_has_hyperref rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then if b9
                                                                 then 
                                                                   ref_009_has_hyperref
                                                                    rest
                                                                 else 
                                                                   if b10
                                                                   then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b34
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b42
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b50
                                                                    then 
                                                                    if b51
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    if b56
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b58
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    if b64
                                                                    then 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    (match rest with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | l0 :: l1 ->
                                                                    (match l0 with
                                                                    | TBeginGroup ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | l2 :: l3 ->
                                                                    (match l2 with
                                                                    | TText s10 ->
                                                                    (match s10 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a9::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a10::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a11::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b96
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b98
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a12::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a13::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b114
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a14::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b122
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a15::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | a16::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b139
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    | l4 :: _ ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    true
                                                                    | _ ->
                                                                    ref_009_has_hyperref
                                                                    rest))
                                                                    | _::_ ->
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a16)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a15)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a14)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a13)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a12)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a11)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a10)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a9)
                                                                    | _ ->
                                                                    ref_009_has_hyperref
                                                                    rest))
                                                                    | _ ->
                                                                    ref_009_has_hyperref
                                                                    rest))
                                                                    | _::_ ->
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a8)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a7)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a6)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a5)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a4)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                                    else 
                                                                    ref_009_has_hyperref
                                                                    rest
                                                            else ref_009_has_hyperref
                                                                   rest
                                                       else ref_009_has_hyperref
                                                              rest)
                                                       a0)
                                        else ref_009_has_hyperref rest
                                   else ref_009_has_hyperref rest
                              else ref_009_has_hyperref rest
                    else ref_009_has_hyperref rest
          else ref_009_has_hyperref rest)
          a)
   | _ -> ref_009_has_hyperref rest)

(** val ref_009_check : latex_token list -> bool **)

let ref_009_check tokens0 =
  (&&) (ref_009_has_url tokens0) (negb (ref_009_has_hyperref tokens0))

(** val ref_009_validator : document_state -> validation_issue list **)

let ref_009_validator doc =
  if ref_009_check doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('0'::('9'::[])))))));
         issue_severity = Warning; message =
         ('U'::('R'::('L'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::('s'::(' '::('u'::('s'::('e'::('d'::(' '::('w'::('i'::('t'::('h'::('o'::('u'::('t'::(' '::('h'::('y'::('p'::('e'::('r'::('r'::('e'::('f'::(' '::('p'::('a'::('c'::('k'::('a'::('g'::('e'::[]))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('a'::('d'::('d'::('_'::('h'::('y'::('p'::('e'::('r'::('r'::('e'::('f'::('_'::('p'::('a'::('c'::('k'::('a'::('g'::('e'::[])))))))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_009_rule : validation_rule **)

let ref_009_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('0'::('9'::[]))))))); description =
    ('U'::('R'::('L'::(' '::('c'::('o'::('m'::('m'::('a'::('n'::('d'::('s'::(' '::('u'::('s'::('e'::('d'::(' '::('w'::('i'::('t'::('h'::('o'::('u'::('t'::(' '::('h'::('y'::('p'::('e'::('r'::('r'::('e'::('f'::(' '::('p'::('a'::('c'::('k'::('a'::('g'::('e'::[]))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('a'::('d'::('d'::('_'::('h'::('y'::('p'::('e'::('r'::('r'::('e'::('f'::('_'::('p'::('a'::('c'::('k'::('a'::('g'::('e'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_009_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('0'::('9'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val ref_010_check_bibstyle : latex_token list -> bool **)

let rec ref_010_check_bibstyle = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> ref_010_check_bibstyle rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then ref_010_check_bibstyle rest
          else if b0
               then if b1
                    then ref_010_check_bibstyle rest
                    else if b2
                         then ref_010_check_bibstyle rest
                         else if b3
                              then ref_010_check_bibstyle rest
                              else if b4
                                   then if b5
                                        then if b6
                                             then ref_010_check_bibstyle rest
                                             else (match s0 with
                                                   | [] ->
                                                     ref_010_check_bibstyle
                                                       rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then ref_010_check_bibstyle
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   ref_010_check_bibstyle
                                                                    rest
                                                                 else 
                                                                   if b10
                                                                   then 
                                                                    if b11
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    if b43
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b51
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b56
                                                                    then 
                                                                    if b57
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b58
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    if b64
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b66
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b72
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b74
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b98
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b104
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b113
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b114
                                                                    then 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b120
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    (match rest with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | l0 :: l1 ->
                                                                    (match l0 with
                                                                    | TBeginGroup ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | l2 :: l3 ->
                                                                    (match l2 with
                                                                    | TText style ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    | l4 :: rest0 ->
                                                                    (match l4 with
                                                                    | TEndGroup ->
                                                                    if 
                                                                    (||)
                                                                    (string_eqb
                                                                    style
                                                                    ('p'::('l'::('a'::('i'::('n'::[]))))))
                                                                    (string_eqb
                                                                    style
                                                                    ('a'::('b'::('b'::('r'::('v'::[]))))))
                                                                    then true
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest0
                                                                    | _ ->
                                                                    ref_010_check_bibstyle
                                                                    rest))
                                                                    | _ ->
                                                                    ref_010_check_bibstyle
                                                                    rest))
                                                                    | _ ->
                                                                    ref_010_check_bibstyle
                                                                    rest))
                                                                    | _::_ ->
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a15)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a14)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a13)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a12)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a11)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a10)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a9)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a8)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a7)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a6)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a5)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a4)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                    else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                                   else 
                                                                    ref_010_check_bibstyle
                                                                    rest
                                                       else ref_010_check_bibstyle
                                                              rest)
                                                       a0)
                                        else ref_010_check_bibstyle rest
                                   else ref_010_check_bibstyle rest
               else ref_010_check_bibstyle rest)
          a)
   | _ -> ref_010_check_bibstyle rest)

(** val ref_010_validator : document_state -> validation_issue list **)

let ref_010_validator doc =
  if ref_010_check_bibstyle doc.tokens
  then { rule_id = ('R'::('E'::('F'::('-'::('0'::('1'::('0'::[])))))));
         issue_severity = Info; message =
         ('C'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('m'::('o'::('d'::('e'::('r'::('n'::(' '::('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::(' '::('s'::('t'::('y'::('l'::('e'::(' '::('('::('e'::('.'::('g'::('.'::(','::(' '::('n'::('a'::('t'::('b'::('i'::('b'::(')'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('m'::('o'::('d'::('e'::('r'::('n'::('i'::('z'::('e'::('_'::('b'::('i'::('b'::('s'::('t'::('y'::('l'::('e'::[])))))))))))))))))));
         rule_owner =
         ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[]))))))))) } :: []
  else []

(** val ref_010_rule : validation_rule **)

let ref_010_rule =
  { id = ('R'::('E'::('F'::('-'::('0'::('1'::('0'::[]))))))); description =
    ('C'::('o'::('n'::('s'::('i'::('d'::('e'::('r'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('m'::('o'::('d'::('e'::('r'::('n'::(' '::('b'::('i'::('b'::('l'::('i'::('o'::('g'::('r'::('a'::('p'::('h'::('y'::(' '::('s'::('t'::('y'::('l'::('e'::[]))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('r'::('e'::('f'::('-'::('t'::('e'::('a'::('m'::[])))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('m'::('o'::('d'::('e'::('r'::('n'::('i'::('z'::('e'::('_'::('b'::('i'::('b'::('s'::('t'::('y'::('l'::('e'::[])))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = ref_010_validator; rule_sound = (Some
    ('r'::('e'::('f'::('_'::('0'::('1'::('0'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))) }

(** val style_001_check : char list -> bool **)

let style_001_check s =
  (||) (string_contains_substring s (' '::('='::(' '::[]))))
    (string_contains_substring s ('='::(' '::[])))

(** val style_001_validator : document_state -> validation_issue list **)

let style_001_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if style_001_check s
      then { rule_id =
             ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('1'::[])))))))));
             issue_severity = Info; message =
             ('I'::('n'::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('a'::('r'::('o'::('u'::('n'::('d'::(' '::('e'::('q'::('u'::('a'::('l'::('s'::(' '::('s'::('i'::('g'::('n'::[])))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))))))))))))))));
             rule_owner =
             ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val style_001_rule : validation_rule **)

let style_001_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('1'::[])))))))));
    description =
    ('I'::('n'::('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('a'::('r'::('o'::('u'::('n'::('d'::(' '::('e'::('q'::('u'::('a'::('l'::('s'::(' '::('s'::('i'::('g'::('n'::[])))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[])))))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_001_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('1'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_002_check : char list -> bool **)

let style_002_check s =
  string_contains_substring s (' '::(' '::[]))

(** val style_002_validator : document_state -> validation_issue list **)

let style_002_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if style_002_check s
      then { rule_id =
             ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('2'::[])))))))));
             issue_severity = Info; message =
             ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('c'::('o'::('n'::('s'::('e'::('c'::('u'::('t'::('i'::('v'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))))))));
             rule_owner =
             ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val style_002_rule : validation_rule **)

let style_002_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('2'::[])))))))));
    description =
    ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('c'::('o'::('n'::('s'::('e'::('c'::('u'::('t'::('i'::('v'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('n'::('o'::('r'::('m'::('a'::('l'::('i'::('z'::('e'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_002_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('2'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_003_check : char list -> bool **)

let style_003_check s =
  string_contains_substring s
    ((ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))::[])

(** val style_003_validator : document_state -> validation_issue list **)

let style_003_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if style_003_check s
      then { rule_id =
             ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('3'::[])))))))));
             issue_severity = Warning; message =
             ('T'::('a'::('b'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('-'::(' '::('u'::('s'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('i'::('n'::('s'::('t'::('e'::('a'::('d'::[])))))))))))))))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('t'::('a'::('b'::('s'::('_'::('t'::('o'::('_'::('s'::('p'::('a'::('c'::('e'::('s'::[])))))))))))))));
             rule_owner =
             ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val style_003_rule : validation_rule **)

let style_003_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('3'::[])))))))));
    description =
    ('T'::('a'::('b'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::(' '::('-'::(' '::('u'::('s'::('e'::(' '::('s'::('p'::('a'::('c'::('e'::('s'::(' '::('i'::('n'::('s'::('t'::('e'::('a'::('d'::[])))))))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('t'::('a'::('b'::('s'::('_'::('t'::('o'::('_'::('s'::('p'::('a'::('c'::('e'::('s'::[])))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_003_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('3'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_004_check : char list -> bool **)

let style_004_check =
  string_ends_with_spaces

(** val style_004_validator : document_state -> validation_issue list **)

let style_004_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if style_004_check s
      then { rule_id =
             ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('4'::[])))))))));
             issue_severity = Info; message =
             ('T'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::(' '::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('t'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))))))))))))));
             rule_owner =
             ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val style_004_rule : validation_rule **)

let style_004_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('4'::[])))))))));
    description =
    ('T'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::(' '::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('r'::('e'::('m'::('o'::('v'::('e'::('_'::('t'::('r'::('a'::('i'::('l'::('i'::('n'::('g'::('_'::('w'::('h'::('i'::('t'::('e'::('s'::('p'::('a'::('c'::('e'::[])))))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_004_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('4'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_005_has_frac : latex_token list -> bool **)

let rec style_005_has_frac = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> style_005_has_frac rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then style_005_has_frac rest
          else if b0
               then if b1
                    then if b2
                         then style_005_has_frac rest
                         else if b3
                              then style_005_has_frac rest
                              else if b4
                                   then if b5
                                        then if b6
                                             then style_005_has_frac rest
                                             else (match s0 with
                                                   | [] ->
                                                     style_005_has_frac rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then style_005_has_frac
                                                              rest
                                                       else if b8
                                                            then if b9
                                                                 then 
                                                                   style_005_has_frac
                                                                    rest
                                                                 else 
                                                                   if b10
                                                                   then 
                                                                    style_005_has_frac
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    style_005_has_frac
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    style_005_has_frac
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    true
                                                                    | _::_ ->
                                                                    style_005_has_frac
                                                                    rest)
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                                    else 
                                                                    style_005_has_frac
                                                                    rest
                                                            else style_005_has_frac
                                                                   rest)
                                                       a0)
                                        else style_005_has_frac rest
                                   else style_005_has_frac rest
                    else style_005_has_frac rest
               else style_005_has_frac rest)
          a)
   | _ -> style_005_has_frac rest)

(** val style_005_has_tfrac : latex_token list -> bool **)

let rec style_005_has_tfrac = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> style_005_has_tfrac rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then style_005_has_tfrac rest
          else if b0
               then style_005_has_tfrac rest
               else if b1
                    then if b2
                         then style_005_has_tfrac rest
                         else if b3
                              then if b4
                                   then if b5
                                        then if b6
                                             then style_005_has_tfrac rest
                                             else (match s0 with
                                                   | [] ->
                                                     style_005_has_tfrac rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then style_005_has_tfrac
                                                              rest
                                                       else if b8
                                                            then if b9
                                                                 then 
                                                                   if b10
                                                                   then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    if b33
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b34
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    true
                                                                    | _::_ ->
                                                                    style_005_has_tfrac
                                                                    rest)
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                    else 
                                                                    style_005_has_tfrac
                                                                    rest
                                                                 else 
                                                                   style_005_has_tfrac
                                                                    rest
                                                            else style_005_has_tfrac
                                                                   rest)
                                                       a0)
                                        else style_005_has_tfrac rest
                                   else style_005_has_tfrac rest
                              else style_005_has_tfrac rest
                    else style_005_has_tfrac rest)
          a)
   | _ -> style_005_has_tfrac rest)

(** val style_005_check : latex_token list -> bool **)

let style_005_check tokens0 =
  (&&) (style_005_has_frac tokens0) (style_005_has_tfrac tokens0)

(** val style_005_validator : document_state -> validation_issue list **)

let style_005_validator doc =
  if style_005_check doc.tokens
  then { rule_id =
         ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('5'::[])))))))));
         issue_severity = Info; message =
         ('M'::('i'::('x'::('e'::('d'::(' '::('f'::('r'::('a'::('c'::('t'::('i'::('o'::('n'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('('::('\\'::('\\'::('f'::('r'::('a'::('c'::(' '::('a'::('n'::('d'::(' '::('\\'::('\\'::('t'::('f'::('r'::('a'::('c'::(')'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('u'::('n'::('i'::('f'::('y'::('_'::('f'::('r'::('a'::('c'::('t'::('i'::('o'::('n'::('_'::('s'::('t'::('y'::('l'::('e'::[])))))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
  else []

(** val style_005_rule : validation_rule **)

let style_005_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('5'::[])))))))));
    description =
    ('M'::('i'::('x'::('e'::('d'::(' '::('f'::('r'::('a'::('c'::('t'::('i'::('o'::('n'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('u'::('n'::('i'::('f'::('y'::('_'::('f'::('r'::('a'::('c'::('t'::('i'::('o'::('n'::('_'::('s'::('t'::('y'::('l'::('e'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_005_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('5'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_006_check_line_length : char list -> bool **)

let style_006_check_line_length s =
  Nat.ltb (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (length0 s)

(** val style_006_validator : document_state -> validation_issue list **)

let style_006_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if style_006_check_line_length s
      then { rule_id =
             ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('6'::[])))))))));
             issue_severity = Info; message =
             ('L'::('i'::('n'::('e'::(' '::('e'::('x'::('c'::('e'::('e'::('d'::('s'::(' '::('8'::('0'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('b'::('r'::('e'::('a'::('k'::('_'::('l'::('o'::('n'::('g'::('_'::('l'::('i'::('n'::('e'::('s'::[])))))))))))))))));
             rule_owner =
             ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val style_006_rule : validation_rule **)

let style_006_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('6'::[])))))))));
    description =
    ('L'::('i'::('n'::('e'::(' '::('e'::('x'::('c'::('e'::('e'::('d'::('s'::(' '::('8'::('0'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('b'::('r'::('e'::('a'::('k'::('_'::('l'::('o'::('n'::('g'::('_'::('l'::('i'::('n'::('e'::('s'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_006_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('6'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_007_count_brackets :
    latex_token list -> int -> int -> int * int **)

let rec style_007_count_brackets tokens0 left right =
  match tokens0 with
  | [] -> (left, right)
  | l :: rest ->
    (match l with
     | TCommand cmd ->
       if string_eqb cmd ('l'::('e'::('f'::('t'::[]))))
       then style_007_count_brackets rest (Stdlib.Int.succ left) right
       else if string_eqb cmd ('r'::('i'::('g'::('h'::('t'::[])))))
            then style_007_count_brackets rest left (Stdlib.Int.succ right)
            else style_007_count_brackets rest left right
     | TText s ->
       if string_contains_substring s ('\\'::('l'::('e'::('f'::('t'::[])))))
       then style_007_count_brackets rest (Stdlib.Int.succ left) right
       else if string_contains_substring s
                 ('\\'::('r'::('i'::('g'::('h'::('t'::[]))))))
            then style_007_count_brackets rest left (Stdlib.Int.succ right)
            else style_007_count_brackets rest left right
     | _ -> style_007_count_brackets rest left right)

(** val style_007_check : latex_token list -> bool **)

let style_007_check tokens0 =
  let (left, right) = style_007_count_brackets tokens0 0 0 in
  negb ((=) left right)

(** val style_007_validator : document_state -> validation_issue list **)

let style_007_validator doc =
  if style_007_check doc.tokens
  then { rule_id =
         ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('7'::[])))))))));
         issue_severity = Warning; message =
         ('M'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('\\'::('\\'::('l'::('e'::('f'::('t'::(' '::('a'::('n'::('d'::(' '::('\\'::('\\'::('r'::('i'::('g'::('h'::('t'::(' '::('b'::('r'::('a'::('c'::('k'::('e'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('b'::('a'::('l'::('a'::('n'::('c'::('e'::('_'::('b'::('r'::('a'::('c'::('k'::('e'::('t'::('s'::[])))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
  else []

(** val style_007_rule : validation_rule **)

let style_007_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('7'::[])))))))));
    description =
    ('M'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::('e'::('d'::(' '::('\\'::('\\'::('l'::('e'::('f'::('t'::(' '::('a'::('n'::('d'::(' '::('\\'::('\\'::('r'::('i'::('g'::('h'::('t'::(' '::('b'::('r'::('a'::('c'::('k'::('e'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Warning; rule_maturity =
    Draft; owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('b'::('a'::('l'::('a'::('n'::('c'::('e'::('_'::('b'::('r'::('a'::('c'::('k'::('e'::('t'::('s'::[])))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_007_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('7'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_008_has_itemize : latex_token list -> bool **)

let rec style_008_has_itemize = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if string_contains_substring cmd
          ('i'::('t'::('e'::('m'::('i'::('z'::('e'::[])))))))
     then true
     else style_008_has_itemize rest
   | _ -> style_008_has_itemize rest)

(** val style_008_has_enumerate : latex_token list -> bool **)

let rec style_008_has_enumerate = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand cmd ->
     if string_contains_substring cmd
          ('e'::('n'::('u'::('m'::('e'::('r'::('a'::('t'::('e'::[])))))))))
     then true
     else style_008_has_enumerate rest
   | _ -> style_008_has_enumerate rest)

(** val style_008_check : latex_token list -> bool **)

let style_008_check tokens0 =
  (&&) (style_008_has_itemize tokens0) (style_008_has_enumerate tokens0)

(** val style_008_validator : document_state -> validation_issue list **)

let style_008_validator doc =
  if style_008_check doc.tokens
  then { rule_id =
         ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('8'::[])))))))));
         issue_severity = Info; message =
         ('M'::('i'::('x'::('e'::('d'::(' '::('l'::('i'::('s'::('t'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('('::('i'::('t'::('e'::('m'::('i'::('z'::('e'::(' '::('a'::('n'::('d'::(' '::('e'::('n'::('u'::('m'::('e'::('r'::('a'::('t'::('e'::(')'::(' '::('i'::('n'::(' '::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::('_'::('l'::('i'::('s'::('t'::('_'::('s'::('t'::('y'::('l'::('e'::[]))))))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
  else []

(** val style_008_rule : validation_rule **)

let style_008_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('8'::[])))))))));
    description =
    ('M'::('i'::('x'::('e'::('d'::(' '::('l'::('i'::('s'::('t'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('i'::('n'::(' '::('d'::('o'::('c'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('c'::('o'::('n'::('s'::('i'::('s'::('t'::('e'::('n'::('t'::('_'::('l'::('i'::('s'::('t'::('_'::('s'::('t'::('y'::('l'::('e'::[]))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_008_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('8'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_009_has_emph : latex_token list -> bool **)

let rec style_009_has_emph = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> style_009_has_emph rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then if b0
               then style_009_has_emph rest
               else if b1
                    then if b2
                         then style_009_has_emph rest
                         else if b3
                              then style_009_has_emph rest
                              else if b4
                                   then if b5
                                        then if b6
                                             then style_009_has_emph rest
                                             else (match s0 with
                                                   | [] ->
                                                     style_009_has_emph rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then style_009_has_emph
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   if b10
                                                                   then 
                                                                    if b11
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    style_009_has_emph
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    style_009_has_emph
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    true
                                                                    | _::_ ->
                                                                    style_009_has_emph
                                                                    rest)
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest
                                                                    else 
                                                                    style_009_has_emph
                                                                    rest
                                                                   else 
                                                                    style_009_has_emph
                                                                    rest
                                                                 else 
                                                                   style_009_has_emph
                                                                    rest
                                                       else style_009_has_emph
                                                              rest)
                                                       a0)
                                        else style_009_has_emph rest
                                   else style_009_has_emph rest
                    else style_009_has_emph rest
          else style_009_has_emph rest)
          a)
   | _ -> style_009_has_emph rest)

(** val style_009_has_textit : latex_token list -> bool **)

let rec style_009_has_textit = function
| [] -> false
| l :: rest ->
  (match l with
   | TCommand s ->
     (match s with
      | [] -> style_009_has_textit rest
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then style_009_has_textit rest
          else if b0
               then style_009_has_textit rest
               else if b1
                    then if b2
                         then style_009_has_textit rest
                         else if b3
                              then if b4
                                   then if b5
                                        then if b6
                                             then style_009_has_textit rest
                                             else (match s0 with
                                                   | [] ->
                                                     style_009_has_textit rest
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then if b8
                                                            then style_009_has_textit
                                                                   rest
                                                            else if b9
                                                                 then 
                                                                   if b10
                                                                   then 
                                                                    style_009_has_textit
                                                                    rest
                                                                   else 
                                                                    if b11
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    style_009_has_textit
                                                                    rest
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    style_009_has_textit
                                                                    rest
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    style_009_has_textit
                                                                    rest
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    style_009_has_textit
                                                                    rest
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b40
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    true
                                                                    | _::_ ->
                                                                    style_009_has_textit
                                                                    rest)
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest)
                                                                    a4)
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest)
                                                                    a3)
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest)
                                                                    a2)
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest)
                                                                    a1)
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                    else 
                                                                    style_009_has_textit
                                                                    rest
                                                                 else 
                                                                   style_009_has_textit
                                                                    rest
                                                       else style_009_has_textit
                                                              rest)
                                                       a0)
                                        else style_009_has_textit rest
                                   else style_009_has_textit rest
                              else style_009_has_textit rest
                    else style_009_has_textit rest)
          a)
   | _ -> style_009_has_textit rest)

(** val style_009_check : latex_token list -> bool **)

let style_009_check tokens0 =
  (&&) (style_009_has_emph tokens0) (style_009_has_textit tokens0)

(** val style_009_validator : document_state -> validation_issue list **)

let style_009_validator doc =
  if style_009_check doc.tokens
  then { rule_id =
         ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('9'::[])))))))));
         issue_severity = Info; message =
         ('M'::('i'::('x'::('e'::('d'::(' '::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('('::('\\'::('\\'::('e'::('m'::('p'::('h'::(' '::('a'::('n'::('d'::(' '::('\\'::('\\'::('t'::('e'::('x'::('t'::('i'::('t'::(')'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))));
         loc = None; suggested_fix = (Some
         ('u'::('n'::('i'::('f'::('y'::('_'::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::('_'::('s'::('t'::('y'::('l'::('e'::[])))))))))))))))))))));
         rule_owner =
         ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
  else []

(** val style_009_rule : validation_rule **)

let style_009_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('0'::('9'::[])))))))));
    description =
    ('M'::('i'::('x'::('e'::('d'::(' '::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::(' '::('s'::('t'::('y'::('l'::('e'::('s'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Command; auto_fix = (Some
    ('u'::('n'::('i'::('f'::('y'::('_'::('e'::('m'::('p'::('h'::('a'::('s'::('i'::('s'::('_'::('s'::('t'::('y'::('l'::('e'::[])))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_009_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('0'::('9'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val style_010_check : char list -> bool **)

let style_010_check s =
  (||) (string_contains_substring s ('.'::[]))
    ((||) (string_contains_substring s (','::[]))
      (string_contains_substring s (';'::[])))

(** val style_010_validator : document_state -> validation_issue list **)

let style_010_validator doc =
  flat_map (fun tok ->
    match tok with
    | TText s ->
      if style_010_check s
      then { rule_id =
             ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('1'::('0'::[])))))))));
             issue_severity = Info; message =
             ('C'::('h'::('e'::('c'::('k'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('p'::('u'::('n'::('c'::('t'::('u'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))));
             loc = None; suggested_fix = (Some
             ('f'::('i'::('x'::('_'::('p'::('u'::('n'::('c'::('t'::('u'::('a'::('t'::('i'::('o'::('n'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[]))))))))))))))))))))))));
             rule_owner =
             ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[]))))))))))) } :: []
      else []
    | _ -> []) doc.tokens

(** val style_010_rule : validation_rule **)

let style_010_rule =
  { id = ('S'::('T'::('Y'::('L'::('E'::('-'::('0'::('1'::('0'::[])))))))));
    description =
    ('C'::('h'::('e'::('c'::('k'::(' '::('s'::('p'::('a'::('c'::('i'::('n'::('g'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('p'::('u'::('n'::('c'::('t'::('u'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))));
    precondition = L0_Lexer; default_severity = Info; rule_maturity = Draft;
    owner =
    ('@'::('s'::('t'::('y'::('l'::('e'::('-'::('t'::('e'::('a'::('m'::[])))))))))));
    performance_bucket = TokenKind_Text; auto_fix = (Some
    ('f'::('i'::('x'::('_'::('p'::('u'::('n'::('c'::('t'::('u'::('a'::('t'::('i'::('o'::('n'::('_'::('s'::('p'::('a'::('c'::('i'::('n'::('g'::[]))))))))))))))))))))))));
    implementation_file =
    ('r'::('u'::('l'::('e'::('s'::('/'::('p'::('h'::('a'::('s'::('e'::('1'::('/'::('T'::('y'::('p'::('o'::('R'::('u'::('l'::('e'::('s'::('.'::('v'::[]))))))))))))))))))))))));
    validator = style_010_validator; rule_sound = (Some
    ('s'::('t'::('y'::('l'::('e'::('_'::('0'::('1'::('0'::('_'::('s'::('o'::('u'::('n'::('d'::('n'::('e'::('s'::('s'::[])))))))))))))))))))) }

(** val all_l0_rules : validation_rule list **)

let all_l0_rules =
  typo_001_rule :: (typo_002_rule :: (typo_003_rule :: (typo_004_rule :: (typo_005_rule :: (typo_006_rule :: (typo_007_rule :: (typo_008_rule :: (typo_009_rule :: (typo_010_rule :: (typo_011_rule :: (typo_012_rule :: (typo_013_rule :: (typo_014_rule :: (typo_015_rule :: (typo_016_rule :: (typo_017_rule :: (typo_018_rule :: (typo_019_rule :: (typo_020_rule :: (typo_021_rule :: (typo_022_rule :: (typo_023_rule :: (typo_024_rule :: (typo_025_rule :: (enc_001_rule :: (enc_002_rule :: (enc_003_rule :: (enc_004_rule :: (enc_005_rule :: (char_001_rule :: (char_002_rule :: (char_003_rule :: (char_004_rule :: (char_005_rule :: (env_001_rule :: (env_002_rule :: (env_003_rule :: (env_004_rule :: (env_005_rule :: (math_001_rule :: (math_002_rule :: (math_003_rule :: (math_004_rule :: (math_005_rule :: (struct_001_rule :: (struct_002_rule :: (struct_003_rule :: (struct_004_rule :: (struct_005_rule :: (struct_006_rule :: (struct_007_rule :: (struct_008_rule :: (struct_009_rule :: (struct_010_rule :: (ref_001_rule :: (ref_002_rule :: (ref_003_rule :: (ref_004_rule :: (ref_005_rule :: (ref_006_rule :: (ref_007_rule :: (ref_008_rule :: (ref_009_rule :: (ref_010_rule :: (style_001_rule :: (style_002_rule :: (style_003_rule :: (style_004_rule :: (style_005_rule :: (style_006_rule :: (style_007_rule :: (style_008_rule :: (style_009_rule :: (style_010_rule :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type rule_chunk = validation_rule list

(** val combine_results :
    validation_issue list list -> validation_issue list **)

let rec combine_results = function
| [] -> []
| issues :: rest -> app issues (combine_results rest)

(** val execute_chunk :
    rule_chunk -> document_state -> validation_issue list **)

let execute_chunk =
  execute_rules_bucketed

(** val create_chunks_helper :
    validation_rule list -> int -> int -> rule_chunk list **)

let rec create_chunks_helper rules chunk_size fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun fuel' ->
    match rules with
    | [] -> []
    | _ :: _ ->
      let chunk = firstn chunk_size rules in
      let remaining = skipn chunk_size rules in
      (match remaining with
       | [] -> chunk :: []
       | _ :: _ -> chunk :: (create_chunks_helper remaining chunk_size fuel')))
    fuel

(** val create_chunks : validation_rule list -> int -> rule_chunk list **)

let create_chunks rules chunk_size =
  let fuel = Stdlib.Int.succ (length rules) in
  create_chunks_helper rules chunk_size fuel

(** val optimal_chunk_size : validation_rule list -> int -> int **)

let optimal_chunk_size rules domain_count =
  let total_rules = length rules in
  let chunk_size = div total_rules domain_count in
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Stdlib.Int.succ 0)
     (fun _ -> chunk_size)
     chunk_size)

(** val parallel_execute_spec :
    validation_rule list -> document_state -> int -> validation_issue list **)

let parallel_execute_spec rules doc_state domain_count =
  let chunk_size = optimal_chunk_size rules domain_count in
  let chunks = create_chunks rules chunk_size in
  let chunk_results = map (fun chunk -> execute_chunk chunk doc_state) chunks
  in
  combine_results chunk_results

type rule_priority =
| HighPriority
| MediumPriority
| LowPriority

(** val get_rule_priority : validation_rule -> rule_priority **)

let get_rule_priority rule =
  match rule.performance_bucket with
  | TokenKind_Text -> HighPriority
  | TokenKind_Command -> HighPriority
  | TokenKind_Other -> LowPriority
  | _ -> MediumPriority

(** val filter_by_priority :
    validation_rule list -> rule_priority -> validation_rule list **)

let filter_by_priority rules priority =
  filter (fun rule ->
    match get_rule_priority rule with
    | HighPriority -> (match priority with
                       | HighPriority -> true
                       | _ -> false)
    | MediumPriority ->
      (match priority with
       | MediumPriority -> true
       | _ -> false)
    | LowPriority -> (match priority with
                      | LowPriority -> true
                      | _ -> false)) rules

(** val parallel_execute_prioritized :
    validation_rule list -> document_state -> int -> validation_issue list **)

let parallel_execute_prioritized rules doc_state domain_count =
  let high_priority_rules = filter_by_priority rules HighPriority in
  let medium_priority_rules = filter_by_priority rules MediumPriority in
  let low_priority_rules = filter_by_priority rules LowPriority in
  let high_results =
    parallel_execute_spec high_priority_rules doc_state domain_count
  in
  let medium_results =
    parallel_execute_spec medium_priority_rules doc_state domain_count
  in
  let low_results =
    parallel_execute_spec low_priority_rules doc_state domain_count
  in
  app high_results (app medium_results low_results)

(** val execute_rules_early_termination :
    validation_rule list -> document_state -> int -> validation_issue list **)

let rec execute_rules_early_termination rules doc_state max_issues =
  match rules with
  | [] -> []
  | rule :: rest ->
    let issues = execute_rule rule doc_state in
    let current_count = length issues in
    if leb max_issues current_count
    then firstn max_issues issues
    else let remaining_issues =
           execute_rules_early_termination rest doc_state
             (sub max_issues current_count)
         in
         app issues remaining_issues

(** val parallel_execute_early_termination :
    validation_rule list -> document_state -> int -> int -> validation_issue
    list **)

let parallel_execute_early_termination rules doc_state domain_count max_issues =
  let chunk_size = optimal_chunk_size rules domain_count in
  let chunks = create_chunks rules chunk_size in
  let chunk_results =
    map (fun chunk ->
      execute_rules_early_termination chunk doc_state
        (div max_issues domain_count)) chunks
  in
  let combined = combine_results chunk_results in firstn max_issues combined

(** val balance_chunks : validation_rule list -> int -> rule_chunk list **)

let balance_chunks rules domain_count =
  create_chunks rules (optimal_chunk_size rules domain_count)

(** val enterprise_parallel_execute :
    validation_rule list -> document_state -> int -> int -> validation_issue
    list **)

let enterprise_parallel_execute rules doc_state domain_count max_issues =
  let balanced_chunks = balance_chunks rules domain_count in
  let chunk_results =
    map (fun chunk ->
      execute_rules_early_termination chunk doc_state
        (div max_issues domain_count)) balanced_chunks
  in
  let combined = combine_results chunk_results in firstn max_issues combined

(** val all_parallel_functions :
    ((((((((validation_rule list -> document_state -> int -> validation_issue
    list) * (validation_rule list -> document_state -> int ->
    validation_issue list)) * (validation_rule list -> document_state -> int
    -> int -> validation_issue list)) * (validation_rule list ->
    document_state -> int -> int -> validation_issue
    list)) * (validation_rule list -> int -> rule_chunk
    list)) * (validation_rule list -> int -> int)) * (validation_rule list ->
    int -> rule_chunk list)) * (rule_chunk -> document_state ->
    validation_issue list)) * (validation_issue list list -> validation_issue
    list) **)

let all_parallel_functions =
  ((((((((parallel_execute_spec, parallel_execute_prioritized),
    parallel_execute_early_termination), enterprise_parallel_execute),
    create_chunks), optimal_chunk_size), balance_chunks), execute_chunk),
    combine_results)

(** val parallel_all_l0_rules : validation_rule list **)

let parallel_all_l0_rules =
  all_l0_rules

(** val estimate_parallel_speedup : validation_rule list -> int -> int **)

let estimate_parallel_speedup rules domain_count =
  let total_rules = length rules in
  let parallel_cost = add (div total_rules domain_count) (Stdlib.Int.succ 0)
  in
  div total_rules parallel_cost
