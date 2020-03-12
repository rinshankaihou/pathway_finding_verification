
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')
 end

(** val hd_error : 'a1 list -> 'a1 option **)

let hd_error = function
| Nil -> None
| Cons (x, _) -> Some x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| Nil -> Nil
| Cons (_, m) -> m

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Nil -> Nil
| Cons (x, t) -> app (f x) (flat_map f t)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f x with
   | True -> Cons (x, (filter f l0))
   | False -> filter f l0)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

(** val eqn : nat -> nat -> bool **)

let rec eqn m n =
  match m with
  | O -> (match n with
          | O -> True
          | S _ -> False)
  | S m' -> (match n with
             | O -> False
             | S n' -> eqn m' n')

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | Nil -> s2
  | Cons (x, s1') -> Cons (x, (cat s1' s2))

type vertex = nat
  (* singleton inductive, whose constructor was index *)

(** val eqv : vertex -> vertex -> bool **)

let eqv =
  Nat.eqb

type node_type = (vertex, vertex) prod

type taxiway_type = string

type edge_type = ((node_type, node_type) prod, taxiway_type) prod

type graph_type = edge_type list

type state_type =
| State of edge_type list * string * string list * string list

(** val s_1 : state_type -> edge_type list **)

let s_1 = function
| State (cur_path, _, _, _) -> cur_path

(** val s_2 : state_type -> string **)

let s_2 = function
| State (_, atc_h, _, _) -> atc_h

(** val s_3 : state_type -> string list **)

let s_3 = function
| State (_, _, atc_t, _) -> atc_t

(** val s_4 : state_type -> string list **)

let s_4 = function
| State (_, _, _, atc_used) -> atc_used

(** val if_on_next_taxiway : state_type -> edge_type -> bool **)

let if_on_next_taxiway cur_s e =
  match hd_error (s_3 cur_s) with
  | Some t -> eqb1 t (snd e)
  | None -> False

(** val if_on_current_taxiway : state_type -> edge_type -> bool **)

let if_on_current_taxiway cur_s e =
  eqb1 (s_2 cur_s) (snd e)

(** val if_reach_endpoint : state_type -> vertex -> bool **)

let if_reach_endpoint cur_s end_v =
  match hd_error (s_1 cur_s) with
  | Some e ->
    (match eqv (fst (snd (fst e))) end_v with
     | True -> eqn (length (s_3 cur_s)) O
     | False -> False)
  | None -> False

(** val next_edges : node_type -> edge_type -> bool **)

let next_edges current e =
  match eqv (fst current) (fst (fst (fst e))) with
  | True -> eqv (snd current) (snd (fst (fst e)))
  | False -> False

(** val find_edge : node_type -> graph_type -> edge_type list **)

let find_edge current d =
  filter (next_edges current) d

(** val step_state_by_e : state_type -> edge_type -> state_type list **)

let step_state_by_e cur_s e =
  match if_on_current_taxiway cur_s e with
  | True ->
    Cons ((State ((Cons (e, (s_1 cur_s))), (s_2 cur_s), (s_3 cur_s),
      (s_4 cur_s))), Nil)
  | False ->
    (match if_on_next_taxiway cur_s e with
     | True ->
       Cons ((State ((Cons (e, (s_1 cur_s))), (snd e), (tl (s_3 cur_s)),
         (Cons ((s_2 cur_s), (s_4 cur_s))))), Nil)
     | False -> Nil)

(** val step_states : state_type -> graph_type -> state_type list **)

let step_states cur_s d =
  match hd_error (s_1 cur_s) with
  | Some e -> flat_map (step_state_by_e cur_s) (find_edge (snd (fst e)) d)
  | None -> Nil

(** val find_path_aux :
    vertex -> graph_type -> nat -> state_type -> edge_type list list **)

let rec find_path_aux end_v d round_bound cur_s =
  match round_bound with
  | O -> Nil
  | S n ->
    cat
      (match if_reach_endpoint cur_s end_v with
       | True -> Cons ((rev (s_1 cur_s)), Nil)
       | False -> Nil)
      (flat_map (find_path_aux end_v d n) (step_states cur_s d))

(** val input : vertex **)

let input =
  O

(** val find_path :
    vertex -> vertex -> string list -> graph_type -> edge_type list list
    option **)

let find_path start_v end_v aTC d =
  match aTC with
  | Nil -> None
  | Cons (t, rest) ->
    Some
      (find_path_aux end_v d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (State ((Cons ((Pair ((Pair ((Pair (start_v, input)), (Pair (start_v,
        input)))), t)), Nil)), t, rest, Nil)))
