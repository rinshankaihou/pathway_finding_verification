
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

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

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

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

type taxiway_type = string

type edge_type = ((vertex, vertex) prod, taxiway_type) prod

type n_Graph_type = edge_type list

type node_type = (vertex, vertex) prod

type arc_type = ((node_type, node_type) prod, taxiway_type) prod

type c_Graph_type = arc_type list

type state_type =
| State of arc_type list * string * string list * string list

(** val s_1 : state_type -> arc_type list **)

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

(** val input : vertex **)

let input =
  O

(** val edge_inv : edge_type -> edge_type **)

let edge_inv edge =
  Pair ((Pair ((snd (fst edge)), (fst (fst edge)))), (snd edge))

(** val undirect_to_bidirect : n_Graph_type -> n_Graph_type **)

let undirect_to_bidirect ng =
  filter (fun x -> negb (eqv (fst (fst x)) input))
    (flat_map (fun edge -> Cons (edge, (Cons ((edge_inv edge), Nil)))) ng)

(** val previous_edges : edge_type -> n_Graph_type -> edge_type list **)

let previous_edges cur bg =
  filter (fun x ->
    match eqv (fst (fst x)) (snd (fst cur)) with
    | True -> negb (eqv (snd (fst x)) (fst (fst cur)))
    | False -> False) bg

(** val generate_edges : n_Graph_type -> edge_type -> arc_type list **)

let generate_edges bg edge =
  map (fun x -> Pair ((Pair ((fst x), (fst edge))), (snd edge)))
    (previous_edges edge bg)

(** val to_C : n_Graph_type -> c_Graph_type **)

let to_C ng =
  let bg = undirect_to_bidirect ng in flat_map (generate_edges bg) bg

(** val if_on_next_taxiway : state_type -> arc_type -> bool **)

let if_on_next_taxiway cur_s arc =
  match hd_error (s_3 cur_s) with
  | Some t -> eqb1 t (snd arc)
  | None -> False

(** val if_on_current_taxiway : state_type -> arc_type -> bool **)

let if_on_current_taxiway cur_s arc =
  eqb1 (s_2 cur_s) (snd arc)

(** val if_reach_endpoint : state_type -> vertex -> bool **)

let if_reach_endpoint cur_s end_v =
  match hd_error (s_1 cur_s) with
  | Some arc ->
    (match eqv (fst (snd (fst arc))) end_v with
     | True -> eqn (length (s_3 cur_s)) O
     | False -> False)
  | None -> False

(** val next_Arcs : node_type -> arc_type -> bool **)

let next_Arcs current arc =
  match eqv (fst current) (fst (fst (fst arc))) with
  | True -> eqv (snd current) (snd (fst (fst arc)))
  | False -> False

(** val find_Arc : node_type -> c_Graph_type -> arc_type list **)

let find_Arc current d =
  filter (next_Arcs current) d

(** val step_state_by_arc : state_type -> arc_type -> state_type list **)

let step_state_by_arc cur_s arc =
  match if_on_current_taxiway cur_s arc with
  | True ->
    Cons ((State ((Cons (arc, (s_1 cur_s))), (s_2 cur_s), (s_3 cur_s),
      (s_4 cur_s))), Nil)
  | False ->
    (match if_on_next_taxiway cur_s arc with
     | True ->
       Cons ((State ((Cons (arc, (s_1 cur_s))), (snd arc), (tl (s_3 cur_s)),
         (Cons ((s_2 cur_s), (s_4 cur_s))))), Nil)
     | False -> Nil)

(** val step_states : state_type -> c_Graph_type -> state_type list **)

let step_states cur_s d =
  match hd_error (s_1 cur_s) with
  | Some arc ->
    flat_map (step_state_by_arc cur_s) (find_Arc (snd (fst arc)) d)
  | None -> Nil

(** val find_path_aux :
    vertex -> c_Graph_type -> nat -> state_type -> arc_type list list **)

let rec find_path_aux end_v d bound cur_s =
  match bound with
  | O -> Nil
  | S n ->
    cat
      (match if_reach_endpoint cur_s end_v with
       | True -> Cons ((rev (s_1 cur_s)), Nil)
       | False -> Nil)
      (flat_map (find_path_aux end_v d n) (step_states cur_s d))

(** val input0 : vertex **)

let input0 =
  O

(** val find_path :
    vertex -> vertex -> string list -> c_Graph_type -> arc_type list list
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
        (State ((Cons ((Pair ((Pair ((Pair (start_v, input0)), (Pair
        (start_v, input0)))), t)), Nil)), t, rest, Nil)))

(** val c_to_n : arc_type -> edge_type **)

let c_to_n ce =
  Pair ((snd (fst ce)), (snd ce))

(** val to_N : arc_type list -> edge_type list **)

let to_N le =
  map c_to_n le

(** val path_finding_algorithm :
    vertex -> vertex -> taxiway_type list -> n_Graph_type -> edge_type list
    list option **)

let path_finding_algorithm start_v end_v aTC graph =
  match find_path start_v end_v aTC (to_C graph) with
  | Some v -> Some (map to_N v)
  | None -> None
