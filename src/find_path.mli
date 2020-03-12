
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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : nat -> nat -> bool
 end

val hd_error : 'a1 list -> 'a1 option

val tl : 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

val eqn : nat -> nat -> bool

val cat : 'a1 list -> 'a1 list -> 'a1 list

type vertex = nat
  (* singleton inductive, whose constructor was index *)

val eqv : vertex -> vertex -> bool

type node_type = (vertex, vertex) prod

type taxiway_type = string

type edge_type = ((node_type, node_type) prod, taxiway_type) prod

type graph_type = edge_type list

type state_type =
| State of edge_type list * string * string list * string list

val s_1 : state_type -> edge_type list

val s_2 : state_type -> string

val s_3 : state_type -> string list

val s_4 : state_type -> string list

val if_on_next_taxiway : state_type -> edge_type -> bool

val if_on_current_taxiway : state_type -> edge_type -> bool

val if_reach_endpoint : state_type -> vertex -> bool

val next_edges : node_type -> edge_type -> bool

val find_edge : node_type -> graph_type -> edge_type list

val step_state_by_e : state_type -> edge_type -> state_type list

val step_states : state_type -> graph_type -> state_type list

val find_path_aux :
  vertex -> graph_type -> nat -> state_type -> edge_type list list

val input : vertex

val find_path :
  vertex -> vertex -> string list -> graph_type -> edge_type list list option
