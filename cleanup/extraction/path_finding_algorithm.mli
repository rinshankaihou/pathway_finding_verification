
type bool =
| True
| False

val negb : bool -> bool

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

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

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

type taxiway_type = string

type edge_type = ((vertex, vertex) prod, taxiway_type) prod

type n_Graph_type = edge_type list

type node_type = (vertex, vertex) prod

type arc_type = ((node_type, node_type) prod, taxiway_type) prod

type c_Graph_type = arc_type list

type state_type =
| State of arc_type list * string * string list * string list

val s_1 : state_type -> arc_type list

val s_2 : state_type -> string

val s_3 : state_type -> string list

val s_4 : state_type -> string list

val input : vertex

val edge_inv : edge_type -> edge_type

val undirect_to_bidirect : n_Graph_type -> n_Graph_type

val previous_edges : edge_type -> n_Graph_type -> edge_type list

val generate_edges : n_Graph_type -> edge_type -> arc_type list

val to_C : n_Graph_type -> c_Graph_type

val if_on_next_taxiway : state_type -> arc_type -> bool

val if_on_current_taxiway : state_type -> arc_type -> bool

val if_reach_endpoint : state_type -> vertex -> bool

val next_Arcs : node_type -> arc_type -> bool

val find_Arc : node_type -> c_Graph_type -> arc_type list

val step_state_by_arc : state_type -> arc_type -> state_type list

val step_states : state_type -> c_Graph_type -> state_type list

val find_path_aux :
  vertex -> c_Graph_type -> nat -> state_type -> arc_type list list

val input0 : vertex

val find_path :
  vertex -> vertex -> string list -> c_Graph_type -> arc_type list list option

val c_to_n : arc_type -> edge_type

val to_N : arc_type list -> edge_type list

val path_finding_algorithm :
  vertex -> vertex -> taxiway_type list -> n_Graph_type -> edge_type list
  list option
