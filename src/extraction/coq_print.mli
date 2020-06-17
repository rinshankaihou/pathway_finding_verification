
type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

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

val eqb0 : char list -> char list -> bool

val append : char list -> char list -> char list

val eqn : nat -> nat -> bool

val cat : 'a1 list -> 'a1 list -> 'a1 list

type vertex = nat
  (* singleton inductive, whose constructor was index *)

val eqv : vertex -> vertex -> bool

type taxiway_type = char list

type edge_type = (vertex * vertex) * taxiway_type

type n_Graph_type = edge_type list

type node_type = vertex * vertex

type arc_type = (node_type * node_type) * taxiway_type

type c_Graph_type = arc_type list

type state_type =
| State of arc_type list * char list * char list list * char list list

val s_1 : state_type -> arc_type list

val s_2 : state_type -> char list

val s_3 : state_type -> char list list

val s_4 : state_type -> char list list

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
  vertex -> vertex -> char list list -> c_Graph_type -> arc_type list list
  option

val c_to_n : arc_type -> edge_type

val to_N : arc_type list -> edge_type list

val path_finding_algorithm :
  vertex -> vertex -> taxiway_type list -> n_Graph_type -> edge_type list
  list option

type t =
| New

type command = __

type answer = __

type 'x t0 =
| Ret of 'x
| Call of command
| Let of __ t0 * (__ -> 'x t0)
| Choose of 'x t0 * 'x t0
| Join of __ t0 * __ t0

module Notations :
 sig
  val ret : t -> 'a1 -> 'a1 t0

  val call : t -> command -> answer t0
 end

type t1 = char list

module Option :
 sig
  val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option
 end

module LString :
 sig
  val of_string : char list -> t1

  val s : char list -> t1

  type t = char list

  module Char :
   sig
    val n : char
   end
 end

type t2 =
| ListFiles of LString.t
| ReadFile of LString.t
| WriteFile of LString.t * LString.t
| DeleteFile of LString.t
| System of LString.t
| Eval of LString.t list
| Print of LString.t
| ReadLine

val effect : t

val printl : LString.t -> bool t0

val log : LString.t -> unit t0

val apply : ('a1 -> 'a2) -> 'a1 -> 'a2

module BigInt :
 sig
  type t = Big_int.big_int

  val to_Z_aux :
    t -> 'a1 -> ('a2 -> 'a1) -> ('a2 -> 'a1) -> 'a2 -> ('a2 -> 'a2) -> ('a2
    -> 'a2) -> 'a1

  val to_Z : t -> z
 end

module String :
 sig
  type t = string

  val of_lstring : LString.t -> t

  val to_lstring : t -> LString.t
 end

module Sys :
 sig
  val argv : String.t list
 end

module Lwt :
 sig
  type 'a t = 'a Lwt.t

  val ret : 'a1 -> 'a1 t

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val join : 'a1 t -> 'a2 t -> ('a1 * 'a2) t

  val choose : 'a1 t -> 'a1 t -> 'a1 t

  val launch : 'a1 t -> 'a1

  val list_files : String.t -> String.t list option t

  val read_file : String.t -> String.t option t

  val write_file : String.t -> String.t -> bool t

  val delete_file : String.t -> bool t

  val system : String.t -> bool option t

  val eval : String.t list -> ((BigInt.t * String.t) * String.t) option t

  val print : String.t -> bool t

  val read_line : unit -> String.t option t
 end

val eval_command : command -> answer Lwt.t

val eval0 : 'a1 t0 -> 'a1 Lwt.t

val launch0 : (LString.t list -> unit t0) -> unit

val aA3 : vertex

val aB : vertex

val aC : vertex

val aA1 : vertex

val ch : vertex

val bC : vertex

val a3r : vertex

val a2r : vertex

val a1r : vertex

val a : taxiway_type

val b : char list

val c : char list

val a1 : char list

val a2 : char list

val a3 : char list

val naive_ann_arbor : n_Graph_type

val ann_arbor_v2s : vertex -> char list

val string_list_append : char list list -> char list

val edge_to_string : (vertex -> char list) -> edge_type -> char list

val ann_arbor_e2s : edge_type list -> char list list

val example_result_to_string :
  edge_type list list option -> char list list list

val path_finding_example : edge_type list list option

val path_finding_example_string : char list list list

val print_start : char list

val print_empty : char list

val print_concat : char list

val print_line : char list -> unit t0

val print_path : char list list -> unit t0

val print_result : char list list list -> unit t0

val print_example : LString.t list -> unit t0

val main : unit
