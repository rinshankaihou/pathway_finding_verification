
type __ = Obj.t

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a0 -> Some (f a0)
| None -> None

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a0 :: l1 -> a0 :: (app l1 m)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')
 end

(** val hd_error : 'a1 list -> 'a1 option **)

let hd_error = function
| [] -> None
| x :: _ -> Some x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: m -> m

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a0 :: t3 -> (f a0) :: (map f t3)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t3 -> app (f x) (flat_map f t3)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c0::s1' -> c0::(append s1' s2)

(** val eqn : nat -> nat -> bool **)

let rec eqn m n0 =
  match m with
  | O -> (match n0 with
          | O -> true
          | S _ -> false)
  | S m' -> (match n0 with
             | O -> false
             | S n' -> eqn m' n')

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

type vertex = nat
  (* singleton inductive, whose constructor was index *)

(** val eqv : vertex -> vertex -> bool **)

let eqv =
  Nat.eqb

type taxiway_type = char list

type edge_type = (vertex * vertex) * taxiway_type

type n_Graph_type = edge_type list

type node_type = vertex * vertex

type arc_type = (node_type * node_type) * taxiway_type

type c_Graph_type = arc_type list

type state_type =
| State of arc_type list * char list * char list list * char list list

(** val s_1 : state_type -> arc_type list **)

let s_1 = function
| State (cur_path, _, _, _) -> cur_path

(** val s_2 : state_type -> char list **)

let s_2 = function
| State (_, atc_h, _, _) -> atc_h

(** val s_3 : state_type -> char list list **)

let s_3 = function
| State (_, _, atc_t, _) -> atc_t

(** val s_4 : state_type -> char list list **)

let s_4 = function
| State (_, _, _, atc_used) -> atc_used

(** val input : vertex **)

let input =
  O

(** val edge_inv : edge_type -> edge_type **)

let edge_inv edge =
  (((snd (fst edge)), (fst (fst edge))), (snd edge))

(** val undirect_to_bidirect : n_Graph_type -> n_Graph_type **)

let undirect_to_bidirect ng =
  filter (fun x -> negb (eqv (fst (fst x)) input))
    (flat_map (fun edge -> edge :: ((edge_inv edge) :: [])) ng)

(** val previous_edges : edge_type -> n_Graph_type -> edge_type list **)

let previous_edges cur bg =
  filter (fun x ->
    (&&) (eqv (fst (fst x)) (snd (fst cur)))
      (negb (eqv (snd (fst x)) (fst (fst cur))))) bg

(** val generate_edges : n_Graph_type -> edge_type -> arc_type list **)

let generate_edges bg edge =
  map (fun x -> (((fst x), (fst edge)), (snd edge))) (previous_edges edge bg)

(** val to_C : n_Graph_type -> c_Graph_type **)

let to_C ng =
  let bg = undirect_to_bidirect ng in flat_map (generate_edges bg) bg

(** val if_on_next_taxiway : state_type -> arc_type -> bool **)

let if_on_next_taxiway cur_s arc =
  match hd_error (s_3 cur_s) with
  | Some t3 -> eqb0 t3 (snd arc)
  | None -> false

(** val if_on_current_taxiway : state_type -> arc_type -> bool **)

let if_on_current_taxiway cur_s arc =
  eqb0 (s_2 cur_s) (snd arc)

(** val if_reach_endpoint : state_type -> vertex -> bool **)

let if_reach_endpoint cur_s end_v =
  match hd_error (s_1 cur_s) with
  | Some arc ->
    (&&) (eqv (fst (snd (fst arc))) end_v) (eqn (length (s_3 cur_s)) O)
  | None -> false

(** val next_Arcs : node_type -> arc_type -> bool **)

let next_Arcs current arc =
  (&&) (eqv (fst current) (fst (fst (fst arc))))
    (eqv (snd current) (snd (fst (fst arc))))

(** val find_Arc : node_type -> c_Graph_type -> arc_type list **)

let find_Arc current d =
  filter (next_Arcs current) d

(** val step_state_by_arc : state_type -> arc_type -> state_type list **)

let step_state_by_arc cur_s arc =
  if if_on_current_taxiway cur_s arc
  then (State ((arc :: (s_1 cur_s)), (s_2 cur_s), (s_3 cur_s),
         (s_4 cur_s))) :: []
  else if if_on_next_taxiway cur_s arc
       then (State ((arc :: (s_1 cur_s)), (snd arc), (tl (s_3 cur_s)),
              ((s_2 cur_s) :: (s_4 cur_s)))) :: []
       else []

(** val step_states : state_type -> c_Graph_type -> state_type list **)

let step_states cur_s d =
  match hd_error (s_1 cur_s) with
  | Some arc ->
    flat_map (step_state_by_arc cur_s) (find_Arc (snd (fst arc)) d)
  | None -> []

(** val find_path_aux :
    vertex -> c_Graph_type -> nat -> state_type -> arc_type list list **)

let rec find_path_aux end_v d bound cur_s =
  match bound with
  | O -> []
  | S n0 ->
    cat
      (if if_reach_endpoint cur_s end_v then (rev (s_1 cur_s)) :: [] else [])
      (flat_map (find_path_aux end_v d n0) (step_states cur_s d))

(** val input0 : vertex **)

let input0 =
  O

(** val find_path :
    vertex -> vertex -> char list list -> c_Graph_type -> arc_type list list
    option **)

let find_path start_v end_v aTC d =
  match aTC with
  | [] -> None
  | t3 :: rest ->
    Some
      (find_path_aux end_v d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (State (((((start_v, input0), (start_v, input0)), t3) :: []), t3,
        rest, [])))

(** val c_to_n : arc_type -> edge_type **)

let c_to_n ce =
  ((snd (fst ce)), (snd ce))

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

module Notations =
 struct
  (** val ret : t -> 'a1 -> 'a1 t0 **)

  let ret _ x =
    Ret x

  (** val call : t -> command -> answer t0 **)

  let call _ command0 =
    Call command0
 end

type t1 = char list

module Option =
 struct
  (** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

  let bind x f =
    match x with
    | Some x0 -> f x0
    | None -> None
 end

module LString =
 struct
  (** val of_string : char list -> t1 **)

  let rec of_string = function
  | [] -> []
  | c0::s1 -> c0 :: (of_string s1)

  (** val s : char list -> t1 **)

  let s =
    of_string

  type t = char list

  module Char =
   struct
    (** val n : char **)

    let n =
      '\n'
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

(** val effect : t **)

let effect =
  New

(** val printl : LString.t -> bool t0 **)

let printl message =
  Obj.magic Notations.call effect (Print (app message (LString.Char.n :: [])))

(** val log : LString.t -> unit t0 **)

let log message =
  Let ((Obj.magic printl message), (fun _ -> Notations.ret effect ()))

(** val apply : ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let apply f =
  f

module BigInt =
 struct
  type t = Big_int.big_int

  (** val to_Z_aux :
      t -> 'a1 -> ('a2 -> 'a1) -> ('a2 -> 'a1) -> 'a2 -> ('a2 -> 'a2) -> ('a2
      -> 'a2) -> 'a1 **)

  let to_Z_aux = IoSystem.Big.to_Z_aux

  (** val to_Z : t -> z **)

  let to_Z big =
    to_Z_aux big Z0 (fun x -> Zpos x) (fun x -> Zneg x) XH (fun x -> XO x)
      (fun x -> XI x)
 end

module String =
 struct
  type t = string

  (** val of_lstring : LString.t -> t **)

  let of_lstring = IoSystem.String.of_lstring

  (** val to_lstring : t -> LString.t **)

  let to_lstring = IoSystem.String.to_lstring
 end

module Sys =
 struct
  (** val argv : String.t list **)

  let argv = IoSystem.argv
 end

module Lwt =
 struct
  type 'a t = 'a Lwt.t

  (** val ret : 'a1 -> 'a1 t **)

  let ret = Lwt.return

  (** val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t **)

  let bind = Lwt.bind

  (** val join : 'a1 t -> 'a2 t -> ('a1 * 'a2) t **)

  let join = IoSystem.join

  (** val choose : 'a1 t -> 'a1 t -> 'a1 t **)

  let choose = IoSystem.choose

  (** val launch : 'a1 t -> 'a1 **)

  let launch = Lwt_main.run

  (** val list_files : String.t -> String.t list option t **)

  let list_files = IoSystem.list_files

  (** val read_file : String.t -> String.t option t **)

  let read_file = IoSystem.read_file

  (** val write_file : String.t -> String.t -> bool t **)

  let write_file = IoSystem.write_file

  (** val delete_file : String.t -> bool t **)

  let delete_file = IoSystem.delete_file

  (** val system : String.t -> bool option t **)

  let system = IoSystem.system

  (** val eval :
      String.t list -> ((BigInt.t * String.t) * String.t) option t **)

  let eval = IoSystem.eval

  (** val print : String.t -> bool t **)

  let print = IoSystem.print

  (** val read_line : unit -> String.t option t **)

  let read_line = IoSystem.read_line
 end

(** val eval_command : command -> answer Lwt.t **)

let eval_command c0 =
  match Obj.magic c0 with
  | ListFiles folder ->
    Lwt.bind (apply Lwt.list_files (String.of_lstring folder)) (fun files ->
      apply (Obj.magic Lwt.ret)
        (Option.bind files (fun files0 -> Some
          (map String.to_lstring files0))))
  | ReadFile file_name ->
    Lwt.bind (apply Lwt.read_file (String.of_lstring file_name))
      (fun content ->
      apply (Obj.magic Lwt.ret) (option_map String.to_lstring content))
  | WriteFile (file_name, content) ->
    let file_name0 = String.of_lstring file_name in
    let content0 = String.of_lstring content in
    Obj.magic Lwt.write_file file_name0 content0
  | DeleteFile file_name ->
    apply (Obj.magic Lwt.delete_file) (String.of_lstring file_name)
  | System command0 -> Obj.magic Lwt.system (String.of_lstring command0)
  | Eval command0 ->
    let command1 = map String.of_lstring command0 in
    Lwt.bind (Lwt.eval command1) (fun result ->
      Lwt.ret
        (apply
          (Obj.magic option_map (fun result0 ->
            let (y, err) = result0 in
            let (status, output) = y in
            (((BigInt.to_Z status), (String.to_lstring output)),
            (String.to_lstring err)))) result))
  | Print message ->
    let message0 = String.of_lstring message in Obj.magic Lwt.print message0
  | ReadLine ->
    Lwt.bind (Lwt.read_line ()) (fun line ->
      apply (Obj.magic Lwt.ret) (option_map String.to_lstring line))

(** val eval0 : 'a1 t0 -> 'a1 Lwt.t **)

let rec eval0 = function
| Ret x0 -> Lwt.ret x0
| Call command0 -> Obj.magic eval_command command0
| Let (x0, f) -> Lwt.bind (Obj.magic eval0 x0) (fun x1 -> eval0 (f x1))
| Choose (x1, x2) -> Lwt.choose (eval0 x1) (eval0 x2)
| Join (x0, y) ->
  Obj.magic Lwt.join (eval0 (Obj.magic x0)) (eval0 (Obj.magic y))

(** val launch0 : (LString.t list -> unit t0) -> unit **)

let launch0 main0 =
  let argv0 = map String.to_lstring Sys.argv in
  Lwt.launch (eval0 (main0 argv0))

(** val aA3 : vertex **)

let aA3 =
  S O

(** val aB : vertex **)

let aB =
  S (S O)

(** val aC : vertex **)

let aC =
  S (S (S O))

(** val aA1 : vertex **)

let aA1 =
  S (S (S (S O)))

(** val ch : vertex **)

let ch =
  S (S (S (S (S O))))

(** val bC : vertex **)

let bC =
  S (S (S (S (S (S O)))))

(** val a3r : vertex **)

let a3r =
  S (S (S (S (S (S (S O))))))

(** val a2r : vertex **)

let a2r =
  S (S (S (S (S (S (S (S O)))))))

(** val a1r : vertex **)

let a1r =
  S (S (S (S (S (S (S (S (S O))))))))

(** val a : taxiway_type **)

let a =
  'A'::[]

(** val b : char list **)

let b =
  'B'::[]

(** val c : char list **)

let c =
  'C'::[]

(** val a1 : char list **)

let a1 =
  'A'::('1'::[])

(** val a2 : char list **)

let a2 =
  'A'::('2'::[])

(** val a3 : char list **)

let a3 =
  'A'::('3'::[])

(** val naive_ann_arbor : n_Graph_type **)

let naive_ann_arbor =
  ((ch, input0), []) :: (((a1r, input0), []) :: (((a2r, input0),
    []) :: (((a3r, input0), []) :: (((bC, input0), []) :: (((ch, bC),
    c) :: (((bC, aB), b) :: (((aB, aA3), a) :: (((aA3, a3r), a3) :: (((aB,
    a2r), a2) :: (((bC, aC), c) :: (((aB, aC), a) :: (((aC, aA1),
    a) :: (((aA1, a1r), a1) :: [])))))))))))))

(** val ann_arbor_v2s : vertex -> char list **)

let ann_arbor_v2s = function
| O -> 'i'::('n'::('p'::('u'::('t'::[]))))
| S n0 ->
  (match n0 with
   | O -> 'A'::('A'::('3'::[]))
   | S n1 ->
     (match n1 with
      | O -> 'A'::('B'::[])
      | S n2 ->
        (match n2 with
         | O -> 'A'::('C'::[])
         | S n3 ->
           (match n3 with
            | O -> 'A'::('A'::('1'::[]))
            | S n4 ->
              (match n4 with
               | O -> 'C'::('h'::[])
               | S n5 ->
                 (match n5 with
                  | O -> 'B'::('C'::[])
                  | S n6 ->
                    (match n6 with
                     | O -> 'A'::('3'::('r'::[]))
                     | S n7 ->
                       (match n7 with
                        | O -> 'A'::('2'::('r'::[]))
                        | S n8 ->
                          (match n8 with
                           | O -> 'A'::('1'::('r'::[]))
                           | S _ ->
                             'E'::('r'::('r'::('o'::('r'::(' '::('V'::('e'::('r'::('t'::('e'::('x'::[]))))))))))))))))))))

(** val string_list_append : char list list -> char list **)

let rec string_list_append = function
| [] -> []
| h :: t3 -> append h (string_list_append t3)

(** val edge_to_string : (vertex -> char list) -> edge_type -> char list **)

let edge_to_string f e =
  string_list_append
    (('('::('f'::('r'::('o'::('m'::(' '::[])))))) :: ((f (snd (fst e))) :: ((' '::('t'::('o'::(' '::[])))) :: (
    (f (fst (fst e))) :: ((' '::('o'::('n'::(' '::('t'::('a'::('x'::('i'::('w'::('a'::('y'::(' '::[])))))))))))) :: (
    (snd e) :: ((')'::[]) :: [])))))))

(** val ann_arbor_e2s : edge_type list -> char list list **)

let ann_arbor_e2s le =
  map (edge_to_string ann_arbor_v2s) le

(** val example_result_to_string :
    edge_type list list option -> char list list list **)

let example_result_to_string = function
| Some s0 -> map ann_arbor_e2s s0
| None ->
  (('N'::('o'::(' '::('p'::('a'::('t'::('h'::(' '::('f'::('o'::('u'::('n'::('d'::('.'::[])))))))))))))) :: []) :: []

(** val path_finding_example : edge_type list list option **)

let path_finding_example =
  path_finding_algorithm ch a3r (c :: (a :: (a3 :: []))) naive_ann_arbor

(** val path_finding_example_string : char list list list **)

let path_finding_example_string =
  example_result_to_string path_finding_example

(** val print_start : char list **)

let print_start =
  '['::[]

(** val print_empty : char list **)

let print_empty =
  []

(** val print_concat : char list **)

let print_concat =
  ';'::[]

(** val print_line : char list -> unit t0 **)

let print_line s0 =
  log (app (LString.s s0) (LString.s print_concat))

(** val print_path : char list list -> unit t0 **)

let rec print_path = function
| [] -> log (LString.s (']'::[]))
| h :: t3 -> Let ((Obj.magic print_line h), (fun _ -> print_path t3))

(** val print_result : char list list list -> unit t0 **)

let rec print_result = function
| [] -> log (LString.s print_empty)
| h :: t3 ->
  Let ((Obj.magic log (LString.s print_start)), (fun _ -> Let
    ((Obj.magic print_path h), (fun _ -> print_result t3))))

(** val print_example : LString.t list -> unit t0 **)

let print_example _ =
  print_result path_finding_example_string

(** val main : unit **)

let main =
  launch0 print_example
