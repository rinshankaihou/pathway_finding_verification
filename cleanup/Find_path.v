(*
    The functions to implement the algorithm,
    dependencies and declarations are discribed in Types.v

    The top-level function is find_path
*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Coq.Program.Tactics.
From Taxiway Require Export Types.

(* ============ comparision functions ============*)

(*
    check whether the Arc arc is on the next ATC command in state cur_s
*)
Definition if_on_next_taxiway (cur_s : State_type) (arc :  Arc_type) : bool :=
    match hd_error cur_s@3 with
    | None => false
    | Some t => t =? arc.2
    end.

(*
    check whether the Arc arc is on current taxiway of state cur_s
*)
Definition if_on_current_taxiway (cur_s : State_type) (arc :  Arc_type) : bool :=
    cur_s@2 =? arc.2.

Lemma on_current_taxiway_lemma : forall (s:State_type) (arc:Arc_type), 
    if_on_current_taxiway s arc -> (arc.2 =? s@2).
Proof. intros s arc H. unfold if_on_current_taxiway in H. 
    rewrite -> String.eqb_sym. assumption. Qed.

(*
    check whether current state reaches the endpoint
*)
Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match hd_error cur_s@1 with
    | None => false (*will never reach*)
    | Some arc => (eqv arc.1.2.1 end_v) && (eqn (List.length cur_s@3) 0)
    end.  

(*
    check whether an Arc starts from current node
*)
Definition next_Arcs (current : Node_type) (arc :  Arc_type) : bool :=
    (eqv current.1 arc.1.1.1) && (eqv current.2 arc.1.1.2).

(* ============ find Arcs ============*)

(*
    filter on the graph to find all Arcs start from current noe
*)
Definition find_Arc (current : Node_type) (D : C_Graph_type) : list Arc_type :=
    filter (next_Arcs current) D.

(* ============ step functions ============*)

(*
    step_state_by_arc takes a state and an Arc as input,
        it checks whether the Arc arc is valid for next step,
        if is valid return a list of one corresponding state,
        if not, return an empty list
*)
Definition step_state_by_arc (cur_s : State_type) (arc :  Arc_type) : list State_type :=
    if if_on_current_taxiway cur_s arc
    then [State (arc::cur_s@1) cur_s@2 cur_s@3 cur_s@4]
    else if if_on_next_taxiway cur_s arc (* on the next taxiway *)
        then [State (arc::cur_s@1) arc.2 (tail cur_s@3) (cur_s@2 :: cur_s@4)]
        else [].


(*
    step_states takes a state and a graph as input, 
        it will return all possible states after a valid step
    
    step_states may find other possible paths to endpoint
*)
Definition step_states (cur_s : State_type) (D : C_Graph_type) : list State_type :=
    match hd_error cur_s@1 with
    | None => []
    | Some arc => flat_map (step_state_by_arc cur_s) (find_Arc arc.1.2 D)
    end.


(* ============ main functions ============*)

(*
    find_path_aux takes an endpoint, a graph, bound and a state,
        it will return a list of possible paths
    
    find_path_aux first checks whether state reaches endpoint,
        and find all possible states for next step (no matter reach end or not),
        then recursive on all states returned

    find_path_aux may return zero or more than one path,
        it requires a sufficient large bound
*)
Fixpoint find_path_aux (end_v : Vertex) (D : C_Graph_type) (bound : nat) (cur_s : State_type) : list (list Arc_type) :=
    match bound with
    | 0 => []
    | S n =>
        (if if_reach_endpoint cur_s end_v  (*reach endpoint*)
        then [rev cur_s@1]
        else []) ++
        (flat_map (find_path_aux end_v D n) (step_states cur_s D))
    end. 


(* 
    hardcoded input vertex. if a vertex is start_vertex in the naive graph, 
    we encode input Node in the complete graph to be ((start_vertex, input), (start_vertex, input)) 
*)
Definition input : Vertex := index 0.

(*
    find_path is the top-level function
    find_path packs original input into initial state and call find_path_aux
*)
Definition find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type) : option (list (list Arc_type)) :=
    match ATC with
    | [] => None (* ATC error *)
    | t :: rest => Some (find_path_aux end_v D 100 (State [(((start_v, input), (start_v, input)), t)] t rest []))
    end.


