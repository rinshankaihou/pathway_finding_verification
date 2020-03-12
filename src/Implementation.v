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
    check whether the edge e is on the next ATC command in state cur_s
*)
Definition if_on_next_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    match hd_error cur_s@3 with
    | None => false
    | Some t => t =? e.2
    end.

(*
    check whether the edge e is on current taxiway of state cur_s
*)
Definition if_on_current_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    cur_s@2 =? e.2.

Lemma on_current_taxiway_lemma : forall (s:State_type) (e:Edge_type), 
    if_on_current_taxiway s e -> (e.2 =? s@2).
Proof. intros s e H. unfold if_on_current_taxiway in H. 
    rewrite -> String.eqb_sym. assumption. Qed.

(*
    check whether current state reaches the endpoint
*)
Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match hd_error cur_s@1 with
    | None => false (*will never reach*)
    | Some e => (eqv e.1.2.1 end_v) && (eqn (List.length cur_s@3) 0)
    end.  

(*
    check whether an edge starts from current node
*)
Definition next_edges (current : Node_type) (e : Edge_type) : bool :=
    (eqv current.1 e.1.1.1) && (eqv current.2 e.1.1.2).

(* ============ find edges ============*)

(*
    filter on the graph to find all edges start from current noe
*)
Definition find_edge (current : Node_type) (D : Graph_type) : list Edge_type :=
    filter (next_edges current) D.

(* ============ step functions ============*)

(*
    step_state_by_e takes a state and an edge as input,
        it checks whether the edge e is valid for next step,
        if is valid return a list of one corresponding state,
        if not, return an empty list
*)
Definition step_state_by_e (cur_s : State_type) (e : Edge_type) : list State_type :=
    if if_on_current_taxiway cur_s e
    then [State (e::cur_s@1) cur_s@2 cur_s@3 cur_s@4]
    else if if_on_next_taxiway cur_s e (* on the next taxiway *)
        then [State (e::cur_s@1) e.2 (tail cur_s@3) (cur_s@2 :: cur_s@4)]
        else [].


(*
    step_states takes a state and a graph as input, 
        it will return all possible states after a valid step
    
    step_states may find other possible paths to endpoint
*)
Definition step_states (cur_s : State_type) (D : Graph_type) : list State_type :=
    match hd_error cur_s@1 with
    | None => []
    | Some e => flat_map (step_state_by_e cur_s) (find_edge e.1.2 D)
    end.


(* ============ main functions ============*)

(*
    find_path_aux takes an endpoint, a graph, round bound and a state,
        it will return a list of possible paths
    
    find_path_aux first checks whether state reaches endpoint,
        and find all possible states for next step (no matter reach end or not),
        then recursive on all states returned

    find_path_aux may return zero or more than one path,
        it requires a sufficient large round bound
*)
Fixpoint find_path_aux (end_v : Vertex) (D : Graph_type) (round_bound : nat) (cur_s : State_type) : list (list Edge_type) :=
    match round_bound with
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
Definition find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : option (list (list Edge_type)) :=
    match ATC with
    | [] => None (* ATC error *)
    | t :: rest => Some (find_path_aux end_v D 100 (State [(((start_v, input), (start_v, input)), t)] t rest []))
    end.


