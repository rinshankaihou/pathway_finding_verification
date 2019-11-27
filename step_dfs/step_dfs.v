From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
Require Import Coq.Lists.List Coq.Bool.Bool.


(*
    Argument: add "-arg -impredicative-set" in the _CoqProject

    Using type:
        Vertex, the node in the graph
        V_list:= list Vertex, the taxiway
        list V_list, the graph
    
    Using data structure:
        (V_List, list V_List) as current state
        fst: the previous visited node, or the reversed path
             the first element is current vertex, last element is the first
        snd: the rest taxiway we're going to go
             the first element is current taxiway
    
    Algorithm:
        maintain a list as stack, storing all possible states to check

        Start from pushing the origin vertex
        Fetch one element in stack until empty:
            Check if it's a valid path:
                if is, store and continue
                if not, push next possible states into stack
        
        Push next possible states:
            Fetch all neighbors, drop the last visited
            If on the same taxiway, push
            If on next taxiway, push and delete current taxiway 

    Explanation:
        By using this step algorithm, we consider next step, and check possible steps.
        The advantage is we don't need to deal with specs such as loop
        We can thus find all possible paths.
        There's only one easy fixpoint dealing with stack.

    TO PROOF:
        1. get neighbors get all the neighbors
        2. the result of filter and pack neighbors are under specs, we don't miss them
        3. The result is correct
        4. The fixpoint will end (currently use counter)
            - prove the unvisited states/vertex are mono decreasing
            - If we can prove it, it's same as we check all possibilities
            - with the 1,2,3 means we find every correct answer, so everything is done

*)


(*
    Basic support functions
*)

Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Fixpoint v_in_vlist (v : Vertex) (vlst : V_list) : bool :=
  match vlst with
  | [] => false
  | a :: rst => if eqv a v then true else v_in_vlist v rst
  end.


(*
    All these functions are to get the neighbors 
*)

Fixpoint list_after_v (v : Vertex) (taxiway : V_list) {struct taxiway}: V_list :=
  match taxiway with  
  | a::rest => if eqv a v then rest else list_after_v v rest
  | _ => []
  end.

Definition next_neighbor (v : Vertex) (taxiway : V_list) : V_list :=
  match list_after_v v taxiway with
  | next_elem::rest => [next_elem]
  | _ => []
  end.

Definition both_side_neighbor (v: option Vertex) (taxiway : option V_list) : V_list :=
  match v with
  | None => []
  | Some v => match taxiway with
    | None => []
    | Some taxiway => next_neighbor v taxiway ++ next_neighbor v (rev taxiway)
    end
  end. 


(*
    These functions are to pack a vertex into the data structure
*)

Definition on_next_ATC (v : Vertex) (cur_v : V_list * list V_list) : bool :=
    match snd cur_v with
    | [] => false
    | a :: nil => false
    | a :: b :: _ => v_in_vlist v b     (*if ... then true else false*)
    end.

Definition is_last_node (v : Vertex) (cur_v : V_list * list V_list)  : bool :=
    match head (tail (fst cur_v)) with
    | None => false
    | Some a => if eqv a v then true else false
    end.

Definition filter_neighbor (cur_v : V_list * list V_list) (v : Vertex) : list (V_list * list V_list) :=
    if is_last_node v cur_v then [] else 
    [(v::(fst cur_v), snd cur_v)] ++ 
        if on_next_ATC v cur_v then [(v::(fst cur_v), tail (snd cur_v))] else [].
  

(*
    Main parts
*)

Definition push_stack (cur_v : V_list * list V_list) : list (V_list * list V_list) :=
    flat_map (filter_neighbor cur_v) (both_side_neighbor (head (fst cur_v)) (head (snd cur_v))).

Definition is_the_path (cur_v : V_list * list V_list) (end_v : Vertex): bool :=
    match head (fst cur_v) with
    | None => false
    | Some a => eqv a end_v && (length (snd cur_v) == 1)
    end.

Fixpoint find_path (cur_stack : list (V_list * list V_list)) (end_v : Vertex) (iter : nat): list V_list :=
    match iter with
    | 0 => []
    | S n => match cur_stack with
        | [] => []
        | a :: l => if is_the_path a end_v then [rev (fst a)] ++ find_path (l) end_v n
                  else find_path (l ++ push_stack a) end_v n
        end
    end.  


(*
    The function to call, in order to preserve with previous versions
    return a list of all possible paths
*)

Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (taxiway_names : list V_list) : list V_list :=
    find_path [([start_v], taxiway_names)] end_v 100.




(*
    TestCases, related to the latest graph notation
*)

Example A1_24 := index 0.
Example AA1 := index 1.
Example A2_6 := index 2.
Example A3_6 := index 3.
Example AA3 := index 8.
Example C1 := index 4.
Example CB := index 5.
Example BA := index 6.
Example CA := index 7.

Example tC  := [C1; CB; CA].
Example tA1 := [AA1; A1_24].
Example tA2 := [A2_6; BA].
Example tA := [AA3; BA; CA; AA1].
Example tB := [CB; BA].
Example tA3 := [AA3; A3_6].
Example eg_taxiways :=
  [tC; tA1; tA2; tA; tB; tA3].

Example eg_find_path_1 : find_path_wrapper C1 AB [tC] = [].
Proof. reflexivity. Qed.

Example eg_find_path_2 : find_path_wrapper C1 BC [tC] = [[C1; BC]].
Proof. reflexivity. Qed.

Example eg_find_path_3 : find_path_wrapper C1 AA3 [tC;tB;tA] = [[C1; BC; AB; AA3]].
Proof. reflexivity. Qed.

Example eg_find_path_4 : find_path_wrapper AA3 AA1 [tA;tB;tC;tA] = [[AA3; AB; BC; AC; AA1]].
Proof. reflexivity. Qed.

Example eg_find_path_5 : find_path_wrapper A3_6 A1_24 [tA3; tA; tA1] = [[A3_6; AA3; AB; AC; AA1; A1_24]].
Proof. reflexivity. Qed.

Example eg_find_path_6 : find_path_wrapper C1 C1 [tC; tB; tA; tC; tB; tA; tC] = [[C1; BC; AB; AC; BC; AB; AC; BC; C1]].
Proof. reflexivity. Qed.