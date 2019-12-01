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

Forall ...., res = find_path_wrapper 
-> last res = end_v.

Forall


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
Example AB := index 6.
Example CA := index 7.

Example tC  := [C1; CB; CA].
Example tA1 := [AA1; A1_24].
Example tA2 := [A2_6; AB].
Example tA := [AA3; AB; CA; AA1].
Example tB := [CB; AB].
Example tA3 := [AA3; A3_6].
Example eg_taxiways :=
  [tC; tA1; tA2; tA; tB; tA3].

Example eg_find_path_1 : find_path_wrapper C1 AB [tC] = [].
Proof. reflexivity. Qed.

Example eg_find_path_2 : find_path_wrapper C1 CB [tC] = [[C1; CB]].
Proof. reflexivity. Qed.

Example eg_find_path_3 : find_path_wrapper C1 AA3 [tC;tB;tA] = [[C1; CB; AB; AA3]].
Proof. reflexivity. Qed.

Example eg_find_path_4 : find_path_wrapper AA3 AA1 [tA;tB;tC;tA] = [[AA3; AB; CB; CA; AA1]].
Proof. reflexivity. Qed.

Example eg_find_path_5 : find_path_wrapper A3_6 A1_24 [tA3; tA; tA1] = [[A3_6; AA3; AB; CA; AA1; A1_24]].
Proof. reflexivity. Qed.

Example eg_find_path_6 : find_path_wrapper C1 C1 [tC; tB; tA; tC; tB; tA; tC] = [[C1; CB; AB; CA; CB; AB; CA; CB; C1]].
Proof. reflexivity. Qed.








































From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
Require Import Coq.Lists.List Coq.Bool.Bool.

(*
Using the basic pair (V_list, list V_list)
    - fst is the vertice lists that previously visited, the first is current 
    - snd is the remaining ATC commend, first is this one

Whenever we deal with a pair, we get all its neighbors, and only consider the vertices having taxiway name
    - this taxiway => push into the stack
    - next taxiway => delete snd's first element, and push into the stack
meanwhile adding the node to the previous node list

not using option type, or none
*)


(*
    push_stack accepts a pair, and return as list of pairs with requirements of the pair
    find_path acts like while(not empty), and when accepting the push_stack, check if there's valid path 
*)


Example AA3 := index 1.
Example AB := index 2.
Example AC := index 3.
Example AA1 := index 4.
Example C1 := index 5.
Example BC := index 6.
Example A3_6 := index 7.
Example A2_6 := index 8.
Example A1_24 := index 9.

Example tC  := [C1; BC; AC].
Example tA := [AA3; AB; AC; AA1].
Example tB := [BC; AB].
Example tA1 := [AA1; A1_24].
Example tA2 := [AB; A2_6].
Example tA3 := [AA3; A3_6].

Example eg_taxiways :=
[tC; tA; tB; tA1; tA2; tA3].


Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Fixpoint eqv_list (vlst1 : V_list) (vlst2 : V_list) : bool :=
  match vlst1, vlst2 with
  | v1::r1, v2::r2 => if eqv v1 v2 then eqv_list r1 r2 else false
  | [], [] => true
  | _, _ => false
  end.

Fixpoint v_in_vlist (v : Vertex) (vlst : V_list) : bool :=
  match vlst with
  | [] => false
  | a :: rst => if eqv a v then true else v_in_vlist v rst
  end.


(* Example vin : v_in_vlist CA nA = true.
Proof. reflexivity. Qed. *)


(* return sublist after v, or [] *)
Fixpoint list_after_v (v : Vertex) (taxiway : V_list) {struct taxiway}: V_list :=
  match taxiway with  
  | a::rest => if eqv a v then rest else list_after_v v rest
  | _ => []
  end.

(* TODO should return option Vertex *)
(* return [next_elem] after v, or [] *)
Definition next_neighbor (v : Vertex) (taxiway : V_list) : V_list :=
  match list_after_v v taxiway with
  | next_elem::rest => [next_elem]
  | _ => []
  end.

(* this is like the wrapper, so we don't use None anymore
need to prove that result is on the current taxiway*)
Definition both_side_neighbor (v: option Vertex) (taxiway : option V_list) : V_list :=
  match v with
  | None => []
  | Some v => match taxiway with
    | None => []
    | Some taxiway => next_neighbor v taxiway ++ next_neighbor v (rev taxiway)
    end
  end. 


(* easy to prove that at most 2 elements, 
using property of list, will drop which on the pre_list*)
(*todo: don't accept cur_V, but accept taxiway, if not on taxiway, next_neighbor will return []*)
(* This will return all vertex that not visited and on cur_taxi and next_taxi*)
(* Definition neighbors_on_the_taxiway (cur_v : (V_list * list V_list)) : list Vertex :=
    match both_side_neighbor (head (fst cur_v)) (head (snd cur_v)) with
    | [] => []
    | a :: nil => if (v_in_vlist a (fst cur_v)) then [] else [a]
    | a :: b :: nil => if v_in_vlist a (fst cur_v) then 
                            if v_in_vlist b (fst cur_v) then [] else [b]
                        else 
                            if v_in_vlist b (fst cur_v) then [a] else [a;b]
    | a :: b :: l => [] (*will not encounter*)
    end. *)





(* only when is on next ATC will return true,
so if only one taxiway indicates it's the last ATC taixway, will return false to proceed on
  need to prove that will never be none *)
Definition on_next_ATC (v : Vertex) (cur_v : V_list * list V_list) : bool :=
    match snd cur_v with
    | [] => false
    | a :: nil => false
    | a :: b :: _ => v_in_vlist v b     (*if ... then true else false*)
    end.


(* Example foo : v_in_vlist BA [BA] = true.
Proof. reflexivity. Qed.

Eval vm_compute in on_next_ATC (BA) ([CB;C1], [nB; nA]).

Example o1 : on_next_ATC (BA) ([CB;C1], [nC;nB]) = true.
Proof. reflexivity. Qed. *)

(* input v, cur_v. (f cur_v) can be flat_mapped
    check v:
      if on pre_nodes, return []
      if on this_taxi (surely), return [(v::pre_nodes, taxis)] ++ 
        if on next_taxi, return [(v::pre_nodes, tail taxis)]*)

(* modify: we only check the last visited node in case loop commanded by ATC*)
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
  push_stack is used to take a node, and push the results into stack. push_neighbor do that

  match neighbors (already dropped the previous), 
    - if [a]
      + if a on next_ATC == true
          return 2 result
      + else return 1 result
    - if [a,b], if a on next_ATC 
          then 2 results
        else 1 result     ++  if b on next_ATC
          then 2 results
        else 1 result
TODO: if a neighbor is either on current or next ATC, we push next neighbor
so which means we check neighbors for 2 taxiways 
*)


(* a helper function to make life easier*)
Definition push_stack (cur_v : V_list * list V_list) : list (V_list * list V_list) :=
    flat_map (filter_neighbor cur_v) (both_side_neighbor (head (fst cur_v)) (head (snd cur_v))).

(* Eval vm_compute in push_stack s1.
Example p1 : push_stack s1 = [([BA;CB;C1], [nB; nA]); ([BA;CB;C1], [nA])].
Proof. reflexivity. Qed.

Eval vm_compute in push_stack ([CA;CB;C1], [nC; nA]).
Example p2 : push_stack ([CA;CB;C1], [nC; nA]) = [].
Proof. reflexivity. Qed. *)

(* This is a function to check whether we reach the end of a path
  put it outside just to make things more clear*)
(* need to prove will never appear None*)
Definition is_the_path (cur_v : V_list * list V_list) (end_v : Vertex): bool :=
    match head (fst cur_v) with
    | None => false
    | Some a => eqv a end_v && (length (snd cur_v) == 1)
    end.

(* Eval vm_compute in is_the_path ([CB;C1],[nC]) CB. *)

(* find_path maintains a stack, if is empty, end.
each iteration it will fetch the first one in stack:
  first check whether is end, 
    if is: continue (return is the path)
    if not: call push_neighbors (return nothing)

push front is dfs, push back is bfs. Here we use dfs
iter is to let coq know we will end
or we should prove that it will ends
*)
Fixpoint find_path (cur_stack : list (V_list * list V_list)) (end_v : Vertex) (iter : nat): list V_list :=
    match iter with
    | 0 => []
    | S n => match cur_stack with
        | [] => []
        | a :: l => if is_the_path a end_v then [rev (fst a)] ++ find_path (l) end_v n
                  else find_path (l ++ push_stack a) end_v n
        end
    end.  

(* Eval vm_compute in find_path [([C1], [nC])] CB 100. *)


Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (taxiway_names : list V_list) : list V_list :=
    find_path [([start_v], taxiway_names)] end_v 100.





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

  (* Example eg_find_path_5: find_path_wrapper C1 BA [nB] = [].
  Proof. reflexivity. Qed.  
    
  Eval vm_compute in find_path_wrapper C1 CB [nC].
  Eval vm_compute in find_path_wrapper C1 A3 [nC;nB;nA].
 Example eg_find_path_4: find_path_wrapper C1 CB [nC] = [[C1;CB]].
  Proof.  reflexivity. Qed.
  Example eg_find_path_1: find_path_wrapper C1 A3 [nC;nB;nA] = [[C1; CB; BA; A3]].
  Proof.  reflexivity. Qed.
  Example eg_find_path_2: find_path_wrapper A3 C1 (rev [nC;nB;nA]) = [rev [C1; CB; BA; A3]].
  Proof. reflexivity. Qed.
  Example eg_find_path_3: find_path_wrapper C1 A3 [nC;nA] = [[C1; CB; CA; BA; A3]].
  Proof. reflexivity. Qed.

Eval vm_compute in find_path_wrapper C1 A3 [nC;nB;nA;nC;nB;nA;nC;nB;nA].
  Example eg_find_path_6: find_path_wrapper C1 A3 [nC;nB;nA;nC;nB;nA;nC;nB;nA] = [[C1;CB;BA;CA;CB;BA;CA;CB;BA;A3]].
  Proof. reflexivity. Qed.
   *)



(* The definitions imported GraphBasics.Vertices:
     Vertex: nat->Vertex, indexed by nat
     V_list = list Vertex
   New definitions:
     taxiway : V_list, an ordered list of all vertices on the taxiway. 
                       There is no name for a taxiway. 
                       
     taxiways : list taxiway, a list of all taxiways. order does not matter.
                              TODO Consider using string->V_list to replace taxiways.
   taxiways represents all information in the graph for now
   ATC Command is: (start_vertex, end_vertex, taxiway_names)
   Entry point (top level function) find_path_wrapper.

Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Fixpoint eqv_list (vlst1 : V_list) (vlst2 : V_list) : bool :=
  match vlst1, vlst2 with
  | v1::r1, v2::r2 => if eqv v1 v2 then eqv_list r1 r2 else false
  | [], [] => true
  | _, _ => false
  end.

(* a state of searching, a pair of current partial path and the remaining taxiway names *)
Definition state : Type := V_list * (list V_list).


Definition stepping (partial_path : V_list) (taxiway_names : list V_list): list V_list :=
  match partial_path with
  | [] => []
  | cur_vertex::rest_partial_path => V_list 
 
Print map.
Fixpoint dfs (cur_stack : list V_list) (end_vtx : Vertex) (taxiway_names : list V_list): list V_list :=
  match cur_stack with
  | [] => []
  | partial_path::rest_cur_stack => step partial_path ++ (dfs rest_cur_stack

Fixpoint dfs_wrapper (start_vtx : Vertex) (end_vtx : Vertex) (taxiway_names : list V_list): list V_list :=
  dfs [[start_vtx]] end_vtx taxiway_names. 

  *)