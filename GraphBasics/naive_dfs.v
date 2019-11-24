
From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
(*From Coq Require Import FSets.FMapInterface.*)
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

(* define taxiway name as their index in taxiway_names *)


Example tC  := [C1; CB; CA].
Example tA1 := [AA1; A1_24].
Example tA2 := [A2_6; BA].
Example tA := [AA3; BA; CA; AA1].
Example tB := [CB; BA].
Example tA3 := [AA3; A3_6].
Example eg_taxiways :=
  [tC; tA1; tA2; tA; tB; tA3].
(* abandoned example *)
(* Example eg_indexing (e : Edge) : nat :=
  match e with
  | E_ends C1 CB => tC
  | E_ends A1 CA => tA1
  | E_ends A2 BA => tA2
  | E_ends A3 BA => tA
  | E_ends CB C1 => tC | E_ends CB BA => tB | E_ends CB CA => tC
  | E_ends BA A2 => tA2 | E_ends BA A3 => tA | E_ends BA CB => B | E_ends BA CA => tA
  | E_ends CA A1 => tA1 | E_ends CA CB => tC | E_ends CA BA => tA
  end. *)



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


(* return all neighboring vertices of v *)
Fixpoint all_neighbors (v : Vertex) (taxiways : list V_list) : V_list :=
  match taxiways with
  | [] => []
  | taxiway::rest_taxiway =>
    (next_neighbor v taxiway) ++
    (next_neighbor v (rev taxiway)) ++
    (all_neighbors v rest_taxiway)
  end. 


(* find a vertex in cur_taxi that is also in next_taxi, and chop the rest *)
(* find intersection of cur_lst and next_taxi and keep cur_lst up to this intersection *)
Fixpoint chop_tail (cur_lst : V_list) (next_taxi : V_list) : option V_list :=
  match cur_lst with
  | [] => None
  | fst::rest => if (V_in_dec fst next_taxi) then Some [fst] else
      match chop_tail rest next_taxi with
      | None => None
      | Some res => Some (fst::res)
      end
  end.

(* for demonstration. Do not use in algo *)
Definition unwrap {T : Type} (thing : option (list T)) : list T := 
  match thing with 
  | Some thing' => thing' 
  | None => []
  end.

Lemma chop_tail_never_return_nil :  forall (cur_lst : V_list) (next_taxi : V_list),
  (chop_tail cur_lst next_taxi <> None) ->
  ((chop_tail cur_lst next_taxi) <> Some []).
Proof.
intros cur_lst next_taxi H0.
 destruct cur_lst as []eqn:split1.
  - discriminate.
  - simpl.  
     destruct (is_left (V_in_dec v next_taxi)) as []eqn:split2.
     + discriminate.
     + destruct (chop_tail v0 next_taxi) as []eqn:split3.
       -discriminate.
       -discriminate.
Qed.

Lemma chop_tail_extend_not_none : 
  forall (fst : Vertex) (rest : V_list) (next_taxi : V_list),
  (chop_tail rest next_taxi <> None) ->
  ((chop_tail (fst::rest) next_taxi) <> None).
Proof.
intros fst rest next_taxi H0.
unfold chop_tail.
destruct (is_left (V_in_dec fst next_taxi)) as []eqn:split1.
- discriminate.
- fold chop_tail. destruct (chop_tail rest next_taxi)  as []eqn:split2. 
  + discriminate. 
  + contradiction H0. reflexivity.
Qed.

Lemma chop_tail_last_correct : forall (cur_lst : V_list) (next_taxi : V_list),
                             (chop_tail cur_lst next_taxi <> None) ->
                             V_in_dec (last (unwrap (chop_tail cur_lst next_taxi) ) (index 0)) next_taxi.
Proof. intros cur_lst next_taxi ret_not_none.
induction cur_lst as [|fst_of_cur_lst rest_of_cur_lst IH1].
- simpl. simpl in ret_not_none. contradiction.
- simpl. destruct (is_left (V_in_dec fst_of_cur_lst next_taxi)) as []eqn:split1.
  + simpl. exact split1.
  + assert (lemma1 : (chop_tail rest_of_cur_lst next_taxi <> None)).
    {
      simpl in ret_not_none. rewrite -> split1 in ret_not_none. 
      destruct (chop_tail rest_of_cur_lst next_taxi) as []eqn:split2.
      - discriminate.
      - contradiction.
    }
    apply IH1 in lemma1 as lemma2.
    destruct (chop_tail rest_of_cur_lst next_taxi) as []eqn:split2.
    * simpl. rewrite <- split2 in lemma1. apply chop_tail_never_return_nil in lemma1.
      rewrite split2 in lemma1. assert (v_not_empty : v <> []). {destruct v. -contradiction. -discriminate. }
      simpl in lemma2.
      destruct v as [|v']. 
        {contradiction. }
        {exact lemma2. }
    * contradiction.
Qed.


(* tC = XX XXX C1 CB CA XX XX
tB = CB BA *)
(* example *)
Eval vm_compute in eqv_list (unwrap (chop_tail tC tB)) [C1; CB] == true.


(* TODO for now, if there are multiple intermediate vertices, we arbitrary pick one *)
(* return a path segment of cur_taxi, from cur_vertex (exclusive) to a vertex on the next taxiway (inclusive) *) 
Definition get_seg (cur_vertex : Vertex) (cur_taxi : V_list) (next_taxi : V_list) : option V_list :=
  match (chop_tail  (list_after_v cur_vertex cur_taxi) next_taxi), 
        (chop_tail  (list_after_v cur_vertex (rev cur_taxi)) next_taxi) with 
    | None, None => None
    (* should fail if there are multiple segments; TODO consider putting requirements in spec *)
    | Some lst1, Some lst2 => None
    | Some lst1, None => Some lst1
    | None, Some lst2 => Some lst2
  end.
(* test cases *)
(* Example eg_get_seg_1: get_seg CA nA [A3; A3] = Some [BA; A3]. 
Proof. reflexivity. Qed.
Example eg_get_seg_2: get_seg C1 nC nA = Some [CB; CA].
Proof. reflexivity. Qed.
Example eg_get_seg_3: get_seg C1 nC nB = Some [CB].
Proof. reflexivity. Qed.
Example eg_get_seg_4: get_seg CA nC nB = Some [CB].
Proof. reflexivity. Qed. *)

(* the last element of get_seg is on next_taxi *)
Print option.
Lemma get_seg_last_correct : forall (cur_vertex : Vertex) (cur_taxi : V_list) (next_taxi : V_list),
                             (get_seg cur_vertex cur_taxi next_taxi <> None) ->
                             In (last (unwrap (get_seg cur_vertex cur_taxi next_taxi)) (index 0)) next_taxi.
Proof. intros cur_vertex cur_taxi next_taxi.
       intro seg_not_none. btauto.


Fixpoint find_path (cur_vertex : Vertex) (cur_taxiway : V_list) (rest_taxiway_names : list V_list) : option V_list :=
    match rest_taxiway_names with
    | [] => Some []
    | next_taxiway::rest_taxiway =>
      match get_seg cur_vertex cur_taxiway next_taxiway with
        | None => None
        | Some seg => match rev seg with (* rev is to extract the last elem *)
          | [] => None (* Should be unreachable, since a valid seg contains at least a vertex on the next taxiway *)
          | last_vertex::rest => 
            match (find_path last_vertex next_taxiway rest_taxiway) with
            | None => None
            | Some result (* result of the recursive call *) => Some (seg ++ result)
            end
          end
      end
    end.
(* ATC CMD: (start_vertex, end_vertex, taxiway_names). taxiway_names is a subset of every taxiway in the graph *)
Definition find_path_wrapper (start_vertex : Vertex) (end_vertex : Vertex) (taxiway_names : list V_list) : option V_list :=
  match taxiway_names with
  | [] => None
  | fst_taxiway::rest_taxiways =>
    (* create a dummy taxiway in the end *)
    match find_path start_vertex fst_taxiway (rest_taxiways ++ [[end_vertex;end_vertex]]) with
    | None => None
    | Some res => Some (start_vertex::res)
    end   
  end.

Definition first_elem (op_lst : option V_list) : V_list:=
  match op_lst with
  | None => []
  | Some lst =>
    match lst with
    | [] => []
    | s::rest => [s]
    end
  end.


