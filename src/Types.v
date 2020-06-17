(*
    We define the type encodings of the algorithm in this file.
    We use naming conventions of (vertex, edge) for undirected graph and (node, arc) for directed graph
    In the algorithm, we don't use term undirected or directed because they might cause confusion. Instead, we use
        - "naive" for undirected
        - "complete" for directed 
    The term complete is because the directed expanded map is what contains full information.
*)


From mathcomp Require Import all_ssreflect.
(* 
    The order is important, mathcomp also implements List,
        hence we need to cover the definition.
    We're using the notation ".1", ".2" in the mathcomp 
*)

Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Relation_Definitions Setoid.
Require Import Relations.
Require Import Compare_dec.
Require Import ArithRing. 
Require Import Omega.
Require Import Coq.Program.Tactics.

From Hammer Require Import Hammer.

(* ========== Naive (undirected) Graph ========== *)

(* 
    a vertex in the (undirected) graph. 
    index maps a nat to a Vertex
*)
Inductive Vertex : Type := | index (i : nat).

(*
    compare if two vertexs are equal
*)
Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
    match v1, v2 with
    index n1, index n2 => Nat.eqb n1 n2
    end.
Notation "a =v= b" := (eqv a b)  (at level 70).
Notation "a >v< b" := (~~(eqv a b)) (at level 70).

Eval compute in ((index 1) >v< (index 2)).
(* configure Hintdb *)
Create HintDb VertexBase.
Hint Resolve beq_nat_refl: VertexBase.

Lemma eqv_eq :
  forall v1 v2,(v1 =v= v2) <-> (v1 = v2). 
Proof. intros. split. 
    - intros. unfold eqv in H. destruct v1 as [n1]. destruct v2 as [n2]. 
    apply (Nat.eqb_eq n1 n2) in H. rewrite H. reflexivity.
    - intros. rewrite -> H. induction v2. simpl. auto with VertexBase. 
Qed.

Definition dec_Vertex_Type : forall (a b : Vertex), {a = b} + {a <> b}.
Proof. intros. destruct (eqv a b) eqn : H.
    - left. hammer.
    - right. hammer.
Defined.

(* Definition eq_n (n1 : Node_type) (n2 : Node_type) : bool :=
    (eqv n1.1 n2.1) && (eqv n1.2 n2.2).

Lemma eqn_eq : 
    forall n1 n2, (eq_n n1 n2 = true) <-> (n1=n2).
Proof. intros. split.
    - intros. unfold eq_n in H. hammer.
    - hammer.
Qed. *)

Lemma eqv_inv:
    forall v1 v2, (v1 >v< v2) <-> (v1 <> v2).
Proof. intros. split.
    - intros. hammer.
    - intros. assert ((v1 = v2 -> v1 =v= v2) -> (v1 <> v2 -> v1 >v< v2)). intros. hammer. auto.  
Qed.


Lemma eqv_rewrite_1:
    forall v1 v2, (v1 =v= v2) -> (v1 =v= v2) = true.
Proof. eauto. Qed.

Lemma eqv_rewrite_2:
    forall v1 v2, (v1 >v< v2) -> (v1 =v= v2) = false.
Proof. intros. hammer. Qed.

Hint Rewrite -> eqv_rewrite_1 : VertexBase.
Hint Rewrite -> eqv_rewrite_2 : VertexBase.

Lemma eqv_refl: reflexive Vertex eqv.
Proof. unfold reflexive. intros. apply eqv_eq. reflexivity. Qed.

Lemma eqv_sym: symmetric Vertex eqv.
Proof. unfold symmetric. intros. hammer. Qed.

Lemma eqv_trans: transitive Vertex eqv.
Proof. unfold transitive. intros. hammer. Qed.


(* Vertex is a setoid with relation eqv *)
(* Theorem Vertexoid: Setoid_Theory _ eqv.
split. exact eqv_refl. exact eqv_sym. exact eqv_trans. Qed. *)

(* By this relation, we can use equal of vertex like "=" *)
Add Parametric Relation : Vertex eqv
  reflexivity proved by eqv_refl
  symmetry proved by (eqv_sym )
  transitivity proved by (eqv_trans )
  as eq_vertex_rel.


(* Add Setoid Vertex eqv Vertexoid as Vertoid. *)

Example test1: forall a, a=v=a.
Proof. intros. reflexivity. Qed.


Example test2: forall (a b c: Vertex), a=v=b /\ b=v=c -> c=v=a.
Proof. intros.
 destruct H. 
transitivity b.
-easy. (* easy will try symmetry, refl etc *)
-easy.
Qed.


(* 
    Taxiway_type is a string of the taxiway name
*)
Definition Taxiway_type : Type := string.

(*
    an edge in the undirected graph
    meaning = (one vertex, another vertex, taiwayname)
*)
Definition Edge_type : Type := ((Vertex * Vertex) * Taxiway_type).

(*  
    a graph is the naive graph,
        in the form of a list of undirected edges, not necessarily ordered
*)
Definition N_Graph_type : Type := list Edge_type.

(* ========== Complete (directed) Graph ========== *)

(* 
    a node in the complete (directed) graph. 
    meaning = (current_vertex, previous_vertex) 
*)
Definition Node_type : Type :=   (Vertex  *  Vertex).

(* 
    a directed edge in the complete (directed) graph.
    meaning = ((start node, end node), the taxiway name of the edge)
*)
Definition Arc_type : Type := (Node_type * Node_type) * Taxiway_type.

(*  
    a graph is the complete graph,
        in the form of a list of edges, not necessarily ordered
*)
Definition C_Graph_type : Type := list Arc_type.


(* 
    a state is a packed information of the result after some steps
    the consturctor State takes four arguments to construct a State_type
    meaning = 
        cur_path,           (the path to current node in reverse order)
        atc_h,              (the taxiway name we're currently on)
        atc_t,              (the rest ATC commands we need to go through)
        atc_used.           (the ATC commands have gone through)
    
    Here we have an invarient that
        Input ATC = (rev atc_used) ++ [atc_f] ++ atc_t 
*)
Inductive State_type : Type :=
    | State :  (list Arc_type) -> string -> (list string) -> (list string) -> State_type.

(*
    For easier use, we introduce a set of notation to access component in State_type
    "s @n" means the n-th component in the State_type 
*)
Definition s_1 (s : State_type) : (list Arc_type) := match s with | State cur_path _ _ _ => cur_path end.
Definition s_2 (s : State_type) : string := match s with | State _ atc_h _ _ => atc_h end.
Definition s_3 (s : State_type) : (list string) := match s with | State _ _ atc_t _ => atc_t end.
Definition s_4 (s : State_type) : (list string) := match s with | State _ _ _ atc_used => atc_used end.
Notation "S @1" := (s_1 S) (at level 1, no associativity).
Notation "S @2" := (s_2 S) (at level 1, no associativity).
Notation "S @3" := (s_3 S) (at level 1, no associativity).
Notation "S @4" := (s_4 S) (at level 1, no associativity).

(*
    A lemma for the notation
*)
Lemma s_notation_sound : forall (s : State_type),
    s = State s@1 s@2 s@3 s@4.
Proof. intro s. destruct s as [s1 s2 s3 s4] eqn:H. reflexivity. Qed.


(* a short example for State_type*)
(* 
Example eg_state : State_type := State [] "2" ["3"; "4"] ["1"].
Eval compute in  (eg_state@1, eg_state@2, eg_state@3, eg_state@4). 
*)


(* 
    hardcoded input vertex. if a vertex is start_vertex in the naive graph, 
    we encode input Node in the complete graph to be ((start_vertex, input), (start_vertex, input)), a self looping arc
    input is a placeholder to form a valid structure
*)
Example input : Vertex := index 0.