Require Import BinInt Orders.

Require Import FunInd ZArith Recdef Lia.

Require Bool.

Module WeightBalancedTree (X: OrderedType').


Inductive Tree : Type :=
  | Empty
  | Node (size: Z) (left: Tree) (value: X.t) (right: Tree).

Check X.t -> Prop.

(* inductive? *)
Parameter mem : X.t -> Tree -> Prop.

Notation "v \in t" := (mem v t) (at level 60, no associativity).

Import Bool.

(* must be decidable --- the search function essentially *)
(* think about optimizing it, say, like in (Okasaki, Exc. 2.2) or
 via 3-valued comparison *)
Parameter mem_b : X.t -> Tree -> bool.

Notation "v \in? t" := (mem_b v t) (at level 60, no associativity).

(* purely cosmetical *)
Coercion is_true: bool >-> Sortclass.

Lemma mem_spec' : forall v t, v \in t <-> v \in? t.
Admitted.

Lemma mem_spec : forall v t, reflect (v \in t) (v \in? t).
Admitted.

(* Having both inductive and boolean versions of your decidable
   predicates is VERY helpful in proofs. Of course, just
   the Boolean versions are REQUIRED (as you're verifying ALGOS). *)

Parameter isBST : Tree -> Prop.
Parameter isBST_b : Tree -> bool.

Lemma isBST_spec : forall t, reflect (isBST t) (isBST_b t).
Admitted.

Parameter isBalanced : Tree -> Prop.
Parameter isBalanced_b : Tree -> bool.

Lemma isBalanced_spec : forall t, reflect (isBalanced t) (isBalanced_b t).
Admitted.

Parameter insert : X.t -> Tree -> Tree.

Definition insert_spec := forall v t, let t' := insert v t in
 (isBST t /\ isBalanced t -> isBST t' /\ isBalanced t') /\
  v \in t' /\ forall u, (u <> v -> (u \in t <-> u \in t')).

Theorem insert_is_sound : insert_spec.
Admitted.

Parameter delete : X.t -> Tree -> Tree.

Definition delete_spec := forall v t, let t' := delete v t in
 (isBST t /\ isBalanced t -> isBST t' /\ isBalanced t') /\
  ~v \in t' /\ forall u, (u <> v -> (u \in t <-> u \in t')).

Theorem delete_is_sound : delete_spec.
Admitted.


(* If you have these done, you may want to add more things like
   flattening a tree to a list, searching for min/max (this might
   be need earlier as an intermediate step, though), etc. *)


