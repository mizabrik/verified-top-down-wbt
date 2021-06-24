Require Import FunInd Recdef MSetInterface MSetGenTree BinInt Int Lia Nat.

Require Import ExtrHaskellBasic.
Extraction Language Haskell.

(* Module Ops (Import I:Int)(X:OrderedType) <: MSetInterface.Ops X. *)
Module Ops (X:OrderedType) <: RawSets X.

(* Use generic BST as a base; implements read-only operations. *)
Include MSetGenTree.Ops X Nat.

Local Open Scope nat_scope.

Definition size (t : tree) := 
   match t with
  | Leaf => 0
  | Node s _ _ _ => s
  end.

Definition node l x r := Node (1 + size l + size r) l x r.
Definition singleton x := node Leaf x Leaf.


Definition weight t := 1 + size t.

Definition Delta := 3.
Definition Gamma := 2.



(* 1 + 1 + 2(1 + 1 + 3 + 5) *)
Function add x t {measure cardinal t} :=
  match t with
  | Leaf => singleton x
  | Node _ l y r =>
    match X.compare x y with
    | Eq => t
    | Lt =>
      if 1 + weight l <=? Delta * weight r
      then node (add x l) y r
      else match l with
      | Node _ ll ly lr =>
        match X.compare x ly with
        | Eq => t
        | Lt => 
          if weight lr <=? Gamma * weight ll
          then node (add x ll) ly (node lr y r)
          else match lr with
          | Node _ lrl lry lrr =>
            node (add x (node ll ly lrl)) lry (node lrr y r)
          | Leaf => (* impossible *) node (add x l) y r
          end
        | Gt =>
          if 1 + weight lr <=? Gamma * weight ll
          then node ll ly (add x (node lr y r))
          else match lr with
          | Node _ lrl lry lrr =>
            match X.compare x lry with
            | Eq => t
            | Lt => node (add x (node ll ly lrl)) lry (node lrr y r)
            | Gt => node (node ll ly lrl) lry (add x (node lrr y r))
            end
          | Leaf => (* impossible *) node (add x l) y r
          end
        end
      | Leaf => (* impossible *) node (add x l) y r
      end
    | Gt =>
      if 1 + weight r <=? Delta * weight l
      then node l y (add x r)
      else match r with
      | Node _ rl ry rr =>
        match X.compare x ry with
        | Eq => t
        | Lt =>
          if 1 + weight rl <=? Gamma * weight rr
          then node (add x (node l y rl)) ry rr
          else match rl with
          | Node _ rll rly rlr =>
            match X.compare x rly with
            | Eq => t
            | Lt => node (add x (node l y rll)) rly (node rlr ry rr)
            | Gt => node (node l y rll) rly (add x (node rlr ry rr))
            end
          | Leaf => (* impossible *) node l y (add x r)
          end
        | Gt =>
          if weight rl <=? Gamma * weight rr
          then node (node l y rl) ry (add x rr)
          else match rl with
          | Node _ rll rly rlr =>
            node (node l y rll) rly (add x (node rlr ry rr))
          | Leaf => (* impossible *) node l y (add x r)
          end
        end
      | Leaf => (* impossible *) node l y (add x r)
      end
    end
  end.
all: intros; simpl; lia. Defined.

Definition remove (x: elt) (t: tree) := Leaf. 

Definition filter (f: elt -> bool) t :=
  fold (fun x t' => if f x then t else remove x t') t t.
Definition partition f t :=
  (filter f t, filter (fun b => negb (f b)) t).


Definition union := fold add.
Definition inter t1 t2 := filter (fun x => mem x t2) t1.
Definition diff := fold remove.

Definition t := tree.
(*End Ops.

Module MakeRaw (Import I:Int)(X:OrderedType) <: RawSets X.
Include Ops I X.*)

Local Close Scope Z_scope.
Include MSetGenTree.Props X Nat.

Lemma singleton_spec : forall x y,
  InT y (singleton x) <-> X.eq y x.
Proof.
  intros. split; intro H.
  - inversion H; auto; inversion H1.
  - constructor; auto.
Qed.

Check add_ind.

Import MX.

  Hint Constructors InT.  Hint Constructors InT.
Lemma gt_tree_l : forall x s l y r,
  gt_tree x (Node s l y r) -> gt_tree x l.
Proof.
  unfold gt_tree. intuition.
Qed.
Lemma gt_tree_r : forall x s l y r,
  gt_tree x (Node s l y r) -> gt_tree x r.
Proof.
  unfold gt_tree. intuition.
Qed.
Hint Resolve gt_tree_l gt_tree_r.

Lemma lt_tree_l : forall x s l y r,
  lt_tree x (Node s l y r) -> lt_tree x l.
Proof.
  unfold lt_tree. intuition.
Qed.
Lemma lt_tree_r : forall x s l y r,
  lt_tree x (Node s l y r) -> lt_tree x r.
Proof.
  unfold lt_tree. intuition.
Qed.
Hint Resolve lt_tree_l lt_tree_r.

Ltac ih_ok := match goal with
  | IH : Ok ?t' -> _ |- _ =>
    let Hok := fresh
    in assert (Hok : Ok t')
           by (inv; unfold node, Ok in *; eauto);
    specialize (IH Hok)
  | _ => idtac
end.

Print HintDb core.

Lemma add_spec : forall t x y `{Ok t},
  InT y (add x t) <-> X.eq y x \/ InT y t.
Proof.
  Hint Constructors bst.
  Local Hint Resolve MX.compare_eq MX.eq_trans.
  intros t x y H.
  functional induction add x t; ih_ok;
  match goal with
  | H : X.compare x ?z = Eq |- _ =>
    intuition; apply MX.compare_eq in H; eauto using MX.eq_trans
  | _ => idtac
  end; [
    rewrite singleton_spec; assert (~InT y Leaf); [
      apply empty_spec | intuition
    ] |
    unfold node in *; intuition_in ..
  ].
Qed.

Lemma leaf_ok : Ok Leaf.
Proof. constructor. Qed.
Hint Resolve leaf_ok.

Lemma lt_tree_node_iff : forall y s l x r,
  lt_tree y (Node s l x r) <->
  lt_tree y l /\ X.lt x y /\ lt_tree y r.
Proof.
  split.
  - intuition; unfold lt_tree in *; eauto. 
  - intuition; auto using lt_tree_node.
Qed.

Lemma gt_tree_node_iff : forall y s l x r,
  gt_tree y (Node s l x r) <->
  gt_tree y l /\ X.lt y x /\ gt_tree y r.
Proof.
  split.
  - intuition; unfold gt_tree in *; eauto. 
  - intuition; auto using gt_tree_node.
Qed.

Print Ok.

(* Local Hint Resolve lt_tree_node_iff gt_tree_node_iff. *)

Local Hint Resolve MX.eq_refl MX.lt_trans.

Instance add_ok t x `(Ok t) : Ok (add x t).
Proof.
  functional induction add x t; ih_ok; intuition.
  all: try solve [
    inv; constructor; intuition;
    (* intuition can not prove Ok Leaf. *) unfold Ok in *; auto;
    unfold lt_tree, gt_tree in *;
    intro; rewrite add_spec; intuition;
    try rewrite MX.compare_lt_iff in *;
    try rewrite MX.compare_gt_iff in *;
    order
  ].

  all:
    inv; unfold node; constructor; eauto;
    match goal with
    | |- context [add _ _] => intro; rewrite add_spec; intuition;
      try rewrite MX.compare_lt_iff in *;
      try rewrite MX.compare_gt_iff in *;
      inv; eapply X.lt_compat; eauto
    | _ => 
      (apply lt_tree_node || apply gt_tree_node); auto;
      (eapply lt_tree_trans || eapply gt_tree_trans); eauto
    end.
Qed.

Inductive sizedTree : tree -> Prop :=
  | SizedLeaf : sizedTree Leaf
  | SizedNode : forall l x r,
                sizedTree l ->
                sizedTree r ->
                sizedTree (Node (1 + size l + size r) l x r)
.

Lemma size_spec : forall tr,
  sizedTree tr -> size tr = cardinal tr.
Proof.
  induction 1 as [| l x r Hl IHl Hr IHr].
  - reflexivity.
  - rewrite IHl, IHr; reflexivity.
Qed.

Lemma singleton_size : forall x, sizedTree (singleton x).
Proof. repeat constructor. Qed.

Local Hint Resolve singleton_size : core.
Local Hint Constructors sizedTree : core.

Ltac size_inversion :=
  match goal with
  | H : sizedTree (Node _ _ _ _) |- _ =>
    clear_inversion H; size_inversion
  | _ => idtac
  end.

Lemma add_sized : forall t x,
  sizedTree t -> sizedTree (add x t).
Proof.
  intros t x H.
  functional induction add x t;
  unfold node in *; size_inversion; auto.
Qed.

Local Close Scope Z_scope.

Local Open Scope nat_scope.
Check  (_ <=? _).
Search nat.

Inductive balanced (coef: nat) : tree -> Prop :=
  | BalancedLeaf : balanced coef Leaf
  | BalancedNode : forall s l x r,
      balanced coef l -> balanced coef r ->
      (1 + cardinal l) <= coef * (1 + cardinal r) ->
      (1 + cardinal r) <= coef * (1 + cardinal l) ->
      balanced coef (Node s l x r)
.

Local Hint Constructors balanced : core.

Lemma singleton_balanced : forall x,
  balanced 3 (singleton x).
Proof. repeat constructor. Qed.

Lemma add_cardinal : forall t x,
  cardinal (add x t) = 1 + cardinal t
  \/ cardinal (add x t) = cardinal t.
Proof.
  intros t x; functional induction add x t;
  try solve [left; reflexivity | right; reflexivity].
  17: { simpl; lia. }
  all:
    destruct IHt0 as [IH | IH]; [left | right];
    simpl; rewrite IH; simpl; lia.
Qed.

Require Import ZArith.

Lemma leaf_is_bounded : forall coef tr,
  (sizedTree tr) -> (coef > 1)%I ->
  I.leb (weight Leaf) (coef * weight tr) = true.
Proof.
  intros.
  assert (eq_1 : weight Leaf = 1%I). {
    unfold weight, size; MI.i2z; reflexivity.
  }
  assert (weight_positive : (i2z (weight tr) > 0)%Z). {
    unfold weight; MI.i2z; rewrite size_spec;
    [ lia | assumption].
  }
  rewrite eq_1.
  unfold weight; MI.i2z; repeat rewrite size_spec.
  rewrite Z.mul_add_distr_l.
  enough (Z.of_nat (cardinal tr) >= 0)%Z.
  - lia.
  - lia.
  - assumption.
Qed.

Lemma delta_is_good : (Delta > 1)%I.
Proof. unfold Delta; MI.i2z; lia. Qed.

Lemma gamma_is_good : (Gamma > 1)%I.
Proof. unfold Gamma; MI.i2z; lia. Qed.

Local Hint Resolve delta_is_good gamma_is_good : core.

Theorem add_balanced : forall t x,
  sizedTree t -> balanced 3 t ->
  balanced 3 (add x t).
Proof.
  intros t x Hsize Hbalance.
  functional induction add x t;
  auto using singleton_balanced.
  1: {
    inversion Hsize; inversion Hbalance.
    unfold node; simple apply BalancedNode;
    [apply IHt0; assumption | assumption | ..].
    + destruct (add_cardinal l x) as [Hin | Hnin].
      * rewrite Hin.
        unfold Delta, weight in *. MI.i2z.
        rewrite (size_spec _ H1) in e1.
        rewrite (size_spec _ H4) in e1.
        lia.
        (* zify. rewrite Zle_is_le_bool. assumption. *)
      * rewrite Hnin; assumption.
    + destruct (add_cardinal l x) as [Hin | Hnin].
      * rewrite Hin; lia.
      * rewrite Hnin; assumption.
  }

  8: {
    rewrite leaf_is_bounded in *; try easy.
    enough (forall tr, I.leb (weight Leaf) (Gamma * weight tr) = true).
    now rewrite H in *.
    specialize (H ll). congruence.
    MI.i2z. unfold weight, Gamma in e4. simpl in e4. lia.
  - 
Qed.

(* END OF MEANINGFUL PART *)

End MakeRaw.

Module WeightBalancedTree (X: OrderedType').


Inductive Tree : Type :=
  | Empty
  | Node (size: Z) (left: Tree) (value: X.t) (right: Tree)
.

Fixpoint cardinal (tree: Tree) : nat :=
  match tree with
  | Empty => 0
  | Node _ l _ r => 1 + size' l + size' r
  end.

Local Open Scope Z_scope.

Definition size (tree: Tree) : Z :=
  match tree with
  | Empty => 0
  | Node s _ _ _ => s
  end.
Definition weight (tree: Tree) : Z :=
  match tree with
  | Empty => 1
  | Node s _ _ _ => 1 + s
  end.

Fixpoint IsOk (t: Tree) : Prop := match t with
  | Empty => True
  | Node s l x r => s = Z.from_nat (size' tree)
                 /\ IsOk l
            

Definition singleton x := Node 1 Empty x Empty.
Definition node l x r := Node (1 + size l + size r) l x r.

Fixpoint member tree x := match tree with
  | Empty => false
  | Node _ l y r => match X.compare x y with
    | Eq => true
    | Lt => member l x
    | Gt => member r x
  end
end.

Inductive In (x: X.t) : Tree -> Prop :=
  | InRoot : forall s l y r, X.eq x y -> In x (Node s l y r)
  | InLeft : forall s l y r, In x l -> In x (Node s l y r)
  | InRight : forall s l y r, In x r -> In x (Node s l y r)
.


(*
Fixpoint deleteMin l x r := match l with
  | Empty => (x, r)
  | Node _ ll y rr =>
    let (min, l') := deleteMin ll y rr in
    (min, maybeRotateL l' x r)
end.

Fixpoint delete tree x := match tree with
  | Empty => Empty
  | Node _ l y r => match X.compare x y with
    | Eq => match l, r with
      | Empty, _ => r
      | _, Empty => l
      | _, Node _ rl z rr =>
        let (y', r') := deleteMin rl z rr in
        maybeRotateR l y' r'
    end
    | Lt => maybeRotateL (delete l x) y r
    | Gt => maybeRotateR l y (delete r x)
  end
end.*)

(* Recursive Extraction size insert. *)

End WeightBalancedTree.

Module ZSet := WeightBalancedTree(Z).

Require Import Bool List String DecimalString.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Search (Z -> string).

Fixpoint inorder t := match t with
  | ZSet.Empty => "()"
  | ZSet.Node _ l x r => fold_left append [
    "("; inorder l; " "; NilZero.string_of_int (Z.to_int x); " "; inorder r; ")"
  ] ""
end.

Definition testMember set := forallb (ZSet.member set).

(*Fixpoint testDelete set xs := match xs with
  | [] => true
  | x :: xs' =>
    let set' := ZSet.delete set x in
    negb (ZSet.member set' x) && testMember set' xs' && testDelete set' xs'
end.*)

Definition test xs :=
  let set := fold_left ZSet.insert xs ZSet.Empty in
  testMember set xs (*&& testDelete set xs*).

Compute test [4;2;42;1;15;22;5;16;48].