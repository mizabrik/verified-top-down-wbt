Require Import Program FunInd Recdef MSetInterface MSetGenTree BinInt Int Lia.

Require Import ExtrHaskellBasic.
Extraction Language Haskell.

(* Module Ops (Import I:Int)(X:OrderedType) <: MSetInterface.Ops X. *)
Module Ops (Import I:Int)(X:OrderedType) <: RawSets X.
Local Open Scope Int_scope.
Local Notation int := I.t.

Inductive rawTree : Type :=
  | Leaf
  | Node (n: int) (left: rawTree) (value: X.t) (right: rawTree)
.

Definition size t := 
   match t with
  | Leaf => 0
  | Node n _ _ _ => n
  end.

Inductive validTree : rawTree -> Prop :=
  | ValidLeaf : validTree Leaf
  | ValidNode : forall l x r,
                validTree l -> validTree r ->
                validTree (Node (1 + size l + size r) l x r)
.

Definition tree := { t | validTree t }.

Module MI := MoreInt(I).

Set Program Mode.

Definition singleton x : tree := Node 1 Leaf x Leaf.
Next Obligation.
  assert (H : 1 = 1 + size Leaf + size Leaf). {
    simpl. MI.i2z. reflexivity.
  }
  rewrite H. repeat constructor.
Defined.

Definition node (l : rawTree | validTree l) (x : X.t) (r : rawTree | validTree r)
  : tree :=
  Node (1 + size l + size r) l x r.
Next Obligation.
  constructor; assumption.
Qed.

Check node.

Definition weight t := 1 + size t.

Definition Delta := 3.
Definition Gamma := 2.

(* Notation "[ e ]" := (exist _ e _ ). *)
Notation "[ e ]" := e.

Fixpoint cardinal t := match t with
  | Leaf => 0%nat
  | Node _ l _ r => (1 + cardinal l + cardinal r)%nat
end.

Print cardinal.


(* 1 + 1 + 2(1 + 1 + 3 + 5) *)
Fixpoint add (x: X.t) (t : rawTree | validTree t) {measure (cardinal t)} : tree :=
  match t with
  | Leaf => singleton x
  | Node _ l y r =>
    match X.compare x y with
    | Eq => exist _ t _
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
          then node ll ly (node (add x lr) y r)
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
      if 1 + weight r <=? weight l
      then node l y (add x r)
      else match r with
      | Node _ rl ry rr =>
        match X.compare x ry with
        | Eq => t
        | Lt =>
          if 1 + weight rl <=? Gamma * weight rr
          then node (node l y (add x rl)) ry rr
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
Next Obligation.
  inversion H; assumption.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  inversion H; assumption.
  intros.
  simpl.
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
Include MSetGenTree.Props X I.

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

Lemma add_spec : forall t x y `{Ok t},
  InT y (add x t) <-> X.eq y x \/ InT y t.
Proof.
  Hint Constructors bst.
  Local Hint Resolve MX.compare_eq MX.eq_trans.
  intros t x y H.
  functional induction add x t;
  match goal with
  | H : X.compare x ?z = Eq |- _ =>
    intuition; apply MX.compare_eq in H; eauto using MX.eq_trans
  | IH : Ok ?t' -> _ |- _ =>
    let Hok := fresh
    in assert (Hok : Ok t')
           by (inv; unfold node, Ok in *; eauto);
    specialize (IH Hok)
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

Instance add_ok t x `(Ok t) : Ok (add x t).
Proof.
  functional induction add x t; intuition.
  all: try solve [
    inv; constructor; intuition;
    (* intuition can not prove Ok Leaf. *) unfold Ok in *; auto;
    unfold lt_tree, gt_tree in *;
    intro; rewrite add_spec; intuition;
    try rewrite MX.compare_lt_iff in *;
    try rewrite MX.compare_gt_iff in *;
    order
  ].
  
  9: {
    inv; constructor; intuition; unfold node; eauto.
    rewrite lt_tree_node_iff in *; intuition.

    match goal with
    | |- ?pred ?r (add x ll) => idtac "ok"
    end.

    unfold lt_tree, gt_tree in *.
    intro; rewrite add_spec; intuition.
    try rewrite MX.compare_lt_iff in *.
    try rewrite MX.compare_gt_iff in *.
    order.
    rewrite 
    (apply lt_tree_node || apply gt_tree_node); auto.
    unfold gt_tree in *.
    intuition. inv. intuition.
    intros. inv. eauto using MX.lt_trans. order.
  }
  8: {
    inv; constructor; intuition. 
    unfold Ok in *. auto.
    unfold lt_tree, gt_tree in *;
    intro; rewrite add_spec; intuition;
    try rewrite MX.compare_lt_iff in *;
    try rewrite MX.compare_gt_iff in *;
    order.

  2: {
    order. add_spec. inv. Print bst.   Hint Constructors bst. auto.

    Print OrderedType.
    Check (Proper (X.eq ==> X.eq ==> iff) X.lt). Print Proper. Print relation.
  - intuition.
  - apply H.
  -  k. t x.
  - intuition.
  - (* EQ *)
    unfold add. unfold add_terminate.
    apply BSNode.
    apply H
  - elim_compare x t3. apply BSNode. intuition. apply BSNode.
 induct t x.
 1: { unfold Ok. apply BSNode.
   1,2: apply BSLeaf.
   all: intros y Hy; inversion Hy.  }
 1: {
 2: { { Print InT. ; discriminate Hy. simpl. auto.
 induct s x; auto; apply bal_ok; auto;
  intros y; rewrite add_spec'; intuition; order.
Qed.


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