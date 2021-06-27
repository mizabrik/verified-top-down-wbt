Require Import FunInd Recdef MSetInterface MSetGenTree BinInt Int Lia.

Require Import ExtrHaskellBasic.
Extraction Language Haskell.

(* Module Ops (Import I:Int)(X:OrderedType) <: MSetInterface.Ops X. *)
Module Ops (Import I:Int)(X:OrderedType) <: RawSets X.
Local Open Scope Int_scope.
Local Notation int := I.t.

(* Use generic BST as a base; implements read-only operations. *)
Include MSetGenTree.Ops X I.

Definition size (t : tree) := 
   match t with
  | Leaf => 0
  | Node s _ _ _ => s
  end.

Definition node l x r := Node (1 + size l + size r) l x r.
Definition singleton x := node Leaf x Leaf.


Definition weight t := 1 + size t.


(* В статьях, описывающих алгоритм, условие баланса записывается
   как alpha <= w(L) / (w(L) + w(R)) <= 1 - alpha; на практике же,
   эффективнее пользоваться эквивалентными неравенствами
     w(L) <= Delta * w(R)),
     w(R) <= Delta * w(L),
   где Delta = (1 - alpha) / alpha. *)

Structure BalanceBound : Set := mkBalanceBound {
  nominator : int;
  denominator : int;
}.

Definition Delta := {|
  nominator := 3;
  denominator := 1;
|}.

(* В ходе балансировки дерева применяются простые и двойные
   вращения; выбор между ними делается в зависимости от того,
   выполняется ли подобное условие баланса с коэффициентом;
   например, для L-поворотов простое вращение выбирается при
     w(LL)/(w(LL) + w(RR)) <= gamma,
   где gamma = 1/(2 - alpha). Аналогичным образом, в реализации
   мы приводим неравенство к виду 
     w(LL) <= Gamma * w(RR),
   где
     Gamma := gamma/(1 - gamma) = 1/(1 - alpha).
   Обращая определение Delta, получим alpha = 1/(1 + Delta),
   и тогда если Delta = n/m, то
     Gamma = (1 + Delta)/Delta = (m + n)/n. *)


Definition Gamma := match Delta with
  {| nominator := n; denominator := m |} =>
    {| nominator := m + n; denominator := n |}
end.

Definition boundedBy c l r := match c with
  {| nominator := n; denominator := m |} =>
    m * l <=? n * r
end.

(* 1 + 1 + 2(1 + 1 + 3 + 5) *)
Function add x t {measure cardinal t} :=
  match t with
  | Leaf => singleton x
  | Node _ l y r =>
    match X.compare x y with
    | Eq => t
    | Lt =>
      if boundedBy Delta (1 + weight l) (weight r)
      then node (add x l) y r
      else match l with
      | Node _ ll ly lr =>
        match X.compare x ly with
        | Eq => t
        | Lt => 
          if boundedBy Gamma (weight lr) (weight ll)
          then node (add x ll) ly (node lr y r)
          else match lr with
          | Node _ lrl lry lrr =>
            node (add x (node ll ly lrl)) lry (node lrr y r)
          | Leaf => (* impossible *) node (add x l) y r
          end
        | Gt =>
          if boundedBy Gamma (1 + weight lr) (weight ll)
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
      if boundedBy Delta (1 + weight r) (weight l)
      then node l y (add x r)
      else match r with
      | Node _ rl ry rr =>
        match X.compare x ry with
        | Eq => t
        | Lt =>
          if boundedBy Gamma (1 + weight rl) (weight rr)
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
          if boundedBy Gamma (weight rl) (weight rr)
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

Module MI := MoreInt(I).

Lemma size_spec : forall tr,
  sizedTree tr -> i2z (size tr) = Z.of_nat (cardinal tr).
Proof.
  induction 1 as [| l x r Hl IHl Hr IHr].
  - simpl; MI.i2z; reflexivity.
  - simpl; MI.i2z; rewrite IHl, IHr. lia.
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

Local Close Scope Int_scope.

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

Lemma cardinal_node : forall s l x r,
  cardinal (Node s l x r) = 1 + cardinal l + cardinal r.
Proof. reflexivity. Qed.

Lemma size_node : forall l x r,
  (size (node l x r) = 1 + size l + size r)%I.
Proof. reflexivity. Qed.

Ltac reflect_boundedBy := lazymatch goal with
  | H : boundedBy _ _ _ = _ |- _ =>
    simpl in H;
    MI.i2z;
    rewrite ?size_spec in H;
    [ reflect_boundedBy | assumption.. ]
  | _ => idtac
end.

Hint Extern 8 => rewrite cardinal_node in * : core.

Ltac rw_add_cardinal := match goal with
  | |- context [cardinal (add ?x ?tr)] =>
    let H := fresh in
    destruct (add_cardinal tr x) as [H | H];
    rewrite H
end.

Hint Extern 9 => rw_add_cardinal : core.

Hint Constructors balanced : core.
Hint Extern 10 => lia : core.

Hint Resolve singleton_balanced : core.

Theorem add_balanced : forall t x,
  sizedTree t -> balanced 3 t ->
  balanced 3 (add x t).
Proof.
  intros t x Hsize Hbalance.
  functional induction add x t;
  unfold weight, node in *;
  invtree sizedTree;
  invtree balanced;
  reflect_boundedBy;
  auto 6.
Qed.