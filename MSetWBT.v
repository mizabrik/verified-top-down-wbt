Require Import MiniMSetInterface MiniMSetGenTree.
Require Import FunInd Recdef BinInt Int Lia.

Module Ops (Import I:Int) (X:OrderedType) <: MiniMSetInterface.Ops X.
Include MiniMSetGenTree.Ops X I.

Local Open Scope Int_scope.
Local Notation int := I.t.

(* Use generic BST as a base; implements read-only operations. *)
Definition size (t : tree) := 
   match t with
  | Leaf => 0
  | Node sz _ _ _ => sz
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
Function add x s {measure cardinal s} :=
  match s with
  | Leaf => singleton x
  | Node _ l y r =>
    match X.compare x y with
    | Eq => s
    | Lt =>
      if boundedBy Delta (1 + weight l) (weight r)
      then node (add x l) y r
      else match l with
      | Node _ ll ly lr =>
        match X.compare x ly with
        | Eq => s
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
            | Eq => s
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
        | Eq => s
        | Lt =>
          if boundedBy Gamma (1 + weight rl) (weight rr)
          then node (add x (node l y rl)) ry rr
          else match rl with
          | Node _ rll rly rlr =>
            match X.compare x rly with
            | Eq => s
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

Definition t := tree.

End Ops.


Module MakeRaw (Import I:Int)(X:OrderedType) <: RawSets X.
Include Ops I X.

Include MiniMSetGenTree.Props X I.

Local Hint Constructors bst InT : core.
Local Hint Resolve bst_Ok empty_ok : core.

Lemma singleton_spec : forall x y,
  InT y (singleton x) <-> X.eq y x.
Proof. unfold singleton, node; intuition_in. Qed.

Instance singleton_ok x : Ok (singleton x).
Proof. auto with typeclass_instances. Qed.

Ltac reflect_compare :=
  try rewrite MX.compare_eq_iff in *;
  try rewrite MX.compare_lt_iff in *;
  try rewrite MX.compare_gt_iff in *.

Lemma add_spec' : forall s x y,
  InT y (add x s) <-> X.eq y x \/ InT y s.
Proof.
  intros; functional induction add x s;
  [ rewrite singleton_spec | reflect_compare.. ];
  unfold node in *;
  intuition_in;
  eauto using MX.eq_trans.
Qed.

Lemma add_spec : forall s x y `{Ok s},
  InT y (add x s) <-> X.eq y x \/ InT y s.
Proof. intros; apply add_spec'. Qed.

Local Hint Resolve ok lt_tree_node gt_tree_node : core.

Lemma lt_tree_inv : forall y s l x r,
  lt_tree y (Node s l x r) ->
  lt_tree y l /\ X.lt x y /\ lt_tree y r.
Proof.
  intuition; unfold lt_tree; auto.
Qed.

Lemma gt_tree_inv : forall y s l x r,
  gt_tree y (Node s l x r) ->
  gt_tree y l /\ X.lt y x /\ gt_tree y r.
Proof.
  intuition; unfold gt_tree; auto.
Qed.

Ltac inv_xt_tree := try match goal with
  | H : lt_tree _ (Node _ _ _ _) |- _ =>
    apply lt_tree_inv in H;
    decompose [and] H; clear H;
    inv_xt_tree
  | H : gt_tree _ (Node _ _ _ _) |- _ =>
    apply gt_tree_inv in H;
    decompose [and] H; clear H;
    inv_xt_tree
end.

Ltac xt_tree_add :=
  match goal with
  | |- lt_tree _ (add _ _) => idtac
  | |- gt_tree _ (add _ _) => idtac
  end;
  reflect_compare;
  intro; (* unfolds head *)
  rewrite add_spec;
  [ intros [ | ]; [ | inv ] | ].

Ltac xt_tree_trans := match goal with
  | H1 : X.lt ?y ?x, H2 : lt_tree ?y ?s
    |- lt_tree ?x ?s => apply lt_tree_trans with y
  | H1 : X.lt ?x ?y, H2 : gt_tree ?y ?s
    |- gt_tree ?x ?s => apply gt_tree_trans with y
  end; assumption.

Ltac X_trans := match goal with
  | H1 : X.lt ?x ?y, H2 : X.lt ?y ?z
    |- X.lt ?x ?y =>
    apply MX.lt_trans with z; assumption
end.

Local Hint Extern 5 (X.lt _ _) => order.
Local Hint Extern 5 => xt_tree_add.
Local Hint Extern 6 => xt_tree_trans.


Instance add_ok t x `(Ok t) : Ok (add x t).
Proof.
  functional induction add x t;
  [ apply singleton_ok | constructor.. ];
  unfold node in *;
  inv; inv_xt_tree;
  auto.
Qed.

Lemma remove_spec : forall s x y `{Ok s},
  In y (remove x s) <-> In y s /\ ~X.eq y x. Admitted.
Instance remove_ok s x `(Ok s) : Ok (remove x s). Admitted.

End MakeRaw.


Module BalanceProps (Import I:Int) (X:OrderedType).
Include Ops I X.
Include MiniMSetGenTree.Props X I.

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

Inductive balanced (n m: nat) : tree -> Prop :=
  | BalancedLeaf : balanced n m Leaf
  | BalancedNode : forall s l x r,
      balanced n m l -> balanced n m r ->
      m * (1 + cardinal l) <= n * (1 + cardinal r) ->
      m * (1 + cardinal r) <= n * (1 + cardinal l) ->
      balanced n m (Node s l x r)
.

Local Hint Constructors balanced : core.


Definition i2n i := Z.to_nat (i2z i).

Definition delta_balanced := match Delta with
  | {| nominator := n; denominator := m |}
    => balanced (i2n n) (i2n m)
end.

Lemma singleton_balanced : forall x,
  delta_balanced (singleton x).
Proof.
  repeat constructor;
  unfold i2n; MI.i2z;
  lia.
Qed.

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

Ltac simpl_boundedBy := lazymatch goal with
  | H : boundedBy _ _ _ = _ |- _ =>
    simpl in H;
    MI.i2z;
    rewrite ?size_spec in H;
    [ simpl_boundedBy | assumption.. ]
  | _ => idtac
end.

Ltac rw_add_cardinal := match goal with
  | |- context [cardinal (add ?x ?tr)] =>
    let H := fresh in
    destruct (add_cardinal tr x) as [H | H];
    rewrite H
end.

Local Hint Extern 8 => rewrite cardinal_node in * : core.
Local Hint Extern 9 => rw_add_cardinal : core.
Local Hint Constructors balanced : core.
Local Hint Extern 10 => lia : core.

Local Hint Resolve singleton_balanced : core.

Theorem add_balanced : forall t x,
  sizedTree t -> delta_balanced t ->
  delta_balanced (add x t).
Proof.
  intros t x Hsize Hbalance.
  functional induction add x t;
  try apply singleton_balanced;
  unfold weight, node in *;
  unfold delta_balanced, Delta, i2n in *;
  invtree balanced;
  invtree sizedTree;
  simpl_boundedBy;
  auto 6.
Qed.

End BalanceProps.