Require Import BinInt Orders.
Require Import ExtrHaskellBasic.
Extraction Language Haskell.

Module WeightBalancedTree (X: OrderedType').

Local Open Scope Z_scope.

Inductive Tree : Type :=
  | Empty
  | Node (size: Z) (left: Tree) (value: X.t) (right: Tree)
.

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

Definition singleton x := Node 1 Empty x Empty.
Definition node l x r := Node (1 + size l + size r) l x r.


Definition Delta := 3.
Definition Gamma := 2.

Fixpoint insert tree x :=
  match tree with
  | Empty => singleton x
  | Node _ l y r =>
    match X.compare x y with
    | Eq => tree
    | Lt =>
      if 1 + weight l <=? Delta * weight r
      then node (insert l x) y r
      else match l with
      | Node _ ll ly lr =>
        match X.compare x ly with
        | Eq => tree
        | Lt => 
          if weight lr <=? Gamma * weight ll
          then node (insert ll x) ly (node lr y r)
          else match lr with
          | Node _ lrl lry lrr =>
            node (node (insert ll x) ly lrl) lry (node lrr y r)
          | Empty => (* impossible *) tree
          end
        | Gt =>
          if 1 + weight lr <=? Gamma * weight ll
          then node ll ly (node (insert lr x) y r)
          else match lr with
          | Node _ lrl lry lrr =>
            insert (node (node ll ly lrl) lry (node lrr y r)) x
          | Empty => (* impossible *) tree
          end
        end
      | Empty => (* impossible *) tree
      end
    | Gt =>
      if 1 + weight r <=? weight l
      then node l y (insert r x)
      else match r with
      | Node _ rl ry rr =>
        match X.compare x ry with
        | Eq => tree
        | Lt =>
          if 1 + weight rl <=? Gamma * weight rr
          then node (node l y (insert rl x)) ry rr
          else match rl with
          | Node _ rll rly rlr =>
            insert (node (node l y rll) rly (node rlr ry rr)) x
          | Empty => (* impossible *) tree
          end
        | Gt =>
          if weight rl <=? Gamma * weight rr
          then node (node l y rl) ry (insert rr x)
          else match rl with
          | Node _ rll rly rlr =>
            node (node l y rll) rly (node rlr ry (insert rr x))
          | Empty => (* impossible *) tree
          end
        end
      | Empty => (* impossible *) tree
      end
    end
  end.

Fixpoint member tree x := match tree with
  | Empty => false
  | Node _ l y r => match X.compare x y with
    | Eq => true
    | Lt => member l x
    | Gt => member r x
  end
end.

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