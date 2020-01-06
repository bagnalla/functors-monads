Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Export functor.
Require Import monad.

Inductive tree A : Type :=
| Leaf : A -> tree A
| Split : tree A -> tree A -> tree A.
(* | Fail : tree A. *)

Fixpoint tree_fmap (A B : Type) (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf _ x => Leaf _ (f x)
  | Split _ t1 t2 => Split _ (tree_fmap _ _ f t1) (tree_fmap _ _ f t2)
  (* | Fail _ => Fail _ *)
  end.

(** tree is a covariant functor. *)
Instance Fmap_tree : Fmap tree := tree_fmap.

Instance Functor_tree : Functor tree.
Proof.
  constructor.
  - intro A; unfold fmap, Fmap_tree.
    apply functional_extensionality; intro t.
    induction t; auto.
    simpl; rewrite IHt1, IHt2; auto.
  - intros A B C f g.
    apply functional_extensionality; intro t.
    unfold fmap, Fmap_tree.
    induction t; auto.
    simpl; rewrite IHt1, IHt2; auto.
Qed.

(** tree is a Jmonad. *)
Instance Return_tree : Return tree := Leaf.

Fixpoint tree_join (A : Type) (t : tree (tree A)) : tree A :=
  match t with
  | Leaf _ t' => t'
  | Split _ t1 t2 => Split _ (tree_join _ t1) (tree_join _ t2)
  (* | Fail _ => Fail _ *)
  end.

Instance Join_tree : Join tree := tree_join.

Instance Jmonad_tree : Jmonad tree.
Proof.
  constructor; auto.
  - unfold fmap, Fmap_tree, join, Join_tree.
    intros A t. induction t; auto; simpl.
    rewrite IHt1, IHt2; reflexivity.
  - unfold fmap, Fmap_tree, join, Join_tree.
    intros A t. induction t; auto; simpl.
    rewrite IHt1, IHt2; reflexivity.
  - intros A B f.
    apply functional_extensionality; intro t.
    unfold fmap, Fmap_tree, join, Join_tree, compose.
    induction t; auto; simpl.
    rewrite IHt1, IHt2; reflexivity.
Qed.
