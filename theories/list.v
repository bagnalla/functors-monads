Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Import List.
Require Export functor.
Require Import monad monoid.

(** list is a covariant functor. *)
Instance Fmap_list : Fmap list := map.

Instance Functor_list : Functor list.
Proof.
  constructor; unfold fmap, Fmap_list; intros; extensionality l;
    induction l; auto; simpl; rewrite IHl; auto.
Qed.


(** list is a Jmonad. *)
Instance Return_list : Return list := fun _ x => x :: nil.

Instance Join_list : Join list := concat.

Instance Jmonad_list : Jmonad list.
Proof.
  constructor.
  - apply app_nil_r.
  - unfold fmap, Fmap_list, join, Join_list.
    intros ? l; induction l; auto; simpl; rewrite IHl; auto.
  - intros A l. induction l; auto.
    unfold join, Join_list in *. simpl.
    unfold fmap, Fmap_list in *.
    rewrite <- IHl.
    apply concat_app.
  - firstorder.
  - intros A B f.
    unfold fmap, Fmap_list, join, Join_list, compose; simpl.
    extensionality l; induction l; simpl; auto.
    rewrite <- IHl, map_app; auto.
Qed.


Instance Mappend_list A : Mappend (list A) := @app _.

Instance Semigroup_list A : Semigroup (list A).
Proof. constructor; apply app_assoc_reverse. Qed.


Instance Mempty_list A : Mempty (list A) := nil.

Instance Monoid_list A : Monoid (list A).
Proof. constructor; auto; apply app_nil_r. Qed.
