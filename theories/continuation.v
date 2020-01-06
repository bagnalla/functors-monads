Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Export functor.
Require Import monad.

Definition cont R A := (A -> R) -> R.

Instance Fmap_cont R : Fmap (cont R) :=
  fun _ _ f m k => m (k ∘ f).

Instance Functor_cont R : Functor (cont R).
Proof. firstorder. Qed.

Instance Return_cont R : Return (cont R) :=
  fun _ => flip apply.

Instance Join_cont R : Join (cont R) :=
  fun _ m r => m (flip apply r).

Instance Jmonad_cont R : Jmonad (cont R).
Proof. firstorder. Qed.
