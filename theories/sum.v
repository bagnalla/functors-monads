Require Import FunctionalExtensionality.
Require Import functor monad.


(** sum is a covariant bifunctor. *)
Instance Bimap_sum : Bimap sum :=
  fun _ _ _ _ f g s =>
    match s with
    | inl x => inl (f x)
    | inr y => inr (g y)
    end.

Instance Bifunctor_sum : Bifunctor sum.
Proof. constructor; intros; extensionality x; destruct x; auto. Qed.


(** sum is a Jmonad. *)
Instance Return_sum A : Return (sum A) :=
  fun _ => inr.

Instance Join_sum A : Join (sum A) :=
  fun _ s => match s with
          | inl x => inl x
          | inr y => y
          end.

Instance Jmonad_sum A : Jmonad (sum A).
Proof.
  constructor; firstorder; try destruct m; auto.
  extensionality x. destruct x; auto.
Qed.
