Require Import FunctionalExtensionality.
Require Import functor.


(** prod is a covariant bifunctor. *)
Instance Bimap_prod : Bimap prod :=
  fun _ _ _ _ f g p => let (x, y) := p in (f x, g y).

Instance Bifunctor_prod : Bifunctor prod.
Proof. constructor; intros; extensionality x; destruct x; auto. Qed.
