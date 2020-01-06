Require Import FunctionalExtensionality.
Require Export functor.


(** prod is a covariant bifunctor. *)
Instance Bimap_prod : Bimap prod :=
  fun _ _ _ _ f g p => let (x, y) := p in (f x, g y).

Instance Bifunctor_prod : Bifunctor prod.
Proof. constructor; intros; extensionality x; destruct x; auto. Qed.

Definition swap {A B} : prod A B -> prod B A :=
  fun p => (snd p, fst p).
