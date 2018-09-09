Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Import functor.


(** hom profunctor (the bifunctor version of reader). *)
Definition hom := fun A B => A -> B.

Instance Dimap_hom : Dimap hom :=
  fun _ _ _ _ f g h => g ∘ h ∘ f.

Instance Profunctor_hom : Profunctor hom.
Proof. constructor; intros; extensionality x; auto. Qed.
