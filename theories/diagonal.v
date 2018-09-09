Require Import functor prod.


(** △ diagonal functor. *)
Definition diag := fun A => prod A A.

Instance Fmap_diag : Fmap diag :=
  fun _ _ f => bimap f f.

Instance Functor_diag : Functor diag.
Proof.
  constructor; intros.
  - apply bimap_id.
  - apply bimap_comp.
Qed.
