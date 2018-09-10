Require Import functor.


(** The identity functor. *)
Instance Fmap_id : Fmap id := fun _ _ => id.

Instance Functor_id : Functor id.
Proof. firstorder. Qed.

Instance Fmap_id' : Fmap (fun X => X) := Fmap_id.
Instance Functor_id' : Functor (fun X => X) := Functor_id.


(** The identity monad is defined at the bottom of monad.v because of
dependency order (the definition of adjunctions uses the identity
functor). *)
