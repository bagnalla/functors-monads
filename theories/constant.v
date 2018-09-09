Require Import Coq.Program.Basics.
Require Import functor.


(** The constant functor. *)
Instance Fmap_const A : Fmap (const A) := fun _ _ _ => id.

Instance Functor_const A : Functor (const A).
Proof. firstorder. Qed.

Instance Fmap_const' A : Fmap (fun _ => A) := Fmap_const A.
Instance Functor_const' A : Functor (fun _ => A) := Functor_const A.
