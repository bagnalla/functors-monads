Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Import adjunction functor monad prod.


(** The reader functor is covariant. *)
Definition reader R := fun A => R -> A.

Instance Fmap_reader R : Fmap (reader R) :=
  fun _ _ f g => f ∘ g.

Instance Functor_reader R : Functor (reader R).
Proof. firstorder. Qed.


(** The reader monad. *)

Instance Return_reader R : Return (reader R) :=
  fun _ => const.

Instance Join_reader R : Join (reader R) :=
  fun _ f r => f r r.

(*
  reader R (reader R A) -> reader R A

  (R -> R -> A) -> R -> A
*)

Instance Jmonad_reader R : Jmonad (reader R).
Proof. constructor; firstorder. Qed.


(** flip prod is left adjoint to reader.
    I.e., flip prod S -| reader S
    
    L = flip prod S = (-, S)
    R = reader S = S -> - 

    R ∘ L = reader S ∘ flip prod S = S -> - ∘ (-, S) = S -> (-, S)
    L ∘ R = flip prod S ∘ reader S = (-, S) ∘ S -> - = (S -> -, S)
 *)

Instance AdjunctionUnit_prod_reader S
  : AdjunctionUnit (flip prod S) (reader S) :=
  fun _ => pair.

Instance AdjunctionCounit_prod_reader S
  : AdjunctionCounit (flip prod S) (reader S) :=
  fun _ => curry apply.

Instance Adjunction_prod_reader S
  : Adjunction (flip prod S) (reader S).
Proof.
  constructor; unfold natural; intros; (firstorder;
    extensionality x; destruct x; firstorder).
Qed.
