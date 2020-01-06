Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Export functor.
Require Import monad monadtransformer prod.


(** The reader functor is covariant. *)
Definition reader R := fun A => R -> A.

Instance Fmap_reader R : Fmap (reader R) :=
  fun _ _ f g => f ∘ g.

Instance Functor_reader R : Functor (reader R).
Proof. firstorder. Qed.


(** The reader monad. *)

Instance Return_reader R : Return (reader R) :=
  fun _ => const.

(*
  reader R (reader R A) -> reader R A

  (R -> R -> A) -> R -> A
*)

Instance Join_reader R : Join (reader R) :=
  fun _ f r => f r r.

Instance Jmonad_reader R : Jmonad (reader R).
Proof. constructor; firstorder. Qed.


Definition ask {R} : reader R R := id.

Definition asks {R A} : (R -> A) -> reader R A := compose ask.

Definition local {R A} : (R -> R) -> reader R A -> reader R A :=
  flip compose.

Definition runReader {R A} : reader R A -> R -> A := apply.

Definition mapReader {R A B} : (A -> B) -> reader R A -> reader R B :=
  compose.

Definition withReader {R R' A} : (R' -> R) -> reader R A -> reader R' A :=
  flip compose.


(** reader monad transformer. *)
Definition readerT R (T : Type -> Type) : Type -> Type := reader R ∘ T.

(* Instance Fmap_readerT R (T : Type -> Type) `{Fmap T} : Fmap (readerT R T) := *)
(*   fun _ _ f g r => fmap f (g r). *)

(* Instance Functor_readerT R (T : Type -> Type) `{Functor T} *)
(*   : Functor (readerT R T). *)
(* Proof. *)
(*   constructor. *)
(*   - intros A; unfold fmap, Fmap_readerT, fmap. *)
(*     destruct H; rewrite fmap_id; auto. *)
(*   - intros A B C f g. destruct H. *)
(*     unfold fmap, Fmap_readerT, fmap, compose. *)
(*     unfold compose in fmap_comp. *)
(*     (* TODO: is this possible without funext? *) *)
(*     extensionality x. extensionality r. *)
(*     rewrite fmap_comp; auto. *)
(* Qed. *)

Instance TransReturn_readerT R : TransReturn (readerT R) :=
  fun M _ _ _ _ _ _ x => const (ret x).

Instance TransBind_readerT R : TransBind (readerT R) :=
  fun M _ _ _ _ _ _ _ m f r => m r >>= fun x => f x r.

