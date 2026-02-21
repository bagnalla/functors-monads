Require Import Coq.Program.Basics.

Require Export functor.
Require Import monad.

Open Scope program_scope.
Open Scope functor_scope.

(* Class TransReturn (T : (Type -> Type) -> Type -> Type) : Type := *)
(*   transRet :> forall M `{Jmonad M}, Return (T M). *)

(* Class TransJoin (T : (Type -> Type) -> Type -> Type) : Type := *)
(*   transJoin :> forall M `{Jmonad M}, Join (T M). *)

(* Class JmonadLift (T : (Type -> Type) -> Type -> Type) : Type := *)
(*   jmonadLift : forall {M} `{Jmonad M} {A}, M A -> T M A. *)

(* Class JmonadTrans (T : (Type -> Type) -> Type -> Type) *)
(*       {r : TransReturn T} {j : TransJoin T} *)
(*       {l : JmonadLift T} *)
(*   : Prop := *)
(*   { jmonadtrans_left_id : forall M `{Jmonad M} A (m : T M A), μ (ret m) = m *)
(*   ; jmonadtrans_right_id : forall M `{Jmonad M} `{Functor (T M)} A (m : T M A), *)
(*       μ (ret <$> m) = m *)
(*   ; jmonadtrans_assoc : forall M `{Jmonad M} `{Functor (T M)} *)
(*                           A (m : T M (T M (T M A))), *)
(*       μ (μ m) = μ (μ <$> m) *)
(*   ; jmonadtrans_ret_nat : forall M `{Jmonad M} `{Functor (T M)} A B (f : A -> B), *)
(*       @fmap (T M) _ _ _ f ∘ ret = ret ∘ f *)
(*   ; jmonadtrans_bind_nat : forall M `{Jmonad M} `{Functor (T M)} A B (f : A -> B), *)
(*       @fmap (T M) _ _ _ f ∘ μ = μ ∘ fmap (fmap f) *)
(*   ; jmonadtrans_lift_ret : forall M `{Jmonad M} A, jmonadLift ∘ @ret M _ A = ret *)
(*   (* join rule? *) *)
(*   (* ; jmonadtrans_lift_join : forall M `{Jmonad M} A, jmonadLift ∘ @join M _ A = join ∘ jmonadLift *) *)
(*   }. *)

(* Instance JmonadTrans_Jmonad (T : (Type -> Type) -> Type -> Type) *)
(*          `{JmonadTrans T} M `{Jmonad M} `{Functor (T M)} : Jmonad (T M). *)
(* Proof. firstorder. Qed. *)




Class TransReturn (T : (Type -> Type) -> Type -> Type) : Type :=
  transRet :: forall M `{Monad M}, Return (T M).

Class TransBind (T : (Type -> Type) -> Type -> Type) : Type :=
  transBind :: forall M `{Monad M}, Bind (T M).

Class MonadLift (T : (Type -> Type) -> Type -> Type) : Type :=
  monadLift : forall {M} `{Monad M} {A}, M A -> T M A.

Class MonadTrans (T : (Type -> Type) -> Type -> Type)
      {r : TransReturn T} {b : TransBind T}
      {l : MonadLift T}
  : Prop :=
  { monad_left_id : forall M `{Monad M} A B x (f : A -> T M B), ret x >>= f = f x
  ; monad_right_id : forall M `{Monad M} A (m : T M A), m >>= ret = m
  ; monad_assoc :
      forall M `{Monad M} A B C (m : T M A) (f : A -> T M B) (g : B -> T M C),
      (m >>= f) >>= g = m >>= (fun x => f x >>= g)
  ; monadtrans_lift_ret : forall M `{Monad M} A, monadLift ∘ @ret M _ A = ret
  ; monadtrans_lift_bind : forall M `{Monad M} A B (m : M A) (k : A -> M B),
      monadLift (m >>= k) = monadLift m >>= (monadLift ∘ k) }.

Instance Monad_MonadTrans (T : (Type -> Type) -> Type -> Type)
         `{MonadTrans T} M `{Monad M} `{Functor (T M)} : Monad (T M).
Proof. firstorder. Qed.
