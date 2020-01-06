Require Import Coq.Program.Basics.
Require Export functor.
Require Import monad reader.


(** The state functor is the composition of the reader and flipped
    prod functor (an adjoint pair).

    state S X = X -> X*S
*)
Definition state S := reader S ∘ flip prod S.

(* Definition state S X := S -> S*X. *)


(** The state monad. *)

Instance Return_state S : Return (state S) :=
  fun _ => pair.

Instance Join_state S : Join (state S) :=
  (* fun _ f r => let (g, s') := f r in g s'. *)
  fun _ => compose (uncurry apply) ∘ apply.

Instance Jmonad_state S : Jmonad (state S).
Proof.
  constructor; try solve [firstorder].
  - admit.
  - admit.
  - admit.
Admitted.

Instance Monad_state S : Monad (state S) := _.


Definition get {S} : state S S := id △ id.

Definition gets {S A} : (S -> A) -> state S A := bind get ∘ compose ret.

Definition put {S} : S -> state S unit := curry const tt.

Definition modify {S} : (S -> S) -> state S unit := bind get ∘ compose put.

Definition runState {S A} : state S A -> S -> A*S := apply.

Definition evalState {S A} : state S A -> S -> A := compose fst ∘ runState.

Definition execState {S A} : state S A -> S -> S := compose snd ∘ runState.
