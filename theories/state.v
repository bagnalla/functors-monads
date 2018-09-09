Require Import Coq.Program.Basics.
Require Import functor monad reader.


(** The state functor is the composition of the reader and flipped
    prod functor (an adjoint pair).

    state S X = X -> S*X
*)
Definition state S := reader S ∘ flip prod S.


(** The state monad instance is derived automatically. We state it
    explicitly here so we can easily access proofs about state monads
    by destructing Monad_state. *)
Instance Monad_state S : Monad (state S) := _.


Definition get {S} : state S S := fun s => (s, s).

Definition gets {S A} : (S -> A) -> state S A :=
  (* fun f s => (f s, s). *)
  fun f => get >>= ret ∘ f.
  (* bind get ∘ compose ret. *)

Definition put {S} : S -> state S unit := uncurry const tt.

Definition modify {S} : (S -> S) -> state S unit :=
  (* fun f s => (tt, f s). *)
  fun f => get >>= put ∘ f.
  (* bind get ∘ compose put. *)


Definition runState {S A} (m : state S A) (s : S) : A*S := m s.

Definition evalState {S A} (m : state S A) (s : S) : A := fst (m s).

Definition execState {S A} (m : state S A) (s : S) : S := snd (m s).
