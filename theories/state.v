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


Definition get {S} : state S S := tuple_fun id id.

Definition gets {S A} : (S -> A) -> state S A := bind get ∘ compose ret.

Definition put {S} : S -> state S unit := curry const tt.

Definition modify {S} : (S -> S) -> state S unit := bind get ∘ compose put.

Definition runState {S A} : state S A -> S -> A*S := apply.

Definition evalState {S A} : state S A -> S -> A := compose fst ∘ runState.

Definition execState {S A} : state S A -> S -> S := compose snd ∘ runState.
