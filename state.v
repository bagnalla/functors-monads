Require Import Coq.Program.Basics.
Require Import functor monad.


(** The state functor is the composition of the reader and flipped
    prod functor (an adjoint pair).

    state S X = X -> S*X
*)
Definition state S := reader S ∘ flip prod S.


(** The state monad from adjunctions (we never explicitly define the
    state monad instance -- it is derived from the adjunction of the
    reader and product functors :D). *)
Definition get {S} : state S S := fun s => (s, s).

Definition put {S} : S -> state S unit := uncurry const tt.

Definition runState {S A} (m : state S A) (s : S) : A*S := m s.

Definition TestM A := state nat A.
(* Hmm.. it doesn't resolve the instance properly when we use a type
synonym like this. *)

(* Definition test : TestM bool := *)
Definition test : state nat bool :=
  ret false >> get >>= fun s => if Nat.even s then ret true else ret false.

Definition result := fst (runState test 0).

Eval compute in result.
