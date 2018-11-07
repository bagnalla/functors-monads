Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Import functor monad monoid prod.


(** We can't define a monad instance for prod in general, but we can
    if the first type argument is a monoid. This is called the writer
    monad. *)

(** writer is a synonym for prod *)
Definition writer W A := prod W A.

Instance Return_writer W `{Monoid W} : Return (writer W) :=
  fun _ => pair mempty.

(* 
  writer W (writer W A) -> writer W A

  W*(W*A) -> W*A
*)

(** We technically only need semigroup here since join doesn't need
    mempty, but it doesn't really matter.  *)
Instance Join_writer W `{Semigroup W} : Join (writer W) :=
  fun _ x => (fst x ⊗ fst (snd x), snd (snd x)).

Instance Jmonad_writer W `{Monoid W} : Jmonad (writer W).
Proof.
  constructor.
  - intros A []; unfold join, Join_writer; simpl;
      destruct H2; rewrite mempty_left; auto.
  - intros A []; unfold join, Join_writer; simpl;
      destruct H2; rewrite mempty_right; auto.
  - intros A [? [? []]]; unfold join, Join_writer; simpl;
      destruct H0; rewrite mappend_assoc; auto.
  - firstorder.
  - intros A B f; extensionality w; destruct w as [? []];
      firstorder.
Qed.


Definition tell {W} : W -> writer W unit := flip pair tt.

Definition listen {W A} : writer W A -> writer W (A*W) :=
  fst △ swap.

Definition pass {W A} : writer W (A * (W -> W)) -> writer W A :=
  eval ∘ ((snd ∘ snd) △ fst) △ fst ∘ snd.

Definition listens {W A B} : (W -> B) -> writer W A -> writer W (A*B) :=
  tuple_fun fst ∘ tuple_fun snd ∘ flip compose fst.

Definition censor {W A} : (W -> W) -> writer W A -> writer W A :=
  flip bimap id.

Definition runWriter {W A} : writer W A -> W*A := id.

Definition execWriter {W A} : writer W A -> W := fst.

Definition mapWriter {W W' A B}
  : (A*W -> B*W') -> writer W A -> writer W' B :=
  compose swap ∘ flip compose swap.
