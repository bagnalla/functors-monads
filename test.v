Require Import monad state.


(* Definition TestM A := state nat A. *)
(* Hmm.. it doesn't resolve the instance properly when we use a type
synonym like this. *)


Definition test : state nat bool :=
  ret tt >> put 123 >> get >>=
      fun s => if Nat.even s then ret true else ret false.

Definition test' : state nat bool :=
  put 123 >> get >>=
      fun s => if Nat.even s then ret true else ret false.

Lemma test_test'_eq : test = test'.
Proof.
  unfold test, test'.
  destruct (Monad_state nat).
  rewrite monad_left_id; auto.
Qed.

Definition result := fst (runState test 0).
Eval compute in result.


Definition add1 : state nat unit :=
  modify (fun n => n + 1).

Definition add1_test : state nat nat :=
  add1 >> get.

Definition add1_result := fst (runState add1_test 0).
Eval compute in add1_result.

Lemma add1_test_spec n :
  evalState add1_test n = S n.
Proof.
  unfold evalState; simpl.
  rewrite PeanoNat.Nat.add_comm; auto.
Qed.

Definition addn : nat -> state nat unit :=
  fun n => modify (fun m => m + n).

Lemma addn_spec n m :
  execState (addn m) n = n + m.
Proof. firstorder. Qed.
