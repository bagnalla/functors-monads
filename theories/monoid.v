Require Import Coq.Program.Basics.

Open Scope program_scope.


(** A binary "multiplication" operation. *)
Class Mappend (A : Type) : Type :=
  mappend : A -> A -> A.

Notation "f ⊗ x" := (mappend f x) (at level 65, left associativity)
                    : monoid_scope.
Open Scope monoid_scope.

(** A semigroup just has an associative binary operation. *)
Class Semigroup (A : Type) `{Mappend A} : Prop :=
  { mappend_assoc : forall x y z, (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z) }.

(** A distinguished element of A. *)
Class Mempty (A : Type) : Type :=
  mempty : A.

(** A monoid is a semigroup in addition to a distinguished element
    which is the left and right unit of the multiplicaton operator. *)
Class Monoid (A : Type) `{Semigroup A} `{Mempty A} : Prop :=
  { mempty_left : forall x, mempty ⊗ x = x
  ; mempty_right : forall x, x ⊗ mempty = x }.


(** Example instances for nat. *)
Require Import NArith.
Instance Mappend_nat : Mappend nat := Nat.add.
Instance Semigroup_nat : Semigroup nat.
Proof. firstorder. Qed.
Instance Mempty_nat : Mempty nat := O.
Instance Monoid_nat : Monoid nat.
Proof. firstorder. Qed.
