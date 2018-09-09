Require Import Coq.Program.Basics.
Require Import functor identity.

(** Natural transformations. *)

(* It should be the case that any such α is a natural transformation,
   but I'm not sure that it's provable... *)
Definition natural {F G} `{Functor F} `{Functor G}
           (α : forall X, F X -> G X) :=
  forall A B (f : A -> B), fmap f ∘ α A = α B ∘ fmap f.

Record natural_transformation
       (F G : Type -> Type) `{Functor F} `{Functor G} :=
  { nat_app :> forall A, F A -> G A
  ; nat_pf : natural nat_app }.


(** Adjunctions (in terms of unit and counit). *)
(** NOTE: we only support adjunctions between endofunctors since we
    only consider the category of types (or Set if we want to
    pretend). *)

Class AdjunctionUnit (L R : Type -> Type) `{Functor L} `{Functor R}
  : Type :=
  adjUnit : forall A, A -> R (L A).

Class AdjunctionCounit (L R : Type -> Type) `{Functor L} `{Functor R}
  : Type :=
  adjCounit : forall A, L (R A) -> A.


Notation "'η'" := adjUnit : functor_scope.
Notation "'ϵ'" := adjCounit : functor_scope.

(*  fmap η : L A -> L (R (L A))
    ϵ : L (R (L A)) -> L A

    ϵ ∘ fmap η = id

    η : R A -> R (L (R A))
    fmap ϵ : R (L (R A)) -> R A 

    fmap ϵ ∘ η = id
*)

Class Adjunction (L R : Type -> Type) `{Functor L} `{Functor R}
      {u : AdjunctionUnit L R} {c : AdjunctionCounit L R}
  : Prop :=
  { adj_tri1 : forall A, ϵ _ ∘ fmap (η A) = @id (L A)
  ; adj_tri2 : forall A, fmap (ϵ _) ∘ (η (R A)) = @id (R A)
  ; adj_unit_nat : natural (@adjUnit L R _ _ _ _ _)
  ; adj_counit_nat : natural (@adjCounit L R _ _ _ _ _) }.


(** Adjunctions as isomorphisms of hom-sets. *)
Class AdjunctionLeft (L R : Type -> Type) `{Functor L} `{Functor R}
  : Type :=
  adjLeft : forall {A B}, (L A -> B) -> A -> R B.

Class AdjunctionRight (L R : Type -> Type) `{Functor L} `{Functor R}
  : Type :=
  adjRight : forall {A B}, (A -> R B) -> L A -> B.

Definition isomorphic {A B} (f : A -> B) (g : B -> A) :=
  f ∘ g = id /\ g ∘ f = id.

Class AdjunctionIso (L R : Type -> Type) `{Functor L} `{Functor R}
      {l : AdjunctionLeft L R} {r : AdjunctionRight L R} : Prop :=
  { adj_iso : forall A B, isomorphic (l A B) (r A B)
  (* ; adj_left_nat : natural  *) (* TODO? *)
 }.
