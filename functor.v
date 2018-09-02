Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope program_scope.

(** This file contains class definitions for functors and monads with
some basic instances for things like pairs and lists, mostly in
Haskell style (we work only in the category of types, so all functors
are endofunctors). *)

(* In this version, we just assume function extensionality which makes
things WAY simpler since we don't have to deal with equivalence
relations and proper instances and all that.

Anyway, the idea is to formalize composition of functors and the
construction of monads from adjunctions. Then we can, e.g., show that
the state monad is defined by the adjunction of the product and reader
(I think) functors. *)

Notation "f $ x" := (apply f x) (at level 100) : functor_scope.
Open Scope functor_scope.

(** Covariant functors *)
Class Fmap (F : Type -> Type) : Type :=
  fmap : forall {A B}, (A -> B) -> F A -> F B.

Notation "f <$> x" := (fmap f x) (at level 60) : functor_scope.

Class Functor (F : Type -> Type) {fMap : Fmap F} : Prop :=
  { fmap_id : forall A, fmap (@id A) = id
  ; fmap_comp : forall A B C (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f }.


(** Bifunctors (covariant in both arguments)*)
Class Bimap (F : Type -> Type -> Type) : Type :=
  bimap : forall {A B C D}, (A -> C) -> (B -> D) -> F A B -> F C D.

Class Bifunctor (F : Type -> Type -> Type) {biMap : Bimap F} : Prop :=
  { bimap_id : forall A B, bimap (@id A) (@id B) = id
  ; bimap_comp : forall A B C D E H
                   (f : A -> B) (g : D -> E) (h : B -> C) (k : E -> H),
      bimap (h ∘ f) (k ∘ g) = bimap h k ∘ bimap f g }.

(** Map over the first argument of a bifunctor. *)
Definition first {F : Type -> Type -> Type} `{Bifunctor F}
           {A B C} (f : A -> C) :
  F A B -> F C B := bimap f id.

(** Map over the second argument of a bifunctor. *)
Definition second {F : Type -> Type -> Type} `{Bifunctor F}
           {A B C} (g : B -> C) :
  F A B -> F A C := bimap id g.


(** A bifunctor automatically induces a regular functor when the first
    argument is fixed. *)
Instance Fmap_bimap (F : Type -> Type -> Type) `{Bimap F} A
  : Fmap (F A) := fun _ _ => bimap id.

Instance Functor_bifunctor (F : Type -> Type -> Type) `{Bifunctor F} A
  : Functor (F A).
Proof.
  constructor.
  - destruct H as [H _]; apply H.
  - intros B C D f g; destruct H as [_ H].
    unfold fmap, Fmap_bimap.
    assert (Hid: @id A = id ∘ id) by auto.
    rewrite Hid; apply H.
Qed.


(** A similar construction but with the second argument fixed. *)
Instance Fmap_bimap2 (F : Type -> Type -> Type) `{Bimap F} B :
  Fmap (flip F B) := fun _ _ => flip bimap id.

Instance Functor_bifunctor2 (F : Type -> Type -> Type) `{Bifunctor F} B
  : Functor (flip F B).
Proof.
  constructor.
  - intros; destruct H as [H _]; apply H.
  - intros A C D f g; destruct H as [_ H].
    unfold fmap, Fmap_bimap2.
    assert (Hid: @id B = id ∘ id) by auto.
    rewrite Hid; apply H.
Qed.


(** Profunctors (bifunctors which are contravariant in their first
    argument and covariant in the second) *)
Class Dimap (F : Type -> Type -> Type) : Type :=
  dimap : forall {A B C D}, (C -> A) -> (B -> D) -> F A B -> F C D.

Class Profunctor (F : Type -> Type -> Type) {diMap : Dimap F} : Prop :=
  { dimap_id : forall A B, dimap (@id A) (@id B) = id
  ; dimap_comp : forall A B C D E H
                   (f : C -> B) (g : D -> E) (h : B -> A) (k : E -> H),
      dimap (h ∘ f) (k ∘ g) = dimap f k ∘ dimap h g }.

(** Map over the first argument of a profunctor (contravariant). *)
Definition lmap {F : Type -> Type -> Type} `{Profunctor F}
           {A B C} (f : C -> A) :
  F A B -> F C B := dimap f id.

(** Map over the second argument of a profunctor (covariant). *)
Definition rmap {F : Type -> Type -> Type} `{Profunctor F}
           {A B C} (g : B -> C) :
  F A B -> F A C := dimap id g.


(** A profunctor automatically induces a regular functor when the
    first argument is fixed. *)
Instance Fmap_dimap (F : Type -> Type -> Type) `{Dimap F} A
  : Fmap (F A) := fun _ _ => dimap id.

Instance Functor_profunctor (F : Type -> Type -> Type) `{Profunctor F} A
  : Functor (F A).
Proof.
  constructor.
  - destruct H as [H _]; apply H.
  - destruct H as [_ H].
    intros B C D f g.
    unfold fmap, Fmap_dimap.
    assert (Hid: @id A = id ∘ id) by auto.
    rewrite Hid.
    apply H.
Qed.


(** Functor composition *)
Instance Fmap_compose F G `{Fmap F} `{fG : Fmap G} : Fmap (G ∘ F) :=
  fun _ _ => fG _ _ ∘ fmap.

Instance Functor_compose F G `{Functor F} `{Functor G} : Functor (G ∘ F).
Proof.
  constructor.
  - intros ?; unfold fmap, Fmap_compose, compose.
    destruct H as [H _], H0 as [H0 _]; rewrite H, H0; auto.
  - intros A B C f g; destruct H, H0.
    unfold fmap, Fmap_compose, fmap, compose in *.
    rewrite fmap_comp0, fmap_comp1; auto.
Qed.


(** list is a covariant functor. *)
Instance Fmap_list : Fmap list := map.

Instance Functor_list : Functor list.
Proof.
  constructor; unfold fmap, Fmap_list; intros; extensionality l;
    induction l; auto; simpl; rewrite IHl; auto.
Qed.


(** prod is a covariant bifunctor. *)
Instance Bimap_prod : Bimap prod :=
  fun _ _ _ _ f g p => let (x, y) := p in (f x, g y).

Instance Bifunctor_prod : Bifunctor prod.
Proof. constructor; intros; extensionality x; destruct x; auto. Qed.


(** sum is a covariant bifunctor. *)
Instance Bimap_sum : Bimap sum :=
  fun _ _ _ _ f g s =>
    match s with
    | inl x => inl (f x)
    | inr y => inr (g y)
    end.

Instance Bifunctor_sum : Bifunctor sum.
Proof. constructor; intros; extensionality x; destruct x; auto. Qed.


(** option is a covariant functor. *)
Instance Fmap_option : Fmap option :=
  fun _ _ f x => match x with
              | Some y => Some (f y)
              | None   => None
              end.

Instance Functor_option : Functor option.
Proof. constructor; intros; extensionality x; destruct x; auto. Qed.


(** The reader functor is covariant. *)
Definition reader A := fun B => A -> B.

Instance Fmap_reader A : Fmap (reader A) :=
  fun _ _ f g => f ∘ g.

Instance Functor_reader A : Functor (reader A).
Proof. firstorder. Qed.


(** hom profunctor (the bifunctor version of reader). *)
Definition hom := fun A B => A -> B.

Instance Dimap_hom : Dimap hom :=
  fun _ _ _ _ f g h => g ∘ h ∘ f.

Instance Profunctor_hom : Profunctor hom.
Proof. constructor; intros; extensionality x; auto. Qed.


(* The state functor is the composition of the reader and flipped prod
   functor (an adjoint pair).
   state S X = X -> S*X
 *)
Definition state S := reader S ∘ flip prod S.

Instance Fmap_state S : Fmap (state S) :=
  fun _ _ => fmap.

Instance Functor_state S : Functor (state S).
Proof.
  constructor; intros; apply Functor_compose;
    try apply Functor_reader;
    apply Functor_bifunctor2, Bifunctor_prod.
Qed.
