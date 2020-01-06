Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.

Open Scope program_scope.


Notation "f $ x" := (apply f x) (at level 100) : functor_scope.
Open Scope functor_scope.

Definition curry {A B C} (f : A*B -> C) (x : A) (y : B) : C :=
  f (x, y).

Definition uncurry {A B C} (f : A -> B -> C) (p : A*B) : C :=
  f (fst p) (snd p).

Definition eval {A B} : (A -> B) * A -> B :=
  uncurry apply.

Definition tuple_fun {A B C} (f : A -> B) (g : A -> C) : A -> B*C :=
  fun x => (f x, g x).

Notation "f △ g" := (tuple_fun f g) (at level 60) : functor_scope.


(** Covariant functors *)
Class Fmap (F : Type -> Type) : Type :=
  fmap : forall {A B}, (A -> B) -> F A -> F B.

Notation "f <$> x" := (fmap f x) (at level 60) : functor_scope.

Class Functor (F : Type -> Type) {fMap : Fmap F} : Prop :=
  { fmap_id : forall A, fmap (@id A) = id
  ; fmap_comp : forall A B C (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f }.


(** Contravariant functors *)
Class Contramap (F : Type -> Type) : Type :=
  contramap : forall {A B}, (A -> B) -> F B -> F A.

Class ContraFunctor (F : Type -> Type) {contraMap : Contramap F} : Prop :=
  { contramap_id : forall A, contramap (@id A) = id
  ; contramap_comp : forall A B C (f : A -> B) (g : B -> C),
      contramap (g ∘ f) = contramap f ∘ contramap g }.


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


(** A profunctor automatically induces a covariant monofunctor when
    the first argument is fixed. *)
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
    rewrite Hid; apply H.
Qed.


(** A profunctor automatically induces a contravariant monofunctor
    when the first argument is fixed. *)
Instance Contramap_dimap (F : Type -> Type -> Type) `{Dimap F} A
  : Contramap (flip F A) := fun _ _ => flip dimap id.

Instance ContraFunctor_profunctor (F : Type -> Type -> Type) `{Profunctor F} A
  : ContraFunctor (flip F A).
Proof.
  constructor.
  - destruct H as [H _]; intros ?; apply H.
  - destruct H as [_ H].
    intros B C D f g.
    unfold contramap, Contramap_dimap.
    assert (Hid: @id A = id ∘ id) by auto.
    rewrite Hid; apply H.
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

(* I would think that Typeclasses Transparent would do this.. but we
   add these synonym instances so they can be found during
   resolution. *)
Instance Fmap_compose' F G `{Fmap F} `{fG : Fmap G}
  : Fmap (fun X => G (F X)) := Fmap_compose F G.
Instance Functor_compose' F G `{Functor F} `{Functor G}
  : Functor (fun X => G (F X)) := Functor_compose F G.


(* TODO: move somewhere *)
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
