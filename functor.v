Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope program_scope.

(** This file contains class definitions for functors with some basic
    instances for things like pairs and lists, mostly in Haskell style
    (we work only in the category of types, so all functors are
    endofunctors). *)

(* In this version, we just assume function extensionality which makes
   things WAY simpler since we don't have to deal with equivalence
   relations and proper instances and all that. *)


Notation "f $ x" := (apply f x) (at level 100) : functor_scope.
Open Scope functor_scope.

Definition curry {A B C} (f : A -> B -> C) (p : A*B) : C :=
  f (fst p) (snd p).

Definition uncurry {A B C} (f : A*B -> C) (x : A) (y : B) : C :=
  f (x, y).


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

(* I would think that Typeclasses Transparent would do this.. but we
   add these synonym instances so they can be found during
   resolution. *)
Instance Fmap_compose' F G `{Fmap F} `{fG : Fmap G}
  : Fmap (fun X => G (F X)) := Fmap_compose F G.
Instance Functor_compose' F G `{Functor F} `{Functor G}
  : Functor (fun X => G (F X)) := Functor_compose F G.


(** The identity functor. *)
Instance Fmap_id : Fmap id := fun _ _  => id.

Instance Functor_id : Functor id.
Proof. firstorder. Qed.

Instance Fmap_id' : Fmap (fun X => X) := Fmap_id.
Instance Functor_id' : Functor (fun X => X) := Functor_id.


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

Class AdjunctionUnit (L R : Type -> Type) `{Functor L} `{Functor R}
  : Type :=
  adjUnit : forall A, A -> R (L A).

Class AdjunctionCounit (L R : Type -> Type) `{Functor L} `{Functor R}
  : Type :=
  adjCounit : forall A, L (R A) -> A.

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
  { adj_tri1 : forall A, ϵ _ ∘ fmap (adjUnit A) = @id (L A)
  ; adj_tri2 : forall A, fmap (ϵ _) ∘ (adjUnit (R A)) = @id (R A)
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
  (* ; adj_left_nat : natural  *) (* TODO *)
 }.


(** The constant functor. *)
Instance Fmap_const A : Fmap (const A) := fun _ _ _ => id.

Instance Functor_const A : Functor (const A).
Proof. firstorder. Qed.

Instance Fmap_const' A : Fmap (fun _ => A) := Fmap_const A.
Instance Functor_const' A : Functor (fun _ => A) := Functor_const A.


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


(** △ diagonal functor. *)
Definition diag := fun A => prod A A.

Instance Fmap_diag : Fmap diag :=
  fun _ _ f => bimap f f.

Instance Functor_diag : Functor diag.
Proof.
  constructor; intros.
  - apply bimap_id.
  - apply bimap_comp.
Qed.


(* The state functor is the composition of the reader and flipped prod
   functor (an adjoint pair).
   state S X = X -> S*X
 *)
Definition state S := reader S ∘ flip prod S.


(** flip prod is left adjoint to reader.
    I.e., flip prod S  -| reader S
    
    L = flip prod S = (-, S)
    R = reader S = S -> - 

    R ∘ L = reader S ∘ flip prod S = S -> - ∘ (-, S) = S -> (-, S)
    L ∘ R = flip prod S ∘ reader S = (-, S) ∘ S -> - = (S -> -, S)
 *)

Instance AdjunctionUnit_prod_reader S
  : AdjunctionUnit (flip prod S) (reader S) :=
  fun _ => pair.

Instance AdjunctionCounit_prod_reader S
  : AdjunctionCounit (flip prod S) (reader S) :=
  fun _ => curry apply.

Instance Adjunction_prod_reader S
  : Adjunction (flip prod S) (reader S).
Proof.
  constructor; unfold natural; intros; (firstorder;
    extensionality x; destruct x; firstorder).
Qed.
