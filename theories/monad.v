Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import adjunction functor identity monoid.

Open Scope program_scope.
Open Scope functor_scope.


(** Monads (return and bind). *)
Class Return (T : Type -> Type) : Type :=
  ret : forall {A}, A -> T A.

Class Bind (T : Type -> Type) : Type :=
  bind : forall {A B}, T A -> (A -> T B) -> T B.

Notation "f =<< g" := (bind g f) (at level 60) : monad_scope.
Notation "f << g" := (bind g (fun _ => f)) (at level 60) : monad_scope.
Notation "f >>= g" := (bind f g) (at level 60) : monad_scope.
Notation "f >> g" := (bind f (fun _ => g)) (at level 60) : monad_scope.

Notation "x <-- f ; m" := (bind f (fun x => m)) 
  (at level 100, right associativity, only parsing) : monad_scope.
Notation "f ;; m" := (bind f (fun _ => m)) 
  (at level 100, right associativity, only parsing) : monad_scope.

Open Scope monad_scope.

Class Monad (T : Type -> Type) `{Functor T} {r : Return T} {b : Bind T}
  : Prop :=
  { monad_left_id : forall A B x (f : A -> T B), ret x >>= f = f x
  ; monad_right_id : forall A (m : T A), m >>= ret = m
  ; monad_assoc : forall A B C (m : T A) (f : A -> T B) (g : B -> T C),
      (m >>= f) >>= g = m >>= (fun x => f x >>= g)
}.

(** Composition of kleisli arrows. *)
Definition kleisli_comp {T : Type -> Type} `{Monad T} {A B C}
  : (A -> T B) -> (B -> T C) -> A -> T C :=
  fun f g x => f x >>= g.

Notation "f >=> g" := (kleisli_comp f g) (at level 60) : monad_scope.
Notation "f <=< g" := (kleisli_comp g f) (at level 60) : monad_scope.


(** Chickenbutt (applicative functor thing) *)
Definition ap {T : Type -> Type} `{Monad T} {A B}
  : T (A -> B) -> T A -> T B :=
  fun f m => f >>= fun g => g <$> m.

Notation "f <*> x" := (ap f x) (at level 60) : monad_scope.
Notation "x *> y" := (flip const x y) (at level 60) : monad_scope.
(* Notation "x <* y" := (const x y) (at level 60) : monad_scope. *)


Definition liftA2 {T : Type -> Type} `{Monad T} {A B C}
  : (A -> B -> C) -> T A -> T B -> T C :=
  fun f x y => ret f <*> x <*> y.


(* 
Naturality condition for any α:

      F f
 F A  ->  F B

  |α      |α

 G A  ->  G B
      G f

G f ∘ α = α ∘ F f
*)


(** Monads in terms of return and join. Instances of the other monad
classes can be derived from this one, so it's probably good to define
a Jmonad instance whenever possible. It's also the closest to the
categorical definition of a monad as a monoid object in the category
of endofunctors (from whatever category we are in back to itself). *)

Class Join (T : Type -> Type) : Type :=
  join : forall {A}, T (T A) -> T A.

Notation "'μ'" := join : monad_scope.


(*
Naturality condition for return:

      f
 A   ->   B

 |η      |η

T A  ->  T B
     T f

I.e.,  F f ∘ η = η ∘ f

Naturality condition for join:

         T (T f)
 T (T A)   ->     T (T B)

   |μ               |μ

  T A      ->      T B
           T f

I.e.,  T f ∘ μ = μ ∘ T (T f)
*)


(* These laws seem a bit nicer when defined pointwise. *)
(* TODO: define the naturality conditions using the general definition
         of natural? *)
Class Jmonad (T : Type -> Type) `{Functor T} {r : Return T} {j : Join T}
  : Prop :=
  { jmonad_left_id : forall A (m : T A), μ (ret m) = m
  ; jmonad_right_id : forall A (m : T A), μ (ret <$> m) = m
  ; jmonad_assoc : forall A (m : T (T (T A))), μ (μ m) = μ (μ <$> m)
  ; jmonad_ret_nat : forall A B (f : A -> B), fmap f ∘ ret = ret ∘ f
  ; jmonad_bind_nat : forall A B (f : A -> B), fmap f ∘ μ = μ ∘ fmap (fmap f) }.


(* Construction of Monad instance from JMonad.*)
Instance Bind_join (T : Type -> Type) `{Functor T} `{Join T} : Bind T :=
  fun _ _ m f => μ (f <$> m).

(* It seems that we need the naturality conditions for this proof. *)
Instance Monad_Jmonad (T : Type -> Type) `{Jmonad T} : Monad T.
Proof.
  constructor.
  - intros A B x f.
    destruct H0.
    unfold bind, Bind_join.
    specialize (jmonad_ret_nat0 A (T B) f).
    eapply equal_f in jmonad_ret_nat0.
    unfold compose in jmonad_ret_nat0.
    rewrite jmonad_ret_nat0. auto.
  - intros A m.
    unfold bind, Bind_join.
    destruct H0; auto.
  - intros A B C m f g.
    unfold bind, Bind_join.
    destruct H0 as [_ _ Hassoc _ Hbind].
    unfold compose in Hbind.
    pose proof (Hbind B (T C) g) as H0.
    eapply equal_f in H0; rewrite H0.
    rewrite Hassoc; destruct H as [_ Hcomp].
    unfold compose in Hcomp.
    pose proof (Hcomp _ _ _ (fmap g ∘ f) μ) as H1.
    unfold compose in H1; rewrite H1.
    pose proof (Hcomp _ _ _ f (fmap g)) as H2.
    rewrite H2; auto.
Qed.

Instance Return_adjunction L R `{u : AdjunctionUnit L R}
  : Return (R ∘ L) := u.

(* This is annoying. *)
Program Instance Join_adjunction L R `{c : AdjunctionCounit L R}
  : Join (R ∘ L) :=
  (* fun A => fmap (@adjCounit L R _ _ _ _ _ (L A)). *)
  fun A => @fmap _ _ _ (L A) _.
Next Obligation. unfold compose in X. apply adjCounit in X; auto. Defined.

Instance Jmonad_adjunction L R `{Adjunction L R} : Jmonad (R ∘ L).
Proof.
  constructor.
  - destruct H1 as [_ Htri]; intros A m; apply (equal_f (Htri _)).
  - intros A m.
    unfold join, Join_adjunction, Join_adjunction_obligation_1,
    fmap, Fmap_compose', Fmap_compose.
    pose proof H0 as H2. destruct H2.
    unfold compose in fmap_comp; unfold compose.
    match goal with
    | [ |- fMap0 ?B ?C ?g (fMap0 ?A ?B ?f m) = m ] =>
      pose proof (fmap_comp A B C f g) as H2
    end.
    eapply equal_f in H2; rewrite <- H2.
    pose proof H1 as H3; destruct H3 as [Htri _].
    specialize (Htri A).
    unfold fmap, compose, adjUnit in Htri.
    unfold fmap, ret, Return_adjunction; rewrite Htri.
    destruct H; rewrite fmap_id; auto.
  - intros A m.
    unfold join, Join_adjunction, Join_adjunction_obligation_1,
    fmap, Fmap_compose.
    pose proof H0 as H2; destruct H2; unfold fmap, compose in fmap_comp.
    match goal with
    | [ |- fMap0 ?B ?C ?g (fMap0 ?A _ ?f _) = _ ] =>
      pose proof (fmap_comp A B C f g) as H2
    end.
    eapply equal_f in H2; rewrite <- H2; destruct H1.
    unfold fmap, Fmap_compose', Fmap_compose, Fmap_id', Fmap_id, id, compose
      in adj_counit_nat.
    specialize (adj_counit_nat (L (R (L A))) (L A) (ϵ (L A))).
    assert (H1: (fun x : L (R (L (R (L A)))) =>
                   ϵ (L A) (ϵ (L (R (L A))) x)) =
            (fun x : L (R (L (R (L A)))) =>
               ϵ (L A) (fMap (R (L (R (L A))))
                             (R (L A)) (fmap (ϵ (L A))) x))).
    { extensionality x; eapply equal_f in adj_counit_nat;
        apply adj_counit_nat. }
    unfold compose; rewrite H1; rewrite fmap_comp; auto.
  - firstorder.
  - intros A B f.
    extensionality x.
    unfold fmap, Fmap_compose', Fmap_compose, fmap, join,
    Join_adjunction, Join_adjunction_obligation_1, fmap, compose.
    pose proof H0 as H2; destruct H2; unfold fmap, compose in fmap_comp.
    match goal with
    | [ |- fMap0 ?B ?C ?g (fMap0 ?A _ ?f _) = _ ] =>
      pose proof (fmap_comp A B C f g) as H2
    end.
    eapply equal_f in H2; rewrite <- H2; destruct H1.
    unfold natural, fmap, Fmap_compose', Fmap_compose, Fmap_id',
    Fmap_id, id, compose in adj_counit_nat.
    specialize (adj_counit_nat _ _ (fMap _ _ f)).
    rewrite adj_counit_nat; rewrite fmap_comp; auto.
Qed.


(** The identity monad. *)
Instance Return_id : Return id := fun _ => id.
Instance Join_id : Join id := fun _ => id.
Instance Jmonad_id : Jmonad id.
Proof. constructor; firstorder. Qed.
