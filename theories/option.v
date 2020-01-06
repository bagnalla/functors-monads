Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Export functor.
Require Import monad monadtransformer.


(** option is a covariant functor. *)
Instance Fmap_option : Fmap option :=
  fun _ _ f x => match x with
              | Some y => Some (f y)
              | None   => None
              end.

Instance Functor_option : Functor option.
Proof. constructor; intros; extensionality x; destruct x; auto. Qed.


(** option is a Jmonad. *)
Instance Return_option : Return option := fun _ => Some.

Instance Join_option : Join option :=
  fun _ x => match x with
        | Some y => y
        | None => None
        end.

Instance Jmonad_option : Jmonad option.
Proof.
  constructor; firstorder; try destruct m; auto.
  extensionality x. destruct x; auto.
Qed.


(** option monad transformer. *)
Definition optionT (T : Type -> Type) : Type -> Type := T ∘ option.

(* Instance Fmap_optionT (T : Type -> Type) `{Fmap T} : Fmap (optionT T) := *)
(*   fun _ _ => fmap. *)

(* Instance Functor_optionT (T : Type -> Type) `{Functor T} *)
(*   : Functor (optionT T). *)
(* Proof. *)
(*   constructor. *)
(*   - intros A. unfold fmap, Fmap_optionT. *)
(*     unfold fmap, Fmap_compose, fmap, Fmap_option, compose, id. *)
(*     assert ((fun x : option A => match x with *)
(*                               | Some y => Some y *)
(*                               | None => None end) = id). *)
(*     { extensionality x. destruct x; auto. } *)
(*     rewrite H0. destruct H. apply fmap_id. *)
(*   - intros A B C f g. *)
(*     extensionality x. *)
(*     unfold fmap, Fmap_optionT. *)
(*     unfold fmap, Fmap_compose. *)
(*     unfold fmap, Fmap_option. *)
(*     destruct H. *)
(*     unfold fmap, compose in *. *)

(*     specialize (fmap_comp (option A) (option B) (option C) (fmap f) (fmap g)). *)
(*     unfold fmap, Fmap_option in fmap_comp. *)
(*     assert ((fun x : option A => *)
(*                  match *)
(*                    match x with *)
(*                    | Some y => Some (f y) *)
(*                    | None => None *)
(*                    end *)
(*                  with *)
(*                  | Some y => Some (g y) *)
(*                  | None => None *)
(*                  end) = fmap (g ∘ f)). *)
(*     { extensionality y. destruct y; auto. } *)
(*     rewrite H in fmap_comp. *)
(*     unfold compose in fmap_comp. *)
(*     unfold fmap, Fmap_option in fmap_comp. *)
(*     rewrite fmap_comp; auto. *)
(* Qed. *)

Instance TransReturn_optionT : TransReturn optionT :=
  fun M _ _ _ _ _ _ => ret ∘ Some.

(* Instance Return_optionT (T : Type -> Type) `{Return T} *)
(*   : Return (optionT T) := fun _ => ret ∘ Some. *)

Instance TransBind_optionT : TransBind optionT :=
  fun M _ _ _ _ _ _ _ m f =>
    @bind M _ _ _ m (fun x => match x with
                           | None => ret None
                           | Some x' => f x'
                           end).

(* Instance Bind_optionT (T : Type -> Type) `{Return T} `{Bind T} *)
(*   : Bind (optionT T) := *)
(*   fun _ _ m f => *)
(*     @bind T _ _ _ m (fun x => match x with *)
(*                            | None => ret None *)
(*                            | Some x' => f x' *)
(*                            end). *)

Instance MonadLift_optionT : MonadLift optionT :=
  fun M _ _ _ _ _ _ m => m >>= ret ∘ Some.

Instance MonadTrans_optionT : MonadTrans optionT.
Proof.
  constructor.
  - intros M Hfmap Hfunc Hret Hbind Hmonad A B x f.
    unfold bind, transBind, TransBind_optionT.
    destruct Hmonad.
    pose proof (monad_left_id (option A) (option B) (ret x)) as H0.
    rewrite H0; auto.
  - intros M Hfmap Hfunc Hret Hbind Hmonad A m.
    unfold bind, transBind, TransBind_optionT.
    destruct Hmonad. unfold bind in *.
    pose proof (monad_right_id (option A) m) as H0.
    unfold ret in *; unfold transRet, TransReturn_optionT, ret.
    assert ((fun x : option A =>
     match x with
     | Some x' => (Hret (option A) ∘ Some) x'
     | None => Hret (option A) None
     end) = Hret (option A)).
    { extensionality x. destruct x; auto. }
    unfold transRet, TransReturn_optionT, ret.
    rewrite H; auto.
  - 
    intros M Hfmap Hfunc r b Hmonad A B C m f g.
    unfold bind, transBind, TransBind_optionT, bind, ret.
    destruct Hmonad.
    rewrite monad_assoc.
    unfold bind. f_equal.
    extensionality x. destruct x; auto.
    rewrite monad_left_id; auto.
  - intros M Hfmap Hfunc r b Hmonad A.
    unfold ret, transRet, TransReturn_optionT, ret.
    unfold monadLift, MonadLift_optionT, ret.
    destruct Hmonad.
    extensionality x.
    unfold compose.
    rewrite monad_left_id; auto.
  - intros M Hfmap Hfunc r b Hmonad A B m k.
    unfold monadLift, MonadLift_optionT, ret.
    destruct Hmonad.
    unfold compose, bind, transBind, TransBind_optionT, bind, ret.
    rewrite 2!monad_assoc.
    assert (H0: (fun x : A =>
                   r (option A) (Some x) >>=
                     (fun x0 : option A =>
                        match x0 with
                        | Some x' => b B (option B) (k x')
                                      (fun x1 : B => r (option B) (Some x1))
                        | None => r (option B) None
                        end)) = (fun x => k x >>= (fun y => r _ (Some y)))).
    { extensionality x; rewrite monad_left_id; auto. }
    rewrite H0. auto.
Qed.

(* Instance Monad_optionT (T : Type -> Type) `{Monad T} : Monad (optionT T). *)
(* Proof. *)
(*   constructor. *)
(*   - intros A B c f. *)
(*     unfold bind, Bind_optionT. *)
(*     destruct H0. *)
(*     unfold bind in *. *)
(*     pose proof (monad_left_id (option A) (option B) (ret c)) as H0. *)
(*     rewrite H0; auto. *)
(*   - intros A m. *)
(*     unfold bind, Bind_optionT. *)
(*     destruct H0. unfold bind in *. *)
(*     pose proof (monad_right_id (option A) m) as H0. *)
(*     unfold ret in *; unfold Return_optionT, ret. *)
(*     assert ((fun x : option A => *)
(*      match x with *)
(*      | Some x' => (r (option A) ∘ Some) x' *)
(*      | None => r (option A) None *)
(*      end) = r (option A)). *)
(*     { extensionality x. destruct x; auto. } *)
(*     rewrite H1; auto. *)
(*   - intros A B C m f g. *)
(*     destruct H0. *)
(*     unfold bind in *. *)
(*     unfold Bind_optionT. *)
(*     unfold bind. *)
(*     admit. *)
(* Admitted. *)
