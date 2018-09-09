Require Import FunctionalExtensionality.
Require Import functor monad.


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
