Require Import ZArith List String Omega.

From Coq Require Import
 Setoids.Setoid
 Classes.Morphisms
 Classes.RelationClasses
 Relations.Relation_Operators.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.Monads.OptionMonad.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope list_scope.

Set Implicit Arguments.


Section Permissions.

  Variable S : Type.

  (* Denotation of permissions *)
  Record perm := mkPerm {
    view : relation S;  (* PER over configs *)
    upd  : relation S;  (* allowed transitions *)
  }.

  Class goodPerm (p:perm) : Prop := {
     view_PER          :> PER (view p) ;   (* the view is a PER *)
(*
     upd_transitive    :> Transitive (upd p) ;
*)
     upd_PO  :> PreOrder (upd p) ;   (* the update relation is a partial order *)
     (* SAZ: This is too strong because this + separation implies that (view p) is reflexive.
        Reflexivity is too much?  *)

     (* SAZ: *)
     view_bisim  : forall x1 x2 y1, view p x1 x2
                               -> upd p x1 y1
                               -> view p y1 y1
                               -> exists y2, view p y1 y2 /\ upd p x2 y2 ;
  }.


  Record lte_perm (p q:perm) : Prop := {
     view_inc : forall x y, (view q) x y -> (view p) x y;
     upd_inc : forall x y, (upd p) x y -> (upd q) x y;
  }.

  Definition join_perm (p q:perm) : perm := {|
     view := clos_trans S (fun x y => (view p x y) \/ (view q x y)) ;  (* disjunction *)
     upd  := fun x y => (upd p x y) /\ (upd q x y) ;    (* conjunction *)
  |}.

  Definition bottom_perm : perm := {|
     view := fun x y => False ;
     upd  := fun x y => True ;
  |}.

  Definition top_perm : perm := {|
     view := fun x y => True ;
     upd  := fun x y => False ;
  |}.

  Record sep_at (x:S) (p q:perm) : Prop :=
    {
      inp : view p x x ;
      inq : view q x x ;
      upd1: forall x' y:S, view p x x' -> (upd p) x' y -> (view q) x' y;
      upd2: forall x' y:S, view q x x' -> (upd q) x' y -> (view p) x' y;
    }.

  Definition separate (p q : perm) : Prop := forall x, sep_at x p q.

  Instance separate_symm (x:S) : Symmetric (sep_at x).
  Proof.
    unfold Symmetric.
    intuition.
    destruct H as [H0 H1]. split; eauto.
  Qed.


  (* If upd is not reflexive, then this lemma is not true, but maybe not ever needed? *)
  Lemma sep_at_refl1 : forall x p q `{goodPerm q}, sep_at x p q -> (view p) x x.
  Proof.
    intuition.
    destruct H0 as [G1 G2].
    destruct H.
    (* apply G2. reflexivity. *)
  Abort.

  (* SAZ: same here *)
  Lemma sep_at_refl2 : forall x p q `{goodPerm p}, sep_at x p q -> (view q) x x.
  Proof.
    intuition.
    destruct H0 as [G1 G2].
  Abort.

  Lemma separate_anti_monotone : forall (p1 p2 q : perm) (HSep: separate p2 q) (Hlt: lte_perm p1 p2),
      separate p1 q.
  Proof.
    intros p1 p2 q HSep Hlt.
    destruct Hlt.
    unfold separate in HSep.
    unfold separate.
    intros. constructor; intuition.
  Admitted.
(*
    apply HSep. intuition.
    apply view_inc0. apply HSep. assumption.
  Qed.
*)

  Lemma PER_symm_refl : forall A (R : relation A) `{PER A R} (x y : A), R x y -> R x x.
  Proof.
    intuition.
    eapply transitivity . apply H0. symmetry. assumption.
  Qed.


  (* This seems to be the key lemma for good separation properties.
     SAZ: But... it doesn't seem to be provable.  Perhaps it just doesn't hold.

   *)
  Lemma eqv_sep_at : forall p `{goodPerm p} q `{goodPerm q} x y,
    (view p) x y -> (sep_at x p q) <-> (sep_at y p q).
  Proof.
    intuition.
    - split.
      + admit. (* easy *)
      + admit. (* easy *)
      + intros.
      assert (exists z, view p x z /\ upd p x z).
  Abort.

End Permissions.

Section Typing.


End Typing.


Section CounterExample.

  Inductive Pv: nat -> nat -> Prop :=
  | pv00 : Pv 0 0
  | pv01 : Pv 0 1
  | pv10 : Pv 1 0
  | pv11 : Pv 1 1
  | pv22 : Pv 2 2.


  (* SAZ: Note this update relation is _not_ proper, which is what leads to the counterexample *)
  Inductive Pu : nat -> nat -> Prop :=
  | pu02 : Pu 0 2
  | purefl : forall x, Pu x x.

  Definition P := mkPerm Pv Pu.

  (* If we omit the proper requirement, then we can prove the first two facts about perms. *)
  Instance goodPerm_Pv : goodPerm P.
  Proof.
    repeat split.
    - unfold Symmetric; intros. destruct H; econstructor.
    - unfold Transitive; intros. simpl in *. destruct H; auto. inversion H0. econstructor. econstructor. remember 0 as x. inversion H0; subst; try solve econstructor.
      econstructor. econstructor. inversion H. inversion H. inversion H.
    - unfold Reflexive. intros. simpl. apply purefl.
    - simpl. unfold Transitive. intros.
      inversion H. subst. remember 2 as y. inversion H0. subst. inversion H1. subst. assumption.
      subst.  assumption.
  Qed.

  Definition Q : perm nat := mkPerm eq eq.

  Instance goodPerm_Q : goodPerm Q.
  Proof.
    repeat split; simpl; auto.
    unfold Transitive. intros. eapply transitivity; eauto.
    unfold Transitive. intros. eapply transitivity; eauto.
  Qed.

  (* P and Q are separate at 1 *)
  Lemma sep_at1 : sep_at 1 P Q.
  Proof.
    split; intuition.
    - simpl in *. remember 1 as x. inversion H. subst. inversion H0. reflexivity.
    - simpl in *. subst. econstructor.
  Qed.

  (* But they are not separate at 0 *)
  Lemma not_sep_at0 : not (sep_at 0 P Q).
  intuition. destruct H as [G1 G2].
  simpl in *.
  assert (Pu 0 2).
  econstructor. apply G1 in H.
  inversion H.
  Qed.




End CounterExample.


