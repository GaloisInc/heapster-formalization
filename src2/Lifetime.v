(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     FSets.FMaps.

From Heapster2 Require Import
     Utils.

From ITree Require Import
     ITree
     Events.Exception.

Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

Variant status := current | finished.

Definition status_lte (s1 s2 : status) : Prop :=
  match s1, s2 with
  | finished, current => False
  | _, _ => True
  end.
Global Instance status_lte_preorder : PreOrder status_lte.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; constructor.
  - destruct x, y, z; auto.
Qed.

Definition statusOf_lte (s1 s2 : option status) : Prop :=
  match s1, s2 with
  | Some s1, Some s2 => status_lte s1 s2
  | Some _, None => False
  | _, _ => True
  end.
Global Instance statusOf_lte_preorder : PreOrder statusOf_lte.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; cbn; auto. reflexivity.
  - destruct x, y, z; cbn in *; intuition.
    etransitivity; eauto.
Qed.

(** [s1] subsumes [s2], now with unstarted lifetimes (None) *)
Definition statusOf_subsumes (s1 s2 : option status) : Prop :=
  match s1, s2 with
  (* [s1] can't end before [s2] *)
  | Some finished, Some finished => True
  | Some finished, _ => False
  (* [s2] can't start before [s1] *)
  | None, Some _ => False
  | _, _ => True
  end.

Global Instance statusOf_subsumes_preorder : PreOrder statusOf_subsumes.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; [destruct s |]; cbn; auto.
  - destruct x, y, z; cbn in *; intuition; destruct s, s0; intuition.
Qed.

Definition Lifetimes := list status.

Definition lifetime : Lifetimes -> nat -> option status :=
  @nth_error status.

Definition replace_lifetime (l : Lifetimes) (n : nat) (new : status) : Lifetimes :=
  replace_list_index l n new.

(** [n1] in the lifetime list [x1] subsumes [n2] in the lifetime list [x2] *)
Definition subsumes n1 n2 x1 x2 :=
  statusOf_subsumes (lifetime x1 n1) (lifetime x2 n2).

Definition Lifetimes_lte (ls ls' : Lifetimes) : Prop :=
  forall l, statusOf_lte (lifetime ls l) (lifetime ls' l).

Global Instance Lifetimes_lte_preorder : PreOrder Lifetimes_lte.
Proof.
  constructor; repeat intro.
  - destruct (lifetime x l); [destruct s |]; cbn; auto.
  - specialize (H l). specialize (H0 l). etransitivity; eauto.
Qed.

Lemma subsumes_1_none_inv : forall s n1 n2,
    lifetime s n1 = None ->
    subsumes n1 n2 s s ->
    lifetime s n2 = None.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n2); auto. destruct s0; contradiction.
Qed.

Lemma subsumes_1_finished_inv : forall s n1 n2,
    lifetime s n1 = Some finished ->
    subsumes n1 n2 s s ->
    lifetime s n2 = Some finished.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n2); auto. 2: inversion H0. destruct s0; auto; contradiction.
Qed.

Lemma subsumes_2_none_inv : forall s n1 n2,
    lifetime s n2 = None ->
    subsumes n1 n2 s s ->
    lifetime s n1 = None \/ lifetime s n1 = Some current.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n1); auto. destruct s0; auto. contradiction.
Qed.

Lemma subsumes_2_current_inv : forall s n1 n2,
    lifetime s n2 = Some current ->
    subsumes n1 n2 s s ->
    lifetime s n1 = Some current.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n1); auto. 2: inversion H0.
  destruct s0; auto. contradiction.
Qed.

Lemma subsumes_2_finished_inv : forall s n1 n2,
    lifetime s n2 = Some finished ->
    subsumes n1 n2 s s ->
    lifetime s n1 = Some current \/ lifetime s n1 = Some finished.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n1); auto. 2: inversion H0.
  destruct s0; auto.
Qed.

Section LifetimeOps.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  (** * Lifetime operations *)
  Definition newLifetime : itree (sceE Si) nat :=
    s <- trigger (Modify id);; (* do read first to use length without subtraction *)
    trigger (Modify (fun s =>
                       (lput s ((lget s) ++ [current]))));;
    Ret (length (lget s)).

  Definition endLifetime (l : nat) : itree (sceE Si) unit :=
    s <- trigger (Modify id);;
    match nth_error (lget s) l with
    | Some current =>
        trigger (Modify (fun s =>
                           (lput s (replace_list_index
                                      (lget s)
                                      l
                                      finished))));;
        Ret tt
    | _ => throw tt
    end.
End LifetimeOps.
