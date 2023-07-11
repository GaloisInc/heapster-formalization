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

From Heapster Require Import
     Utils.

From ITree Require Import
     ITree
     Events.Exception.

Import ListNotations.
Import ITreeNotations.

Local Open Scope itree_scope.
(* end hide *)

(* Lifetime keys *)
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

Definition statusOf (l : nat) (ls : Lifetimes) : option status :=
  nth_error ls l.

Definition Lifetimes_lte (ls ls' : Lifetimes) : Prop :=
  forall l, statusOf_lte (statusOf l ls) (statusOf l ls').

Global Instance Lifetimes_lte_preorder : PreOrder Lifetimes_lte.
Proof.
  constructor; repeat intro.
  - destruct (statusOf l x); [destruct s |]; cbn; auto.
  - specialize (H l). specialize (H0 l). etransitivity; eauto.
Qed.

Lemma Lifetimes_lte_cons_inv ls ls' a a' :
  Lifetimes_lte (a :: ls) (a' :: ls') ->
  Lifetimes_lte ls ls'.
Proof.
  intros H n. specialize (H (S n)).
  cbn in *. auto.
Qed.

Lemma Lifetimes_lte_length ls ls' :
  Lifetimes_lte ls ls' ->
  length ls <= length ls'.
Proof.
  revert ls'. induction ls; intros; cbn; try lia.
  destruct ls'.
  - specialize (H 0). contradiction.
  - cbn. apply le_n_S. apply IHls.
    eapply Lifetimes_lte_cons_inv; eauto.
Qed.

Lemma Lifetimes_lte_app ls ls' r :
  Lifetimes_lte ls ls' ->
  Lifetimes_lte ls (ls' ++ r).
Proof.
  repeat intro. unfold statusOf. destruct (Compare_dec.dec_lt l (length ls)).
  - rewrite nth_error_app1; auto. apply H.
    apply Lifetimes_lte_length in H. lia.
  - rewrite (proj2 (nth_error_None ls l)). 2: lia.
    cbn. auto.
Qed.

Lemma Lifetimes_lte_finished ls l :
  Lifetimes_lte ls (replace_list_index ls l finished).
Proof.
  intro l'. destruct (Compare_dec.lt_eq_lt_dec l l') as [[? | ?] | ?]; subst; unfold statusOf.
  - destruct (Compare_dec.dec_lt l (length ls)).
    + erewrite nth_error_replace_list_index_neq; eauto. reflexivity. lia.
    + erewrite nth_error_replace_list_index_neq_after; try lia.
      erewrite (proj2 (nth_error_None ls l')). reflexivity. lia.
  - rewrite nth_error_replace_list_index_eq.
    destruct (nth_error ls l'); [destruct s |]; constructor.
  - destruct (Compare_dec.dec_lt l (length ls)).
    + erewrite nth_error_replace_list_index_neq; eauto. reflexivity. lia.
    + destruct (Compare_dec.dec_lt l' (length ls)).
      * erewrite nth_error_replace_list_index_neq_before; eauto. reflexivity. lia.
      * erewrite nth_error_replace_list_index_neq_new; try lia.
        destruct (nth_error ls l'); [destruct s |]; cbn; auto.
Qed.

Lemma Lifetimes_lte_replace_list_index_inv ls ls' l s :
  Lifetimes_lte (replace_list_index ls l s) (replace_list_index ls' l s) ->
  statusOf_lte (statusOf l ls) (statusOf l ls') ->
  Lifetimes_lte ls ls'.
Proof.
  intros Hreplace Hl l'. specialize (Hreplace l').
  destruct (Compare_dec.lt_eq_lt_dec l l') as [[? | ?] | ?]; subst; auto.

  (* destruct (Peano_dec.dec_eq_nat l l'); subst; auto. *)
  destruct (Compare_dec.dec_lt l (length ls)).
  -
    destruct (Compare_dec.dec_lt l (length ls')).
Admitted.

Lemma Lifetimes_lte_replace_list_index ls ls' l s :
  Lifetimes_lte ls ls' ->
  Lifetimes_lte (replace_list_index ls l s) (replace_list_index ls' l s).
Proof.
  repeat intro.
  destruct (Peano_dec.dec_eq_nat l l0).
  - subst. red in H. unfold statusOf in *. do 2 rewrite nth_error_replace_list_index_eq.
    reflexivity.
  - destruct (Compare_dec.dec_lt l (length ls)).
    + cbn.
Abort. (* not used right now *)

(** * Lifetime Computations *)
Section LifetimeOps.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  Definition beginLifetime : itree (sceE Si) nat :=
    s <- trigger (Modify id);;
    trigger (Modify (fun s => lput s ((lget s) ++ [current])));;
    Ret (length (lget s)).

  Definition endLifetime (l : nat) : itree (sceE Si) nat :=
    s <- trigger (Modify id);;
    match nth_error (lget s) l with
    | Some current =>
        trigger (Modify (fun s =>
                           (lput s (replace_list_index
                                      (lget s)
                                      l
                                      finished))));;
        Ret l
    | _ => throw tt
    end.
End LifetimeOps.
