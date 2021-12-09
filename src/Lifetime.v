(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms.

From Heapster Require Import
     Utils
     Permissions.

Import ListNotations.
(* end hide *)

Variant Lifetime := current | finished.
Definition Lifetimes := list Lifetime.

(** lifetime helpers **)

Definition lifetime : Lifetimes -> nat -> option Lifetime :=
  @nth_error Lifetime.

Definition replace_lifetime (l : Lifetimes) (n : nat) (new : Lifetime) : Lifetimes :=
  replace_list_index l n new.

Lemma replace_lifetime_same c n l :
  lifetime c n = Some l -> replace_lifetime c n l = c.
Proof.
  apply replace_list_index_eq.
Qed.

Lemma lifetime_replace_lifetime c n l :
  lifetime (replace_lifetime c n l) n = Some l.
Proof.
  apply nth_error_replace_list_index_eq.
Qed.

(** Lifetime ordering **)
Definition lifetime_lte (l1 l2 : option Lifetime) : Prop :=
  match l1, l2 with
  | None, _ => True
  | Some current, None => False
  | Some current, _ => True
  | Some finished, Some finished => True
  | _, _ => False
  end.

Instance lifetime_lte_preorder : PreOrder lifetime_lte.
Proof.
  constructor; repeat intro.
  - destruct x as [[] |]; simpl; auto.
  - destruct x as [[] |], y as [[] |], z as [[] |]; simpl; intuition.
Qed.

Definition monotonic_at (p : perm) (n : nat) (x y : Lifetimes) : Prop :=
  guar p x y -> lifetime_lte (lifetime x n) (lifetime y n).

Instance monotonic_at_reflexive p n : Reflexive (monotonic_at p n).
Proof.
  repeat intro. reflexivity.
Qed.

Lemma bottom_monotonic_at n : forall x y, monotonic_at bottom_perm n x y.
Proof.
  repeat intro. simpl in H. subst. reflexivity.
Qed.

Definition monotonic (P : Perms) (n : nat) : Prop :=
  forall p, p ∈ P -> exists p', p' <= p /\ p' ∈ P /\ forall x y, monotonic_at p' n x y.

Lemma monotonic_bottom n : monotonic bottom_Perms n.
Proof.
  repeat intro. exists bottom_perm. split; [| split].
  apply bottom_perm_is_bottom. auto. apply bottom_monotonic_at.
Qed.

Program Definition restrict_monotonic_at (p : perm) (n : nat) : perm :=
  {|
  pre := pre p;
  rely := rely p;
  guar := fun x y => guar p x y /\ monotonic_at p n x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - split; intuition.
  - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto.
Qed.
Next Obligation.
  respects.
Qed.

Lemma restrict_monotonic_at_monotone p p' n :
  p <= p' -> restrict_monotonic_at p n <= restrict_monotonic_at p' n.
Proof.
  intros []. constructor; intros; simpl; auto. destruct H.
  split; auto. intro. auto.
Qed.

Lemma restrict_monotonic_at_lte p n : restrict_monotonic_at p n <= p.
Proof.
  constructor; intros; simpl in *; intuition.
Qed.

Definition invariant_at (p : perm) (n : nat) : Prop :=
  forall l1 l2 x y, guar p x y <-> guar p (replace_lifetime x n l1) (replace_lifetime y n l2).

Lemma invariant_l p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime y n = Some l2 ->
               guar p x y <-> guar p (replace_lifetime x n l1) y.
Proof.
  intros.
  erewrite <- (replace_list_index_eq _ y n l2) at 2; auto.
Qed.

Lemma invariant_r p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime x n = Some l1 ->
               guar p x y <-> guar p x (replace_lifetime y n l2).
Proof.
  intros.
  rewrite <- (replace_list_index_eq _ x n l1) at 2; auto.
Qed.

Program Definition when (n : nat) (p : perm) : perm :=
  {|
  pre := fun x => lifetime x n = Some current -> pre p x;
  rely := fun x y => lifetime x n = None /\ lifetime y n = None \/
                  lifetime y n = Some finished \/
                  (* This is similar to [lifetime_lte] but we cannot have [lifetime x n =
                  None /\ lifetime y n = Some current], since that would break transitivity
                  of [rely]. This would allow for an earlier period where the lifetime is
                  not started, where the rely of p is not true. *)
                  lifetime x n = Some current /\ lifetime y n = Some current /\ rely p x y;
  guar := fun x y => x = y \/
                  (* state that the guarantee should hold even when you change lifetimes in x, or something like that, kind of like hwat we do in owned *)
                  lifetime x n = Some current /\ lifetime y n = Some current /\ guar p x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - destruct (lifetime x n) as [[] |]; intuition.
  - decompose [and or] H; decompose [and or] H0; subst; auto.
    + rewrite H1 in H3. discriminate H3.
    + rewrite H2 in H3. discriminate H3.
    + rewrite H1 in H2. discriminate H2.
    + rewrite H2 in H5. discriminate H5.
    + right; right. split; [| split]; auto. etransitivity; eauto.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; [| split]; auto. etransitivity; eauto.
Qed.
Next Obligation.
  decompose [and or] H; decompose [or and] H0; subst; auto.
  - rewrite H1 in H4. discriminate H4.
  - rewrite H1 in H3. discriminate H3.
  - eapply pre_respects; eauto.
Qed.

Lemma when_monotone n p1 p2 : p1 <= p2 -> when n p1 <= when n p2.
Proof.
  intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 7.
Qed.

Instance Proper_lte_perm_when :
  Proper (eq ==> lte_perm ==> lte_perm) when.
Proof.
  repeat intro; subst. apply when_monotone; auto.
Qed.

Instance Proper_eq_perm_when :
  Proper (eq ==> eq_perm ==> eq_perm) when.
Proof.
  repeat intro; subst. split; apply when_monotone; auto.
Qed.

Lemma restrict_monotonic_at_when p n : when n p ≡≡ restrict_monotonic_at (when n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto.
  intro. rewrite H1, H0. reflexivity.
Qed.
Lemma when_restrict_monotonic_at p n : when n p ≡≡ when n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H, H0. reflexivity.
Qed.

Program Definition owned (n : nat) (p : perm) : perm :=
  {|
  pre := fun x => lifetime x n = Some current;
  rely := fun x y => lifetime x n = lifetime y n /\ (lifetime x n = Some finished -> rely p x y);
  guar := fun x y => x = y \/
                  lifetime y n = Some finished /\ guar p (replace_lifetime x n finished) y;
  |}.
Next Obligation.
  constructor; repeat intro; auto.
  - split; intuition.
  - destruct H, H0.
    split; etransitivity; eauto. apply H2. rewrite <- H. auto.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; auto. etransitivity; eauto.
  rewrite <- (replace_lifetime_same y n finished); auto.
Qed.

Lemma owned_monotone n p1 p2 : p1 <= p2 -> owned n p1 <= owned n p2.
Proof.
  intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 6.
Qed.

Instance Proper_lte_perm_owned :
  Proper (eq ==> lte_perm ==> lte_perm) owned.
Proof.
  repeat intro; subst. apply owned_monotone; auto.
Qed.

Instance Proper_eq_perm_owned :
  Proper (eq ==> eq_perm ==> eq_perm) owned.
Proof.
  repeat intro; subst. split; apply owned_monotone; auto.
Qed.

Lemma restrict_monotonic_at_owned p n : owned n p ≡≡ restrict_monotonic_at (owned n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto. clear H.
  intro. rewrite H1. destruct (lifetime x n) as [[] |]; simpl; auto.
Qed.
Lemma owned_restrict_monotonic_at p n : owned n p ≡≡ owned n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H. rewrite lifetime_replace_lifetime. reflexivity.
Qed.

(* trivial direction *)
Lemma foo' p q n :
  owned n (restrict_monotonic_at p n ** restrict_monotonic_at q n) <=
  owned n (restrict_monotonic_at (p ** q) n).
Proof.
  rewrite <- owned_restrict_monotonic_at. apply owned_monotone.
  apply sep_conj_perm_monotone; apply restrict_monotonic_at_lte.
Qed.

Lemma lifetimes_sep_gen p q n :
  p ⊥ owned n q -> when n p ⊥ owned n (p ** q).
Proof.
  split; intros.
  - simpl in H0. decompose [and or] H0. subst; intuition.
    simpl. right; left; auto.
  - simpl in H0. decompose [and or] H0. subst; intuition.
    simpl. split. rewrite H1, H2; auto.
    intros. rewrite H2 in H3. discriminate H3.
Qed.

(* not actually a special case of the above *)
Lemma lifetimes_sep n p : when n p ⊥ owned n p.
Proof.
  constructor; intros; simpl in H; auto.
  - decompose [and or] H; subst; try reflexivity.
    simpl. right; left; auto.
  - decompose [and or] H; subst; try reflexivity.
    simpl. split. rewrite H1, H0. auto. intros. rewrite H1 in H2. discriminate H2.
Qed.

Lemma convert p q n (Hmon : forall x y, monotonic_at p n x y) (Hmon' : forall x y, monotonic_at q n x y) :
  when n p ** owned n (p ** q) <= p ** owned n q.
Proof.
  split; intros.
  - simpl in *. decompose [and or] H; auto. split; auto. split; auto.
    eapply lifetimes_sep_gen; eauto.
  - simpl in *. decompose [and or] H; auto. destruct (lifetime x n) as [[] | ]; auto 7.
  - simpl in H. induction H. 2: { econstructor 2; eauto. }
    decompose [and or] H; simpl; subst; try solve [constructor; auto].
    clear H.
    apply Operators_Properties.clos_trans_t1n_iff.
    apply Operators_Properties.clos_trans_t1n_iff in H2.
    constructor 2 with (y:=replace_lifetime x n finished).
    { right; right. split; [apply lifetime_replace_lifetime | reflexivity]. }
    pose proof (lifetime_replace_lifetime x n finished).
    induction H2; intros; subst; auto.
    + constructor. destruct H1; auto. right; right. split; auto.
      rewrite replace_lifetime_same; auto.
    + assert (lifetime y n = Some finished).
      { destruct H1; [apply Hmon in H1 | apply Hmon' in H1]; rewrite H in H1; simpl in H1;
          destruct (lifetime y n) as [[] |]; inversion H1; auto. }
      econstructor 2. 2: apply IHclos_trans_1n; auto.
      destruct H1; auto. right; right. split; auto. rewrite replace_lifetime_same; auto.
Qed.

(* special case of convert *)
Lemma convert_bottom p n (Hmon : forall x y, monotonic_at p n x y) :
  when n p ** owned n p <= p ** owned n bottom_perm.
Proof.
  rewrite <- (sep_conj_perm_bottom p) at 2. apply convert; auto.
  repeat intro. simpl in H. subst. reflexivity.
Qed.

(** [n1] subsumes [n2] in the Lifetime list [x] *)
Definition subsumes x n1 n2 :=
  (Some current = lifetime x n2 -> Some current = lifetime x n1) /\
  (Some finished = lifetime x n1 -> Some finished = lifetime x n2) /\
  (None = lifetime x n1 -> None = lifetime x n2).

Instance subsumes_preorder x : PreOrder (subsumes x).
Proof.
  unfold subsumes.
  constructor; [repeat intro; auto |].
  intros n1 n2 n3. intros (? & ? & ?) (? & ? & ?). split; [| split]; intros.
  - apply H. apply H2; auto.
  - apply H3. apply H0; auto.
  - apply H4. apply H1; auto.
Qed.

(* Lemma lcurrent_pre_trans' x n1 n2 n3 : *)
(*     lcurrent_pre x n1 n3 -> *)
(*     lcurrent_pre x n1 n2 /\ lcurrent_pre x n2 n3. *)
(* Proof. *)
(*   unfold lcurrent_pre. split. *)
(*   - split. *)
(*     + intro. apply H. *)
(* Admitted. *)

(** n1 subsumes n2, and the rely states that lifetimes don't do weird stuff. **)
Program Definition lcurrent n1 n2 : perm :=
  {|
  pre x := subsumes x n1 n2;
  rely x y := x = y \/ (* add a case for when it doesn't subsume in x, then anything, that lets us weaken the guar. *)
              ~subsumes x n1 n2 \/
              (subsumes x n1 n2 /\ subsumes y n1 n2) /\
              lifetime_lte (lifetime x n1) (lifetime y n1) /\
              lifetime_lte (lifetime x n2) (lifetime y n2);
  guar x y := x = y (* \/ (~subsumes x n1 n2 /\ (* only lifetimes version here *) subsumes y n1 n2) *);
  |}.
Next Obligation.
  constructor; repeat intro; intuition; subst; intuition.
  right. right. intuition; etransitivity; eauto.
Qed.
Next Obligation.
  constructor; auto. intros ? ? ? [] []; subst; auto.
Qed.
Next Obligation.
  destruct H; subst; auto. destruct H; intuition.
Qed.

Lemma lcurrent_transitive n1 n2 n3 :
  lcurrent n1 n3 <= lcurrent n1 n2 ** lcurrent n2 n3.
Proof.
  constructor; intros. (* 3: { constructor. auto. } *)
  - destruct H as (? & ? & ?). simpl in *. etransitivity; eauto.
  - destruct H. simpl in *. destruct H, H0; subst; auto. right.
(*     destruct H as (H12 & ? & ?), H0 as (H23 & ? & ?). split; [| split]; auto.
    destruct H12, H23.
    split; etransitivity; eauto.
    (* intros. etransitivity; eauto. apply H12. admit. admit. *)
    (* (* we don't know anything about n2 *) *)
  - constructor; auto.
Qed.*)
Admitted.

Lemma lcurrent_sep n1 n2 n3 n4 :
  lcurrent n1 n2 ⊥ lcurrent n3 n4.
Proof.
  constructor; intros ? ? []; reflexivity.
Qed.

(* Lemma lcurrent_sep_owned n1 n2 p : *)
(*   lcurrent n1 n2 ⊥ owned n1 p. *)
(* Proof. *)
(*   constructor; intros ? ? []; subst; try reflexivity. *)
(*   destruct H. right. *)
(* Qed. *)

Lemma lcurrent_duplicate n1 n2 :
  lcurrent n1 n2 ≡≡ lcurrent n1 n2 ** lcurrent n1 n2.
Proof.
  split.
  - constructor; intros; simpl in *; [apply H | apply H | subst; constructor; left; auto].
  - constructor; intros; simpl in *; subst; auto.
    + split; [| split]; auto. apply lcurrent_sep.
    + induction H; [destruct H |]; subst; auto.
Qed.

(* Weaken the lifetime n1 to n2 *)
Lemma lcurrent_when n1 n2 p :
  (* lcurrent n1 n2 should still be valid too? *)
  lcurrent n1 n2 ** when n2 p <= lcurrent n1 n2 ** when n1 p.
Proof.
  constructor; intros.
  - simpl in *. admit.
  - simpl in *. admit.
  - simpl in *.
Abort.


 (*  - simpl. destruct H as (? & ? & ?). simpl in *. *)
 (*    intro. symmetry in H2. apply H in H2. auto. *)
 (*  - destruct H. destruct H; subst; try reflexivity. destruct H as ((? & ?) & ? & ?). *)
 (*    destruct H0 as [[? ?] | [? | ?]]. *)
 (*    + left. split; symmetry; [apply H | apply H1]; auto. *)
 (*    + right. left. symmetry. apply H1; auto. *)
 (*    + (* subsumes x n1 n2 gives us the wrong direction here. *) *)
 (*      right. destruct (lifetime y n2) eqn:?; auto. destruct l. *)
 (*      * right. destruct H0 as (? & ? & ?). split; [| split]; auto. *)
 (*        destruct (lifetime x n2) eqn:?. destruct l. all: auto; try contradiction H3. *)
 (*        red in H. rewrite H0, Heqo0 in H. *)
 (*        admit. *)
 (*      * admit. *)
 (*      * admit. *)
 (*  (* right. destruct H2 as (? & ? & ?). split; [| split]; admit. *) *)
 (*  admit. admit. *)
 (*  - induction H. 2: econstructor 2; eauto. *)
 (*    destruct H. constructor. left. auto. *)

 (*    destruct H; subst; try reflexivity. destruct H as (? & ? & ?). *)
 (*    constructor. right. right. split; [| split]; auto. *)
 (* Abort. *)
