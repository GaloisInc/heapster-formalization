From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List.

Require Export Heapster.Permissions.

Import ListNotations.

Variant Lifetime := current | finished.

Record config : Type :=
  {
  l : list Lifetime;
  }.
Module Config <: Permissions.Config.
  Definition t := config.
End Config.

Module Permissions' := Permissions Config.
Export Config.
Export Permissions'.

Definition lifetime : config -> nat -> option Lifetime :=
  fun c => nth_error (l c).

Fixpoint replace_list_index {A : Type} (l : list A) (n : nat) (new : A) :=
  match l with
  | [] => repeat new (n + 1)
  | h :: t => match n with
            | O => new :: t
            | S n => h :: replace_list_index t n new
            end
  end.
Definition replace_lifetime (c : config) (n : nat) (new : Lifetime) : config :=
  {| l := replace_list_index (l c) n new |}.

Lemma replace_lifetime_same c n l :
  lifetime c n = Some l -> replace_lifetime c n l = c.
Proof.
  intros. destruct c. unfold lifetime in H. unfold replace_lifetime. f_equal. simpl in *.
  generalize dependent n. induction l0; intros; simpl in *; auto.
  - assert (@nth_error Lifetime [] n <> None). intro. rewrite H in H0. discriminate H0.
    apply nth_error_Some in H0. inversion H0.
  - destruct n; auto.
    + inversion H. auto.
    + rewrite IHl0; auto.
Qed.

Lemma lifetime_replace_lifetime c n l :
  lifetime (replace_lifetime c n l) n = Some l.
Proof.
  destruct c. unfold replace_lifetime. simpl. revert n l.
  induction l0; intros; simpl; induction n; auto.
  unfold lifetime in *. simpl in *. auto.
Qed.

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

Definition monotonic_at (p : perm) (n : nat) (x y : config) : Prop :=
  upd p x y -> lifetime_lte (lifetime x n) (lifetime y n).

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
  dom := dom p;
  view := view p;
  upd := fun x y => upd p x y /\ monotonic_at p n x y;
  |}.
Next Obligation.
  respects.
Qed.
Next Obligation.
  constructor; repeat intro.
  - split; intuition.
  - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto.
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
  forall l1 l2 x y, upd p x y <-> upd p (replace_lifetime x n l1) (replace_lifetime y n l2).

Lemma invariant_l p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime y n = Some l2 ->
               upd p x y <-> upd p (replace_lifetime x n l1) y.
Proof.
  intros.
  rewrite <- (replace_lifetime_same y n l2) at 2; auto.
Qed.

Lemma invariant_r p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime x n = Some l1 ->
               upd p x y <-> upd p x (replace_lifetime y n l2).
Proof.
  intros.
  rewrite <- (replace_lifetime_same x n l1) at 2; auto.
Qed.

Program Definition when (n : nat) (p : perm) : perm :=
  {|
  dom := fun x => (lifetime x n = Some current /\ dom p x) \/
               lifetime x n = Some finished;
  view := fun x y => lifetime x n = None /\ lifetime y n = None \/
                  lifetime y n = Some finished \/
                  lifetime x n = Some current /\ lifetime y n = Some current /\ view p x y;
  upd := fun x y => x = y \/
                 lifetime x n = Some current /\ lifetime y n = Some current /\ upd p x y;
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
  decompose [and or] H; decompose [or and] H0; subst; auto.
  - rewrite H2 in H4. discriminate H4.
  - rewrite H1 in H2. discriminate H2.
  - left. split; auto. eapply dom_respects; eauto.
  - rewrite H1 in H3. discriminate H3.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; [| split]; auto. etransitivity; eauto.
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

Lemma restrict_monotonic_at_when p n : when n p ≡ restrict_monotonic_at (when n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto.
  intro. rewrite H1, H0. reflexivity.
Qed.
Lemma when_restrict_monotonic_at p n : when n p ≡ when n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H, H0. reflexivity.
Qed.

Program Definition owned (n : nat) (p : perm) : perm :=
  {|
  dom := fun x => lifetime x n = Some current;
  view := fun x y => lifetime x n = lifetime y n /\ (lifetime x n = Some finished -> view p x y);
  upd := fun x y => x = y \/
                 lifetime y n = Some finished /\ upd p (replace_lifetime x n finished) y;
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

Lemma restrict_monotonic_at_owned p n : owned n p ≡ restrict_monotonic_at (owned n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto. clear H.
  intro. rewrite H1. destruct (lifetime x n) as [[] |]; simpl; auto.
Qed.
Lemma owned_restrict_monotonic_at p n : owned n p ≡ owned n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H. rewrite lifetime_replace_lifetime. reflexivity.
Qed.

(* trivial direction *)
Lemma foo' p q n :
  owned n (restrict_monotonic_at p n * restrict_monotonic_at q n) <=
  owned n (restrict_monotonic_at (p * q) n).
Proof.
  rewrite <- owned_restrict_monotonic_at. apply owned_monotone.
  apply sep_conj_perm_monotone; apply restrict_monotonic_at_lte.
Qed.

Lemma lifetimes_sep_gen p q n :
  p ⊥ owned n q -> when n p ⊥ owned n (p * q).
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
  when n p * owned n (p * q) <= p * owned n q.
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
  when n p * owned n p <= p * owned n bottom_perm.
Proof.
  rewrite <- (sep_conj_perm_bottom p) at 2. apply convert; auto.
  repeat intro. simpl in H. subst. reflexivity.
Qed.
