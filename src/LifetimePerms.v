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

From ITree Require Import
     ITree
     Eq.Eqit
     Events.Exception.

From Heapster Require Import
     Utils
     Permissions
     PermissionsSpred2
     Lifetime
     Typing
     SepStep
     MemoryPerms.

From Paco Require Import
     paco.

Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.
Open Scope list_scope.
(* end hide *)

Section LifetimePerms.

  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  Program Definition lifetime_perm (n : nat) : (@perm (Si * Ss)) :=
    {|
      pre '(x, _) := length (lget x) = n;

      rely '(x, _) '(y, _) :=
      length (lget x) = length (lget y) /\
        (* Lifetimes_lte (lget x) (lget y) /\ *)
        (forall n', n' >= n -> statusOf n' (lget x) = statusOf n' (lget y));

      guar '(x, _) '(y, _) :=
      (exists (ls : Lifetimes), y = lput x ls) /\
        (* Lifetimes_lte (lget x) (lget y) /\ *)
        (forall l, l < n ->
              statusOf l (lget x) = statusOf l (lget y));
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; [| split]; reflexivity.
    - destruct x, y, z. destruct H as (? & ?), H0 as (? & ?).
      split; etransitivity; eauto.
      transitivity (statusOf n' (lget s1)); auto.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; [| split]; try reflexivity.
      eexists. rewrite lPutGet. reflexivity.
    - destruct x, y, z. destruct H as ((? & ?) & ?), H0 as ((? & ?) & ?). subst.
      split.
      + eexists. rewrite lPutPut. reflexivity.
      + intros. transitivity (statusOf l (lget (lput s x))); eauto.
  Qed.
  Next Obligation.
    destruct x, y. destruct H. rewrite <- H. auto.
  Qed.

  Definition nonLifetime p : Prop :=
    forall n, p ⊥ lifetime_perm n.

  Definition guar_inv (p : @perm (Si * Ss)) : Prop :=
    forall si si' ss ss' l s,
      guar p (si, ss) (si', ss') ->
      (* if we instead let any changes happen, then p would not be nonLifetime *)
      guar p
           (lput si (replace_list_index (lget si) l s), ss)
           (lput si' (replace_list_index (lget si') l s), ss').

  Lemma guar_inv_sep_conj_perm p q (Hp : guar_inv p) (Hq : guar_inv q) :
    guar_inv (p ** q).
  Proof.
    repeat intro. remember (si, ss). remember (si', ss').
    revert s si ss si' ss' Heqp0 Heqp1.
    induction H; intros; subst.
    - constructor. destruct H; [left; apply Hp | right; apply Hq]; auto.
    - destruct y. etransitivity.
      apply IHclos_trans1; eauto.
      apply IHclos_trans2; eauto.
  Qed.

  (*
  (* the smallest perm that satisfies guar_inv *)
  Program Definition bottom_perm_lifetimes : (@perm (Si * Ss)) :=
    {|
      pre := fun x => True;
      rely := fun x y => True;
      guar := fun '(si, ss) '(si', ss') => exists s, si' = lput si s /\ ss = ss';
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. eexists. split; auto. symmetry. apply lPutGet.
    - destruct x, y, z. destruct H as (? & ? & ?), H0 as (? & ? & ?).
      subst. eexists. split; auto.
      rewrite lPutPut. reflexivity.
  Qed.

  Lemma guar_inv_bottom :
    guar_inv bottom_perm_lifetimes.
  Proof.
    repeat intro. cbn in *. destruct H as (? & ? & ?).
    rewrite H. rewrite lPutPut. eexists. split; auto.
    rewrite lPutPut. reflexivity.
  Qed.
   *)

  Lemma guar_inv_bottom :
    guar_inv bottom_perm.
  Proof.
    repeat intro. cbn in *. inversion H. subst. reflexivity.
  Qed.

  Lemma nonLifetime_guar p :
    nonLifetime p ->
    (forall x y, guar p x y -> lget (fst x) = lget (fst y)).
  Proof.
    intros. specialize (H 0). destruct H.
    specialize (sep_r _ _ H0).
    cbn in sep_r. destruct x, y.
    cbn. destruct sep_r as (? & ?).
    unfold statusOf in *.
    apply nth_error_eq. intros. apply H1; lia.
  Qed.

  Lemma nonLifetime_rely p :
    nonLifetime p ->
    forall si si' ss ss' s1 s2,
      rely p (si, ss) (si', ss') ->
      rely p (lput si s1, ss) (lput si' s2, ss').
  Proof.
    intros. destruct (H 0) as (? & _).
    etransitivity.
    {
      pose proof (sep_l (lput si s1, ss) (si, ss)).
      apply H1. cbn. split.
      - setoid_rewrite lPutPut. eexists. symmetry. apply lPutGet.
      - intros. lia.
    }
    etransitivity; eauto.
    apply sep_l. split.
    - eexists. reflexivity.
    - intros. lia.
  Qed.

  Lemma nonLifetime_rely' p :
    nonLifetime p ->
    forall si si' ss ss' s1 s2,
      rely p (lput si s1, ss) (lput si' s2, ss') ->
      rely p (si, ss) (si', ss').
  Proof.
    intros. rewrite <- (lPutGet si), <- (lPutGet si').
    rewrite <- (lPutPut si s1 _), <- (lPutPut si' s2 _).
    apply nonLifetime_rely; auto.
  Qed.

  Lemma clos_trans_nonLifetime p q (Hp : nonLifetime p) (Hq : nonLifetime q) x y :
    Relation_Operators.clos_trans (Si * Ss) (guar p \2/ guar q) x y ->
    lget (fst x) = lget (fst y).
  Proof.
    repeat intro. induction H.
    - destruct H.
      + eapply nonLifetime_guar. apply Hp. eauto.
      + eapply nonLifetime_guar. apply Hq. eauto.
    - etransitivity; eauto.
  Qed.

  Lemma nonLifetime_sep_conj p q (Hp : nonLifetime p) (Hq : nonLifetime q) :
    p ⊥ q ->
    nonLifetime (p ** q).
  Proof.
    repeat intro.
    symmetry. apply separate_sep_conj_perm; symmetry; auto.
  Qed.

  Lemma nonLifetime_bottom : nonLifetime bottom_perm.
  Proof.
    repeat intro. symmetry. apply separate_bottom.
  Qed.

  Lemma nonLifetime_lte p q :
    nonLifetime p -> q <= p -> nonLifetime q.
  Proof.
    repeat intro. symmetry. eapply separate_antimonotone; eauto. symmetry. apply H.
  Qed.

  Lemma nonLifetime_sep_step p q :
    nonLifetime p -> sep_step p q -> nonLifetime q.
  Proof.
    repeat intro. apply H0. apply H.
  Qed.


  Definition nonLifetime' (p : @perm (Si * Ss)) : Prop :=
    (* cannot change lifetimes *)
    (forall x y, guar p x y -> lget (fst x) = lget (fst y)).
      (*  /\ *)
      (* (* must continue to tolerate states no matter the lifetime *) *)
      (* (forall si ss si' ss' l1 l2, rely p (si, ss) (si', ss') -> *)
      (*                         rely p ((lput si l1), ss) ((lput si' l2), ss')). *)

  (* /\ *)
  (*     (forall si si' ss ss' l s, guar p (si, ss) (si', ss') -> *)
  (*                           guar p ((lput si (replace_list_index (lget si) l s)), ss) *)
  (*                                ((lput si' (replace_list_index (lget si') l s)), ss')). *)

  (*
  Program Definition nonLifetimeify (p : @perm (Si * Ss)) : perm :=
    {|
      pre := pre p;
      rely '(si, ss) '(si', ss') := exists l, rely p ((lput si l), ss) ((lput si' l), ss');
      guar x y := guar p x y /\ lget (fst x) = lget (fst y);
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. exists nil. reflexivity.
    - destruct x, y, z. destruct H, H0.
      eexists. etransitivity; eauto.
  Qed.

  Lemma nonLifetimeify_works :
    nonLifetime (nonLifetimeify p).

    Lemma nonLifetimeify_lte :
      nonLifetimify p <= p.
   *)

  Lemma clos_trans_nonLifetime' p q (Hp : nonLifetime' p) (Hq : nonLifetime' q) x y :
    Relation_Operators.clos_trans (Si * Ss) (guar p \2/ guar q) x y ->
    lget (fst x) = lget (fst y).
  Proof.
    repeat intro. induction H.
    - destruct H; [apply Hp | apply Hq]; auto.
    - etransitivity; eauto.
  Qed.

  Lemma nonLifetime'_sep_conj p q (Hp : nonLifetime' p) (Hq : nonLifetime' q) :
    nonLifetime' (p ** q).
  Proof.
    repeat intro.
    apply (clos_trans_nonLifetime' p q); auto.
  Qed.

  Lemma nonLifetime'_bottom : nonLifetime' bottom_perm.
  Proof.
    repeat intro; cbn in *; subst; auto.
  Qed.

  Lemma nonLifetime'_lte p q :
    nonLifetime' p -> q <= p -> nonLifetime' q.
  Proof.
    repeat intro. apply H0 in H1. apply H; auto.
  Qed.

  Lemma nonLifetime'_sep_step p q :
    nonLifetime' p -> sep_step p q -> nonLifetime' q.
  Proof.
    repeat intro. eapply sep_step_guar in H1; eauto.
  Qed.

  (* Definition lifetime_invariant x y := *)
  (*   (forall n n', subsumes n' n (lget x) (lget x) -> *)
  (*            subsumes n' n (lget y) (lget y)) /\ *)
  (*     (forall n, lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n)). *)

  (* Instance lifetime_invariant_preorder : PreOrder lifetime_invariant. *)
  (* Proof. *)
  (*   split; [split; intuition |]. *)
  (*   - intros ? ? ? [] []. split; auto; etransitivity; eauto. *)
  (* Qed. *)

  (* Definition monotonic_at (p : @perm C) (n : nat) x y : Prop := *)
  (*   guar p x y -> lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n). *)

  (* Instance monotonic_at_reflexive p n : Reflexive (monotonic_at p n). *)
  (* Proof. *)
  (*   repeat intro. reflexivity. *)
  (* Qed. *)

  (* Lemma bottom_monotonic_at n : forall x y, monotonic_at bottom_perm n x y. *)
  (* Proof. *)
  (*   repeat intro. simpl in H. subst. reflexivity. *)
  (* Qed. *)

  (* Definition monotonic (P : Perms) (n : nat) : Prop := *)
  (*   forall p, p ∈ P -> exists p', p' <= p /\ p' ∈ P /\ forall x y, monotonic_at p' n x y. *)

  (* Lemma monotonic_bottom n : monotonic bottom_Perms n. *)
  (* Proof. *)
  (*   repeat intro. exists bottom_perm. split; [| split]. *)
  (*   apply bottom_perm_is_bottom. auto. apply bottom_monotonic_at. *)
  (* Qed. *)

  (* Program Definition restrict_monotonic_at (p : perm) (n : nat) : @perm C := *)
  (*   {| *)
  (*     pre := pre p; *)
  (*     rely := rely p; *)
  (*     guar := fun x y => guar p x y /\ monotonic_at p n x y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro. *)
  (*   - split; intuition. *)
  (*   - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   respects. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_monotone p p' n : *)
  (*   p <= p' -> restrict_monotonic_at p n <= restrict_monotonic_at p' n. *)
  (* Proof. *)
  (*   intros []. constructor; intros; simpl; auto. destruct H. *)
  (*   split; auto. intro. auto. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_lte p n : restrict_monotonic_at p n <= p. *)
  (* Proof. *)
  (*   constructor; intros; simpl in *; intuition. *)
  (* Qed. *)

  (* Definition invariant_at (p : perm) (n : nat) : Prop := *)
  (*   forall l1 l2 x y, guar p x y <-> guar p (replace_lifetime x n l1) (replace_lifetime y n l2). *)

  (* Lemma invariant_l p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime y n = Some l2 -> *)
  (*                guar p x y <-> guar p (replace_lifetime x n l1) y. *)
  (* Proof. *)
  (*   intros. *)
  (*   erewrite <- (replace_list_index_eq _ y n l2) at 2; auto. *)
  (* Qed. *)

  (* Lemma invariant_r p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime x n = Some l1 -> *)
  (*                guar p x y <-> guar p x (replace_lifetime y n l2). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite <- (replace_list_index_eq _ x n l1) at 2; auto. *)
  (* Qed. *)

  (* Note: does not have permission to start or end the lifetime [n] *)
  Program Definition when
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : perm :=
    {|
      pre x :=
      let '(si, _) := x in
      (statusOf l (lget si) = None \/ statusOf l (lget si) = Some current) ->
      pre p x;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      statusOf_lte (statusOf l (lget si)) (statusOf l (lget si')) /\
        (* if the lifetime isn't starting or already started, the rely of p must hold *)
        ((statusOf l (lget si') = None \/ statusOf l (lget si') = Some current) ->
           rely p x y);

      guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          lget si = lget si' /\
            statusOf l (lget si) = Some current /\
            guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros [].
      + etransitivity; eauto. apply H1. left. rewrite H3 in H0.
        destruct (statusOf l (lget s1)); auto; inversion H0.
      + etransitivity; eauto. apply H1. rewrite H3 in H0.
        destruct (statusOf l (lget s1)); [destruct s5 |]; auto; inversion H0.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; auto.
    decompose [and or] H; decompose [and or] H0; clear H H0.
    - inversion H1; inversion H2; subst; auto.
    - inversion H1. subst. auto.
    - inversion H3. subst. auto.
    - right. intuition. etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct x, y.
    destruct H. intros. respects. apply H0.
    destruct H2.
    - rewrite H2 in H.
      destruct (statusOf l (lget s)); auto; inversion H.
    - rewrite H2 in H.
      destruct (statusOf l (lget s)); [destruct s3 |]; auto; inversion H.
  Qed.

  Lemma when_monotone n p1 p2 Hp1 Hp2 : p1 <= p2 -> when n p1 Hp1 <= when n p2 Hp2.
  Proof.
    intros. destruct H. constructor; simpl; intros.
    - destruct x. auto.
    - destruct x, y. destruct H; auto.
    - destruct x, y. intuition.
  Qed.


  (* Instance Proper_lte_perm_when : *)
  (*   Proper (eq ==> lte_perm ==> eq ==> lte_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. apply when_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_when : *)
  (*   Proper (eq ==> eq_perm ==> eq_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply when_monotone; auto. *)
  (* Qed. *)

  (* Gives us permission to end the lifetime [n], which gives us back [p] *)
  Program Definition owned
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : @perm (Si * Ss) :=
    {|
      (* TODO: probably need soemthing with subsumes *)
      pre x := let '(si, _) := x in
               statusOf l (lget si) = Some current;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      (* Lifetimes_lte (lget si) (lget si') /\ *)
        statusOf l (lget si) = statusOf l (lget si') /\
        (statusOf l (lget si) = Some finished -> rely p x y);

      guar x y :=
      let '(si, ss) := x in
      let '(si', ss') := y in
      x = y \/
        (* Lifetimes_lte (lget si) (lget si') /\ *)
          (forall l', l <> l' -> statusOf l' (lget si) = statusOf l' (lget si')) /\
          length (lget si) = length (lget si') /\
          statusOf l (lget si') = Some finished /\
          guar p
               ((lput si (replace_list_index (lget si) l finished)), ss)
               ((lput si' (replace_list_index (lget si') l finished)), ss');
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H, H0.
      split; intros.
      + etransitivity; eauto.
      + etransitivity; eauto. apply H2; auto. rewrite <- H. auto.
  Qed.
  Next Obligation.
    constructor; repeat intro; auto.
    - destruct x. auto.
    - destruct x, y, z.
      decompose [and or] H; decompose [and or] H0; clear H H0.
      + inversion H1. inversion H2. subst; auto.
      + inversion H1. subst. intuition.
      + inversion H4. subst. intuition.
      + right. split; [| split; [| split]]; auto; try (etransitivity; eauto).
        transitivity (statusOf l' (lget s1)); eauto.
  Qed.
  Next Obligation.
    destruct x, y.
    destruct H. rewrite <- H. auto.
  Qed.

  Lemma owned_sep_step l p1 p2 Hp1 Hp2 :
    sep_step p1 p2 -> sep_step (owned l p1 Hp1) (owned l p2 Hp2).
  Proof.
    intros. rewrite sep_step_iff in *. destruct H.
    split; intros [] [] ?; cbn in *.
    - decompose [and or] H1; auto.
    - decompose [and or] H1; auto 7.
  Qed.

  Lemma owned_monotone l p1 p2 Hp1 Hp2 :
    p1 <= p2 -> owned l p1 Hp1 <= owned l p2 Hp2.
  Proof.
    intros. destruct H.
    constructor; cbn; intros.
    - destruct x. decompose [and or] H; auto.
    - destruct x, y. decompose [and or] H; auto.
    - destruct x, y. decompose [and or] H; auto 7.
  Qed.

  (* Instance Proper_lte_perm_owned l ls Hls : *)
  (*   Proper (lte_perm ==> lte_perm) (owned l ls Hls). *)
  (* Proof. *)
  (*   repeat intro; subst. apply owned_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_owned l ls H : *)
  (*   Proper (eq_perm ==> eq_perm) (owned l ls H). *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply owned_monotone; auto. *)
  (* Qed. *)

  Program Definition lfinished
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : perm :=
    {|
      pre x :=
      let '(si, _) := x in
      statusOf l (lget si) = Some finished /\
        pre p x;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      statusOf_lte (statusOf l (lget si)) (statusOf l (lget si')) /\ (* TODO: what if it is ending at the moment *)
        (statusOf l (lget si) = Some finished ->
         rely p x y);

      guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          lget si = lget si' /\
            statusOf l (lget si) = Some finished /\
            guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros. etransitivity; eauto. apply H2. rewrite H3 in H.
        destruct (statusOf l (lget s1)); [destruct s5 |]; auto; inversion H.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; auto.
    decompose [and or] H; decompose [and or] H0; clear H H0.
    - inversion H1; inversion H2; subst; auto.
    - inversion H1. subst. auto.
    - inversion H3. subst. auto.
    - right. intuition. etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct x, y. intuition. rewrite H in H1.
    destruct (statusOf l (lget s1)); [destruct s3 |]; auto; inversion H1.
  Qed.

  Lemma when_finished_sep l p q Hp Hq : when l p Hp ⊥ lfinished l q Hq.
  Proof.
    constructor; intros; cbn in H; auto.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split. rewrite H1. reflexivity.
      intro. rewrite <- H1 in H. rewrite H0 in H. destruct H; inversion H.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split; repeat intro; auto.
      + rewrite H1. reflexivity.
      + rewrite H in H0. inversion H0.
  Qed.

  Lemma lte_lifetimes_guar_owned l s s' :
    (forall l' : nat, l <> l' -> statusOf l' (lget s) = statusOf l' (lget s')) ->
    statusOf l (lget s') = Some finished ->
    Lifetimes_lte (lget s) (lget s').
  Proof.
    intros Hneq Heq l'.
    destruct (Nat.eq_decidable l l').
    - subst. rewrite Heq. destruct (statusOf l' (lget s)); cbn; auto.
      destruct s0; cbn; auto.
    - erewrite Hneq; auto. reflexivity.
  Qed.


  (* not actually a special case of the above *)
  Lemma when_owned_sep l p q Hp Hq : when l p Hp ⊥ owned l q Hq.
  Proof.
    constructor; intros; cbn in H; auto.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split; auto. eapply lte_lifetimes_guar_owned; eauto.
      intros. rewrite H2 in H. destruct H; inversion H.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. rewrite H1 in *. split; auto.
      intros. rewrite H in H0. discriminate H0.
  Qed.

  Lemma when_lifetime_sep n n' p Hp :
    n < n' ->
    when n p Hp ⊥ lifetime_perm n'.
  Proof.
    intros Hlt.
    split; intros [] [] ?.
    - cbn. split.
      + destruct H as (_ & ?). rewrite H; auto. reflexivity.
      + intros. eapply Hp; eauto.
    - destruct H.
      + rewrite H. reflexivity.
      + destruct H. cbn. setoid_rewrite H. split; [| split]; reflexivity.
  Qed.

  Lemma owned_lifetime_sep n n' p Hp :
    p ⊥ lifetime_perm n' ->
    n < n' ->
    owned n p Hp ⊥ lifetime_perm n'.
  Proof.
    intros Hsep Hlt.
    constructor; intros [] [] ?; cbn in *; auto.
    - destruct H as (? & ?). split; auto.
      intros. eapply Hsep. cbn. auto.
    - decompose [and or] H; clear H.
      inversion H0. subst. split; reflexivity.
      split; auto.
      intros. apply H1. lia.
  Qed.

  (* oh. this was not necessary all along *)
  Lemma lifetimes_sep_gen p q l Hp Hq Hsep :
    p ⊥ owned l q Hq ->
    when l p Hp ⊥ owned l (p ** q) (nonLifetime_sep_conj _ _ Hp Hq Hsep).
  Proof.
    intros.
    eapply when_owned_sep.
    (* split; intros. *)
    (* - destruct x, y. cbn in H0. *)
    (*   decompose [and or] H0; [inversion H1; subst; intuition |]. clear H0. *)
    (*   cbn. split; auto. intros []. *)
    (*   + rewrite H0 in H1. inversion H1. *)
    (*   + rewrite H0 in H1. inversion H1. *)
    (* - cbn in H0. destruct x, y. *)
    (*   decompose [and or] H0; [inversion H1; subst; intuition |]; clear H0. *)
    (*   cbn. split; [| split]; auto. *)
    (*   + intros. rewrite H1, H3. auto. *)
    (*   + intros. rewrite H1 in H0. discriminate H0. *)
  Abort.



  Lemma convert p q l Hp Hq Hsep :
    when l p Hp ** owned l (p ** q) (nonLifetime_sep_conj _ _ Hp Hq Hsep) <=
      p ** owned l q Hq.
  Proof.
    split; intros.
    - destruct x. cbn in *.
      decompose [and or] H; auto. split; auto. split; auto.
      eapply when_owned_sep; eauto.
    - destruct x, y. cbn in *.
      destruct H as (? & ? & ?). split; [| split; [| split]]; auto.
      split; auto. rewrite H0. reflexivity.
    - destruct x, y. cbn in H.
      induction H. 2: econstructor 2; eauto.
      clear s s0 s1 s2.
      destruct x, y.
      decompose [and or] H; cbn; subst; try solve [constructor; auto]; clear H.
      rename H0 into Hneq, H1 into Hlen, H2 into Hfin, H4 into Hguar.
      apply Operators_Properties.clos_trans_t1n_iff.
      apply Operators_Properties.clos_trans_t1n_iff in Hguar.

      constructor 2 with (y := (lput s (replace_list_index (lget s) l finished), s0)).
      {
        do 2 right.
        setoid_rewrite lGetPut. rewrite lPutPut.
        split; [| split; [| split]].
        - intros. eapply nth_error_replace_list_index_neq; auto.
          rewrite Hlen.
          apply nth_error_Some. intro. unfold statusOf, Lifetimes in Hfin.
          rewrite Hfin in H0. inversion H0.
        - rewrite Hlen. apply replace_list_index_length. symmetry; auto.
          rewrite <- nth_error_Some. intro. unfold statusOf, Lifetimes in Hfin.
          rewrite Hfin in H. inversion H.
        - apply nth_error_replace_list_index_eq.
        - rewrite replace_list_index_twice. reflexivity.
      }
      rewrite <- (lPutGet s1).
      setoid_rewrite <- (replace_list_index_eq _ (lget s1)).
      2: apply Hfin.

      remember (lput _ _, s0). remember (lput _ _, s2).
      revert s s0 s1 s2 Hneq Hlen Hfin Heqp0 Heqp1. induction Hguar; intros; subst.
      + constructor 1. destruct H; auto.
        do 2 right.
        setoid_rewrite lGetPut. repeat rewrite lPutPut.
        repeat rewrite replace_list_index_twice.
        split; [| split; [| split]]; auto.
        * intros. unfold statusOf, Lifetimes in *.
          assert (l < length (lget s1)).
          { rewrite <- nth_error_Some. intro. rewrite Hfin in H1. inversion H1. }
          rewrite <- nth_error_replace_list_index_neq; auto.
          rewrite <- nth_error_replace_list_index_neq; auto. rewrite Hlen; auto.
        * erewrite <- replace_list_index_length; eauto.
          erewrite <- replace_list_index_length; eauto.
          rewrite Hlen. apply nth_error_Some. intro.
          unfold statusOf, Lifetimes in Hfin. rewrite Hfin in H0. inversion H0.
          apply replace_list_index_length_bound.
        * apply nth_error_replace_list_index_eq.
      + destruct y.
        assert (statusOf l (lget s3) = Some finished).
        {
          destruct H.
          - apply nonLifetime_guar in H; auto. cbn in H.
            rewrite lGetPut in H. rewrite <- H. apply nth_error_replace_list_index_eq.
          - apply nonLifetime_guar in H; auto. cbn in H.
            rewrite lGetPut in H. rewrite <- H. apply nth_error_replace_list_index_eq.
        }
        assert (s3 = lput s3 (replace_list_index (lget s3) l finished)).
        {
          setoid_rewrite <- (lPutGet s3).
          setoid_rewrite <- (replace_list_index_eq _ (lget s3)); eauto.
          rewrite lPutPut, lGetPut. rewrite replace_list_index_twice.
          reflexivity.
        }
        (* rewrite H1 in *. *)
        econstructor 2.
        2: {
          eapply (IHHguar s3 s4 s1 s2); eauto; clear IHHguar.
          - rewrite replace_list_index_eq in Hguar; auto.
            rewrite lPutGet in Hguar.
            apply Operators_Properties.clos_trans_t1n_iff in Hguar.
            pose proof (clos_trans_nonLifetime _ _ Hp Hq _ _ Hguar).
            cbn in H2. rewrite H2. reflexivity.
          - rewrite replace_list_index_eq in Hguar; auto.
            rewrite lPutGet in Hguar.
            apply Operators_Properties.clos_trans_t1n_iff in Hguar.
            pose proof (clos_trans_nonLifetime _ _ Hp Hq _ _ Hguar).
           cbn in H2. setoid_rewrite H2. reflexivity.
          - rewrite H1 at 1; reflexivity.
        }
        clear IHHguar.
        destruct H; auto.
        right. right.
        repeat rewrite lPutPut.
        setoid_rewrite lGetPut.
        repeat rewrite replace_list_index_twice.
        split; [| split; [| split]]; auto.
        * apply nonLifetime_guar in H; auto.
          cbn in H. repeat rewrite lGetPut in H. rewrite H. reflexivity.
        * erewrite <- replace_list_index_length; auto.
          -- symmetry. transitivity (length (lget s1)); auto.
             rewrite replace_list_index_eq in Hguar; auto.
             rewrite lPutGet in Hguar.
             apply Operators_Properties.clos_trans_t1n_iff in Hguar.
             pose proof (clos_trans_nonLifetime _ _ Hp Hq _ _ Hguar).
             cbn in H2. setoid_rewrite H2. reflexivity.
          -- rewrite <- nth_error_Some. intro.
             unfold statusOf, Lifetimes in H0. rewrite H0 in H2. inversion H2.
        * rewrite <- H1. auto.
  Qed.

  (* special case of convert *)
  Lemma convert_bottom p n Hp :
    when n p Hp ** owned n p Hp <= p ** owned n bottom_perm nonLifetime_bottom.
  Proof.
  (*   rewrite <- (sep_conj_perm_bottom p) at 2. eapply convert; auto. *)
  (* Qed. *)
  Abort.

(* Lemma lcurrent_pre_trans' x n1 n2 n3 : *)
(*     lcurrent_pre x n1 n3 -> *)
(*     lcurrent_pre x n1 n2 /\ lcurrent_pre x n2 n3. *)
(* Proof. *)
(*   unfold lcurrent_pre. split. *)
(*   - split. *)
(*     + intro. apply H. *)
  (* Admitted. *)

  (** The naive defn is transitive, at least *)
(*    Program Definition lcurrent n1 n2 : @perm C :=
    {|
      pre x := subsumes n1 n2 (lget x) (lget x);
      rely x y := x = y \/
                    subsumes n1 n2 (lget x) (lget x) /\
                    subsumes n1 n2 (lget y) (lget y);
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; try solve [intuition].
    destruct H, H0; subst; auto.
    right. destruct H, H0. split; eapply subsumes_preorder; eauto; reflexivity.
  Qed.
  Next Obligation.
    constructor; repeat intro; subst; intuition.
  Qed.
  Next Obligation.
    destruct H; subst; auto. destruct H; intuition.
  Qed.

  Lemma lcurrent_transitive n1 n2 n3 :
    lcurrent n1 n3 <= lcurrent n1 n2 ** lcurrent n2 n3.
  Proof.
    constructor; intros; cbn; intuition.
    - destruct H as (? & ? & ?). simpl in *. eapply subsumes_preorder; eauto.
    - destruct H. simpl in *. destruct H, H0; subst; auto. right.
      destruct H, H0. split; auto; eapply subsumes_preorder; eauto.
  Qed.
*)
  Definition lifetime_Perms :=
    meet_Perms (fun Q => exists n : nat, Q = singleton_Perms (lifetime_perm n)).

  Definition when_Perms l P : Perms :=
    meet_Perms (fun R => exists p Hp, p ∈ P /\ R = singleton_Perms (when l p Hp)).

  Definition lfinished_Perms l P : Perms :=
    meet_Perms (fun R => exists p Hp, p ∈ P /\ R = singleton_Perms (lfinished l p Hp)).

  Definition lowned_Perms l P Q : Perms :=
    meet_Perms (fun R => exists r q Hq, R = singleton_Perms (r ** owned l q Hq) /\
                               q ∈ Q /\
                               (forall p, p ∈ P -> forall s, pre r s -> pre p s -> pre q s)).

  Program Definition lowned_Perms' l P Q :=
    {|
      in_Perms x :=
      exists r1 r2 (Hr1 : nonLifetime r1) (Hr2 : nonLifetime r2) (Hr2' : guar_inv r2)
      (* and r2 is "minimal" *),
        r1 ⊥ owned l r2 Hr2 /\
        r2 ∈ Q /\
        r1 ** owned l r2 Hr2 <= x /\
          (forall p, p ∈ P ->
                p ⊥ r1 ** owned l r2 Hr2 ->
                exists q, q ∈ Q /\
                       sep_step r2 q /\ (* means that q is also nonLifetime since r2 is *)
                       (* r1 ⊥ p /\ (* this can't be true for all p... *) *)
                       (forall c1 c2, pre p ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                 pre r1 ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                 pre q ((lput c1 (replace_list_index (lget c1) l finished)), c2)));
    |}.
  Next Obligation.
    destruct H as (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep & Hr2'' & Hlte & H).
    exists r1, r2, Hr1, Hr2, Hr2'. split; [| split; [| split]]; auto. etransitivity; eauto.
  Qed.

  Lemma when_perm_Perms l p Hp P :
    p ∈ P ->
    when l p Hp ∈ when_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p, Hp. split; eauto.
    - cbn. reflexivity.
  Qed.

  Lemma lfinished_perm_Perms l p Hp P :
    p ∈ P ->
    lfinished l p Hp ∈ lfinished_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p, Hp. split; eauto.
    - cbn. reflexivity.
  Qed.

  (* Lemma lowned_perm_Perms l p Hp P : *)
  (*   p ∈ P -> *)
  (*   owned l p Hp ∈ lowned_Perms' l bottom_Perms P. *)
  (* Proof. *)
  (*   intros H. *)
  (*   exists bottom_perm, p, Hp. split. *)
  (*   - rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity. *)
  (*   - intros ? ?. exists p. split; [| split]; auto. reflexivity. *)
  (*     intros. cbn in *. *)
  (* Qed. *)


  (*
    (* TODO: need to add pre_perm *)
  Lemma lowned_perm_Perms l ls Hsub p Hp P :
    p ∈ P ->
    owned l ls Hsub p Hp ∈ lowned_Perms' l ls Hsub P P.
  Proof.
    cbn. intros. cbn. exists p0. split; [| split]; auto. reflexivity.
    - do 3 eexists. split; [| split]. reflexivity.
      apply H.
      intros. apply H1.
    - exists (fun _ H => H). red. rewrite restrict_same.
      rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity.
  Qed.
   *)

  (* returns the new lifetime *)
  Definition beginLifetime : itree (sceE Si) nat :=
    s <- trigger (Modify id);;
    trigger (Modify (fun s => lput s ((lget s) ++ [current])));;
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

  Lemma sep_step_owned_finished l p Hp :
    SepStep.sep_step
      (owned l p Hp)
      (lfinished l p Hp).
  Proof.
    repeat intro. constructor.
    - intros [] [] ?. cbn in *. apply H in H0. cbn in H0. intuition.
      rewrite H1. reflexivity.
    - intros [] [] ?. cbn in *. destruct H0. rewrite H0. reflexivity.
      destruct H0 as (? & ? & ?). apply H. cbn. rewrite H0 in H1.
      setoid_rewrite H0.
      right. intuition.
      do 2 (rewrite replace_list_index_eq; auto).
      rewrite <- H0.
      do 2 rewrite lPutGet; auto.
  Qed.

  Lemma sep_step_beginLifetime n :
    sep_step (lifetime_perm n)
             (owned n bottom_perm nonLifetime_bottom ** lifetime_perm (n + 1)).
  Proof.
    apply sep_step_rg.
    - intros [si ss] [si' ss'] ?. induction H; try solve [etransitivity; eauto].
      destruct H.
      + destruct x, y. cbn in *. destruct H.
        * inversion H. subst.
          split; [| split]; auto; try reflexivity.
          eexists. rewrite lPutGet. reflexivity.
        * destruct H as (? & ? & ? & ?). split.
          -- inversion H2. subst. rewrite (replace_list_index_eq _ (lget s1)) in H4; auto.
             rewrite lPutGet in H4. rewrite <- H4.
             eexists. reflexivity.
          -- intros. apply H. lia.
      + destruct x, y. cbn in *. intuition.
    - intros [si ss] [si' ss'] (Hlen & Hlater). cbn in *.
      split; split; auto. intros. apply Hlater. lia.
  Qed.

  Lemma typing_begin :
    typing lifetime_Perms
           (fun l _ => lowned_Perms' l bottom_Perms bottom_Perms * lifetime_Perms)
           beginLifetime
           (Ret tt).
  Proof.
    intros p' c1 c2 (? & (l & ?) & Hlte) Hpre; subst.
    unfold beginLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    rewritebisim @bind_trigger.
    econstructor; auto.
    {
      apply Hlte in Hpre. cbn in Hpre. subst. apply Hlte. cbn.
      rewrite lGetPut.
      split.
      - eexists. reflexivity.
      - intros. symmetry. apply nth_error_app1; auto.
    }
    etransitivity. apply sep_step_lte'. apply Hlte. apply sep_step_beginLifetime.

    apply Hlte in Hpre. cbn in Hpre.
    econstructor.
    - cbn. do 2 rewrite lGetPut.
      split; [| split]; auto.
      + unfold statusOf. apply nth_error_app_last; auto.
      + rewrite app_length. rewrite Hpre. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_bottom. lia.
    - apply sep_conj_Perms_perm.
      + cbn. exists bottom_perm, bottom_perm, nonLifetime_bottom, nonLifetime_bottom, guar_inv_bottom.
        split; [| split]; auto. symmetry. apply separate_bottom.
        split; intros.
        * rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom.
          rewrite Hpre. reflexivity.
        * exists bottom_perm. split; auto. split. reflexivity.
          intros. cbn. auto.
      + eexists. split. eexists. reflexivity.
        cbn. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_bottom. lia.
  Qed.

  Lemma typing_end l P Q :
    typing (P * (lowned_Perms' l P Q))
           (fun _ _ => lfinished_Perms l Q)
           (endLifetime l)
           (Ret tt).
  Proof.
    intros p' c1 c2 (p & lowned' & Hp & H & Hsep & Hlte) Hpre. cbn in H.
    destruct H as (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf).
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    pose proof Hpre as Hpre''.
    apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
    apply Hlte' in Hpre. destruct Hpre as (_ & H & _).
    cbn in H. setoid_rewrite H.
    rewritebisim @bind_trigger.
    specialize (Hf _ Hp). destruct Hf as (q & Hq & Hsep_step & Hpre).
    { apply Hlte in Hpre''. destruct Hpre'' as (? & ? & ?).
      eapply separate_antimonotone; eauto. }
    econstructor; unfold id. eauto.
    cbn in *. apply Hlte. constructor 1. right.
    apply Hlte'. constructor 1. right. right.
    {
      repeat rewrite lGetPut.
      split; [| split; [| split]].
      - intros. apply nth_error_replace_list_index_neq; auto.
        apply nth_error_Some. intro.
        unfold statusOf, Lifetimes in H. rewrite H1 in H. inversion H.
      - apply replace_list_index_length; auto. apply nth_error_Some. intro.
        unfold statusOf, Lifetimes in H. rewrite H0 in H. inversion H.
      - unfold statusOf. apply nth_error_replace_list_index_eq.
      - rewrite lPutPut, replace_list_index_twice. reflexivity.
    }
    2: {
      econstructor. 2: apply lfinished_perm_Perms; eauto.
      Unshelve. 2: eapply nonLifetime_sep_step; eauto.
      cbn. rewrite lGetPut.
      split. apply nth_error_replace_list_index_eq.
      apply Hpre; auto.
      - apply Hlte in Hpre''. cbn in H. rewrite replace_list_index_eq; auto.
        rewrite lPutGet. apply Hpre''.
      - apply Hlte in Hpre''. destruct Hpre'' as (_ & Hpre'' & _).
        apply Hlte' in Hpre''.
        rewrite replace_list_index_eq; auto.
        rewrite lPutGet. apply Hpre''.
    }
    eapply SepStep.sep_step_lte; eauto.
    eapply SepStep.sep_step_lte. apply lte_r_sep_conj_perm.
    eapply SepStep.sep_step_lte; eauto.
    eapply SepStep.sep_step_lte. apply lte_r_sep_conj_perm.
    etransitivity. 2: apply sep_step_owned_finished.
    apply owned_sep_step; auto.
  Qed.

  Lemma partial l P Q R :
    P * lowned_Perms' l (P * Q) R ⊨ lowned_Perms' l Q R.
  Proof.
    intros p0 (p & powned & Hp & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte).
    assert (Hp' : nonLifetime p) by admit.
    exists (p ** r1), r2. eexists.
    {
      apply nonLifetime_sep_conj; auto.
      eapply separate_antimonotone. apply Hsep.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
    }
    exists Hr2, Hr2'. split.
    {
      symmetry. apply separate_sep_conj_perm.
      - symmetry. eapply separate_antimonotone; eauto.
        etransitivity; eauto. apply lte_r_sep_conj_perm.
      - symmetry. auto.
      - symmetry. eapply separate_antimonotone; eauto.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
    }
    split; [| split]; auto.
    {
      etransitivity; eauto. rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; auto; reflexivity.
    }
    intros q Hq Hsep''.
    rewrite sep_conj_perm_assoc in Hsep''.
    specialize (Hf (p ** q)).
    destruct Hf as (r & Hr & Hsep_step & Hpre).
    - apply sep_conj_Perms_perm; auto. symmetry.
      eapply separate_antimonotone; eauto.
      apply lte_l_sep_conj_perm.
    - symmetry. apply separate_sep_conj_perm.
      + symmetry. eapply separate_antimonotone; eauto.
      + symmetry. eapply separate_antimonotone; eauto. apply lte_r_sep_conj_perm.
      + eapply separate_antimonotone; eauto. apply lte_l_sep_conj_perm.
    - exists r. split; [| split]; auto.
      intros. apply Hpre.
      + destruct H0. split; [| split]; auto.
        symmetry. eapply separate_antimonotone; eauto. apply lte_l_sep_conj_perm.
      + apply H0.
  Admitted.

  Lemma owned_sep l p Hp q (Hq : nonLifetime q) (Hp' : guar_inv p) (Hq' : guar_inv q) :
    q ⊥ owned l p Hp ->
    q ⊥ p.
  Proof.
    split; intros [] [] ?.
    - eapply nonLifetime_rely' with (s1 := (replace_list_index (lget s) l finished))
                                    (s2 := (replace_list_index (lget s1) l finished)); auto.
      apply H. cbn. right.
      pose proof H0 as Hguar.
      apply nonLifetime_guar in H0; auto. cbn in H0. setoid_rewrite H0.
      repeat rewrite lGetPut. repeat rewrite replace_list_index_twice.
      repeat rewrite lPutPut.
      split; [| split; [| split]]; auto.
      + apply nth_error_replace_list_index_eq.
      + rewrite <- H0. auto.
    - eapply nonLifetime_rely' with (s1 := (replace_list_index (lget s) l finished))
                                    (s2 := (replace_list_index (lget s1) l finished)); auto.
      destruct H.
      specialize (sep_r (lput s (replace_list_index (lget s) l finished), s0)
                        (lput s1 (replace_list_index (lget s1) l finished), s2)).
      apply sep_r.
      2: { rewrite lGetPut. apply nth_error_replace_list_index_eq. }
      apply Hq'; auto.
  Qed.

  Lemma sep_when l p q Hp (Hq : nonLifetime q) :
    p ⊥ q ->
    when l p Hp ⊥ q.
  Proof.
    intros. split; intros [] [] ?.
    - cbn. split; auto.
      + pose proof (nonLifetime_guar _ Hq _ _ H0). cbn in H1. rewrite H1.
        reflexivity.
      + intros. apply H; auto.
    - destruct H0. rewrite H0. reflexivity.
      apply H. apply H0.
  Qed.

  Lemma sep_owned l p q r (Hp : nonLifetime p) Hr Hq Hqr :
    p ⊥ q ->
    p ⊥ owned l r Hr ->
    p ⊥ owned l (q ** r) (nonLifetime_sep_conj _ _ Hq Hr Hqr).
  Proof.
    intros Hpq Hpo.
    split; intros [] [] ?.
    - cbn in *. destruct H. rewrite H. reflexivity.
      destruct H as (? & ? & ? & ?).
      remember (lput s _, _). remember (lput s1 _, _).
      revert s s0 s1 s2 H H0 H1 Heqp0 Heqp1. induction H2; intros; subst.
      + destruct H.
        * eapply nonLifetime_rely'; eauto. apply Hpq. eauto.
        * apply Hpo. cbn. right. split; [| split]; auto.
      + destruct y.
        apply clos_trans_nonLifetime in H2_; auto. cbn in H2_. rewrite lGetPut in H2_.
        pose proof (lPutGet s3). rewrite <- H2_ in H2. rewrite <- H2 in IHclos_trans1.
        assert (l < length (lget s)).
        {
          unfold statusOf, Lifetimes in *.
          rewrite H0. apply nth_error_Some. intro. rewrite H3 in H1. inversion H1.
        }
        etransitivity.
        {
          eapply (IHclos_trans1 s s0 (lput s3 (replace_list_index (lget s3) l finished)) s4); eauto.
          - intros. rewrite lGetPut. setoid_rewrite <- H2_. rewrite replace_list_index_twice.
            unfold statusOf, Lifetimes in *.
            rewrite <- nth_error_replace_list_index_neq; auto.
          - rewrite lGetPut. rewrite <- H2. rewrite lGetPut. rewrite replace_list_index_twice.
            apply replace_list_index_length; auto.
          - rewrite lGetPut. apply nth_error_replace_list_index_eq.
          - rewrite lGetPut, lPutPut. setoid_rewrite <- H2_.
            repeat rewrite replace_list_index_twice. reflexivity.
        }
        {
          setoid_rewrite <- H2_. rewrite replace_list_index_twice.
          apply IHclos_trans2; auto.
          - intros. rewrite lGetPut.
            unfold statusOf, Lifetimes in *.
            rewrite <- nth_error_replace_list_index_neq; auto.
          - rewrite lGetPut.
            symmetry. apply replace_list_index_length; auto. rewrite <- H0. auto.
          - rewrite lGetPut, lPutPut.
            repeat rewrite replace_list_index_twice. rewrite H2_. rewrite lPutGet. reflexivity.
        }
    - split. pose proof (nonLifetime_guar _ Hp _ _ H). cbn in H0. rewrite H0. reflexivity.
      intros. split.
      apply Hpq; auto.
      destruct Hpo. specialize (sep_r _ _ H). cbn in sep_r. apply sep_r; auto.
  Qed.

  (* P initially = write_Perms p
     inside the owned P = read_Perms p

keep the permission on the value separate?
   *)
  Lemma foo l P Q R :
    P * lowned_Perms' l Q R ⊨
    when_Perms l P * lowned_Perms' l (when_Perms l P * Q) (P * R).
  Proof.
    intros p0 (p & powned & Hp & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte).
    assert (Hp' : nonLifetime p) by admit.
    assert (Hp'' : guar_inv p) by admit.
    exists (when l p Hp').
    assert (Hpr2 : p ⊥ r2).
    {
      eapply owned_sep; auto.
      eapply separate_antimonotone; eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
    }
    eexists (r1 ** owned l (p ** r2) (nonLifetime_sep_conj _ _ Hp' Hr2 Hpr2)).
    split; [| split; [| split]]; auto.
    - apply when_perm_Perms; auto.
    - exists r1, (p ** r2), Hr1, (nonLifetime_sep_conj _ _ Hp' Hr2 Hpr2), (guar_inv_sep_conj_perm _ _ Hp'' Hr2').
      split; [| split; [| split]].
      3: reflexivity.
      {
        apply sep_owned; auto. symmetry.
        eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      }
      {
        apply sep_conj_Perms_perm; auto.
      }
      intros p1 (pw & q & (? & (pr & Hpr' & Hpr & ?) & Hlte''') & Hq' & Hsep''' & Hlte'') Hsep''; subst.
      cbn in Hlte'''.
      specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
      {
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        eapply separate_antimonotone in Hsep''; eauto.
        2: apply lte_r_sep_conj_perm.
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        apply sep_conj_perm_monotone. reflexivity.
        apply owned_monotone. apply lte_r_sep_conj_perm.
      }
      exists (pr ** r). split; [| split].
      + apply sep_conj_Perms_perm; auto.
        symmetry.
        apply Hsep_step. symmetry.
        (* we don't have p ⊥ r, best we can do is that p ⊥ owned r2, and r2 ~> r *)
        admit.
      + admit. (* p ~ pr should be ok if they're both pointer permissions, but them being separate from r/r2 is a problem. we only have that p ⊥ owned r2 *)
      + intros. split; [| split]; auto.
        * apply Hlte'' in H. destruct H as (? & ? & ?).
          apply Hlte''' in H. cbn in H.
          rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
          admit. (* should be ok if pr is a ptr permission *)
        * apply Hpre; auto. apply Hlte''; auto.
        * admit. (* we sort of have owned l r2 ⊥ when l r, but thta's true for any permissions inside the when and owned *)
    - apply separate_sep_conj_perm.
      + apply sep_when; auto. eapply separate_antimonotone. apply Hsep. etransitivity; eauto.
        apply lte_l_sep_conj_perm.
      + apply when_owned_sep.
      + symmetry. apply sep_owned; auto. symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
    - etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].
      apply convert.
  Qed.

  (* Require Import Heapster.Typing. *)

  (* Definition startLifetime : itree (sceE C) nat := *)
  (*   ret 0. *)
End LifetimePerms.
