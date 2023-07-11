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
     Eq.Eqit.

From Heapster Require Import
     Utils
     Permissions
     Lifetime
     Typing
     SepStep.

From Paco Require Import
     paco.

Import ListNotations.
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
        (forall n', n' >= n -> statusOf n' (lget x) = statusOf n' (lget y));

      guar '(x, _) '(y, _) :=
      (exists (ls : Lifetimes), y = lput x ls) /\
        (forall l, l < n ->
              statusOf l (lget x) = statusOf l (lget y)) /\
        Lifetimes_lte (lget x) (lget y);
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
    - destruct x, y, z. destruct H as ((? & ?) & ? & ?), H0 as ((? & ?) & ? & ?). subst.
      split.
      + eexists. rewrite lPutPut. reflexivity.
      + split; repeat intro; transitivity (statusOf l (lget (lput s x))); eauto.
  Qed.

  Definition lifetime_Perms :=
    meet_Perms (fun Q => exists n : nat, Q = singleton_Perms (lifetime_perm n)).

  Definition nonLifetime p : Prop :=
    forall n, p ⊥ lifetime_perm n.
  Lemma nonLifetime_guar p x y :
    nonLifetime p ->
    guar p x y ->
    lget (fst x) = lget (fst y).
  Proof.
    intros Hp Hguar. specialize (Hp 0). destruct Hp.
    specialize (sep_r _ _ Hguar).
    cbn in sep_r. destruct x, y.
    cbn. destruct sep_r as (_ & H).
    unfold statusOf in *.
    apply nth_error_eq. intros. apply H; lia.
  Qed.

  Definition pre_inv (p : @perm (Si * Ss)) : Prop :=
    forall si ss l s,
      pre p (si, ss) ->
      pre p
        (lput si (replace_list_index (lget si) l s), ss).
  Lemma pre_inv_sep_conj_perm p q (Hp : pre_inv p) (Hq : pre_inv q) :
    pre_inv (p ** q).
  Proof.
    repeat intro. destruct H as (Hp' & Hq' & Hsep).
    split; [| split]; auto.
  Qed.

  Lemma pre_inv_bottom :
    pre_inv bottom_perm.
  Proof.
    repeat intro. auto.
  Qed.

  Definition rely_inv (p : @perm (Si * Ss)) : Prop :=
    forall si si' ss ss' s s',
      Lifetimes_lte s s' ->
      rely p (si, ss) (si', ss') ->
      rely p
        (lput si s, ss)
        (lput si' s', ss').
        (* (lput si s, ss) *)
        (* (lput si' s, ss'). *)

  Lemma rely_inv_sep_conj_perm p q (Hp : rely_inv p) (Hq : rely_inv q) :
    rely_inv (p ** q).
  Proof.
    repeat intro. destruct H0. split; auto.
  Qed.

  Lemma rely_inv_bottom :
    rely_inv bottom_perm.
  Proof.
    repeat intro. cbn. auto.
  Qed.

  (* Lemma rely_inv_reverse p (si si' : Si) (ss ss' : Ss) l s : *)
  (*   rely_inv p -> *)
  (*   Lifetimes_lte (lget si) (lget si') -> *)
  (*   rely p *)
  (*     (lput si (replace_list_index (lget si) l s), ss) *)
  (*     (lput si' (replace_list_index (lget si') l s), ss') -> *)
  (*   rely p (si, ss) (si', ss'). *)
  (* Proof. *)
  (*   intros Hp Hlte Hrely. *)
  (*   specialize (Hlte l). *)
  (*   rewrite <- (lPutGet si), <- (lPutGet si'). *)
  (*   destruct x, y. cbn. *)
  (*   apply *)
  (* Qed. *)



  (* Lemma rely_inv_reverse p si ss si' ss' l s : *)
  (*   lget si = lget si' -> *)
  (*   rely_inv p -> *)
  (*   rely p *)
  (*     (lput si (replace_list_index (lget si) l s), ss) *)
  (*     (lput si' (replace_list_index (lget si') l s), ss') -> *)
  (*   rely p (si, ss) (si', ss'). *)
  (* Proof. *)
  (*   intros Heq Hinv Hp. *)
  (*   rewrite <- (lPutGet si), <- (lPutGet si'). *)
  (*   rewrite Heq. *)
  (*   apply Hinv. *)
  (*   eapply Hinv in Hp. *)
  (*   rewrite !lPutPut in Hp. rewrite !lGetPut in Hp. *)
  (*   do 2 rewrite lPutPut in Hp. apply Hp. *)
  (* Qed. *)

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

  Lemma guar_inv_bottom :
    guar_inv bottom_perm.
  Proof.
    repeat intro. cbn in *. inversion H. subst. reflexivity.
  Qed.


  (*
  Lemma nonLifetime_rely p :
    nonLifetime p ->
    forall si si' ss ss' l s,
      rely p (si, ss) (si', ss') ->
      rely p
        (lput si (replace_list_index (lget si) l s), ss)
        (lput si' (replace_list_index (lget si') l s), ss').
  Proof.
    intros. destruct (H 0) as (? & _).
    apply sep_l.
    cbn. split; [| split].
    - setoid_rewrite lPutPut. admit.
    - lia.
    - intros.

    etransitivity.
    {
      apply (sep_l (lput si (replace_list_index (lget si) l s), ss) (si, ss)).
      cbn. split; [| split].
      - setoid_rewrite lPutPut. eexists. symmetry. apply lPutGet.
      - intros. lia.
      - intros.
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
   *)

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

  Lemma nonLifetime_sep_conj_perm p q (Hp : nonLifetime p) (Hq : nonLifetime q) :
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

  Definition nonLifetime_Perms P : Prop :=
    forall p,
      p ∈ P ->
      exists p',
        p' ∈ P /\
          p' <= p /\
          nonLifetime p' /\
          rely_inv p' /\
          guar_inv p' /\
          pre_inv p'.

  Lemma nonLifetime_Perms_bottom :
    nonLifetime_Perms bottom_Perms.
  Proof.
    repeat intro. exists bottom_perm. split; [| split; [| split; [| split; [| split]]]]; auto.
    apply bottom_perm_is_bottom.
    apply nonLifetime_bottom.
    apply rely_inv_bottom.
    apply guar_inv_bottom.
    apply pre_inv_bottom.
  Qed.

  Lemma nonLifetime_Perms_sep_conj_Perms P Q :
    nonLifetime_Perms P ->
    nonLifetime_Perms Q ->
    nonLifetime_Perms (P * Q).
  Proof.
    intros HP HQ p0 (p & q & Hp & Hq & Hsep & Hlte).
    destruct (HP _ Hp) as (p' & Hp' & Hpp' & Hnlp & Hrelyp & Hguarp & Hprep).
    destruct (HQ _ Hq) as (q' & Hq' & Hqq' & Hnlq & Hrelyq & Hguarq & Hpreq).
    assert (p' ⊥ q').
    {
      eapply separate_antimonotone. 2: apply Hqq'.
      symmetry. eapply separate_antimonotone. 2: apply Hpp'.
      symmetry. auto.
    }
    exists (p' ** q'). split; [| split; [| split; [| split; [| split]]]].
    - apply sep_conj_Perms_perm; auto.
    - etransitivity; eauto. apply sep_conj_perm_monotone; auto.
    - apply nonLifetime_sep_conj_perm; auto.
    - apply rely_inv_sep_conj_perm; auto.
    - apply guar_inv_sep_conj_perm; auto.
    - apply pre_inv_sep_conj_perm; auto.
  Qed.

  (** * when *)
  (* Note: does not have permission to start or end the lifetime [n] *)
  Program Definition when
          (l : nat)
          (p : @perm (Si * Ss)) : perm :=
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
    - right. intuition; etransitivity; eauto.
  Qed.
  Next Obligation.
    intros. respects. apply H0.
    destruct H2.
    - rewrite H2 in H.
      destruct (statusOf l (lget s1)); auto; inversion H.
    - rewrite H2 in H.
      destruct (statusOf l (lget s1)); [destruct s3 |]; auto; inversion H.
  Qed.

  Definition when_Perms l P : Perms :=
    meet_Perms (fun R => exists p, p ∈ P /\ R = singleton_Perms (when l p)).

  Lemma when_perm_Perms l p P :
    p ∈ P ->
    when l p ∈ when_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p. split; eauto.
    - cbn. reflexivity.
  Qed.

  Lemma when_monotone n p1 p2 : p1 <= p2 -> when n p1 <= when n p2.
  Proof.
    intros. destruct H. constructor; simpl; intros.
    - destruct x. auto.
    - destruct x, y. destruct H; auto.
    - destruct x, y. intuition.
  Qed.

  (* the rely requires that l moves forwards *)
  Lemma when_bottom l :
    when l bottom_perm <= bottom_perm.
  Proof.
    split.
    - intros []. cbn; auto.
    - intros [] []. cbn; auto. admit.
    - intros [] []. cbn; intros; auto. destruct H; auto. apply H.
  Abort.

  Lemma sep_when l p q (Hq : nonLifetime q) :
    p ⊥ q ->
    when l p ⊥ q.
  Proof.
    intros. split; intros [] [] ?.
    - cbn. split; auto.
      + pose proof (nonLifetime_guar _ _ _ Hq H0). cbn in H1. rewrite H1.
        reflexivity.
      + intros. apply H; auto.
    - destruct H0. rewrite H0. reflexivity.
      apply H. apply H0.
  Qed.

  (*
  Lemma when_lifetime_sep n n' p :
    n < n' ->
    when n p ⊥ lifetime_perm n'.
  Proof.
    intros Hlt.
    split; intros [] [] ?.
    - cbn. split.
      + destruct H as (_ & ? & _). rewrite H; auto. reflexivity.
      + intros. eapply Hp; eauto.
    - destruct H.
      + rewrite H. reflexivity.
      + destruct H. cbn. setoid_rewrite H. split; [| split]; reflexivity.
  Qed.
   *)

  Lemma when_nonLifetime l p (Hp : nonLifetime p) :
    nonLifetime (when l p).
  Proof.
    repeat intro. split; intros [] [] ?.
    - cbn. split.
      + apply H.
      + intros. eapply Hp; eauto.
    - destruct H.
      + rewrite H. reflexivity.
      + destruct H. cbn. setoid_rewrite H. split; [| split]; reflexivity.
  Qed.

  (* Lemma when_rely l p (Hp : rely_inv p) : *)
  (*   rely_inv (when l p). *)
  (* Proof. *)
  (*   intros si si' ss ss' s s' Hlte [Hl Hrely]. *)
  (*   split. { rewrite !lGetPut. apply Hlte. } *)
  (*   rewrite lGetPut. intros. apply Hp; auto. *)
  (*   apply Hrely. destruct H. *)
  (*   - left. apply H *)
  (* Qed. *)

  Lemma when_preserves_sep l p q :
    p ⊥ q -> when l p ⊥ when l q.
  Proof.
    intros Hsep.
    split; intros [] [] ?.
    - destruct H.
      + inversion H. subst. reflexivity.
      + destruct H as (? & ? & ?).
        cbn. rewrite H. split. reflexivity.
        intros. apply Hsep. auto.
    - destruct H.
      + inversion H. subst. reflexivity.
      + destruct H as (? & ? & ?).
        cbn. rewrite H. split. reflexivity.
        intros. apply Hsep. auto.
  Qed.

  Lemma when_sep_conj_perm_dist l p q (Hsep : p ⊥ q) :
    when l p ** when l q <= when l (p ** q).
  Proof.
    split; intros.
    - destruct x. cbn in *. split; [| split]; try solve [apply H].
      apply when_preserves_sep; auto.
    - destruct x, y. destruct H. split; split; auto; apply H0; auto.
    - induction H.
      + destruct x, y. destruct H.
        * cbn in *. destruct H; auto.
          destruct H as (? & ? & ?). right.
          split; [| split]; auto. constructor. left. auto.
        * cbn in *. destruct H; auto.
          destruct H as (? & ? & ?). right.
          split; [| split]; auto. constructor. right. auto.
      + etransitivity; eauto.
  Qed.

  Lemma when_sep_conj_Perms_dist l P Q :
    when_Perms l (P * Q) ⊨ when_Perms l P * when_Perms l Q.
  Proof.
    intros x (? & ((pq & Hpq & ?) & Hlte)). subst. cbn in Hlte.
    destruct Hpq as (p & q & Hp & Hq & Hsep & Hlte').
    exists (when l p), (when l q).
    split; [| split; [| split]]; try solve [apply when_perm_Perms; auto].
    - apply when_preserves_sep; auto.
    - etransitivity; eauto.
      etransitivity. 2: apply when_monotone; eauto.
      apply when_sep_conj_perm_dist; auto.
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
  (* Next Obligation. *)
  (*   destruct x, y. *)
  (*   destruct H. rewrite <- H. auto. *)
  (* Qed. *)

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
          (p : @perm (Si * Ss)) : perm :=
    {|
      pre x :=
      let '(si, _) := x in
      Some finished = statusOf l (lget si) /\
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
    - right. intuition; etransitivity; eauto.
  Qed.
  Next Obligation.
    rewrite <- H0 in H.
    destruct (statusOf l (lget s)); [destruct s3 |]; auto; try inversion H.
    split; auto. respects.
  Qed.

  Lemma lfinished_monotone l p q :
    p <= q -> lfinished l p <= lfinished l q.
  Proof.
    split.
    - intros [] ?. split. apply H0.
      apply H. apply H0.
    - intros [] [] ?. split. apply H0. intros. apply H. apply H0. auto.
    - intros [] [] ?. cbn in *. destruct H0; auto. destruct H0 as (? & ? & ?).
      right. split; [| split]; auto.
      apply H; auto.
  Qed.

  Lemma lfinished_separate l p q :
    p ⊥ q -> lfinished l p ⊥ lfinished l q.
  Proof.
    split; intros [] [] ?.
    - destruct H0. rewrite H0. reflexivity.
      destruct H0 as (? & ? & ?).
      split. rewrite H0. reflexivity.
      intros. apply H; auto.
    - destruct H0. rewrite H0. reflexivity.
      destruct H0 as (? & ? & ?).
      split. rewrite H0. reflexivity.
      intros. apply H; auto.
  Qed.

  Lemma lfinished_separate' l p q (Hq : nonLifetime q) :
    p ⊥ q -> lfinished l p ⊥ q.
  Proof.
    split; intros [] [] ?.
    - cbn. split.
      + eapply nonLifetime_guar in Hq; eauto. cbn in Hq. rewrite Hq. reflexivity.
      + intros. apply H. auto.
    - destruct H0. rewrite H0. reflexivity.
      destruct H0 as (? & ? & ?).
      apply H; auto.
  Qed.

  Lemma lfinished_sep_conj_perm_dist l p q :
    lfinished l p ** lfinished l q <= lfinished l (p ** q).
  Proof.
    split.
    - intros [] ?. destruct H as (? & ? & ? & ?).
      split; [| split]; cbn; auto.
      apply lfinished_separate; auto.
    - intros [] [] ?. destruct H.
      split; split; auto; apply H0; auto.
    - intros. induction H.
      2: etransitivity; eauto.
      destruct x, y. cbn in *.
      destruct H; destruct H; auto; destruct H as (? & ? & ?); right; (split; [| split]; auto).
      + constructor. left. auto.
      + constructor. right. auto.
  Qed.

  Lemma when_finished_sep l p q : when l p ⊥ lfinished l q.
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

  Lemma when_owned_sep l p q Hq : when l p ⊥ owned l q Hq.
  Proof.
    constructor; intros; cbn in H; auto.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split; auto. eapply lte_lifetimes_guar_owned; eauto.
      intros. rewrite H2 in H. destruct H; inversion H.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. rewrite H1 in *. split; auto.
      intros. rewrite H in H0. discriminate H0.
  Qed.

  Lemma owned_lifetime_sep n n' p Hp :
    p ⊥ lifetime_perm n' ->
    n < n' ->
    owned n p Hp ⊥ lifetime_perm n'.
  Proof.
    intros Hsep Hlt.
    constructor; intros [] [] ?; cbn in *; auto.
    - destruct H as (? & ? & ?). split; auto.
      intros. eapply Hsep. cbn. auto.
    - decompose [and or] H; clear H.
      inversion H0. subst. split; reflexivity.
      split; auto.
      intros. apply H1. lia.
  Qed.

  (* note: just lifting this to Perms doesn't work, we need a few additional assumptions like
     that there are unique smallest perms in the sets (see the ptr version) *)
  Lemma convert p q l Hp Hq Hsep :
    when l p ** owned l (p ** q) (nonLifetime_sep_conj_perm _ _ Hp Hq Hsep) <=
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
    when n p ** owned n p Hp <= p ** owned n bottom_perm nonLifetime_bottom.
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
  Definition lfinished_Perms l P : Perms :=
    meet_Perms (fun R => exists p, p ∈ P /\ R = singleton_Perms (lfinished l p)).

  Program Definition lowned_Perms l P Q :=
    {|
      in_Perms x :=
        (* [r1] should always be either bottom or a [when l p] *)
        exists r1 r2 (Hsepr1 : forall r H, r1 ⊥ owned l r H) (Hnlr1 : nonLifetime r1)
          (Hnlr2 : nonLifetime r2) (Hrelyr2 : rely_inv r2) (Hguarr2 : guar_inv r2),
        r2 ∈ Q /\
        r1 ** owned l r2 Hnlr2 <= x /\
          (forall p, p ∈ P ->
                p ⊥ r1 ** owned l r2 Hnlr2 ->
                exists q, q ∈ Q /\ (* also that q is minimal *)
                       sep_step r2 q /\ (* means that q is also nonLifetime since r2 is *)
                       (forall c1 c2, pre p ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                 pre r1 ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                 pre q ((lput c1 (replace_list_index (lget c1) l finished)), c2)));
    |}.
  Next Obligation.
    rename H into r1, H1 into r2, H2 into Hsepr1, H3 into Hnlr1, H4 into Hnlr2, H5 into Hrelyr2, H6 into Hguarr2, H7 into Hr2, H8 into Hlte, H9 into Hpre.
    exists r1, r2, Hsepr1, Hnlr1, Hnlr2, Hrelyr2, Hguarr2. split; [| split]; auto. etransitivity; eauto.
  Qed.

  Lemma lfinished_perm_Perms l p P :
    p ∈ P ->
    lfinished l p ∈ lfinished_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p. split; eauto.
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

  Lemma sep_step_owned_finished l p Hp :
    sep_step
      (owned l p Hp)
      (lfinished l p).
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
        * destruct H as (? & ? & ? & ?). split; [| split].
          -- inversion H2. subst. rewrite (replace_list_index_eq _ (lget s1)) in H4; auto.
             rewrite lPutGet in H4. rewrite <- H4.
             eexists. reflexivity.
          -- intros. apply H. lia.
          -- intros. intro l. destruct (Nat.eq_decidable n l).
             ++ subst. rewrite H1.
                destruct (statusOf l (lget s)); [destruct s3 |]; cbn; auto.
             ++ rewrite H; auto; reflexivity.
      + destruct x, y. cbn in *. intuition.
    - intros [si ss] [si' ss'] (Hlen & Hlater). cbn in *.
      split; split; auto. intros. apply Hlater. lia.
  Qed.

  Lemma typing_begin :
    typing lifetime_Perms
      (fun l _ => lowned_Perms l bottom_Perms bottom_Perms * lifetime_Perms)
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
      split; [| split].
      - eexists. reflexivity.
      - intros. symmetry. apply nth_error_app1; auto.
      - intros. apply Lifetimes_lte_app. reflexivity.
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
      + exists bottom_perm, bottom_perm. eexists.
        { intros. symmetry. apply separate_bottom. }
        exists nonLifetime_bottom, nonLifetime_bottom, rely_inv_bottom, guar_inv_bottom.
        split; [| split].
        * cbn; auto.
        * rewrite Hpre. rewrite sep_conj_perm_commut. apply sep_conj_perm_bottom.
        * exists bottom_perm. split; auto. split. reflexivity.
          intros. cbn. auto.
      + eexists. split. eexists. reflexivity.
        cbn. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_bottom. lia.
  Qed.

  Lemma typing_end l P Q :
    typing (P * (lowned_Perms l P Q))
           (fun _ _ => lfinished_Perms l Q)
           (endLifetime l)
           (Ret tt).
  Proof.
    intros p' c1 c2 (p & lowned' & Hp & H & Hsep & Hlte) Hpre. cbn in H.
    destruct H as (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf).
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
      cbn. rewrite lGetPut.
      split. symmetry. apply nth_error_replace_list_index_eq.
      apply Hpre; auto.
      - apply Hlte in Hpre''. cbn in H. rewrite replace_list_index_eq; auto.
        rewrite lPutGet. apply Hpre''.
      - apply Hlte in Hpre''. destruct Hpre'' as (_ & Hpre'' & _).
        apply Hlte' in Hpre''.
        rewrite replace_list_index_eq; auto.
        rewrite lPutGet. apply Hpre''.
    }
    eapply sep_step_lte; eauto.
    eapply sep_step_lte. apply lte_r_sep_conj_perm.
    eapply sep_step_lte; eauto.
    eapply sep_step_lte. apply lte_r_sep_conj_perm.
    etransitivity. 2: apply sep_step_owned_finished.
    apply owned_sep_step; auto.
    Unshelve. eapply nonLifetime_sep_step; eauto.
  Qed.

  (*
  (* edit so P is a when l P, possibly a when_ptr *)
  Lemma partial l P Q R :
    P * lowned_Perms l (P * Q) R ⊨ lowned_Perms l Q R.
  Proof.
    intros p0 (p & powned & Hp & (r1 & r2 & Hr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte).
    exists (p ** r1), r2.
    exists Hr2, Hr2'. split.
    {
      symmetry. apply separate_sep_conj_perm.
      - eapply separate_antimonotone; eauto.
        symmetry. eapply separate_antimonotone; eauto.
        etransitivity; eauto. apply lte_r_sep_conj_perm. reflexivity.
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
  Qed.
*)

  Lemma owned_sep l p (Hnlp : nonLifetime p) (Hrelyp : rely_inv p) (Hguarp : guar_inv p)
    q (Hnlq : nonLifetime q) (Hrelyq : rely_inv q) (Hguarq : guar_inv q) :
    q ⊥ owned l p Hnlp ->
    q ⊥ p.
  Proof.
    intros Hsep. split; intros [si ss] [si' ss'] Hguar.
    - pose proof Hguar as Hguar'.
      apply nonLifetime_guar in Hguar'; auto. cbn in Hguar'.
      rewrite <- (lPutGet si), <- (lPutGet si').
      erewrite <- (lPutPut si), <- (lPutPut si').
      apply Hrelyq. { rewrite Hguar'. reflexivity. }
      apply Hsep. cbn. right.
      repeat rewrite lGetPut.
      repeat rewrite lPutPut.
      split; [| split; [| split]]; auto.
      + apply nth_error_replace_list_index_eq.
      + rewrite replace_list_index_twice. specialize (Hguarp si si').
        setoid_rewrite Hguar' in Hguarp.
        apply Hguarp; auto.
    - pose proof Hguar as Hguar'.
      apply nonLifetime_guar in Hguar'; auto. cbn in Hguar'.
      rewrite <- (lPutGet si), <- (lPutGet si').
      erewrite <- (lPutPut si), <- (lPutPut si').
      apply Hrelyp. { rewrite Hguar'. reflexivity. }
      destruct Hsep.
      specialize (sep_r (lput si (replace_list_index (lget si) l finished), ss)
                    (lput si' (replace_list_index (lget si') l finished), ss')).
      apply sep_r; auto.
      rewrite lGetPut. apply nth_error_replace_list_index_eq.
  Qed.

  Lemma sep_owned l p (Hp : nonLifetime p) (Hp' : rely_inv p) q (Hq : nonLifetime q) :
    p ⊥ q ->
    p ⊥ owned l q Hq.
  Proof.
    intros. split; intros [si ss] [si' ss'] ?.
    - destruct H0. rewrite H0. reflexivity.
      destruct H0 as (Hneql & Hlen & Hfin & Hguar).
      rewrite <- (lPutGet si), <- (lPutGet si').
      erewrite <- (lPutPut si), <- (lPutPut si').
      apply Hp'.
      {
        eapply nonLifetime_guar in Hguar; auto. cbn in Hguar.
        repeat rewrite lGetPut in Hguar.
        apply (Lifetimes_lte_replace_list_index_inv _ _ l finished).
        setoid_rewrite Hguar. reflexivity.
        rewrite Hfin.
        destruct (statusOf l (lget si)); [destruct s |]; cbn; auto.
      }
      apply H. apply Hguar.
    - split.
      + apply nonLifetime_guar in H0; auto. cbn in H0. rewrite H0. reflexivity.
      + intros. apply H; auto.
  Qed.

  Lemma sep_sep_conj_perm_owned l
    p (Hp : nonLifetime p) (Hrelyp : rely_inv p)
    q (Hq : nonLifetime q) (* (Hrelyq : rely_inv q) *)
    r (Hr : nonLifetime r) (Hqr : q ⊥ r) :
    p ⊥ q ->
    p ⊥ owned l r Hr ->
    p ⊥ owned l (q ** r) (nonLifetime_sep_conj_perm _ _ Hq Hr Hqr).
  Proof.
    intros Hpq Hpo.
    split; intros [si ss] [si' ss'] H.
    - cbn in *. destruct H. rewrite H. reflexivity.
      destruct H as (Heq & Hlen & Hfin & Hguar).
      remember (lput si _, _). remember (lput si' _, _).
      revert si ss si' ss' Heq Hlen Hfin Heqp0 Heqp1. induction Hguar; intros; subst.
      + destruct H.
        * rewrite <- (lPutGet si), <- (lPutGet si').
          erewrite <- (lPutPut si), <- (lPutPut si').
          eapply Hrelyp.
          {
            intros l'. destruct (Peano_dec.dec_eq_nat l l'); subst; auto.
            - rewrite Hfin. destruct (statusOf l' (lget si)); [destruct s |]; cbn; auto.
            - rewrite Heq; auto. reflexivity.
          }
          apply Hpq. eauto.
        * apply Hpo. cbn. auto.
      + destruct y as [si'' ss''].
        apply clos_trans_nonLifetime in Hguar1; auto. cbn in Hguar1. rewrite lGetPut in Hguar1.
        assert (l < length (lget si)).
        {
          unfold statusOf, Lifetimes in *.
          rewrite Hlen. apply nth_error_Some. intro. rewrite H in Hfin. inversion Hfin.
        }
        etransitivity.
        {
          eapply (IHHguar1 si ss (lput si'' (replace_list_index (lget si'') l finished)) ss''); auto.
          - intros. rewrite lGetPut. setoid_rewrite <- Hguar1.
            rewrite replace_list_index_twice.
            unfold statusOf, Lifetimes in *.
            rewrite <- nth_error_replace_list_index_neq; auto.
          - rewrite lGetPut. setoid_rewrite <- Hguar1. rewrite replace_list_index_twice.
            apply replace_list_index_length; auto.
          - rewrite lGetPut. apply nth_error_replace_list_index_eq.
          - rewrite lGetPut, lPutPut. setoid_rewrite <- Hguar1.
            repeat rewrite replace_list_index_twice. rewrite Hguar1. rewrite lPutGet. reflexivity.
        }
        {
          setoid_rewrite <- Hguar1. rewrite replace_list_index_twice.
          apply IHHguar2; auto.
          - intros. rewrite lGetPut.
            unfold statusOf, Lifetimes in *.
            rewrite <- nth_error_replace_list_index_neq; auto.
          - rewrite lGetPut.
            symmetry. apply replace_list_index_length; auto. lia.
          - rewrite lGetPut, lPutPut.
            repeat rewrite replace_list_index_twice. rewrite Hguar1. rewrite lPutGet. reflexivity.
        }
    - split. pose proof (nonLifetime_guar _ _ _ Hp H). cbn in H0. rewrite H0. reflexivity.
      intros. split.
      apply Hpq; auto.
      destruct Hpo. specialize (sep_r _ _ H). cbn in sep_r. apply sep_r; auto.
  Qed.
(*
  Lemma typing_when R1 R2 l P Q R S t s :
    typing
      P Q t s ->
    @typing Si Ss R1 R2
      (when_Perms l P * lowned_Perms l R S)
      Q t s.
  Proof.
    repeat intro.
    destruct H0 as (? & ? & ? & ? & ? & ?).
    destruct H0 as (? & (? & ? & ? & ?) & ?). subst.
    cbn in *.
    red in H.
    apply H4 in H1. destruct H1 as (? & ? & ?). apply H6 in H1. cbn in H1.
    specialize (H _ c1 c2 H0).
    apply H4 in H5.
    apply H4 in H1.

    red in H.

  Qed.
*)
End LifetimePerms.
