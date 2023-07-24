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
     PermType
     Memory
     Lifetime
     MemoryPerms
     LifetimePerms
     Typing
     SepStep
     PermTypeProofs.

From Paco Require Import
     paco.

Import ITreeNotations.
Import ListNotations.

Open Scope list_scope.
Open Scope itree_scope.
(* end hide *)

Section Perms.
  Context {Si Ss : Type}.
  Context `{Hmemory: Lens Si memory}.
  Context `{Hlifetime: Lens Si Lifetimes}.

  Context `{HGetPut1 : (forall x y, @lget _ _ Hmemory (@lput _ _ Hlifetime x y) = @lget _ _ Hmemory x)}.
  Context `{HGetPut2 : (forall x y, @lget _ _ Hlifetime (@lput _ _ Hmemory x y) = @lget _ _ Hlifetime x)}.
  Context `{HPutPut : (forall si x y, @lput _ _ Hmemory (@lput _ _ Hlifetime si x) y =
                                   @lput _ _ Hlifetime (@lput _ _ Hmemory si y) x)}.
  (* Context `{HPutPut2 : (forall si x y, @lput _ _ Hlifetime (@lput _ _ Hmemory si x) y = *)
  (*                                   @lput _ _ Hmemory (@lput _ _ Hlifetime si y) x)}. *)

  Lemma nonLifetime_read_perm p v :
    @nonLifetime _ Ss _ (read_perm p v).
  Proof.
    intros n. split; intros [] [].
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. rewrite HGetPut1. reflexivity.
    - intros. cbn in *. subst. split; reflexivity.
  Qed.
  Lemma nonLifetime_write_perm p v :
    @nonLifetime _ Ss _ (write_perm p v).
  Proof.
    intros n. split; intros [] [].
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. rewrite HGetPut1. reflexivity.
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. do 2 rewrite HGetPut2.
      split; reflexivity.
  Qed.

  Lemma rely_inv_read_perm p v :
    @rely_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn in *. do 2 rewrite HGetPut1. auto.
  Qed.
  Lemma rely_inv_write_perm p v :
    @rely_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. cbn in *. do 2 rewrite HGetPut1. auto.
  Qed.

  Lemma guar_inv_read_perm p v :
    @guar_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn in *. subst. reflexivity.
  Qed.
  Lemma guar_inv_write_perm p v :
    @guar_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. destruct H as ((? & ?) & ? & ? & ?). subst.
    cbn. rewrite !HGetPut1, HGetPut2.
    split; [| split; [| split]]; auto.
    eexists. rewrite HPutPut. reflexivity.
  Qed.

  Lemma pre_inv_read_perm p v :
    @pre_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn. rewrite HGetPut1. auto.
  Qed.
  Lemma pre_inv_write_perm p v :
    @pre_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. cbn. rewrite HGetPut1. auto.
  Qed.

  Lemma nonLifetime_ptr {A} p rw o' a (T : VPermType A) (HT : forall xi xs, nonLifetime_Perms (xi :: T ▷ xs)) :
    @nonLifetime_Perms _ Ss _ ((VPtr p) :: ptr(rw, o', T) ▷ a).
  Proof.
    intros q Hq. destruct p as [b o]. destruct Hq as (? & (v & ?) & ?). subst.
    destruct H0 as (p & pt' & Hp & Ht' & Hsep & Hlte).
    edestruct (HT v a _ Ht') as (pt & Ht & Hlte' & Hnlt & Hrelyt & Hguart & Hpret).
    destruct rw.
    - assert (Hsep' : (read_perm (b, o + o') v) ⊥ pt).
      {
        eapply separate_antimonotone. 2: apply Hlte'.
        symmetry. eapply separate_antimonotone. 2: apply Hp. symmetry; auto.
      }
      exists ((read_perm (b, o + o') v) ** pt). split; [| split; [| split; [| split; [| split]]]].
      + eexists. split. eexists. reflexivity.
        cbn. do 2 eexists. split; [| split; [| split]]; eauto; reflexivity.
      + etransitivity; eauto. apply sep_conj_perm_monotone; auto.
      + apply nonLifetime_sep_conj_perm; auto. apply nonLifetime_read_perm.
      + apply rely_inv_sep_conj_perm; auto. apply rely_inv_read_perm.
      + apply guar_inv_sep_conj_perm; auto. apply guar_inv_read_perm.
      + apply pre_inv_sep_conj_perm; auto. apply pre_inv_read_perm.
    - assert (Hsep' : (write_perm (b, o + o') v) ⊥ pt).
      {
        eapply separate_antimonotone. 2: apply Hlte'.
        symmetry. eapply separate_antimonotone. 2: apply Hp. symmetry; auto.
      }
      exists ((write_perm (b, o + o') v) ** pt). split; [| split; [| split; [| split; [| split]]]].
      + eexists. split. eexists. reflexivity.
        cbn. do 2 eexists. split; [| split; [| split]]; eauto; reflexivity.
      + etransitivity; eauto. apply sep_conj_perm_monotone; auto.
      + apply nonLifetime_sep_conj_perm; auto. apply nonLifetime_write_perm.
      + apply rely_inv_sep_conj_perm; auto. apply rely_inv_write_perm.
      + apply guar_inv_sep_conj_perm; auto. apply guar_inv_write_perm.
      + apply pre_inv_sep_conj_perm; auto. apply pre_inv_write_perm.
  Qed.

  Lemma nonLifetime_trueP :
    forall (xi : Value) (xs : unit), @nonLifetime_Perms _ Ss _ (xi :: trueP ▷ xs).
  Proof.
    repeat intro. exists bottom_perm. cbn. intuition.
    apply bottom_perm_is_bottom.
    apply nonLifetime_bottom.
    apply rely_inv_bottom.
    apply guar_inv_bottom.
    apply pre_inv_bottom.
  Qed.

  Lemma nonLifetime_eqp y :
    forall (xi : Value) (xs : unit), @nonLifetime_Perms _ Ss _ (xi :: eqp y ▷ xs).
  Proof.
    repeat intro. exists bottom_perm. cbn. intuition.
    apply bottom_perm_is_bottom.
    apply nonLifetime_bottom.
    apply rely_inv_bottom.
    apply guar_inv_bottom.
    apply pre_inv_bottom.
  Qed.

  Definition when_ptr_Perms {A} (l : nat) (rw : RW) (p : Value) (a : A) (T : VPermType A)
    : @Perms (Si * Ss) :=
    match p with
    | VNum _ => top_Perms
    | VPtr p =>
        meet_Perms (fun P => exists (v : Value),
                        P = singleton_Perms
                              (match rw with
                               | R => when l (read_perm p v)
                               | W => when l (write_perm p v)
                               end) *
                              (v :: T ▷ a))
    end.

  Definition when_ptr {A} (l : nat) '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => when_ptr_Perms l rw (offset x o) a T;
    |}.

  Definition finished_ptr_Perms {A} (l : nat) (rw : RW) (p : Value) (a : A) (T : VPermType A) : @Perms (Si * Ss) :=
    match p with
    | VNum _ => top_Perms
    | VPtr p =>
        meet_Perms (fun P => exists (v : Value),
                        P = singleton_Perms
                              (match rw with
                               | R => lfinished l (read_perm p v)
                               | W => lfinished l (write_perm p v)
                               end) *
                              (v :: T ▷ a))
    end.

  Definition finished_ptr {A} (l : nat) '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => finished_ptr_Perms l rw (offset x o) a T;
    |}.

  Lemma split_Perms_T {A} b o o' l (P Q : @Perms (Si * Ss)) (T : VPermType A) xs
    (HT : forall xi xs, nonLifetime_Perms (xi :: T ▷ xs)) :
    (VPtr (b, o)) :: ptr(W, o', T) ▷ xs * lowned_Perms l P Q ⊨
      (VPtr (b, o) :: when_ptr l (W, o', T) ▷ xs) *
      lowned_Perms l
        ((VPtr (b, o) :: when_ptr l (R, o', trueP) ▷ tt) * P)
        ((VPtr (b, o) :: ptr(W, o', trueP) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte).
    destruct Hp' as (? & (v & ?) & Hv). subst.
    destruct Hv as (pw & pt & Hpw & Hpt & Hsep'' & Hlte'').
    destruct (HT _ _ _ Hpt) as (pt' & Hpt' & Hltept & Hnlpt & Hguarpt & Hprept).
    assert (Hsepwrite : write_perm (b, o + o') v ⊥ r2).
    {
      eapply owned_sep; auto.
      apply nonLifetime_write_perm. apply rely_inv_write_perm. apply guar_inv_write_perm.
      eapply separate_antimonotone.
      2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
      symmetry.
      eapply separate_antimonotone. 2: apply Hpw.
      eapply separate_antimonotone.
      2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    exists (when l (write_perm (b, o + o') v) ** pt').
    exists (r1 ** owned l (write_perm (b, o + o') v ** r2) (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite)).
    split; [| split; [| split]].
    - cbn. eexists. split. eexists. reflexivity.
      cbn. do 2 eexists. split. reflexivity.
      split; [| split]; try reflexivity; auto.
      apply sep_when; auto.
      eapply separate_antimonotone. 2: apply Hltept.
      symmetry. eapply separate_antimonotone; eauto.
      symmetry; auto.
    - exists r1, (write_perm (b, o + o') v ** r2), Hsepr1, Hnlr1.
      exists (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite).
      exists (rely_inv_sep_conj_perm _ _ (rely_inv_write_perm _ _) Hrelyr2).
      exists (guar_inv_sep_conj_perm _ _ (guar_inv_write_perm _ _) Hguarr2).
      split; [| split]. 2: reflexivity.
      + apply sep_conj_Perms_perm; auto.
        cbn. eexists. split. eexists. reflexivity.
        rewrite sep_conj_Perms_commut.
        rewrite sep_conj_Perms_bottom_identity.
        cbn. reflexivity.
      + intros p1 (pwhen & q & (? & (v' & ?) & Hlte''') & Hq' & Hsep''' & Hlte'''') Hsep''''; subst.
        rewrite sep_conj_Perms_commut in Hlte'''.
        rewrite sep_conj_Perms_bottom_identity in Hlte'''. cbn in Hlte'''.

        specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
        {
          symmetry in Hsep''''.
          eapply separate_antimonotone in Hsep''''; eauto.
          eapply separate_antimonotone in Hsep''''; eauto.
          2: apply lte_r_sep_conj_perm.
          symmetry in Hsep''''.
          eapply separate_antimonotone in Hsep''''; eauto.
          apply sep_conj_perm_monotone. reflexivity.
          apply owned_monotone. apply lte_r_sep_conj_perm.
        }
        exists ((write_perm (b, o + o') v') ** r). split; [| split].
        * apply sep_conj_Perms_perm; auto.
          -- cbn. eexists. split. eexists. reflexivity.
             rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity.
             cbn. reflexivity.
          -- symmetry. apply Hsep_step.
             symmetry. eapply sep_step_write_perm; eauto.
        * etransitivity.
          -- apply sep_step_sep_conj_r; eauto. symmetry. auto.
          -- apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
             eapply sep_step_write_perm.
        * (** Precondition section *)
          intros. split; [| split].
          -- apply Hlte'''' in H. destruct H as (? & ? & ?).
             apply Hlte''' in H. cbn in H.
             rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
             setoid_rewrite HGetPut1 in H.
             cbn. rewrite HGetPut1. symmetry. apply H; auto.
          -- apply Hpre; auto. apply Hlte''''; auto.
          -- symmetry. apply Hsep_step.
             symmetry. eapply sep_step_write_perm; eauto.
    - (** everything is pairwise separate *)
      apply separate_sep_conj_perm_4.
      + apply sep_when; auto.
        eapply separate_antimonotone. 2: apply Hltept.
        symmetry.
        eapply separate_antimonotone. 2: apply Hpw. symmetry. auto.
      + apply sep_when; auto.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_antimonotone. 2: apply Hpw.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
        symmetry. auto.
      + apply when_owned_sep.
      + eapply separate_antimonotone.
        2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_antimonotone. 2: apply Hltept.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
        symmetry. auto.
      + apply sep_sep_conj_perm_owned; auto.
        * eapply separate_antimonotone. 2: apply Hpw.
          symmetry. eapply separate_antimonotone; eauto.
        * eapply separate_antimonotone.
          2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
          symmetry. eapply separate_antimonotone. 2: apply Hltept.
          eapply separate_antimonotone.
          2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
          symmetry. auto.
      + apply Hsepr1.
    - (** Shuffling around permissions using <= *)
      etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 3 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].

      etransitivity. 2: apply sep_conj_perm_monotone; [| reflexivity]; eauto.
      rewrite <- sep_conj_perm_assoc.
      rewrite (sep_conj_perm_commut _ pt).
      rewrite (sep_conj_perm_commut _ pt').
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [assumption |].

      etransitivity. apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.

  Lemma split_Perms_eq b o o' l (P Q : @Perms (Si * Ss)) x :
    (VPtr (b, o)) :: ptr(W, o', eqp x) ▷ tt * lowned_Perms l P Q ⊨
      (VPtr (b, o) :: when_ptr l (W, o', eqp x) ▷ tt) *
      lowned_Perms l
        ((VPtr (b, o) :: when_ptr l (R, o', eqp x) ▷ tt) * P)
        ((VPtr (b, o) :: ptr(W, o', eqp x) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte).
    destruct Hp' as (? & (v & ?) & Hv). subst.
    destruct Hv as (pw & pt & Hpw & Hpt & Hsep'' & Hlte'').
    cbn in Hpt. subst.
    assert (Hsepwrite : write_perm (b, o + o') v ⊥ r2).
    {
      eapply owned_sep; auto.
      apply nonLifetime_write_perm. apply rely_inv_write_perm. apply guar_inv_write_perm.
      eapply separate_antimonotone.
      2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
      symmetry.
      eapply separate_antimonotone. 2: apply Hpw.
      eapply separate_antimonotone.
      2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    exists (when l (write_perm (b, o + o') v)).
    exists (r1 ** owned l (write_perm (b, o + o') v ** r2) (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite)).
    split; [| split; [| split]].
    - cbn. eexists. split. eexists. reflexivity.
      cbn. do 2 eexists.
      split; [| split; [| split]]; try reflexivity; auto.
      apply separate_bottom.
      apply sep_conj_perm_bottom.
    - exists r1, (write_perm (b, o + o') v ** r2), Hsepr1, Hnlr1.
      exists (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite).
      exists (rely_inv_sep_conj_perm _ _ (rely_inv_write_perm _ _) Hrelyr2).
      exists (guar_inv_sep_conj_perm _ _ (guar_inv_write_perm _ _) Hguarr2).
      split; [| split]. 2: reflexivity.
      + apply sep_conj_Perms_perm; auto.
        cbn. eexists. split. eexists. reflexivity.
        do 2 eexists. split; [| split; [| split]]; cbn; try reflexivity.
        apply separate_bottom.
        apply sep_conj_perm_bottom.
      + intros p1 (pwhen & q & (? & (v' & ?) & Hlte''') & Hq' & Hsep''' & Hlte'''') Hsep''''; subst.
        destruct Hlte''' as (? & ? & ? & ? & ? & ?). cbn in H0. subst.
        rename v' into v.
        (* rewrite sep_conj_Perms_commut in Hlte'''. *)
        (* rewrite sep_conj_Perms_bottom_identity in Hlte'''. cbn in Hlte'''. *)

        specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
        {
          symmetry in Hsep''''.
          eapply separate_antimonotone in Hsep''''; eauto.
          eapply separate_antimonotone in Hsep''''; eauto.
          2: apply lte_r_sep_conj_perm.
          symmetry in Hsep''''.
          eapply separate_antimonotone in Hsep''''; eauto.
          apply sep_conj_perm_monotone. reflexivity.
          apply owned_monotone. apply lte_r_sep_conj_perm.
        }
        exists ((write_perm (b, o + o') v) ** r). split; [| split].
        * apply sep_conj_Perms_perm; auto.
          -- cbn. eexists. split. eexists. reflexivity. cbn.
             do 2 eexists. split; [| split; [| split]]; try reflexivity.
             apply separate_bottom.
             apply sep_conj_perm_bottom.
          -- symmetry. apply Hsep_step.
             symmetry. eauto.
        * etransitivity.
          -- apply sep_step_sep_conj_r; eauto. symmetry. auto.
          -- apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
             eapply sep_step_write_perm.
        * (** Precondition section *)
          intros.
          split; [| split].
          -- apply Hlte'''' in H0. destruct H0 as (? & ? & ?).
             apply H2 in H0. destruct H0. apply H in H0. cbn in H0.
             rewrite lGetPut in H0. setoid_rewrite nth_error_replace_list_index_eq in H0.
             setoid_rewrite HGetPut1 in H0.
             cbn. rewrite HGetPut1. symmetry. apply H0; auto.
          -- apply Hpre; auto. apply Hlte''''; auto.
          -- symmetry. apply Hsep_step.
             symmetry. eauto.
    - (** everything is pairwise separate *)
      apply separate_sep_conj_perm.
      + apply sep_when; auto.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_antimonotone. 2: apply Hpw.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
        symmetry. auto.
      + apply when_owned_sep.
      + symmetry. apply Hsepr1.
    - (** Shuffling around permissions using <= *)
      etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].

      etransitivity. 2: apply sep_conj_perm_monotone; [| reflexivity]; eauto.
      rewrite (sep_conj_perm_commut _ pt).
      rewrite sep_conj_perm_assoc.

      etransitivity. 2: apply lte_r_sep_conj_perm.
      etransitivity. apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.

  (** all the when_ptr (R) [Perms] starred together, with a T on each *)
  Fixpoint when_ptrs_T l (vals : list (nat * nat * nat * {A & (prod (VPermType A) A)}))
    : @Perms (Si * Ss) :=
    match vals with
    | nil => bottom_Perms
    | cons v vals => let '(b, o, o', x) := v in
                    (VPtr (b, o) :: when_ptr l (R, o', (fst (projT2 x))) ▷ (snd (projT2 x))) *
                      when_ptrs_T l vals
    end.

  (** all the [when (read_perm)]s starred together *)
  Fixpoint when_read_perms l (vals : list (nat * nat * nat * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => bottom_perm
    | cons v vals => let '(b, o, o', v') := v in
                    when l (read_perm (b, o + o') v') **
                      (when_read_perms l vals)
    end.
  Lemma when_read_perms_sep l b o v l' vals :
    when l (read_perm (b, o) v) ⊥ when_read_perms l' vals.
  Proof.
    revert l b o v.
    induction vals; intros.
    - apply separate_bottom.
    - destruct a as [[[b' o1] o2] v'].
      apply separate_sep_conj_perm.
      + eapply when_preserves_sep. apply read_separate.
      + apply IHvals.
      + symmetry. apply IHvals.
  Qed.

  (** stars the perms inside the list together *)
  Fixpoint star_list (vals : list (perm * {A & (prod (@VPermType Si Ss A) A)} * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => bottom_perm
    | cons v vals => let '(p, _, _) := v in
                    p ** star_list vals
    end.

  (** checks that each of the perms in the list are in the corresponding T in the list, plus some nonLifetime invariants on the perms *)
  Fixpoint perms_in_T_inv (vals : list (perm * {A & (prod (@VPermType Si Ss A) A)} * Value))
    : Prop :=
    match vals with
    | nil => True
    | cons v vals => let '(p, x, v') := v in
                    p ∈ v' :: (fst (projT2 x)) ▷ (snd (projT2 x)) /\
                      nonLifetime p /\
                      rely_inv p /\
                      guar_inv p /\
                      pre_inv p /\
                      perms_in_T_inv vals
    end.

  Lemma star_list_invs vals c :
    pre (star_list vals) c ->
    perms_in_T_inv vals ->
    nonLifetime (star_list vals) /\
      guar_inv (star_list vals) /\
      rely_inv (star_list vals) /\
      pre_inv (star_list vals).
  Proof.
    induction vals.
    - cbn. split; [| split; [| split]].
      apply nonLifetime_bottom.
      apply guar_inv_bottom.
      apply rely_inv_bottom.
      apply pre_inv_bottom.
    - intros Hpre H. destruct a as [[p x] v].
      destruct H as (? & ? & ? & ? & ? & ?).
      split; [| split; [| split]].
      + apply nonLifetime_sep_conj_perm; auto. apply IHvals; auto.
        apply Hpre. apply Hpre.
      + apply guar_inv_sep_conj_perm; auto. apply IHvals; auto. apply Hpre.
      + apply rely_inv_sep_conj_perm; auto. apply IHvals; auto. apply Hpre.
      + apply pre_inv_sep_conj_perm; auto. apply IHvals; auto. apply Hpre.
  Qed.

  (* Fixpoint T_perms (vals : list (nat * nat * nat * {A & (prod (@VPermType Si Ss A) A)} * Value)) : @perm (Si * Ss) := *)
  (*   match vals with *)
  (*   | nil => bottom_perm *)
  (*   | cons v vals => let '(b, o, o', (A, (T, a)), v') := v in *)

  (*                     (T_perms l vals) *)
  (*   end. *)

  (** Gives up the vals that each pointer points to *)
  Lemma split_when_ptrs_T l nov (* no vals *)
    (HT: Forall (fun '(_, _, _, x) => forall (v : Value) (a : (projT1 x)), nonLifetime_Perms (v :: (fst (projT2 x)) ▷ a)) nov)
    p :
    p ∈ when_ptrs_T l nov ->
    (* we are basically only coming up with the list of vals *)
    exists not nop (* no Ts, no s *)
      (Hlen1 : length nov = length not)
      (Hlen2 : length nov = length nop)
      (Heq1: Forall (fun '((b, o1, o2, _), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov not))
      (Heq2: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
      (Heq3: Forall (fun '((_, _, _, v), (_, _, v')) => v = v') (combine not nop)),
      perms_in_T_inv nop /\ (* each of the perms is in v :: T ▷ xs and satisfies invariants *)
      when_read_perms l not ** star_list nop <= p.
  Proof.
    revert p HT. induction nov; intros p HT Hp.
    {
      exists [], []. cbn. do 5 (exists; auto).
      split; auto.
      rewrite sep_conj_perm_bottom. apply bottom_perm_is_bottom.
    }
    destruct a as [[[b o1] o2] X].
    destruct Hp as (p1 & ps & Hp1 & Hps & Hsep & Hlte).
    destruct Hp1 as (? & (v & ?) & Hp1); subst.
    destruct Hp1 as (pptr & pt' & Hpptr & Hpt' & Hsep' & Hlte').
    inversion HT; subst; clear HT.
    rename H2 into HT.
    cbn in H1, Hpt'. specialize (H1 v (snd (projT2 X)) _ Hpt').
    destruct H1 as (pt & Hpt & Hptpt' & Hnlpt & Hrelypt & Hguarpt & Hprept).
    specialize (IHnov ps HT Hps).
    destruct IHnov as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hin & Hlte'').
    exists (cons (b, o1, o2, v) not), (cons (pt, X, v) nop).
    do 5 (exists; cbn; auto).
    split; [split |]; auto.
    etransitivity; eauto.
    rewrite sep_conj_perm_assoc.
    rewrite <- (sep_conj_perm_assoc _ pt).
    rewrite (sep_conj_perm_commut _ pt).
    rewrite sep_conj_perm_assoc.
    rewrite <- sep_conj_perm_assoc.
    apply sep_conj_perm_monotone; auto.
    etransitivity; eauto.
    apply sep_conj_perm_monotone; auto.
  Qed.

  Lemma when_ptrs_T_lte l vals vals'
    (Hlen : length vals = length vals')
    (Heq: Forall (fun '((b, o1, o2, _), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine vals vals')) :
    when_read_perms l vals' ∈ when_ptrs_T l vals.
  Proof.
    revert vals' Hlen Heq.
    induction vals; intros; auto. cbn. auto.
    destruct vals'. inversion Hlen.
    inversion Heq. subst.
    destruct a as [[[b o1] o2] [A [T a]]].
    (* destruct p as [[[[b' o1'] o2'] [A' [T' a']]] ?]. *)
    (* cbn in Hlen. inversion Hlen. *)
    (* destruct H1 as (? & ? & ? & ?). subst. inversion H4. subst. *)
    (* apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H5, H3. subst. *)

    (* apply sep_conj_Perms_perm. *)
    (* - eexists. split. eexists. reflexivity. *)
    (*   do 2 eexists. split; [| split; [| split]]. *)
    (*   + cbn. reflexivity. *)
    (*   + cbn. admit. *)
    (*   + admit. *)
    (*   + admit. *)
    (* - apply IHvals; auto. *)
    (* - admit. *)
  Abort.
  (* Fixpoint T_perms (vals : list (nat * nat * nat * {A & (@VPermType Si Ss A) & A} * Value)) := *)
  (*   match vals with *)
  (*   | nil => bottom_perm *)
  (*   | cons v vals => let '(b, o, o', x, v') := v in *)
  (*                    (read_perm (b, o + o') v') ** *)
  (*                     (when_read_perms l vals) *)
  (*   end. *)

  (** all the when_ptr (R) [Perms] starred together, with a trueP on each *)
  Fixpoint when_ptrs_trueP l (vals : list (nat * nat * nat)) :=
    match vals with
    | nil => bottom_Perms
    | cons v vals => let '(b, o, o') := v in
                    (VPtr (b, o) :: when_ptr l (R, o', trueP) ▷ tt) *
                      when_ptrs_trueP l vals
    end.

  Lemma when_read_perms_when_ptrs_trueP l vals vals'
    (Hlen : length vals = length vals')
    (Heq : Forall (fun '((b, o1, o2, _), (b', o1', o2')) => b = b' /\ o1 = o1' /\ o2 = o2') (combine vals vals')) :
    when_read_perms l vals ∈ when_ptrs_trueP l vals'.
  Proof.
    revert vals' Hlen Heq.
    induction vals; intros; destruct vals'; try solve [inversion Hlen].
    { cbn. auto. }
    destruct a as [[[b o1] o2] v].
    destruct p as [[b' o1'] o2']. inversion Heq; clear Heq.
    destruct H1 as (? & ? & ?); subst.
    rename H2 into Heq. inversion Hlen; clear Hlen. rename H0 into Hlen.
    specialize (IHvals _ Hlen Heq).
    apply sep_conj_Perms_perm.
    - cbn. eexists. split. eexists. reflexivity.
      rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity.
      cbn. reflexivity.
    - apply IHvals.
    - apply when_read_perms_sep.
  Qed.

  Fixpoint ptrs_trueP (vals : list (nat * nat * nat)) : @Perms (Si * Ss) :=
    match vals with
    | nil => bottom_Perms
    | cons v vals => let '(b, o, o') := v in
                    (VPtr (b, o) :: ptr (W, o', trueP) ▷ tt) *
                      ptrs_trueP vals
    end.
  (** all the [(write_perm)]s starred together *)
  Fixpoint write_perms (vals : list (nat * nat * nat * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => bottom_perm
    | cons v vals => let '(b, o, o', v') := v in
                    (write_perm (b, o + o') v') **
                      (write_perms vals)
    end.

  Lemma split_ptrs_trueP p nov :
    p ∈ ptrs_trueP nov ->
    exists vals
      (Hlen : length nov = length vals)
      (Heq : Forall (fun '((b, o1, o2), (b', o1', o2', v)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov vals)),
      write_perms vals <= p.
  Proof.
    revert p. induction nov; intros p Hp.
    {
      exists []. do 2 (exists; auto).
      cbn. apply bottom_perm_is_bottom.
    }
    destruct a as [[b o1] o2].
    destruct Hp as (p1 & ps & Hp1 & Hps & Hsep & Hlte).
    destruct Hp1 as (? & (v & ?) & Hp1); subst.
    rewrite sep_conj_Perms_commut in Hp1. rewrite sep_conj_Perms_bottom_identity in Hp1.
    specialize (IHnov ps Hps).
    destruct IHnov as (vals & Hlen & Heq & Hlte').
    exists (cons (b, o1, o2, v) vals).
    do 2 (exists; cbn; auto).
    etransitivity; eauto.
    apply sep_conj_perm_monotone; auto.
  Qed.

  (* Lemma split_ptrs_trueP l nov (* no vals *) *)
  (*   p : *)
  (*   p ∈ ptrs_trueP nov -> *)
  (*   exists  *)

  Fixpoint finished_write_perms l (vals : list (nat * nat * nat * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => lfinished l bottom_perm
    | cons v vals => let '(b, o, o', v') := v in
                    lfinished l (write_perm (b, o + o') v') **
                      (finished_write_perms l vals)
    end.

  Lemma finished_write_perms_separate l not b o1 o2 v c :
    pre (write_perms not) c ->
    write_perm (b, o1 + o2) v ⊥ write_perms not ->
    lfinished l (write_perm (b, o1 + o2) v) ⊥ finished_write_perms l not.
  Proof.
    revert b o1 o2 v.
    induction not; cbn; intros.
    - apply lfinished_separate. apply separate_bottom.
    - destruct a as [[[b' o1'] o2'] v'].
      cbn. intros.
      apply separate_sep_conj_perm.
      + apply lfinished_separate; auto.
        eapply separate_antimonotone; eauto.
        apply lte_l_sep_conj_perm.
      + apply IHnot.
        apply H.
        eapply separate_antimonotone; eauto.
        apply lte_r_sep_conj_perm.
      + symmetry. apply IHnot; apply H.
  Qed.

  Lemma finished_write_perms_separate' not l p (Hp : nonLifetime p) c :
    pre (write_perms not) c ->
    write_perms not ⊥ p ->
    finished_write_perms l not ⊥ p.
  Proof.
    induction not.
    - cbn. intros _ H. apply lfinished_separate'; auto.
    - destruct a as [[[b o1] o2] v].
      intros Hpre Hsep. cbn.
      symmetry. apply separate_sep_conj_perm.
      + symmetry. apply lfinished_separate'; auto.
        symmetry. symmetry in Hsep. eapply separate_antimonotone; eauto.
        apply lte_l_sep_conj_perm.
      + symmetry. apply IHnot. apply Hpre.
        symmetry. symmetry in Hsep. eapply separate_antimonotone; eauto.
        apply lte_r_sep_conj_perm.
      + symmetry. eapply finished_write_perms_separate; apply Hpre.
  Qed.

  Lemma lfinished_sep_conj_perm_dist' l vals :
    finished_write_perms l vals <= lfinished l (write_perms vals).
  Proof.
    induction vals.
    - reflexivity.
    - destruct a as [[[b o1] o2] v]. cbn.
      etransitivity. 2: apply lfinished_sep_conj_perm_dist.
      eapply sep_conj_perm_monotone; auto. reflexivity.
  Qed.

  Fixpoint finished_ptrs_T l (vals : list (nat * nat * nat * {A & (prod (VPermType A) A)})) :=
    match vals with
    | nil => lfinished_Perms l bottom_Perms
    | cons v vals => let '(b, o, o', x) := v in
                    (VPtr (b, o) :: finished_ptr l (W, o', (fst (projT2 x))) ▷ (snd (projT2 x))) *
                      finished_ptrs_T l vals
    end.

  Lemma typing_end_ptr_n l vals vals'
    (Hlen : length vals = length vals')
    (Heq : Forall (fun '((b, o1, o2, _), (b', o1', o2')) => b = b' /\ o1 = o1' /\ o2 = o2') (combine vals vals'))
    (HT: Forall (fun '(_, _, _, x) => forall (v : Value) (a : (projT1 x)), nonLifetime_Perms (v :: (fst (projT2 x)) ▷ a)) vals) :
    typing (specConfig := Ss)
      (when_ptrs_T l vals *
         lowned_Perms l
           (when_ptrs_trueP l vals')
           (ptrs_trueP vals'))
      (fun l _ => finished_ptrs_T l vals)
      (endLifetime l)
      (Ret tt).
  Proof.
    intros p si ss Hp Hpre.
    destruct Hp as (pwhens & powned & Hpwhens & Hpowned & Hsep & Hlte).
    destruct Hpowned as (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf).
    assert (Hcurrent: statusOf l (lget si) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      apply Hlte' in Hpre. apply Hpre.
    }
    (* read step, don't do anything here *)
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.
    setoid_rewrite Hcurrent.
    (* apply the function we got from the lowned to get the write ptrs *)
    apply split_when_ptrs_T in Hpwhens; auto.
    destruct Hpwhens as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hnop & Hlte'').
    edestruct Hf as (pptrs & Hpptrs & Hsepstep & Hpre').
    apply (when_read_perms_when_ptrs_trueP l not vals').
    { rewrite <- Hlen1. auto. }
    {
      clear Hf HT Hr2.
      clear nop Hlen2 Heq2 Heq3 Hnop Hlte''.
      revert vals not Hlen1 Heq1 Hlen Heq.
      induction vals'; intros.
      - destruct vals; try solve [inversion Hlen].
        destruct not; try solve [inversion Hlen1].
        constructor.
      - destruct vals; try solve [inversion Hlen].
        destruct not; try solve [inversion Hlen1].
        destruct a as [[b o1] o2].
        destruct p0 as [[[b' o1'] o2'] x].
        inversion Heq; subst; clear Heq. rename H2 into Heq.
        destruct H1 as (? & ? & ?); subst.
        destruct p1 as [[[b' o1'] o2'] v].
        inversion Heq1; subst; clear Heq1. rename H2 into Heq1.
        destruct H1 as (? & ? & ?); subst.
        rename b' into b, o1' into o1, o2' into o2.
        constructor. auto. apply IHvals' with (vals := vals); auto.
    }
    {
      eapply separate_antimonotone; eauto.
      symmetry.
      eapply separate_antimonotone.
      2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    apply split_ptrs_trueP in Hpptrs.
    destruct Hpptrs as (not' & Hlen3 & Heq4 & Hlte''').
    (* the values in the read perms from the when and the write perms
       from the lowned must be the same *)
    assert (not = not').
    {
      specialize (Hpre' si ss).
      apply Hlte''' in Hpre'.
      - apply Hlte in Hpre. destruct Hpre as (Hpre & _).
        apply Hlte'' in Hpre. destruct Hpre as (Hpre & _).
        {
          clear HT Hf Hr2.
          revert vals vals' not' nop Hlen Heq Hlen1 Hlen2 Heq1 Heq2 Hnop Heq3 Hlte'' Hlen3 Heq4 Hlte''' Hpre'.
          induction not; intros.
          - destruct vals; try solve [inversion Hlen1].
            destruct vals'; try solve [inversion Hlen].
            destruct not'; try solve [inversion Hlen3]; auto.
          - destruct vals; try solve [inversion Hlen1].
            destruct vals'; try solve [inversion Hlen].
            destruct nop; try inversion Hlen2.
            destruct not'; try solve [inversion Hlen3]; auto.
            destruct p0 as [[[? ?] ?] ?].
            destruct p1 as [[? ?] ?].
            destruct p2 as [[? ?] ?].
            destruct p3 as [[[? ?] ?] ?].
            destruct a as [[[? ?] ?] ?].
            inversion Heq; subst; clear Heq; rename H3 into Heq.
            destruct H2 as (? & ? & ?); subst.
            inversion Heq1; subst; clear Heq1; rename H3 into Heq1.
            destruct H2 as (? & ? & ?); subst.
            inversion Heq2; subst; clear Heq2; rename H3 into Heq2.
            inversion Heq3; subst; clear Heq3; rename H3 into Heq3.
            inversion Heq4; subst; clear Heq4; rename H3 into Heq4.
            destruct H2 as (? & ? & ?); subst.
            f_equal.
            + f_equal; auto.
              clear Hlen Hlen1 Hlen2 Hlen3 Heq Heq1 Heq2 Heq3 Heq4 IHnot Hlte Hlte' Hlte'' Hlte'''.
              destruct Hpre as (? & _), Hpre' as (? & _).
              cbn in H, H1. rewrite HGetPut1 in H1.
              rewrite H in H1; auto.
              inversion H1. auto.
            + apply IHnot with (vals := vals) (vals' := vals') (nop := nop); auto.
              * apply Hpre.
              * apply Hnop.
              * etransitivity; eauto. cbn.
                apply sep_conj_perm_monotone; apply lte_r_sep_conj_perm.
              * etransitivity; eauto. apply lte_r_sep_conj_perm.
              * apply Hpre'.
        }
      - apply Hlte in Hpre. destruct Hpre as (Hpre & _).
        apply Hlte'' in Hpre. destruct Hpre as (Hpre & _).
        rewrite replace_list_index_eq; auto. rewrite lPutGet; auto.
      - apply Hlte'. apply Hlte.
        rewrite replace_list_index_eq; auto. rewrite lPutGet; auto.
    }
    subst. rename not' into not.

    (* End the lifetime *)
    rewritebisim @bind_trigger.
    constructor 6 with (p' := finished_write_perms l not ** star_list nop); unfold id; auto.
    { (* lowned allows us to do this *)
      apply Hlte. constructor 1. right.
      apply Hlte'. constructor 1. right.
      cbn. right.
      repeat rewrite lGetPut.
      split; [| split; [| split]].
      - intros. apply nth_error_replace_list_index_neq; auto.
        apply nth_error_Some. intros Hnone.
        unfold statusOf, Lifetimes in Hcurrent.
        rewrite Hcurrent in Hnone. inversion Hnone.
      - apply replace_list_index_length; auto. apply nth_error_Some. intro Hnone.
        unfold statusOf, Lifetimes in Hcurrent. rewrite Hcurrent in Hnone. inversion Hnone.
      - unfold statusOf. apply nth_error_replace_list_index_eq.
      - rewrite lPutPut, replace_list_index_twice. reflexivity.
    }
    { (* lowned sep_steps to lfinished *)
      eapply sep_step_lte; eauto.
      rewrite sep_conj_perm_commut.
      eapply sep_step_lte.
      {
        apply sep_conj_perm_monotone.
        - etransitivity. 2: apply Hlte'. apply lte_r_sep_conj_perm.
        - etransitivity. 2: apply Hlte''. apply lte_r_sep_conj_perm.
      }
      apply sep_step_sep_conj_l.
      {
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
        symmetry. eapply separate_antimonotone; eauto.
        etransitivity. apply lte_r_sep_conj_perm. eauto.
      }
      etransitivity.
      etransitivity. 2: eapply sep_step_owned_finished.
      apply owned_sep_step; eauto.
      eapply sep_step_lte'.
      etransitivity. 2: apply lfinished_monotone; eauto.
      apply lfinished_sep_conj_perm_dist'.
    }
    constructor.
    - (* the precondition still holds *)
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      split; [| split].
      + assert (Hlen' : length vals' = length not) by auto.
        assert (Heq' : Forall (fun '(b, o1, o2, _, (b', o1', o2')) => b = b' /\ o1 = o1' /\ o2 = o2')
                         (combine not vals')).
        {
          clear Hf HT Hr2.
          clear nop Hlen2 Heq2 Heq3 Hnop Hlte'' Hlen3 Heq4 Hlte''' Hpre' Hpre'' Hlen'.
          revert vals not Hlen1 Heq1 Hlen Heq.
          induction vals'; intros.
          - destruct vals; try solve [inversion Hlen].
            destruct not; try solve [inversion Hlen1].
            constructor.
          - destruct vals; try solve [inversion Hlen].
            destruct not; try solve [inversion Hlen1].
            destruct a as [[b o1] o2].
            destruct p0 as [[[b' o1'] o2'] x].
            inversion Heq; subst; clear Heq. rename H2 into Heq.
            destruct H1 as (? & ? & ?); subst.
            destruct p1 as [[[b' o1'] o2'] v].
            inversion Heq1; subst; clear Heq1. rename H2 into Heq1.
            destruct H1 as (? & ? & ?); subst.
            rename b' into b, o1' into o1, o2' into o2.
            constructor. auto. apply IHvals' with (vals := vals); auto.
        }
        clear Hlen Heq Hlen1 Hlen3 Heq1 Heq3 Heq4 Hlte''' Hpre' Hr2 Hf.
        revert vals' Hlen' Heq'.
        induction not; cbn; intros.
        { split; auto. rewrite lGetPut. symmetry. apply nth_error_replace_list_index_eq. }
        destruct a as [[[b o1] o2] v]. cbn.
        assert (Hv : read (lget si) (b, o1 + o2) = Some v).
        {
          apply Hlte in Hpre. destruct Hpre as (Hpre & _).
          apply Hlte'' in Hpre. cbn in Hpre.
          apply Hpre; auto.
        }
        split; [| split].
        * split. { rewrite lGetPut. symmetry. apply nth_error_replace_list_index_eq. }
          rewrite HGetPut1. auto.
        * destruct vals'. inversion Hlen'.
          apply IHnot with (vals' := vals'); auto.
          -- etransitivity; eauto.
             cbn. rewrite sep_conj_perm_assoc. apply lte_r_sep_conj_perm.
          -- apply Hpre''.
          -- cbn in Heq'. inversion Heq'; subst.
             apply H2.
        * eapply finished_write_perms_separate; apply Hpre''.
      + clear Hlen2 Heq2 Heq3.
        induction nop; cbn; auto.
        destruct a as [[p' ?] ?].
        split; [| split].
        * apply Hnop. apply Hlte''. apply Hlte. apply Hpre.
        * apply IHnop. apply Hnop.
          etransitivity; eauto. cbn.
          apply sep_conj_perm_monotone. reflexivity.
          apply lte_r_sep_conj_perm.
        * apply Hlte in Hpre. destruct Hpre as (Hpre & _).
          apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _). apply Hpre.
      + apply Hlte in Hpre. destruct Hpre as (Hpre & _).
        apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
        destruct (star_list_invs _ _ Hpre Hnop) as (? & ? & ? & ?).

        eapply finished_write_perms_separate'; auto.
        apply Hpre''.
        symmetry. eapply separate_antimonotone. 2: apply Hlte'''.
        symmetry. apply Hsepstep.
        symmetry.
        eapply owned_sep; eauto.
        symmetry.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
        auto.
    - (* we can put everything back together again, hiding the values *)
      clear Hf HT.
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      clear Hpre' Hr2.
      revert vals' not nop Hlen1 Hlen2 Heq1 Heq2 Heq3 Hlen3 Heq4 Hnop Hlte'' Hlte''' Hpre'' Hlen Heq Hpre.
      induction vals; intros.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        cbn. eexists. split. exists bottom_perm. split; auto.
        cbn. rewrite sep_conj_perm_bottom. reflexivity.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        destruct vals'; try solve [inversion Hlen3].
        destruct p0 as [[[b o1] o2] v'].
        destruct p1 as [[p' x] v].
        inversion Heq3; subst; clear Heq3. rename H2 into Heq3.
        destruct a as [[[b' o1'] o2'] x'].
        inversion Heq1; clear Heq1; subst. rename H2 into Heq1.
        destruct H1 as (? & ? & ?). subst.
        inversion Heq2; clear Heq2; subst. rename H2 into Heq2.
        destruct p2 as [[b' o1'] o2'].
        inversion Heq4; clear Heq4; subst. rename H2 into Heq4.
        destruct H1 as (? & ? & ?). subst.
        inversion Heq; subst; clear Heq. clear H1. rename H2 into Heq.
        cbn.
        exists (lfinished l (write_perm (b, o1 + o2) v) ** p'), (finished_write_perms l not ** star_list nop).
        assert (star_list (cons (p', x, v) nop) <= pwhens).
        {
          etransitivity.
          apply lte_r_sep_conj_perm. eauto.
        }
        split; [| split; [| split]].
        * eexists. split. eexists. reflexivity.
          cbn. do 2 eexists. split; [| split; [| split]].
          4: reflexivity. reflexivity. apply Hnop.
          apply lfinished_separate'. apply Hnop.
          symmetry. eapply separate_antimonotone.
          2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
          symmetry. apply Hsepstep.
          symmetry. eapply owned_sep; try apply Hnop; auto.
          eapply separate_antimonotone.
          2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
          symmetry.
          eapply separate_antimonotone.
          2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
          symmetry. auto.
        * apply IHvals with (vals' := vals'); auto.
          -- apply Hnop.
          -- etransitivity. 2: apply Hlte''.
             apply sep_conj_perm_monotone; apply lte_r_sep_conj_perm.
          -- etransitivity; eauto. apply lte_r_sep_conj_perm.
          -- apply Hpre''.
        * apply separate_sep_conj_perm_4.
          -- apply lfinished_separate'. apply Hnop.
             (* copied from above *)
             symmetry. eapply separate_antimonotone.
             2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
             symmetry. auto.
          -- eapply finished_write_perms_separate; apply Hpre''.
          -- apply Hlte in Hpre. destruct Hpre as (Hpre & _).
             apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
             destruct Hpre as (_ & Hpre & _).
             destruct Hnop as (? & ? & ? & ? & ? & Hnop).
             destruct (star_list_invs _ _ Hpre Hnop) as (? & ? & ? & ?).
             apply lfinished_separate'; auto.

             symmetry. eapply separate_antimonotone.
             2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry. auto.
          -- symmetry. eapply finished_write_perms_separate'. apply Hnop.
             apply Hpre''.

             symmetry. eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
             symmetry. auto.
          -- apply Hlte in Hpre. destruct Hpre as (Hpre & _).
             apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
             apply Hpre.
          -- apply Hlte in Hpre. destruct Hpre as (Hpre & _).
             apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
             destruct Hpre as (_ & Hpre & _).
             destruct Hnop as (? & ? & ? & ? & ? & Hnop).
             destruct (star_list_invs _ _ Hpre Hnop) as (? & ? & ? & ?).
             eapply finished_write_perms_separate'; auto.
             apply Hpre''.

             symmetry. eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_antimonotone.
             2: { etransitivity. apply lte_r_sep_conj_perm. eauto. }
             symmetry. auto.
        * rewrite sep_conj_perm_assoc.
          rewrite (sep_conj_perm_commut p').
          rewrite sep_conj_perm_assoc.
          rewrite (sep_conj_perm_commut _ p').
          rewrite sep_conj_perm_assoc. reflexivity.
          Unshelve. eapply nonLifetime_sep_step; eauto.
  Qed.

  Lemma typing_end_ptr {A} l b o (T : VPermType A) xs (HT : forall v a, nonLifetime_Perms (v :: T ▷ a)) :
    typing (specConfig := Ss)
      ((VPtr (b, o)) :: when_ptr l (R, 0, T) ▷ xs *
         (lowned_Perms l ((VPtr (b, o)) :: when_ptr l (R, 0, trueP) ▷ tt)
            ((VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt)))
      (fun l _ => (VPtr (b, o)) :: finished_ptr l (W, 0, T) ▷ xs)
      (endLifetime l)
      (Ret tt).
  Proof.
    intros p' c1 c2 (pwt & lowned' & Hpwt & H & Hsep & Hlte) Hpre.
    destruct Hpwt as (? & (v & ?) & Hpwt); subst.
    destruct Hpwt as (pwhen & pt & Hpwhen & Hpt & Hsep' & Hlte').
    destruct (HT _ _ _ Hpt) as (pt' & Hpt' & Hltept' & Hnlpt' & Hrelypt' & Hguarpt' & Hprept').
    destruct H as (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte'' & Hf).
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    pose proof Hpre as Hpre''.
    apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
    apply Hlte'' in Hpre. destruct Hpre as (_ & H & _).
    cbn in H. setoid_rewrite H.
    rewritebisim @bind_trigger.
    specialize (Hf (when l (read_perm (b, o + 0) v))).
    destruct Hf as (q & Hq & Hsep_step & Hpre).
    {
      eexists. split. eexists. reflexivity. cbn.
      do 2 eexists. split; [| split; [| split]]. 2: auto.
      - reflexivity.
      - apply separate_bottom.
      - rewrite sep_conj_perm_bottom. apply when_monotone.
        reflexivity.
        (* only difference between read and write: *)
        (* apply read_lte_write. *)
    }
    {
      apply Hlte in Hpre''. destruct Hpre'' as (? & ? & ?).
      eapply separate_antimonotone; eauto.
      symmetry. eapply separate_antimonotone; eauto.
      eapply separate_antimonotone; eauto. symmetry. eauto.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
    }
    destruct Hq as (? & (v' & ?) & Hq); subst.
    rewrite sep_conj_Perms_commut in Hq. rewrite sep_conj_Perms_bottom_identity in Hq.
    cbn in Hq.
    assert (Hv: Some v = read (lget c1) (b, o + 0)).
    {
      apply Hlte in Hpre''. destruct Hpre'' as (Hpre'' & _).
      apply Hlte' in Hpre''. destruct Hpre'' as (Hpre'' & _).
      apply Hpwhen in Hpre''. cbn in Hpre''. symmetry. auto.
    }
    assert (v = v'). {
      specialize (Hpre c1 c2).
      apply Hq in Hpre.
      - (* from this we can get that (b, o) points to v using pwhen *)
        cbn in Hpre.
        rewrite HGetPut1 in Hpre. rewrite <- Hv in Hpre. inversion Hpre. auto.
      - rewrite replace_list_index_eq; auto. rewrite lPutGet. cbn.
        intros. symmetry. apply Hv.
      - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
        rewrite lPutGet. auto.
    } subst. rename v' into v.
    assert (Hsep''': owned l r2 Hnlr2 ⊥ pt'). {
      eapply separate_antimonotone; eauto.
      eapply separate_antimonotone. 2: apply lte_r_sep_conj_perm.
      eapply separate_antimonotone; eauto.
      symmetry.
      eapply separate_antimonotone; eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
    }
    econstructor; unfold id; auto.
    {
      cbn in *. apply Hlte. constructor 1. right.
      apply Hlte''. constructor 1. right. right.
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
      econstructor.
      2: {
        cbn. eexists. split. eexists. reflexivity. cbn.
        exists (lfinished l q), pt'. split; [| split; [| split]].
        - apply lfinished_monotone; eauto.
        - auto.
        - apply lfinished_separate'; auto.
          apply Hsep_step. symmetry. eapply owned_sep; eauto. symmetry. eauto.
        - reflexivity.
      }
      cbn. rewrite lGetPut.
      split; split.
      - symmetry. apply nth_error_replace_list_index_eq.
      - apply Hpre.
        + cbn. rewrite lGetPut. rewrite HGetPut1.
          intros. symmetry. apply Hv.
        + rewrite replace_list_index_eq; auto.
          rewrite lPutGet.
          apply Hlte''. apply Hlte. auto.
      - apply Hprept'. apply Hltept'. apply Hlte'. apply Hlte; auto.
      - apply lfinished_separate'; auto.
        apply Hsep_step. symmetry. eapply owned_sep; eauto. symmetry. eauto.
    }
    eapply sep_step_lte; eauto.
    rewrite sep_conj_perm_commut.
    eapply sep_step_lte. apply sep_conj_perm_monotone. eauto.
    etransitivity. 2: apply Hlte'. etransitivity. 2: apply lte_r_sep_conj_perm.
    apply Hltept'.
    eapply sep_step_lte.
    rewrite sep_conj_perm_assoc. apply lte_r_sep_conj_perm.
    apply sep_step_sep_conj_l; auto.
    etransitivity. 2: eapply sep_step_owned_finished.
    apply owned_sep_step; auto.

    Unshelve.
    eapply nonLifetime_sep_step. 2: eauto. auto.
  Qed.

  Lemma partial_ptr b o l o' P Q x :
    (VPtr (b, o) :: when_ptr l (R, o', eqp x) ▷ tt) *
      lowned_Perms l ((VPtr (b, o) :: when_ptr l (R, o', eqp x) ▷ tt) * P) Q
        ⊨
        lowned_Perms l P Q.
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte).
    destruct Hp' as (? & (v & ?) & Hp'); subst.
    destruct Hp' as (pwhen & pt & Hpwhen & Hpt & Hsep' & Hlte''). cbn in Hpt; subst.
    assert (Hsep'': r1 ⊥ when l (read_perm (b, o + o') v)).
    {
      eapply separate_antimonotone. 2: eapply Hpwhen.
      eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
      eapply separate_antimonotone. 2: eauto. symmetry.
      eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
      eapply separate_antimonotone. 2: eauto. auto.
    }
    exists (when l (read_perm (b, o + o') v) ** r1), r2.
    eexists.
    {
      intros. symmetry. apply separate_sep_conj_perm; symmetry; auto.
      - apply when_owned_sep.
      - symmetry; auto.
    }
    eexists.
    {
      apply nonLifetime_sep_conj_perm; auto.
      apply when_nonLifetime. apply nonLifetime_read_perm. symmetry. auto.
    }
    exists Hnlr2, Hrelyr2, Hguarr2.
    split; [| split]; auto.
    {
      etransitivity; eauto. rewrite sep_conj_perm_assoc. apply sep_conj_perm_monotone; auto.
      etransitivity; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm.
    }
    intros p Hp Hsep'''.
    specialize (Hf (when l (read_perm (b, o + o') v) ** p)).
    destruct Hf as (q & Hq & Hsepstep & Hpre).
    - apply sep_conj_Perms_perm; auto.
      + eexists. split. eexists. reflexivity. cbn. do 2 eexists.
        split; [| split; [| split]]; try reflexivity.
        apply separate_bottom. rewrite sep_conj_perm_bottom. reflexivity.
      + symmetry. eapply separate_antimonotone; eauto.
        rewrite sep_conj_perm_assoc. apply lte_l_sep_conj_perm.
    - apply separate_sep_conj_perm_4; auto.
      + rewrite sep_conj_perm_assoc in Hsep'''.
        symmetry. eapply separate_antimonotone; eauto.
        apply lte_l_sep_conj_perm.
      + symmetry; auto.
      + apply when_owned_sep.
      + rewrite (sep_conj_perm_commut _ r1) in Hsep'''. rewrite sep_conj_perm_assoc in Hsep'''.
        eapply separate_antimonotone; eauto.
        apply lte_l_sep_conj_perm.
      + eapply separate_antimonotone; eauto.
        apply lte_r_sep_conj_perm.
    - exists q. split; [| split]; auto.
      intros si ss Hprep (Hprewhen & Hprer1 & Hsep'''').
      apply Hpre; auto.
      split; [| split]; auto.
      rewrite sep_conj_perm_assoc in Hsep'''.
      symmetry. eapply separate_antimonotone; eauto.
      apply lte_l_sep_conj_perm.
  Qed.

  (** Memory rules *)

  Lemma Lifetime_Load xi yi xs l rw P Q :
    xi :: when_ptr l (rw, 0, eqp yi) ▷ xs * lowned_Perms l P Q ⊢
       load xi ⤳
       Ret tt :::
       eqp yi ∅ (xi :: when_ptr l (rw, 0, eqp yi) ▷ xs * lowned_Perms l P Q).
  Proof.
    intros p si ss Hp Hpre.
    repeat intro. pstep. unfold load. rewritebisim @bind_trigger.
    econstructor; eauto; try reflexivity.
    destruct xi as [? | [b o]].
    { destruct Hp as (? & ? & ? & ?). contradiction. }
    destruct Hp as (pwhen & powned & Hpwhen & Hpowned & Hsep & Hlte).
    destruct Hpwhen as (? & (v & ?) & Hpwhen); subst.
    destruct Hpwhen as (pwhen' & peq & Hpwhen' & Hpeq & Hsep' & Hlte'). cbn in Hpeq. subst.
    assert (Hl: statusOf l (lget si) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      destruct Hpowned as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      apply H0 in Hpre. destruct Hpre as (_ & ? & _).
      apply H2.
    }
    assert (Hv: read (lget si) (b, o) = Some v).
    {
      apply Hlte in Hpre. rewrite Nat.add_0_r in *.
      destruct Hpre as (Hpre & _). apply Hlte' in Hpre.
      destruct Hpre as (Hpre & _). apply Hpwhen' in Hpre.
      destruct rw.
      apply Hpre; auto.
      symmetry. apply Hpre; auto. (* TODO: why are read_perm and write_perm different *)
    }
    rewrite Hv. constructor; auto.
    cbn in Hpwhen'.
    cbn. exists bottom_perm, p. split; [| split; [| split]]; auto.
    - exists pwhen, powned. split; auto.
      eexists. split; eauto.
      cbn. exists pwhen', bottom_perm. split; [| split; [| split]]; eauto.
      apply separate_bottom.
      rewrite sep_conj_perm_bottom. etransitivity; eauto. apply lte_l_sep_conj_perm.
    - symmetry. apply separate_bottom.
    - rewrite sep_conj_perm_commut. apply sep_conj_perm_bottom.
  Qed.

  Lemma Lifetime_Store xi yi l x P Q :
    xi :: when_ptr l (W, 0, eqp x) ▷ tt *
    lowned_Perms l
      (xi :: when_ptr l (R, 0, eqp x) ▷ tt * P)
      (xi :: ptr(W, 0, eqp x) ▷ tt * Q) ⊢
    store xi yi ⤳
    Ret tt :::
    trueP ∅ (xi :: when_ptr l (W, 0, eqp yi) ▷ tt *
    lowned_Perms l
      (xi :: when_ptr l (R, 0, eqp yi) ▷ tt * P)
      (xi :: ptr(W, 0, eqp yi) ▷ tt * Q)).
  Proof.
    intros p' si ss H Hpre.
    destruct H as (pwhen & powned & Hpwhen & Hpowned & Hsep & Hlte).
    destruct xi as [| [b o]]; try contradiction.
    destruct Hpwhen as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pw & peq & Hwritelte & Heq & Hsep' & Hlte').
    cbn in Heq. subst.
    destruct Hpowned as (r1 & r2 & Hr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte'' & Hf).
    destruct Hr2 as (pwrite' & q & (? & (v' & ?) & Hpwrite) & Hq & Hsep'' & Hlte'''); subst.
    destruct Hpwrite as (pwrite & peq' & Hpwrite & Heq & Hsep''' & Hlte'''').
    cbn in Heq. subst. rename v' into v.
    rewrite Nat.add_0_r in *.
    assert (Hcurrent : statusOf l (lget si) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & ? & _).
      apply Hlte'' in H. destruct H as (_ & ? & _). auto.
    }
    assert (Hread: read (lget si) (b, o) = Some v).
    {
      apply Hlte in Hpre. destruct Hpre as (Hpre & ? & _).
      apply Hlte' in Hpre. destruct Hpre as (Hpre & _).
      apply Hwritelte in Hpre.
      symmetry. apply Hpre; auto.
    }
    eapply (read_success_write _ _ _ yi) in Hread.
    destruct Hread as (c' & Hwrite).
    assert (Hguar : guar p' (si, ss) ((lput si c'), ss)).
    {
      apply Hlte. constructor 1. left.
      apply Hlte'. constructor 1. left. apply Hwritelte. cbn. right.
      split; [| split]; auto.
      repeat rewrite lGetPut.
      split; [| split; [| split]].
      - eexists. reflexivity.
      - eapply write_success_read_neq; eauto.
      - eapply write_success_sizeof; eauto.
      - eapply write_success_length; eauto.
    }
    pstep. unfold store.
    rewritebisim @bind_trigger.
    econstructor; eauto.
    3: {
      rewrite Hwrite. constructor; eauto.
      2: { exists bottom_perm.
           eexists (when l (write_perm (b, o) yi) ** (r1 ** owned l ((write_perm (b, o) yi) ** q) _)).
           split; [| split; [| split]]; auto.
           - cbn; auto.
           - do 2 eexists. split; [| split; [| split]].
             4: reflexivity.
             + eexists. split. eexists. reflexivity.
               cbn. do 2 eexists. split; [| split; [| split]]; try reflexivity.
               apply separate_bottom.
               rewrite Nat.add_0_r.
               apply sep_conj_perm_bottom.
             + eexists r1, (write_perm (b, o) yi ** q). eexists.
               apply Hr1. exists Hnlr1.
               eexists. eexists. admit. eexists. admit. (* need that q satisfies the rely and guar invs *)
               split; [| split].
               2: reflexivity.
               * do 2 eexists. split; [| split; [| split]]. 4: reflexivity.
                 cbn. eexists. split. eexists. reflexivity. cbn.
                 do 2 eexists. split; [| split; [| split]]; try reflexivity.
                 apply separate_bottom.
                 rewrite Nat.add_0_r.
                 apply sep_conj_perm_bottom.
                 auto.
                 eapply sep_step_write_perm; eauto.
                 symmetry. eapply separate_antimonotone.
                 2: apply Hpwrite.
                 eapply separate_antimonotone.
                 2: apply lte_l_sep_conj_perm.
                 eapply separate_antimonotone. 2: eauto.
                 symmetry. auto.
               * intros. exists (write_perm (b, o) yi ** q). split; [| split]. 2: reflexivity.
                 apply sep_conj_Perms_perm; auto.
                 eexists. split. eexists. reflexivity.
                 rewrite Nat.add_0_r.
                 do 2 eexists. split; [| split; [| split]]; cbn; try reflexivity.
                 apply separate_bottom. apply sep_conj_perm_bottom.
                 admit.
                 intros.
             (* need to use Hf here, but cannot get the sep_step result *)
                 admit.
             + admit.
           - admit.
           - reflexivity.
      }
      admit.
    }
    - rewrite Hwrite. auto.
    - rewrite Nat.add_0_r. eapply sep_step_lte; eauto.
      etransitivity.
      + eapply sep_step_lte; [| reflexivity]. apply lte_l_sep_conj_perm.
      + cbn in *. eapply sep_step_lte; eauto. intros ? []. constructor; auto.
  Qed.

  Lemma ex3_typing b o xs :
    typing
      (lifetime_Perms * (VPtr (b, o)) :: ptr (W, 0, IsNat Si Ss) ▷ xs)
      (fun l _ => lifetime_Perms * (VPtr (b, o)) :: finished_ptr l (W, 0, IsNat Si Ss) ▷ xs)
      (l <- beginLifetime ;; Ret tt ;; endLifetime l)
      (Ret tt ;; Ret tt ;; Ret tt).
  Proof.
    eapply typing_bind.
    { apply typing_frame. apply typing_begin. }
    intros. unfold id.
    rewrite sep_conj_Perms_commut.
    rewrite sep_conj_Perms_assoc.
    setoid_rewrite (sep_conj_Perms_commut lifetime_Perms).
    apply typing_frame.

    eapply typing_bind with (Q := (fun _ _ => (VPtr (b, o) :: when_ptr r1 (W, 0, IsNat Si Ss) ▷ xs *
     lowned_Perms r1 (VPtr (b, o) :: when_ptr r1 (R, 0, trueP) ▷ tt * bottom_Perms)
       (VPtr (b, o) :: ptr (W, 0, trueP) ▷ tt * bottom_Perms)))).
    {
      eapply typing_lte with (Q := fun _ _ => VPtr (b, o) :: when_ptr r1 (W, 0, IsNat Si Ss) ▷ xs *
   lowned_Perms r1 (VPtr (b, o) :: when_ptr r1 (R, 0, trueP) ▷ tt * bottom_Perms)
     (VPtr (b, o) :: ptr (W, 0, trueP) ▷ tt * bottom_Perms)).
      2: {
        apply split_Perms_T.
        repeat intro.
        cbn in *. subst. exists bottom_perm.
        split; [| split; [| split; [| split]]]; auto.
        apply bottom_perm_is_bottom.
        apply nonLifetime_bottom.
        apply guar_inv_bottom.
        apply pre_inv_bottom.
      }

      apply typing_ret. reflexivity.
      reflexivity.
    }
    intros _ _. apply typing_end_ptr.

    eapply typing_bind with (Q:=(fun _ _ : unit =>
                                   VPtr (b, o) :: ptr (W, 1, IsNat Si Ss) ▷ xs2 *
                                     lowned_Perms r1 bottom_Perms bottom_Perms *
                                     VPtr (b, o) :: ptr (W, 0, IsNat Si Ss) ▷ xs1)).
    { rewrite <- sep_conj_Perms_assoc.
      rewrite (sep_conj_Perms_commut _ (lowned_Perms _ _ _)).
      rewrite sep_conj_Perms_commut.
      apply typing_frame.
      eapply typing_lte.
      2: { rewrite sep_conj_Perms_commut. eapply split_Perms_T. admit. }
      apply typing_ret.
      reflexivity.
    }
    { rewrite
      }

    eapply typing_lte with (Q:=(fun _ _ : unit =>
                                  VPtr (b, o) :: ptr (W, 0, IsNat Si Ss) ▷ xs1 *
                                    VPtr (b, o) :: ptr (W, 1, IsNat Si Ss) ▷ xs2)).
    3: reflexivity.
    2: {
      rewrite <- sep_conj_Perms_assoc.
      etransitivity.
      apply lte_r_sep_conj_Perms.
      apply split_Perms_T.
      admit.
    }
    eapply typing_lte with (Q:=(fun _ _ : unit =>
                                  VPtr (b, o) :: ptr (W, 0, IsNat Si Ss) ▷ xs1 *
                                    VPtr (b, o) :: ptr (W, 1, IsNat Si Ss) ▷ xs2)).
    3: reflexivity.
    2: {
      apply split_Perms_T.
      admit.
    }


  Qed.

End Perms.
