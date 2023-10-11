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

  (* We *only* have this lemma for pointer permissions, due to contraints about preconditions (I think?) TODO: generalize *)
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
    destruct (HT _ _ _ Hpt) as (pt' & Hpt' & Hltept & Hnlpt & Hrelypt & Hguarpt & Hprept).
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

  Lemma when_ptrs_T_app l l1 l2 :
    when_ptrs_T l (l1 ++ l2) ≡
    when_ptrs_T l l1 * when_ptrs_T l l2.
  Proof.
    revert l2.
    induction l1; intros.
    - cbn. rewrite sep_conj_Perms_bottom_identity. reflexivity.
    - destruct a as [[[? ?] ?] ?]. unfold app. unfold when_ptrs_T.
      rewrite <- sep_conj_Perms_assoc.
      apply Proper_eq_Perms_sep_conj_Perms; [reflexivity | apply IHl1].
  Qed.

  Lemma when_ptrs_T_swap' l a b :
    when_ptrs_T l ([a ; b]) ≡
    when_ptrs_T l ([b ; a]).
  Proof.
    destruct a as [[[? ?] ?] ?].
    destruct b as [[[? ?] ?] ?].
    unfold when_ptrs_T.
    rewrite sep_conj_Perms_commut.
    do 2 rewrite (sep_conj_Perms_commut _ bottom_Perms).
    do 2 rewrite sep_conj_Perms_bottom_identity. reflexivity.
  Qed.

  Lemma when_ptrs_T_swap l l1 a b l2 :
    when_ptrs_T l (l1 ++ [a ; b] ++ l2) ≡
    when_ptrs_T l (l1 ++ [b ; a] ++ l2).
  Proof.
    do 4 rewrite when_ptrs_T_app.
    apply Proper_eq_Perms_sep_conj_Perms; [reflexivity |].
    apply Proper_eq_Perms_sep_conj_Perms; [| reflexivity].
    apply when_ptrs_T_swap'.
  Qed.

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
  Fixpoint star_list (vals : list (perm * {A & @VPermType Si Ss A} * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => bottom_perm
    | cons v vals => let '(p, _, _) := v in
                    p ** star_list vals
    end.

  Fixpoint specs_type' (vals : list (@perm (Si * Ss) * {A & @VPermType Si Ss A} * Value)) : Type :=
    match vals with
    | nil => unit
    | cons v vals =>
        let '(_, T, _) := v in
        prod (projT1 T) (specs_type' vals)
    end.

  (** checks that each of the perms in the list are in the corresponding T in the list, plus some nonLifetime invariants on the perms *)
  Fixpoint perms_in_T_inv (vals : list (@perm (Si * Ss) * {A & @VPermType Si Ss A} * Value)) :
    specs_type' vals -> Prop.
    refine (fun xs => _).
    destruct vals as [| v vals].
    - apply True.
    - destruct v as [[p T] v].
      destruct xs as [x xs].
      apply (p ∈ v :: projT2 T ▷ x /\
               nonLifetime p /\
               rely_inv p /\
               guar_inv p /\
               pre_inv p /\
               perms_in_T_inv vals xs).
  Defined.
  (*             match vals with *)
  (*             | nil => True *)
  (*             | cons v vals' => let '(p, T, v') := v in *)
  (*                             p ∈ v' :: projT2 T ▷ _ /\ *)
  (*                               nonLifetime p /\ *)
  (*                               rely_inv p /\ *)
  (*                               guar_inv p /\ *)
  (*                               pre_inv p /\ *)
  (*                               perms_in_T_inv vals' _ *)
  (*             end). *)
  (*   - apply  *)
  (* Defined. *)

  Lemma star_list_invs vals c xs :
    pre (star_list vals) c ->
    perms_in_T_inv vals xs ->
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
    - intros Hpre H. destruct a as [[p T] v]. destruct xs as [x xs].
      destruct H as (? & ? & ? & ? & ? & ?).
      split; [| split; [| split]].
      + cbn. apply nonLifetime_sep_conj_perm; auto.
        eapply IHvals; eauto.
        apply Hpre. apply Hpre.
      + apply guar_inv_sep_conj_perm; auto. eapply IHvals; eauto. apply Hpre.
      + apply rely_inv_sep_conj_perm; auto. eapply IHvals; eauto. apply Hpre.
      + apply pre_inv_sep_conj_perm; auto. eapply IHvals; eauto. apply Hpre.
  Qed.

  (** Gives up the vals that each pointer points to *)

  (* Lemma split_when_ptrs_T l nov (* no vals *) *)
  (*   (HT: Forall (fun '(_, _, _, x) => forall (v : Value) (a : (projT1 x)), nonLifetime_Perms (v :: (fst (projT2 x)) ▷ a)) nov) *)
  (*   p : *)
  (*   p ∈ when_ptrs_T l nov -> *)
  (*   (* we are basically only coming up with the list of vals *) *)
  (*   exists not nop (* no Ts, no s *) *)
  (*     (Hlen1 : length nov = length not) *)
  (*     (Hlen2 : length nov = length nop) *)
  (*     (Heq1: Forall (fun '((b, o1, o2, _), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov not)) *)
  (*     (Heq2: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop)) *)
  (*     (Heq3: Forall (fun '((_, _, _, v), (_, _, v')) => v = v') (combine not nop)), *)
  (*     perms_in_T_inv nop /\ (* each of the perms is in v :: T ▷ xs and satisfies invariants *) *)
  (*     when_read_perms l not ** star_list nop <= p. *)
  (* Proof. *)
  (*   revert p HT. induction nov; intros p HT Hp. *)
  (*   { *)
  (*     exists [], []. cbn. do 5 (exists; auto). *)
  (*     split; auto. *)
  (*     rewrite sep_conj_perm_bottom. apply bottom_perm_is_bottom. *)
  (*   } *)
  (*   destruct a as [[[b o1] o2] X]. *)
  (*   destruct Hp as (p1 & ps & Hp1 & Hps & Hsep & Hlte). *)
  (*   destruct Hp1 as (? & (v & ?) & Hp1); subst. *)
  (*   destruct Hp1 as (pptr & pt' & Hpptr & Hpt' & Hsep' & Hlte'). *)
  (*   inversion HT; subst; clear HT. *)
  (*   rename H2 into HT. *)
  (*   cbn in H1, Hpt'. specialize (H1 v (snd (projT2 X)) _ Hpt'). *)
  (*   destruct H1 as (pt & Hpt & Hptpt' & Hnlpt & Hrelypt & Hguarpt & Hprept). *)
  (*   specialize (IHnov ps HT Hps). *)
  (*   destruct IHnov as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hin & Hlte''). *)
  (*   exists (cons (b, o1, o2, v) not), (cons (pt, X, v) nop). *)
  (*   do 5 (exists; cbn; auto). *)
  (*   split; [split |]; auto. *)
  (*   etransitivity; eauto. *)
  (*   rewrite sep_conj_perm_assoc. *)
  (*   rewrite <- (sep_conj_perm_assoc _ pt). *)
  (*   rewrite (sep_conj_perm_commut _ pt). *)
  (*   rewrite sep_conj_perm_assoc. *)
  (*   rewrite <- sep_conj_perm_assoc. *)
  (*   apply sep_conj_perm_monotone; auto. *)
  (*   etransitivity; eauto. *)
  (*   apply sep_conj_perm_monotone; auto. *)
  (* Qed. *)

  (** all the when_ptr (R) [Perms] starred together, with a trueP on each *)
  Fixpoint when_ptrs_trueP l (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) :=
    match vals with
    | nil => bottom_Perms
    | cons v vals => let '(b, o, o', _) := v in
                    (VPtr (b, o) :: when_ptr l (R, o', trueP) ▷ tt) *
                      when_ptrs_trueP l vals
    end.

  Lemma when_read_perms_when_ptrs_trueP' l vals vals'
    (Hlen : length vals = length vals')
    (Heq : Forall (fun '((b, o1, o2, _), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine vals vals')) :
    when_read_perms l vals ∈ when_ptrs_trueP l vals'.
  Proof.
    revert vals' Hlen Heq.
    induction vals; intros; destruct vals'; try solve [inversion Hlen].
    { cbn. auto. }
    destruct a as [[[b o1] o2] v].
    destruct p as [[[b' o1'] o2'] x]. inversion Heq; clear Heq.
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
  Fixpoint ptrs_trueP' (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : @Perms (Si * Ss) :=
    match vals with
    | nil => bottom_Perms
    | cons v vals => let '(b, o, o', _) := v in
                    (VPtr (b, o) :: ptr (W, o', trueP) ▷ tt) *
                      ptrs_trueP' vals
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

  Lemma lfinished_bottom_twice l :
    lfinished_Perms (Ss := Ss) l bottom_Perms * lfinished_Perms l bottom_Perms ≡
    lfinished_Perms l bottom_Perms.
  Proof.
    split; repeat intro.
    - do 2 exists (lfinished l bottom_perm). split; [| split; [| split]].
      + cbn. eexists. split. eexists. split. auto. reflexivity.
        cbn. reflexivity.
      + cbn. eexists. split. eexists. split. auto. reflexivity.
        cbn. reflexivity.
      + apply lfinished_separate. apply separate_bottom.
      + cbn in H. destruct H as (? & (? & _ & ?) & ?). subst. cbn in H0.
        etransitivity. apply lfinished_sep_conj_perm_dist.
        etransitivity; eauto.
        apply lfinished_monotone.
        rewrite sep_conj_perm_bottom. apply bottom_perm_is_bottom.
    - destruct H as (? & ? & ? & ? & ? & ?).
      eapply Perms_upwards_closed; eauto. etransitivity; eauto. apply lte_r_sep_conj_perm.
  Qed.

  Lemma finished_ptrs_T_app l l1 l2 :
    finished_ptrs_T l (l1 ++ l2) ≡
      finished_ptrs_T l l1 * finished_ptrs_T l l2.
  Proof.
    revert l2.
    induction l1; intros.
    - cbn. induction l2.
      + cbn. rewrite lfinished_bottom_twice. reflexivity.
      + destruct a as [[[? ?] ?] ?]. unfold finished_ptrs_T. rewrite IHl2.
        do 2 rewrite (sep_conj_Perms_commut (lfinished_Perms l bottom_Perms)).
        rewrite sep_conj_Perms_assoc.
        rewrite <- (sep_conj_Perms_assoc _ (lfinished_Perms l bottom_Perms)).
        rewrite lfinished_bottom_twice.
        reflexivity.
    - destruct a as [[[? ?] ?] ?]. unfold app. unfold finished_ptrs_T.
      rewrite <- sep_conj_Perms_assoc.
      apply Proper_eq_Perms_sep_conj_Perms; [reflexivity | apply IHl1].
  Qed.

  Lemma finished_ptrs_T_swap' l a b :
    finished_ptrs_T l ([a ; b]) ≡
      finished_ptrs_T l ([b ; a]).
  Proof.
    destruct a as [[[? ?] ?] ?].
    destruct b as [[[? ?] ?] ?].
    unfold finished_ptrs_T.
    do 2 rewrite sep_conj_Perms_assoc.
    rewrite (sep_conj_Perms_commut (VPtr (n, n0) :: finished_ptr l (W, n1, fst (projT2 s)) ▷ snd (projT2 s))).
    reflexivity.
  Qed.

  Lemma finished_ptrs_T_swap l l1 a b l2 :
    finished_ptrs_T l (l1 ++ [a ; b] ++ l2) ≡
      finished_ptrs_T l (l1 ++ [b ; a] ++ l2).
  Proof.
    do 4 rewrite finished_ptrs_T_app.
    apply Proper_eq_Perms_sep_conj_Perms; [reflexivity |].
    apply Proper_eq_Perms_sep_conj_Perms; [| reflexivity].
    apply finished_ptrs_T_swap'.
  Qed.

  (*
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
    intros.
    eapply typing_lte.
    apply (typing_end_ptr_n l [(b, o, 0, existT _ A (T, xs))] [(b, o, 0)]).
    - auto.
    - constructor. auto. constructor.
    - constructor. auto. constructor.
    - unfold when_ptrs_T, when_ptrs_trueP.
      rewrite (sep_conj_Perms_commut _ bottom_Perms). rewrite sep_conj_Perms_bottom_identity.
      apply sep_conj_Perms_monotone. reflexivity.
      intros p Hp.
      destruct Hp as (r1 & r2 & Hsep & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte & Hf).
      exists r1, r2, Hsep, Hnlr1, Hnlr2, Hrelyr2, Hguarr2.
      eexists.
      {
        unfold ptrs_trueP.
        rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. auto.
      }
      eexists. auto.
      intros.
      rewrite sep_conj_Perms_commut in H. rewrite sep_conj_Perms_bottom_identity in H. auto.
      unfold ptrs_trueP.
      setoid_rewrite sep_conj_Perms_commut. setoid_rewrite sep_conj_Perms_bottom_identity.
      apply Hf; auto.
    - intros. unfold finished_ptrs_T.
      apply lte_l_sep_conj_Perms.
  Qed.
*)

  (*
  Definition lowned_Perms' l vals vals' :=
    when_ptrs_T l vals *
    lowned_Perms l
      (when_ptrs_trueP l vals')
      (ptrs_trueP' vals').

  Lemma lowned_Perms_convert l :
    lowned_Perms l bottom_Perms bottom_Perms ≡
      lowned_Perms' l [] [].
  Proof.
    unfold lowned_Perms'. cbn. rewrite sep_conj_Perms_bottom_identity. reflexivity.
  Qed.

  Lemma split' b o o' l A (T : VPermType A) xs vals vals'
    (HT : forall xi xs, nonLifetime_Perms (xi :: T ▷ xs)) :
    (VPtr (b, o)) :: ptr(W, o', T) ▷ xs * lowned_Perms' l vals vals' ⊨
      (VPtr (b, o) :: when_ptr l (W, o', T) ▷ xs) *
      lowned_Perms' l vals (cons (b, o, o') vals').
  Proof.
    unfold lowned_Perms'.
    do 2 rewrite sep_conj_Perms_assoc.
    do 2 rewrite (sep_conj_Perms_commut _ (when_ptrs_T l vals)).
    do 2 rewrite <- sep_conj_Perms_assoc.
    apply sep_conj_Perms_monotone. reflexivity.
    apply split_Perms_T; auto.
  Qed.

  Lemma partial' b o o' l A (T : VPermType A) xs vals vals' :
    (VPtr (b, o) :: when_ptr l (R, o', T) ▷ xs) *
    lowned_Perms' l vals vals' ≡
      lowned_Perms' l (cons (b, o, o', existT _ A (T, xs)) vals) vals'.
  Proof.
    unfold lowned_Perms'.
    rewrite sep_conj_Perms_assoc.
    reflexivity.
  Qed.

  Lemma end_lifetime' l vals vals'
    (Hlen : length vals = length vals')
    (Heq : Forall (fun '((b, o1, o2, _), (b', o1', o2')) => b = b' /\ o1 = o1' /\ o2 = o2') (combine vals vals'))
    (HT: Forall (fun '(_, _, _, x) => forall (v : Value) (a : (projT1 x)), nonLifetime_Perms (v :: (fst (projT2 x)) ▷ a)) vals) :
    typing (specConfig := Ss)
      (lowned_Perms'  l vals vals')
      (fun l _ => finished_ptrs_T l vals)
      (endLifetime l)
      (Ret tt).
  Proof.
    unfold lowned_Perms'. apply typing_end_ptr_n; auto.
  Qed.
*)

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

  Lemma sep_step_when_write_perm l p v v' :
    sep_step (when (Ss := Ss) l (write_perm p v)) (when l (write_perm p v')).
  Proof.
    repeat intro. split; apply H; auto.
  Qed.

  Lemma Lifetime_Store xi yi l x P Q :
    xi :: when_ptr l (W, 0, eqp x) ▷ tt * lowned_Perms l P Q ⊢
    store xi yi ⤳
    Ret tt :::
    trueP ∅ (xi :: when_ptr l (W, 0, eqp yi) ▷ tt * lowned_Perms l P Q).
  Proof.
    intros p' si ss H Hpre.
    destruct H as (pwhen & powned & Hpwhen & Hpowned & Hsep & Hlte).
    destruct xi as [| [b o]]; try contradiction.
    destruct Hpwhen as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pw & peq & Hwritelte & Heq & Hsep' & Hlte').
    cbn in Heq. subst.
    destruct Hpowned as (r1 & r2 & Hr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte'' & Hf).
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
    assert (Hguar : guar pwhen (si, ss) ((lput si c'), ss)).
    {
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
    econstructor; auto.
    3: {
      assert (when l (write_perm (b, o) yi) ⊥ powned).
      {
        eapply sep_step_when_write_perm.
        symmetry. eapply separate_antimonotone.
        2: apply Hwritelte.
        eapply separate_antimonotone.
        2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
        symmetry. eauto.
      }
      rewrite Hwrite. constructor; auto.
      2: {
        exists bottom_perm, (when l (write_perm (b, o) yi) ** powned).
        split; [| split; [| split]].
        - cbn. auto.
        - apply sep_conj_Perms_perm; auto.
          + eexists. split. eexists. reflexivity.
            cbn. eexists. exists bottom_perm.
            split; [| split; [| split]]; eauto; try reflexivity.
            apply separate_bottom.
            rewrite sep_conj_perm_bottom. rewrite Nat.add_0_r. reflexivity.
          + exists r1, r2. exists Hr1, Hnlr1, Hnlr2, Hrelyr2, Hguarr2.
            split; [| split]; auto.
        - symmetry. apply separate_bottom.
        - rewrite sep_conj_perm_commut.
          rewrite sep_conj_perm_bottom. reflexivity.
      }
      split; [| split]; auto.
      - cbn. intros. symmetry. eapply write_success_read_eq; rewrite lGetPut; eauto.
      - respects.
        2: { apply Hlte. apply Hpre. }
        apply Hsep. apply Hguar.
    }
    - rewrite Hwrite. apply Hlte. constructor. left. apply Hguar.
    - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
      cbn in *. eapply sep_step_lte; eauto.
      eapply sep_step_lte. apply lte_l_sep_conj_perm.
      eapply sep_step_lte; eauto.
      intros ? []. constructor; auto.
  Qed.

  Lemma weaken_when_ptr b o o' l A (T : VPermType A) xs :
    VPtr (b, o) :: when_ptr l (W, o', T) ▷ xs ⊨
    VPtr (b, o) :: when_ptr l (R, o', T) ▷ xs.
  Proof.
    unfold when_ptr. unfold when_ptr_Perms.
    repeat intro. cbn in *.
    destruct H as (? & (? & ?) & ?). subst. destruct H0 as (? & ? & ? & ? & ? & ?).
    cbn in *.
    eexists. split. eexists. reflexivity.
    cbn. exists x, x1. split; [| split; [| split]]; eauto.
    etransitivity; eauto. apply when_monotone. apply read_lte_write.
  Qed.

  Lemma nonLifetime_IsNat :
    forall (xi : Value) (xs : {_ : nat & unit}), nonLifetime_Perms (xi :: IsNat Si Ss ▷ xs).
  Proof.
    repeat intro. exists bottom_perm.
    split; [| split; [| split; [| split; [| split]]]]; auto.
    apply bottom_perm_is_bottom.
    apply nonLifetime_bottom.
    apply rely_inv_bottom.
    apply guar_inv_bottom.
    apply pre_inv_bottom.
  Qed.

  (*
  Lemma ex3_typing b o xs xs' :
    typing
      (lifetime_Perms * (VPtr (b, o)) :: ptr (W, 0, IsNat Si Ss) ▷ xs * (VPtr (b, o)) :: ptr (W, 1, IsNat Si Ss) ▷ xs')
      (fun l _ => lifetime_Perms * finished_ptrs_T l
                                  [(b, o, 0, existT _ _ (isNat, xs));
                                   (b, o, 1, existT _ _ (isNat, xs'))])
      (l <- beginLifetime ;; endLifetime l)
      (Ret tt ;; Ret tt).
  Proof.
    eapply typing_bind.
    { rewrite <- sep_conj_Perms_assoc. apply typing_frame. apply typing_begin. }
    intros. unfold id.
    rewrite sep_conj_Perms_commut.
    rewrite sep_conj_Perms_assoc.
    (* setoid_rewrite <- (sep_conj_Perms_assoc lifetime_Perms). *)
    setoid_rewrite (sep_conj_Perms_commut lifetime_Perms).
    apply typing_frame.

    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      etransitivity.
      {
        rewrite sep_conj_Perms_commut. apply sep_conj_Perms_monotone.
        rewrite lowned_Perms_convert. reflexivity.
        reflexivity.
      }
      rewrite sep_conj_Perms_commut.
      rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone. reflexivity.
      apply split'.
      apply nonLifetime_IsNat.
    }
    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      rewrite sep_conj_Perms_commut.
      rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone. reflexivity.
      rewrite sep_conj_Perms_commut.
      apply split'.
      apply nonLifetime_IsNat.
    }

    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      apply sep_conj_Perms_monotone. 2: reflexivity.
      apply weaken_when_ptr.
    }
    rewrite (sep_conj_Perms_commut _ (lowned_Perms' _ _ _)).
    rewrite sep_conj_Perms_assoc.
    rewrite partial'.

    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      apply sep_conj_Perms_monotone. reflexivity.
      apply weaken_when_ptr.
    }
    rewrite sep_conj_Perms_commut.
    rewrite partial'.

    (* apply end_lifetime'; auto. *)
    (* - constructor; auto. *)
    (* - constructor. apply nonLifetime_IsNat. *)
    (*   constructor. apply nonLifetime_IsNat. *)
    (*   constructor. *)
  Abort.
*)

  Check 1.

  Lemma finished_rules {R1 R2} P (Q : R1 -> R2 -> Perms) t s l
    (HP : nonLifetime_Perms P) :
    typing (specConfig := Ss) P Q t s ->
    typing (lfinished_Perms l P) (fun r1 r2 => lfinished_Perms l (Q r1 r2)) t s.
  Proof.
    intros Ht p0 si ss (? & (p' & Hp' & ?) & Hp0) Hpre'; subst.
    destruct (HP _ Hp') as (p & Hp & Hlte & Hnlp & Hrest).
    pose proof Hpre' as H.
    apply Hp0 in H. destruct H as (Hfin & Hpre).
    apply Hlte in Hpre.
    specialize (Ht _ _ _ Hp Hpre).
    pstep. punfold Ht. 2: admit.
    cbn in Hp0.
    (* clear Hlte Hp' p' Hp0. *)
    clear Hp Hp'.
    revert p0 Hp0 Hpre'. (* p' Hp' Hp0 Hlte. *)
    revert p' Hlte.
    (* clear Hp Hp Hrest Hpre. *)
    clear Hrest Hpre.
    induction Ht; intros; auto.
    - constructor 1; auto.
      eexists. split; eauto.
      cbn. etransitivity. 2: apply Hp0. apply lfinished_monotone. auto.
    - constructor 2.
    - constructor 3; eauto.
    - constructor 4; eauto.
    - admit.
    - apply sbuter_gen_pre in Ht. destruct Ht.
      { rewrite H2. constructor 2. }
      econstructor 6; auto.
      + apply Hp0. cbn. right. split; [| split]; auto.
        eapply nonLifetime_guar in H0; auto.
        apply Hlte; auto.
      + cbn in Hp0. eapply sep_step_lte; eauto.
        apply lfinished_sep_step.
        eapply sep_step_lte; eauto.
      + eapply IHHt; auto.
        * eapply nonLifetime_sep_step; eauto.
        * eapply nonLifetime_guar in H0; auto.
          cbn in H0. rewrite <- H0. auto.
        * reflexivity.
        * reflexivity.
        * cbn. split; auto. apply nonLifetime_guar in H0; auto.
          cbn in H0. rewrite <- H0; auto.
    - econstructor 7; auto.
      + apply Hp0. cbn. right. split; [| split]; auto.
        apply Hlte; auto.
      + cbn in Hp0. eapply sep_step_lte; eauto.
        apply lfinished_sep_step.
        eapply sep_step_lte; eauto.
      + apply sbuter_gen_pre in Ht. destruct Ht.
        { rewrite H2. constructor 2. }
        eapply IHHt; auto.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * reflexivity.
        * split; auto.
    - admit.
    - specialize (H1 true).
      apply sbuter_gen_pre in H1. destruct H1.
      { rewrite H1. constructor 2. }
      econstructor 9; auto.
      + cbn in Hp0. eapply sep_step_lte; eauto.
        apply lfinished_sep_step.
        eapply sep_step_lte; eauto.
      + intros b. eapply H2; auto.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * reflexivity.
        * split; auto.
    - econstructor 10; auto.
      + cbn in Hp0. eapply sep_step_lte; eauto.
        apply lfinished_sep_step.
        eapply sep_step_lte; eauto.
      + intros b. specialize (H1 b). apply sbuter_gen_pre in H1.
        destruct H1.
        { rewrite H1. constructor 2. }
        eapply H2; auto.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * reflexivity.
        * split; auto.
    - admit.
  Abort.

  (* Fixpoint when_ptrs_T' l (vals : list (nat * {A & (VPermType (Si := Si) A)})) : *)
  (*   @PermType Si Ss _ _ := *)
  (*   match vals with *)
  (*   | nil => trueP *)
  (*   | cons v vals => *)
  (*       let '(o, x) := v in *)
  (*   (*     ptr (R, o, (projT2 x)) ⋆ when_ptrs_T' l vals *) *)
  (*   (* end. *) *)

  (*       {| ptApp := fun xi xss => *)
  (*                     xi :: ptr (rw, o, T) ▷ Vector.hd xss * *)
  (*                       xi :: arr_perm rw (S o) l' T ▷ Vector.tl xss *)
  (*       |} *)
  (*   end. *)
  (*         let '(b, o, o', x) := v in *)
  (*                   (VPtr (b, o) :: when_ptr l (R, o', (fst (projT2 x))) ▷ (snd (projT2 x))) * *)
  (*                     when_ptrs_T l vals *)
  (*   end. *)

  Fixpoint specs_type (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : Type :=
    match vals with
    | nil => unit
    | cons v vals =>
        let '(_, _, _, x) := v in
        prod (projT1 x) (specs_type vals)
    end.
  (* Fixpoint specs (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : (specs_type vals) := *)
  (*   match vals with *)
  (*   | nil => tt *)
  (*   | cons v vals => *)
  (*       let '(_, _, _, x) := v in *)
  (*       (snd (projT2 x), specs vals) *)
  (*   end. *)
  Fixpoint values_type (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : Type :=
    match vals with
    | nil => unit
    | cons v vals =>
        prod Value (values_type vals)
    end.
  Fixpoint values (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : values_type vals :=
    match vals with
    | nil => tt
    | cons v vals =>
        let '(b, o, _, _) := v in
        (VPtr (b, o), values vals)
    end.
  Definition lowned_Perms'' vals : PermType (Ss := Ss) nat (specs_type vals -> specs_type vals) :=
    {|
      ptApp := fun l _ =>
                 lowned_Perms l
                   (when_ptrs_trueP l vals)
                   (ptrs_trueP' vals)
    |}.

  Fixpoint when_ptrs_T' l (vals : list (nat * nat * nat * {A : Type & VPermType A}))
    : PermType (values_type vals) (specs_type vals) :=
    match vals with
    | nil => trueP
    | cons v vals => let '(_, _, o', x) := v in
                    when_ptr l (R, o', (projT2 x)) ⊗
                      when_ptrs_T' l vals
    end.

  Lemma specs_type_same nov nop
    (Hlen : length nov = length nop)
    (Heq: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
    : specs_type nov = specs_type' nop.
  Proof.
    revert nop Hlen Heq. induction nov; intros.
    - destruct nop; try solve [inversion Hlen].
      cbn in *. reflexivity.
    - destruct nop; try solve [inversion Hlen].
      destruct a as [[[b o] o'] T]. destruct p as [[p T'] v]. cbn in Heq.
      inversion Heq. subst.
      cbn. f_equal. eapply IHnov; auto.
  Qed.
  Definition specs_type_convert nov nop
    (Hlen : length nov = length nop)
    (Heq: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
    : specs_type nov -> specs_type' nop.
    erewrite specs_type_same; eauto.
  Defined.

  Lemma specs_type_convert_cons b o1 o2 T p v nov nop x (xs : specs_type nov)
    Hlen' Heq'
    (Hlen : length nov = length nop)
    (Heq: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
    :
    specs_type_convert (cons (b, o1, o2, T) nov) (cons (p, T, v) nop)
                       Hlen' Heq' (x, xs) =
      (x, specs_type_convert nov nop Hlen Heq xs).
  Proof.
    revert b o1 o2 T p v nop Hlen Heq Hlen' Heq' x xs.
    induction nov; intros.
    - destruct nop; try solve [inversion Hlen].
      unfold specs_type_convert, eq_rect_r. cbn.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
    - destruct nop; try solve [inversion Hlen].
      destruct a as [[[b' o1'] o2'] T'].
      destruct p0 as [[p' T''] v'].
      destruct xs as [x' xs].
      inversion Hlen. inversion Heq. subst.
      rename H0 into Hlen'', H3 into Heq'', T'' into T'.
      erewrite (IHnov b' o1' o2' T').
      Unshelve. all: eauto.
      unfold specs_type_convert, eq_rect_r.
      generalize (eq_sym (specs_type_same nov nop Hlen'' Heq'')).
      generalize (eq_sym
                    (specs_type_same (cons (b, o1, o2, T) (cons (b', o1', o2', T') nov))
                       (cons (p, T, v) (cons (p', T', v') nop)) Hlen' Heq')).
      cbn.
      generalize xs.
      rewrite (specs_type_same nov nop).
      all: auto.
      intros.
      clear nov IHnov Heq' Hlen' Heq Hlen xs Hlen'' Heq''.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
  Qed.

  Lemma split_when_ptrs_T' l nov (* no vals *) xs
    (HT: Forall (fun '(_, _, _, x) => forall (v : Value) (a : (projT1 x)), nonLifetime_Perms (v :: projT2 x ▷ a)) nov)
    p :
    p ∈ values nov :: when_ptrs_T' l nov ▷ xs ->
    (* we are basically only coming up with the list of vals *)
    exists not nop (* no Ts, no s *)
      (Hlen1 : length nov = length not)
      (Hlen2 : length nov = length nop)
      (Heq1: Forall (fun '((b, o1, o2, _), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov not))
      (Heq2: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
      (Heq3: Forall (fun '((_, _, _, v), (_, _, v')) => v = v') (combine not nop)),
      perms_in_T_inv nop (specs_type_convert _ _ Hlen2 Heq2 xs) /\ (* each of the perms is in v :: T ▷ xs and satisfies invariants *)
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
    destruct xs as [x xs].
    inversion HT; subst; clear HT.
    rename H2 into HT.
    cbn in H1, Hpt'. specialize (H1 v x _ Hpt').
    destruct H1 as (pt & Hpt & Hptpt' & Hnlpt & Hrelypt & Hguarpt & Hprept).
    specialize (IHnov xs ps HT Hps).
    destruct IHnov as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hin & Hlte'').
    exists (cons (b, o1, o2, v) not), (cons (pt, X, v) nop).

    exists; cbn; auto.
    eexists. Unshelve. 2: f_equal; auto.
    exists; cbn; auto.
    eexists. Unshelve. 2: constructor; auto.
    exists; cbn; auto.

    erewrite specs_type_convert_cons.
    split; [split |]; eauto.
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

  Lemma split_ptrs_trueP' p nov :
    p ∈ ptrs_trueP' nov ->
    exists vals
      (Hlen : length nov = length vals)
      (Heq : Forall (fun '((b, o1, o2, _), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov vals)),
      write_perms vals <= p.
  Proof.
    revert p. induction nov; intros p Hp.
    {
      exists []. do 2 (exists; auto).
      cbn. apply bottom_perm_is_bottom.
    }
    destruct a as [[[b o1] o2] ?].
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

  Definition lowned_Perms''' (* everything *) back (* just the returned ones *) front :
    @PermType Si Ss nat (specs_type front) :=
    {|
      ptApp := fun l xs =>
                 values front :: when_ptrs_T' l front ▷ xs *
                 lowned_Perms l
                   (when_ptrs_trueP l (front ++ back))
                   (ptrs_trueP' (front ++ back))
    |}.


  Definition when {A B} l (P : PermType A B) : PermType A B :=
    {|
      ptApp := fun a b => when_Perms (Ss := Ss) l (a :: P ▷ b)
    |}.
  Definition finished {A B} l (P : PermType A B) : PermType A B :=
    {|
      ptApp := fun a b => lfinished_Perms (Ss := Ss) l (a :: P ▷ b)
    |}.

  Lemma typing_begin :
    lifetime_Perms ⊢
      l <- beginLifetime;; Ret l ⤳
      Ret tt :::
      lowned_Perms''' [] [] ∅ lifetime_Perms.
  Proof.
    intros p' si ss (? & (l & ?) & Hlte) Hpre; subst.
    unfold beginLifetime. unfold id.
    rewritebisim @bind_trigger.
    rewritebisim @bind_vis.
    pstep. econstructor; eauto; try reflexivity.

    rewritebisim @bind_trigger.
    rewritebisim @bind_vis.
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
    rewritebisim @bind_ret_l.
    econstructor.
    - cbn. do 2 rewrite lGetPut.
      split; [| split]; auto.
      + unfold statusOf. apply nth_error_app_last; auto.
      + rewrite app_length. rewrite Hpre. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_bottom. lia.
    - apply sep_conj_Perms_perm.
      + exists bottom_perm, (owned l bottom_perm nonLifetime_bottom).
        split; [| split; [| split]].
        { cbn. auto. }
        2: { symmetry. apply separate_bottom. }
        2: { rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity. }
        exists bottom_perm, bottom_perm. eexists.
        { intros. cbn. symmetry. apply separate_bottom. }
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

  Fixpoint lfinished_Perms_T' l vals
    : PermType (values_type vals) (specs_type vals) :=
    match vals with
    | nil => trueP
    | cons v vals => let '(_, _, o', x) := v in
                    finished_ptr l (W, o', (projT2 x)) ⊗
                      lfinished_Perms_T' l vals
    end.

  (*
  Lemma typing_end_ptr_n' l vals xs
    (HT: Forall (fun '(_, _, _, x) => forall (v : Value) (a : (projT1 x)), nonLifetime_Perms (v :: projT2 x ▷ a)) vals) :
    typing (specConfig := Ss)
      (values vals :: when_ptrs_T' l vals ▷ xs *
         lowned_Perms l
           (when_ptrs_trueP l vals)
           (ptrs_trueP' vals))
      (fun l' _ => values vals :: lfinished_Perms_T' l' vals ▷ xs * l' :: eqp l ▷ tt)
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

    apply split_when_ptrs_T' in Hpwhens; auto.
    destruct Hpwhens as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hnop & Hlte'').
    edestruct Hf as (pptrs & Hpptrs & Hsepstep & Hpre').
    apply (when_read_perms_when_ptrs_trueP' l not vals).
    { rewrite <- Hlen1. auto. }
    {
      clear Hf HT Hr2.
      clear nop Hlen2 Heq2 Heq3 Hnop Hlte''.
      revert not Hlen1 Heq1.
      induction vals; intros.
      - destruct not; try solve [inversion Hlen1].
        constructor.
      - destruct not; try solve [inversion Hlen1].
        destruct a as [[[b o1] o2] x].
        destruct p0 as [[[b' o1'] o2'] v].
        inversion Heq1; subst; clear Heq1. rename H2 into Heq1.
        destruct H1 as (? & ? & ?); subst.
        rename b' into b, o1' into o1, o2' into o2.
        constructor. auto. apply IHvals; auto.
        apply (snd xs).
    }
    {
      eapply separate_antimonotone; eauto.
      symmetry.
      eapply separate_antimonotone.
      2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    apply split_ptrs_trueP' in Hpptrs.
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
          revert vals xs not' nop Hlen1 Hlen2 Heq1 Heq2 Hnop Heq3 Hlte'' Hlen3 Heq4 Hlte''' Hpre'.
          induction not; intros.
          - destruct vals; try solve [inversion Hlen1].
            destruct not'; try solve [inversion Hlen3]; auto.
          - destruct vals; try solve [inversion Hlen1].
            destruct nop; try inversion Hlen2.
            destruct not'; try solve [inversion Hlen3]; auto.
            destruct p0 as [[[? ?] ?] ?].
            destruct p1 as [[? ?] ?].
            destruct p2 as [[[? ?] ?] ?].
            destruct a as [[[? ?] ?] ?].
            inversion Heq1; subst; clear Heq1; rename H3 into Heq1.
            destruct H2 as (? & ? & ?); subst.
            inversion Heq2; subst; clear Heq2; rename H3 into Heq2.
            inversion Heq3; subst; clear Heq3; rename H3 into Heq3.
            inversion Heq4; subst; clear Heq4; rename H3 into Heq4.
            destruct H2 as (? & ? & ?); subst.
            f_equal.
            + f_equal; auto.
              clear Hlen1 Hlen2 Hlen3 Heq1 Heq2 Heq3 Heq4 IHnot Hlte Hlte' Hlte'' Hlte'''.
              destruct Hpre as (? & _), Hpre' as (? & _).
              cbn in H, H1. rewrite HGetPut1 in H1.
              rewrite H in H1; auto.
              inversion H1. auto.
            + apply IHnot with (vals := vals) (nop := nop); auto.
              * apply Hpre.
              * apply (snd xs).
              * destruct Hnop as (? & Hnop). apply Hnop.
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
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l Lifetime.finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      split; [| split].
      + clear Hlen1 Hlen3 Heq1 Heq3 Heq4 Hlte''' Hpre' Hr2 Hf.
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
        * apply IHnot; auto.
          -- etransitivity; eauto.
             cbn. rewrite sep_conj_perm_assoc. apply lte_r_sep_conj_perm.
          -- apply Hpre''.
        * eapply finished_write_perms_separate; apply Hpre''.
      + clear Hlen2 Heq2 Heq3.
        induction nop; cbn; auto.
        destruct a as [[p' ?] ?].
        destruct Hnop as (? & Hnop).
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
      rewrite sep_conj_Perms_commut.
      assert ((l :: eqp l ▷ tt) ≡ (@bottom_Perms (Si * Ss))).
      {
        cbn. split; repeat intro; cbn; auto.
      }
      rewrite H. rewrite sep_conj_Perms_bottom_identity. clear H.

      clear Hf HT.
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l Lifetime.finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      clear Hpre' Hr2.
      revert not nop Hlen1 Hlen2 Heq1 Heq2 Heq3 Hlen3 Heq4 Hnop Hlte'' Hlte''' Hpre'' Hpre.
      induction vals; intros.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        cbn. auto.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        destruct p0 as [[[b o1] o2] v'].
        destruct p1 as [[p' x] v].
        inversion Heq3; subst; clear Heq3. rename H2 into Heq3.
        destruct a as [[[b' o1'] o2'] x'].
        inversion Heq1; clear Heq1; subst. rename H2 into Heq1.
        destruct H1 as (? & ? & ?). subst.
        inversion Heq2; clear Heq2; subst. rename H2 into Heq2.
        exists (lfinished l (write_perm (b, o1 + o2) v) ** p'), (finished_write_perms l not ** star_list nop).
        assert (star_list (cons (p', x, v) nop) <= pwhens).
        {
          etransitivity.
          apply lte_r_sep_conj_perm. eauto.
        }
        destruct Hnop as (? & Hnop).
        split; [| split; [| split]].
        * cbn. eexists. split. eexists. reflexivity.
          cbn. do 2 eexists.
          split; [| split; [| split]].
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
        * apply IHvals; auto.
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
          rewrite <- sep_conj_perm_assoc. reflexivity.
          Unshelve. eapply nonLifetime_sep_step; eauto.
  Qed.
   *)
  Fixpoint foo front back :
    specs_type front -> (specs_type back -> specs_type (front ++ back)).
    refine (
        match front with
        | [] => fun frontT backT => backT
        | cons f front =>
            let '(b, o, o', x) := f in
            fun frontT backT =>
              let '(f, frontT') := frontT in
              (f, foo _ _ frontT' backT)
        end).
  Defined.

  Definition cast1 vals (a : specs_type vals) : specs_type (vals ++ []).
    rewrite app_nil_r. apply a.
  Defined.
  Definition cast2 vals (a : specs_type (vals ++ [])) : specs_type vals.
    rewrite app_nil_r in a. apply a.
  Defined.

  Lemma cast1_foo vals xs :
    foo vals [] xs tt = cast1 _ xs.
  Proof.
    induction vals.
    - cbn in *. destruct xs. unfold cast1. unfold eq_rect_r. cbn.
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
    - destruct a as [[[b o] o'] T].
      destruct xs as [x xs]. cbn.
      rewrite IHvals. clear IHvals.
      unfold cast1, eq_rect_r.
      generalize (eq_sym (app_nil_r (cons (b, o, o', T) vals))).
      cbn.
      rewrite (app_nil_r vals).
      intros.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
  Qed.

  Lemma cast2_foo vals xs :
    cast2 _ (foo vals [] xs tt) = xs.
  Proof.
    induction vals.
    - cbn in *. destruct xs. unfold cast2.
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
    - destruct a as [[[b o] o'] T].
      destruct xs as [x xs]. cbn.
      rewrite <- (IHvals xs) at 2. clear IHvals.
      unfold cast2.
      generalize (app_nil_r (cons (b, o, o', T) vals)).
      generalize (foo vals [] xs tt).
      cbn.
      rewrite (app_nil_r vals).
      intros.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
  Qed.

  (* A := specs_type vals' *)
  (* B := specs_type (vals - vals') -> specs_type vals *)
  Definition coerce Si' A B
    (F : A -> B) (T : @PermType Si Ss Si' A) : @PermType Si Ss Si' B :=
    {| ptApp := fun n b => meet_Perms (fun S => exists a, F a = b /\ S = ptApp _ _ T n a) |}.

  Definition lowned_Perms'''' front back :=
    coerce _ _ _ (foo front back) (lowned_Perms''' back front).


  Lemma typing_end
    vals l f
    (HT: Forall (fun '(_, _, _, T) =>
                   forall (v : Value) (a : projT1 T), nonLifetime_Perms (v :: projT2 T ▷ a))
           vals) :
    l :: lowned_Perms'''' vals [] ▷ f ⊢
      endLifetime l ⤳
      Ret tt :::
      trueP ∅ values vals :: lfinished_Perms_T' l vals ▷ cast2 _ (f tt).
  Proof.
    cbn.
    intros p si ss Hp Hpre.
    cbn in Hp.
    destruct Hp as (? & ((? & ? & ?) & ?)). subst.
    rewrite app_nil_r in *.
    rewrite cast2_foo.
    eapply sbuter_lte.
    2: { intros. apply (proj1 (sep_conj_Perms_bottom_identity _)). }
    eapply sbuter_lte.
    apply typing_end_ptr_n''. apply HT. apply H1. auto.
    repeat intro. cbn in H.
    destruct H as (? & ? & ? & ? & ? & ?). subst.
    eapply Perms_upwards_closed; eauto.
    etransitivity; eauto.
    apply lte_l_sep_conj_perm.
  Qed.

  Lemma typing_end_ptr_n'' l vals xs
    (HT: Forall (fun '(_, _, _, T) => forall (v : Value) (a : (projT1 T)), nonLifetime_Perms (v :: projT2 T ▷ a)) vals) :
    typing (specConfig := Ss)
      (values vals :: when_ptrs_T' l vals ▷ xs *
         lowned_Perms l
           (when_ptrs_trueP l vals)
           (ptrs_trueP' vals))
      (fun l' _ => values vals :: lfinished_Perms_T' l' vals ▷ xs * l' :: eqp l ▷ tt)
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

    apply split_when_ptrs_T' in Hpwhens; auto.
    destruct Hpwhens as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hnop & Hlte'').
    edestruct Hf as (pptrs & Hpptrs & Hsepstep & Hpre').
    apply (when_read_perms_when_ptrs_trueP' l not vals).
    { rewrite <- Hlen1. auto. }
    {
      clear Hf HT Hr2.
      clear nop Hlen2 Heq2 Heq3 Hnop Hlte''.
      revert not Hlen1 Heq1.
      induction vals; intros.
      - destruct not; try solve [inversion Hlen1].
        constructor.
      - destruct not; try solve [inversion Hlen1].
        destruct a as [[[b o1] o2] T].
        destruct p0 as [[[b' o1'] o2'] v].
        destruct xs as [x xs].
        inversion Heq1; subst; clear Heq1. rename H2 into Heq1.
        destruct H1 as (? & ? & ?); subst.
        rename b' into b, o1' into o1, o2' into o2.
        constructor. auto. apply IHvals; auto.
    }
    {
      eapply separate_antimonotone; eauto.
      symmetry.
      eapply separate_antimonotone.
      2: { etransitivity. apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    apply split_ptrs_trueP' in Hpptrs.
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
          revert vals xs not' nop Hlen1 Hlen2 Heq1 Heq2 Hnop Heq3 Hlte'' Hlen3 Heq4 Hlte''' Hpre'.
          induction not; intros.
          - destruct vals; try solve [inversion Hlen1].
            destruct not'; try solve [inversion Hlen3]; auto.
          - destruct vals; try solve [inversion Hlen1].
            destruct nop; try inversion Hlen2.
            destruct not'; try solve [inversion Hlen3]; auto.
            destruct p0 as [[[? ?] ?] ?].
            destruct p1 as [[? ?] ?].
            destruct p2 as [[[? ?] ?] ?].
            destruct a as [[[? ?] ?] ?].
            destruct xs as [x xs].
            inversion Heq1; subst; clear Heq1; rename H3 into Heq1.
            destruct H2 as (? & ? & ?); subst.
            inversion Heq2; subst; rename H3 into Heq2'.
            inversion Heq3; subst; clear Heq3; rename H3 into Heq3.
            inversion Heq4; subst; clear Heq4; rename H3 into Heq4.
            destruct H2 as (? & ? & ?); subst.
            f_equal.
            + f_equal; auto.
              clear Hlen1 Hlen3 Heq1 Heq3 Heq4 IHnot Hlte Hlte' Hlte'' Hlte'''.
              destruct Hpre as (? & _), Hpre' as (? & _).
              cbn in H, H1. rewrite HGetPut1 in H1.
              rewrite H in H1; auto.
              inversion H1. auto.
            + eapply IHnot with (vals := vals) (nop := nop); eauto.
              * apply Hpre.
              * cbn in Hnop. erewrite specs_type_convert_cons in Hnop. eapply Hnop.
                Unshelve. all: auto.
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
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l Lifetime.finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      split; [| split].
      + clear Hlen1 Hlen3 Heq1 Heq3 Heq4 Hlte''' Hpre' Hr2 Hf.
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
        * apply IHnot; auto.
          -- etransitivity; eauto.
             cbn. rewrite sep_conj_perm_assoc. apply lte_r_sep_conj_perm.
          -- apply Hpre''.
        * eapply finished_write_perms_separate; apply Hpre''.
      + assert (star_list nop <= pwhens).
        {
          etransitivity; eauto.
          apply lte_r_sep_conj_perm.
        }
        clear Heq3. clear r2 not Hlen1 Heq1 Hlte'' Hlen3 Heq4 Hlte''' Hpre' Hpre'' Hnlr2 Hrelyr2 Hguarr2 Hr2 Hlte' Hf Hsepstep.
        revert vals xs HT Hlen2 Heq2 Hnop.
        induction nop; intros; cbn; auto.
        destruct vals; try solve [inversion Hlen2].
        destruct a as [[p' ?] ?].
        destruct p0 as [[[b o] o'] T].
        destruct xs as [x xs].
        inversion Heq2; subst.
        rename H3 into Heq2'.
        cbn in Hnop. erewrite specs_type_convert_cons in Hnop.
        split; [| split].
        * apply Hnop. apply H. apply Hlte. apply Hpre.
        * eapply IHnop with (vals := vals); eauto.
          -- etransitivity; eauto. cbn.
             (* apply sep_conj_perm_monotone. reflexivity. *)
             apply lte_r_sep_conj_perm.
          -- inversion HT. auto.
          -- eapply Hnop.
        * apply Hlte in Hpre. destruct Hpre as (Hpre & _).
          apply H in Hpre. apply Hpre.
      + apply Hlte in Hpre. destruct Hpre as (Hpre & _).
        apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
        destruct (star_list_invs _ _ _ Hpre Hnop) as (? & ? & ? & ?).

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
      rewrite sep_conj_Perms_commut.
      assert ((l :: eqp l ▷ tt) ≡ (@bottom_Perms (Si * Ss))).
      {
        cbn. split; repeat intro; cbn; auto.
      }
      rewrite H. rewrite sep_conj_Perms_bottom_identity. clear H.

      clear Hf HT.
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l Lifetime.finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      clear Hpre' Hr2.
      revert not nop Hlen1 Hlen2 Heq1 Heq2 Heq3 Hlen3 Heq4 Hnop Hlte'' Hlte''' Hpre'' Hpre.
      induction vals; intros.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        cbn. auto.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        destruct p0 as [[[b o1] o2] v'].
        destruct p1 as [[p' T] v].
        inversion Heq3; subst; clear Heq3. rename H2 into Heq3.
        destruct a as [[[b' o1'] o2'] x'].
        inversion Heq1; clear Heq1; subst. rename H2 into Heq1.
        destruct H1 as (? & ? & ?). subst.
        inversion Heq2; subst. rename H2 into Heq2'.
        destruct xs as [x xs].
        erewrite specs_type_convert_cons in Hnop.
        Unshelve. all: auto.
        2: eapply nonLifetime_sep_step; eauto.
        exists (lfinished l (write_perm (b, o1 + o2) v) ** p'), (finished_write_perms l not ** star_list nop).
        assert (star_list (cons (p', T, v) nop) <= pwhens).
        {
          etransitivity.
          apply lte_r_sep_conj_perm. eauto.
        }
        split; [| split; [| split]].
        * cbn. eexists. split. eexists. reflexivity.
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
        * eapply IHvals; auto.
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
             destruct (star_list_invs _ _ _ Hpre Hnop) as (? & ? & ? & ?).
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
             destruct (star_list_invs _ _ _ Hpre Hnop) as (? & ? & ? & ?).
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
          rewrite <- sep_conj_perm_assoc. reflexivity.
  Qed.

  Lemma typing_begin' :
    lifetime_Perms ⊢
      beginLifetime ⤳
      Ret (fun _ => tt) :::
      lowned_Perms'''' [] [] ∅ lifetime_Perms.
  Proof.
    intros p' si ss (? & (l & ?) & Hlte) Hpre; subst.
    unfold beginLifetime. unfold id.
    rewritebisim @bind_trigger.
    (* rewritebisim @bind_vis. *)
    pstep. econstructor; eauto; try reflexivity.

    rewritebisim @bind_trigger.
    (* rewritebisim @bind_vis. *)
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
    (* rewritebisim @bind_ret_l. *)
    econstructor.
    - cbn. do 2 rewrite lGetPut.
      split; [| split]; auto.
      + unfold statusOf. apply nth_error_app_last; auto.
      + rewrite app_length. rewrite Hpre. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_bottom. lia.
    - apply sep_conj_Perms_perm.
      + eexists. split. eexists. split.
        cbn. apply functional_extensionality. intros []. reflexivity.
        reflexivity.
        exists bottom_perm, (owned l bottom_perm nonLifetime_bottom).
        split; [| split; [| split]].
        { cbn. auto. }
        2: { symmetry. apply separate_bottom. }
        2: { rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity. }
        exists bottom_perm, bottom_perm. eexists.
        { intros. cbn. symmetry. apply separate_bottom. }
        exists nonLifetime_bottom, nonLifetime_bottom, rely_inv_bottom, guar_inv_bottom.
        split; [| split].
        * cbn; auto.
        * rewrite Hpre. rewrite sep_conj_perm_commut. apply sep_conj_perm_bottom.
        * exists bottom_perm. split; auto. split. reflexivity.
          intros. cbn. auto.
      + eexists. split. eexists. reflexivity.
        cbn. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_bottom. lia.
        Unshelve. cbn. apply tt.
  Qed.

    Lemma ex3_typing b o xs xs' :
    typing
      (lifetime_Perms * (VPtr (b, o)) :: ptr (W, 0, IsNat Si Ss) ▷ xs * (VPtr (b, o)) :: ptr (W, 1, IsNat Si Ss) ▷ xs')
      (fun l _ => lifetime_Perms * finished_ptrs_T l
                                  [(b, o, 0, existT _ _ (isNat, xs));
                                   (b, o, 1, existT _ _ (isNat, xs'))])
      (l <- beginLifetime ;; endLifetime l)
      (Ret (fun (_ : unit) => tt) ;; Ret tt).
  Proof.
    eapply typing_bind.
    { rewrite <- sep_conj_Perms_assoc. apply typing_frame. apply typing_begin'. }
    intros. unfold id.
    rewrite sep_conj_Perms_commut.
    setoid_rewrite (sep_conj_Perms_commut lifetime_Perms).
    unfold "∅". unfold ptApp.
    rewrite sep_conj_Perms_assoc.
    (* setoid_rewrite <- (sep_conj_Perms_assoc lifetime_Perms). *)
    apply typing_frame.

    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      etransitivity.
      {
        rewrite sep_conj_Perms_commut. apply sep_conj_Perms_monotone.
        rewrite lowned_Perms_convert. reflexivity.
        reflexivity.
      }
      rewrite sep_conj_Perms_commut.
      rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone. reflexivity.
      apply split'.
      apply nonLifetime_IsNat.
    }
    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      rewrite sep_conj_Perms_commut.
      rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone. reflexivity.
      rewrite sep_conj_Perms_commut.
      apply split'.
      apply nonLifetime_IsNat.
    }

    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      apply sep_conj_Perms_monotone. 2: reflexivity.
      apply weaken_when_ptr.
    }
    rewrite (sep_conj_Perms_commut _ (lowned_Perms' _ _ _)).
    rewrite sep_conj_Perms_assoc.
    rewrite partial'.

    eapply typing_lte.
    3: {
      unfold "⊨". intros.
      change (finished_ptrs_T r0 ?l) with ((fun r0 _ => finished_ptrs_T r0 l) r0 r3).
      reflexivity.
    }
    2: {
      apply sep_conj_Perms_monotone. reflexivity.
      apply weaken_when_ptr.
    }
    rewrite sep_conj_Perms_commut.
    rewrite partial'.

    (* apply end_lifetime'; auto. *)
    (* - constructor; auto. *)
    (* - constructor. apply nonLifetime_IsNat. *)
    (*   constructor. apply nonLifetime_IsNat. *)
    (*   constructor. *)
  Abort.


  Lemma typing_end vals l :
    l :: lowned_Perms''' vals vals ▷ id ⊢
      endLifetime l(* ;; Ret (values vals) *) ⤳
      (* Ret tt;;  *)Ret (id (specs vals)) :::
      lfinished_Perms_T' l vals.
  Proof.
    eapply typing_bind.
    cbn. apply typing_end_ptr_n'. admit.
    intros. rewrite sep_conj_Perms_commut.
    repeat intro.
    destruct H as (? & ? & ? & ? & ? & ?). cbn in H. subst.

    (* assert (f = id) by admit. subst. *)

    pstep. constructor; auto.
    eapply Perms_upwards_closed; eauto. etransitivity; eauto.
    apply lte_r_sep_conj_perm.

    (* intros p' c1 c2 (p & lowned' & Hp & H & Hsep & Hlte) Hpre. cbn in H. *)
    (* destruct H as (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf). *)
    (* unfold endLifetime. unfold id. *)
    (* rewritebisim @bind_trigger. *)
    (* pstep. econstructor; eauto; try reflexivity. *)

    (* pose proof Hpre as Hpre''. *)
    (* apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _). *)
    (* apply Hlte' in Hpre. destruct Hpre as (_ & H & _). *)
    (* cbn in H. setoid_rewrite H. *)
    (* rewritebisim @bind_trigger. *)
    (* specialize (Hf _ Hp). destruct Hf as (q & Hq & Hsep_step & Hpre). *)
    (* { apply Hlte in Hpre''. destruct Hpre'' as (? & ? & ?). *)
    (*   eapply separate_antimonotone; eauto. } *)
    (* econstructor; unfold id. eauto. *)
    (* cbn in *. apply Hlte. constructor 1. right. *)
    (* apply Hlte'. constructor 1. right. right. *)
    (* { *)
    (*   repeat rewrite lGetPut. *)
    (*   split; [| split; [| split]]. *)
    (*   - intros. apply nth_error_replace_list_index_neq; auto. *)
    (*     apply nth_error_Some. intro. *)
    (*     unfold statusOf, Lifetimes in H. rewrite H1 in H. inversion H. *)
    (*   - apply replace_list_index_length; auto. apply nth_error_Some. intro. *)
    (*     unfold statusOf, Lifetimes in H. rewrite H0 in H. inversion H. *)
    (*   - unfold statusOf. apply nth_error_replace_list_index_eq. *)
    (*   - rewrite lPutPut, replace_list_index_twice. reflexivity. *)
    (* } *)
    (* 2: { *)
    (*   econstructor. 2: apply lfinished_perm_Perms; eauto. *)
    (*   cbn. rewrite lGetPut. *)
    (*   split. symmetry. apply nth_error_replace_list_index_eq. *)
    (*   apply Hpre; auto. *)
    (*   - apply Hlte in Hpre''. cbn in H. rewrite replace_list_index_eq; auto. *)
    (*     rewrite lPutGet. apply Hpre''. *)
    (*   - apply Hlte in Hpre''. destruct Hpre'' as (_ & Hpre'' & _). *)
    (*     apply Hlte' in Hpre''. *)
    (*     rewrite replace_list_index_eq; auto. *)
    (*     rewrite lPutGet. apply Hpre''. *)
    (* } *)
    (* eapply sep_step_lte; eauto. *)
    (* eapply sep_step_lte. apply lte_r_sep_conj_perm. *)
    (* eapply sep_step_lte; eauto. *)
    (* eapply sep_step_lte. apply lte_r_sep_conj_perm. *)
    (* etransitivity. 2: apply sep_step_owned_finished. *)
    (* apply owned_sep_step; auto. *)
    (* Unshelve. eapply nonLifetime_sep_step; eauto. *)
  Qed.


End Perms.
