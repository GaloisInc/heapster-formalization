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

  Lemma separate_write_perm p l v v' :
    p ⊥ @write_perm _ Ss _ l v ->
    p ⊥ write_perm l v'.
  Proof.
    intros H. split; apply H; auto.
  Qed.

  Lemma sep_step_write_perm p l v v' :
    sep_step p (@write_perm _ Ss _ l v) ->
    sep_step p (write_perm l v').
  Proof.
    repeat intro. split; apply H; auto.
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
      (* + apply sep_owned. admit. admit. eapply separate_antimonotone. 2: apply Hpw. *)
      (*   eapply separate_antimonotone. *)
      (*   2: { etransitivity. apply lte_l_sep_conj_perm. apply Hlte''. } *)
      (*   symmetry. eapply separate_antimonotone; eauto. *)
      (*   etransitivity; eauto. apply lte_l_sep_conj_perm. *)
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
             eapply separate_write_perm.
             symmetry. eauto.
        * etransitivity.
          -- apply sep_step_sep_conj_r; eauto. symmetry. auto.
          -- apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
             eapply sep_step_write_perm.
             apply sep_step_lte'; eauto. reflexivity.
        * (** Precondition section *)
          intros. split; [| split].
          -- apply Hlte'''' in H. destruct H as (? & ? & ?).
             apply Hlte''' in H. cbn in H.
             rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
             setoid_rewrite HGetPut1 in H.
             cbn. rewrite HGetPut1. symmetry. apply H; auto.
          -- apply Hpre; auto. apply Hlte''''; auto.
          -- symmetry. apply Hsep_step.
             eapply separate_write_perm.
             symmetry. eauto.
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

  (*
  Lemma split_Perms_eq b o y l (P Q : @Perms (Si * Ss)) :
    (VPtr (b, o)) :: ptr(W, 0, eqp y) ▷ tt * lowned_Perms l P Q ⊨
      when_Perms l ((VPtr (b, o)) :: ptr(W, 0, eqp y) ▷ tt) *
      lowned_Perms l
        (when_Perms l ((VPtr (b, o)) :: ptr(R, 0, eqp y) ▷ tt) * P)
        (((VPtr (b, o)) :: ptr(W, 0, eqp y) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte).
    destruct (nonLifetime_ptr _ _ _ _ (eqp y) (nonLifetime_eqp y) _ Hp') as (p & Hp & Hpp' & Hnlp & Hguarp & Hprep).
    exists (when l p Hnlp).
    assert (Hpr2 : p ⊥ r2).
    {
      eapply owned_sep; auto.
      eapply separate_antimonotone.
      2: {
        etransitivity. apply lte_r_sep_conj_perm. eauto.
      }
      symmetry. eapply separate_antimonotone; eauto. symmetry. auto.
    }
    eexists (r1 ** owned l (p ** r2) (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2)).
    split; [| split; [| split]]; auto.
    - apply when_perm_Perms; auto.
    - exists r1, (p ** r2), Hr1, (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2), (guar_inv_sep_conj_perm _ _ Hguarp Hr2').
      split; [| split; [| split]].
      3: reflexivity.
      {
        apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      }
      {
        apply sep_conj_Perms_perm; auto.
      }
      (** Precondition part *)
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
      destruct Hp as (? & (v & ?) & Hx). subst. rewrite Nat.add_0_r in Hx.
      cbn in Hx. destruct Hx as (? & ? & ? & ? & ? & ?). subst.
      destruct Hpr as (? & (v' & ?) & Hx'). subst. rewrite Nat.add_0_r in Hx'.
      cbn in Hx'. destruct Hx' as (? & ? & ? & ? & ? & ?). subst.
      exists ((write_perm (b, o) v') ** r). split; [| split].
      + apply sep_conj_Perms_perm; auto.
        * cbn. eexists. split. eexists. reflexivity.
          rewrite Nat.add_0_r.
          cbn. do 2 eexists. split; [| split; [| split]].
          -- reflexivity.
          -- reflexivity.
          -- apply separate_bottom.
          -- rewrite sep_conj_perm_bottom. reflexivity.
        * symmetry. (* eapply separate_write_perm. *)
          apply Hsep_step.
          eapply separate_antimonotone. 2: apply H.
          eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
          eapply separate_antimonotone. 2: eauto.
          symmetry. auto.
      + etransitivity.
        * apply sep_step_sep_conj_r; eauto. symmetry. auto.
        * apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
          apply sep_step_lte'; eauto.
          etransitivity; eauto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
      + intros. split; [| split]; auto.
        * apply Hlte'' in H3. destruct H3 as (? & ? & ?).
          apply Hlte''' in H3. cbn in H3.
          rewrite lGetPut in H3. setoid_rewrite nth_error_replace_list_index_eq in H3.
          apply H5 in H3. destruct H3 as (? & ? & ?).
          apply H0 in H3. cbn in H3. cbn.
          rewrite HGetPut1 in H3 |- *; auto. right. reflexivity.
        * apply Hpre; auto. apply Hlte''; auto.
        * symmetry. apply Hsep_step.
          eapply separate_antimonotone. 2: apply H.
          eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
          eapply separate_antimonotone. 2: eauto.
          symmetry. apply Hpr2.
    - apply separate_sep_conj_perm.
      + apply sep_when; auto.
        symmetry.
        eapply separate_antimonotone. 2: apply Hpp'.
        symmetry.
        eapply separate_antimonotone. apply Hsep. etransitivity; eauto.
        apply lte_l_sep_conj_perm.
      + apply when_owned_sep.
      + symmetry. apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
    - etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].
      etransitivity. apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.
   *)

  Lemma typing_end_ptr {A} l b o (T : VPermType A) xs (HT : forall v a, nonLifetime_Perms (v :: T ▷ a)) :
    typing (specConfig := Ss)
      ((VPtr (b, o)) :: when_ptr l (W, 0, T) ▷ xs *
         (lowned_Perms l ((VPtr (b, o)) :: when_ptr l (R, 0, trueP) ▷ tt)
            ((VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt)))
      (fun l' _ => (VPtr (b, o)) :: finished_ptr l' (W, 0, T) ▷ xs)
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
    specialize (Hf (when l (write_perm (b, o + 0) v))).
    destruct Hf as (q & Hq & Hsep_step & Hpre).
    {
      eexists. split. eexists. reflexivity. cbn.
      do 2 eexists. split; [| split; [| split]]. 2: auto.
      - reflexivity.
      - apply separate_bottom.
      - rewrite sep_conj_perm_bottom. apply when_monotone.
        apply read_lte_write.
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
      apply Hpwhen in Hpre''. cbn in Hpre''. auto.
    }
    assert (v = v'). {
      specialize (Hpre c1 c2).
      apply Hq in Hpre.
      - (* from this we can get that (b, o) points to v using pwhen *)
        cbn in Hpre.
        rewrite HGetPut1 in Hpre. rewrite <- Hv in Hpre. inversion Hpre. auto.
      - rewrite replace_list_index_eq; auto. rewrite lPutGet. cbn.
        intros. apply Hv.
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
          intros. apply Hv.
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

  Lemma partial_ptr R1 R2 b o o' l y P Q (F : R1 -> R2 -> Perms) ti ts :
    typing
      (lowned_Perms l P ((VPtr (b, o) :: ptr(W, o', eqp y) ▷ tt) * Q))
      F ti ts ->
    typing
      ((VPtr (b, o) :: when_ptr l (W, o', eqp y) ▷ tt) *
         lowned_Perms l
           ((VPtr (b, o) :: when_ptr l (R, o', trueP) ▷ tt) * P)
           ((VPtr (b, o) :: ptr(W, o', trueP) ▷ tt) * Q))
      F ti ts.
  Proof.
    intros Ht p0 si ss (pw' & powned & (? & (v & ?) & Hpw') & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte) Hpre; subst.
    cbn in Hr2.
    destruct Hpw' as (pw & p' & Hpw & ? & Hsep'' & Hlte''). cbn in H; subst.
    assert (Hsep': r1 ⊥ when l (write_perm (b, o + o') v)).
    {
      eapply separate_antimonotone. 2: eauto.
      eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
      eapply separate_antimonotone. 2: eauto. symmetry.
      eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
      eapply separate_antimonotone. 2: eauto. auto.
    }
    destruct Hr2 as (p'' & q' & (? & ((v' & ?) & Hp'')) & Hq' & Hsep''' & Hlte'''); subst.
    rewrite sep_conj_Perms_commut in Hp''. rewrite sep_conj_Perms_bottom_identity in Hp''.
    (* assert (v' = v). *)
    (* { *)
    (*   apply Hlte in Hpre. destruct Hpre as (? & ? & _). *)

    (*   apply Hlte' in H0. destruct H0 as (? & ? & _). *)
    (*   cbn in H1. *)

    (*   apply Hlte'' in H. destruct H as (? & _). *)
    (*   apply Hpw in H. cbn in H. *)
    (* } *)

    apply Ht.
Abort.

  Lemma partial_ptr A b o l o' P Q (T : VPermType A) xs :
    (VPtr (b, o) :: when_ptr l (R, o', T) ▷ xs) *
      lowned_Perms l ((VPtr (b, o) :: when_ptr l (R, o', T) ▷ xs) * P) Q
        ⊨
        lowned_Perms l P Q.
  Proof.
    intros.

  Qed.

  Lemma partial_ptr b o l o' y P Q
    (HQ : nonLifetime_Perms Q) :
    (VPtr (b, o) :: when_ptr l (W, o', eqp y) ▷ tt) *
          lowned_Perms l
            ((VPtr (b, o) :: when_ptr l (R, o', trueP) ▷ tt) * P)
            ((VPtr (b, o) :: ptr(W, o', trueP) ▷ tt) * Q)
            ⊨
    lowned_Perms l P ((VPtr (b, o) :: ptr(W, o', eqp y) ▷ tt) * Q).
  Proof.
    intros p0 (pw' & powned & (? & (v & ?) & Hpw') & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte); subst.
    cbn in Hr2.
    destruct Hpw' as (pw & p' & Hpw & ? & Hsep'' & Hlte''). cbn in H; subst.
    assert (Hsep': r1 ⊥ when l (write_perm (b, o + o') v)).
    {
      eapply separate_antimonotone. 2: eauto.
      eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
      eapply separate_antimonotone. 2: eauto. symmetry.
      eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
      eapply separate_antimonotone. 2: eauto. auto.
    }
    destruct Hr2 as (p'' & q' & (? & ((v' & ?) & Hp'')) & Hq' & Hsep''' & Hlte'''); subst.
    destruct (HQ _ Hq') as (q & Hq & Hqq' & Hnlq & Hrelyq & Hguarq & Hpreq).
    exists (r1 ** when l (write_perm (b, o + o') v)).
    exists r2.
    (* exists (write_perm (b, o + o') v ** q). *)
    eexists.
    {
      intros. symmetry.
      apply separate_sep_conj_perm; symmetry; auto.
      apply when_owned_sep.
    }
    eexists.
    {
      apply nonLifetime_sep_conj_perm; auto.
      apply when_nonLifetime. apply nonLifetime_write_perm.
    }
    exists Hnlr2, Hrelyr2, Hguarr2.
    (* eexists. Unshelve. *)
    (* 2: { *)
    (*   apply nonLifetime_sep_conj_perm; auto. apply nonLifetime_write_perm. admit. *)
    (* } *)
    (* eexists. *)
    (* { *)
    (*   apply rely_inv_sep_conj_perm; auto. apply rely_inv_write_perm. *)
    (* } *)
    (* eexists. *)
    (* { *)
    (*   apply guar_inv_sep_conj_perm; auto. apply guar_inv_write_perm. *)
    (* } *)
    split; [| split]; auto.
    {
      exists (write_perm (b, o + o') v), q. split; [| split; [| split]]; auto.
      - eexists. split. eexists. reflexivity.
        cbn. do 2 eexists. split; [| split; [| split]]; try reflexivity.
        apply separate_bottom. rewrite sep_conj_perm_bottom. reflexivity.
      - admit.
      - reflexivity.
    }
    {
      etransitivity; eauto.
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
      + apply H0
  Qed.
    intros p0 (pw' & powned & (? & (v & ?) & Hpw') & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte). subst.
    cbn in Hpw'.
    destruct Hpw' as (pw & p' & Hpw & ? & Hsep'' & Hlte''). subst.
    (* destruct (HP _ Hp') as (p & Hp & Hpp' & Hnlp & Hguarp). *)
    exists (when l (write_perm (b, o + o') v) (nonLifetime_write_perm (b, o + o') v) ** r1), r2. eexists.
    {

    }
    exists Hr2, Hr2'. split.
    {
      symmetry. apply separate_sep_conj_perm.
      - eapply separate_antimonotone; eauto.
        symmetry. eapply separate_antimonotone; eauto.
        etransitivity; eauto. apply lte_r_sep_conj_perm.
      - symmetry. auto.
      - eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone; eauto.
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
      + eapply separate_antimonotone; eauto.
        symmetry. eapply separate_antimonotone; eauto.
      + symmetry. eapply separate_antimonotone; eauto. apply lte_r_sep_conj_perm.
      + eapply separate_antimonotone; eauto. apply lte_l_sep_conj_perm.
    - exists r. split; [| split]; auto.
      intros. apply Hpre.
      + destruct H0. split; [| split]; auto.
        symmetry. eapply separate_antimonotone; eauto. apply lte_l_sep_conj_perm.
      + apply H0.
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
