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
     SepStep.

From Paco Require Import
     paco.

Import ListNotations.
Open Scope list_scope.
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

  Lemma nonLifetime_ptr p rw o' :
    @nonLifetime_Perms _ Ss _ ((VPtr p) :: ptr(rw, o', trueP) ▷ tt).
  Proof.
    intros q Hq. destruct p as [b o]. destruct Hq as (? & (v & ?) & ?). subst.
    destruct H0 as (p & p' & Hp & _ & Hsep & Hlte). destruct rw.
    - exists (read_perm (b, o + o') v). split; [| split; [| split]].
      + eexists. split. eexists. reflexivity.
        cbn. eexists. exists bottom_perm. intuition. reflexivity.
        apply separate_bottom. rewrite sep_conj_perm_bottom. reflexivity.
      + etransitivity; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm.
      + apply nonLifetime_read_perm.
      + apply guar_inv_read_perm.
    - exists (write_perm (b, o + o') v). split; [| split; [| split]].
      + eexists. split. eexists. reflexivity.
        cbn. eexists. exists bottom_perm. intuition. reflexivity.
        apply separate_bottom. rewrite sep_conj_perm_bottom. reflexivity.
      + etransitivity; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm.
      + apply nonLifetime_write_perm.
      + apply guar_inv_write_perm.
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

  Lemma split_Perms b o l (P Q : @Perms (Si * Ss)) :
    (VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt * lowned_Perms' l P Q ⊨
      when_Perms l ((VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt) *
      lowned_Perms' l
                    (when_Perms l ((VPtr (b, o)) :: ptr(R, 0, trueP) ▷ tt) * P)
                    (((VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte).
    destruct (nonLifetime_ptr _ _ _ _ Hp') as (p & Hp & Hpp' & Hnlp & Hguarp).
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
      cbn in Hp.
      destruct Hp as (? & (v & ?) & Hx). subst. rewrite Nat.add_0_r in Hx.
      rewrite sep_conj_Perms_commut in Hx. rewrite sep_conj_Perms_bottom_identity in Hx.
      cbn in Hx.

      destruct Hpr as (? & (v' & ?) & Hx'). subst. rewrite Nat.add_0_r in Hx'.
      rewrite sep_conj_Perms_commut in Hx'. rewrite sep_conj_Perms_bottom_identity in Hx'.
      cbn in Hx'.
      exists ((write_perm (b, o) v') ** r). split; [| split].
      + apply sep_conj_Perms_perm; auto.
        * cbn. eexists. split. eexists. reflexivity.
          rewrite Nat.add_0_r.
          rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity.
          cbn. reflexivity.
        * symmetry. eapply separate_write_perm.
          apply Hsep_step.
          eapply separate_antimonotone.
          2: apply Hx.
          symmetry. auto.
      + etransitivity.
        * apply sep_step_sep_conj_r; eauto. symmetry. auto.
        * apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
          eapply sep_step_write_perm.
          apply sep_step_lte'; eauto.
      + intros. split; [| split]; auto.
        * apply Hlte'' in H. destruct H as (? & ? & ?).
          apply Hlte''' in H. cbn in H.
          rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
          apply Hx' in H. cbn in *.
          rewrite HGetPut1 in H |- *; auto. right. reflexivity.
        * apply Hpre; auto. apply Hlte''; auto.
        * symmetry. apply Hsep_step.
          eapply separate_write_perm.
          eapply separate_antimonotone. symmetry. apply Hpr2. apply Hx.
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
