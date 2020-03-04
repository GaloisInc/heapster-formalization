Require Import Heapster.Permissions.

From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties.

From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus.

From Paco Require Import
     paco.

Import ITreeNotations.
Import ITree.Basics.Basics.Monads.

Require Import ITree.Eq.EqAxiom.

Section ts.

  Definition E := (stateE config +' nondetE).

  Context {R : Type}.

  Definition par_match
             (par : itree E R -> itree E R -> itree E R)
             (t1 t2 : itree E R)
    : itree E R :=
    vis Or (fun b : bool =>
              if b then
                match (observe t1) with
                | RetF _ => t2
                | TauF t => Tau (par t t2)
                | VisF o k => vis o (fun x => par (k x) t2)
                end
              else
                match (observe t2) with
                | RetF _ => t1
                | TauF t => Tau (par t1 t)
                | VisF o k => vis o (fun x => par t1 (k x))
                end).

  CoFixpoint par (t1 t2 : itree E R) := par_match par t1 t2.

  Lemma rewrite_par : forall t1 t2, par t1 t2 = par_match par t1 t2.
  Proof.
    intros. apply bisimulation_is_eq. revert t1 t2.
    ginit. gcofix CIH. intros. gstep. unfold par. constructor. red. intros.
    apply Reflexive_eqit_gen_eq. (* not sure why reflexivity doesn't work here *)
  Qed.

  Variant step : itree E R -> config -> itree E R -> config -> Prop :=
  | step_tau : forall t c, step (Tau t) c t c
  | step_nondet_true : forall k c, step (vis Or k) c (k true) c
  | step_nondet_false : forall k c, step (vis Or k) c (k false) c
  | step_get : forall k c, step (vis (Get _) k) c (k c) c
  | step_put : forall k c c', step (vis (Put _ c') k) c (k tt) c'
  .

  Lemma step_bind : forall (t1 t2 : itree E R) (c1 c2 : config) (k : R -> itree E R),
      step t1 c1 t2 c2 ->
      step (t1 >>= k) c1 (t2 >>= k) c2.
  Proof.
    intros. inversion H; subst.
    - pose proof (bind_tau _ t2 k) as bind_tau.
      apply bisimulation_is_eq in bind_tau. rewrite bind_tau. constructor.
    - pose proof (bind_vis _ _ (subevent _ Or) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
    - pose proof (bind_vis _ _ (subevent _ Or) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
    - pose proof (bind_vis _ _ (subevent _ (Get _)) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
    - pose proof (bind_vis _ _ (subevent _ (Put _ c2)) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
  Qed.

  Lemma step_ret_bind : forall (t1 t2 : itree E R) (c1 c2 : config) (r : R),
      step t1 c1 t2 c2 ->
      step (Ret r;; t1) c1 t2 c2.
  Proof.
    intros. pose proof (bind_ret_l r (fun _ => t1)) as bind_ret.
    apply bisimulation_is_eq in bind_ret. rewrite bind_ret. assumption.
  Qed.

  (* to handle the nondeterminism, par needs double the amount of steps *)
  Lemma par_step_left : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'', step (par t1 t') c t'' c /\ step t'' c (par t2 t') c'.
  Proof.
    inversion 1; subst;
      (rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor).
  Qed.
  Lemma par_step_right : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'', step (par t' t1) c t'' c /\ step t'' c (par t' t2) c'.
  Proof.
    inversion 1; subst;
      (rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor).
  Qed.

  Definition sep_step p q : Prop :=
    (* (forall x, dom p x -> dom q x) /\ *)
    (forall r, p ⊥ r -> q ⊥ r).

  Instance sep_step_refl : Reflexive sep_step.
  Proof.
    repeat intro; auto.
  Qed.

  Instance sep_step_trans : Transitive sep_step.
  Proof.
    repeat intro. auto.
  Qed.

  Lemma sep_step_lte : forall p p' q, p <= p' -> sep_step p q -> sep_step p' q.
  Proof.
    repeat intro. apply H0. symmetry. symmetry in H1. eapply separate_antimonotone; eauto.
  Qed.

  Lemma sep_step_view : forall p q x y, sep_step p q -> view p x y -> view q x y.
  Proof.
    intros. specialize (H (sym_upd_perm p) (separate_self_sym _)).
    apply H; auto.
  Qed.

  Lemma sep_step_upd : forall p q x y, sep_step p q ->
                                  upd q x y ->
                                  clos_refl_sym_trans config (upd p) x y.
  Proof.
    intros. specialize (H (sym_upd_perm p) (separate_self_sym _)).
    apply H; auto.
  Qed.

  Lemma sep_step_sep_conj_l : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (p1 * q) (p2 * q).
  Proof.
    intros p1 p2 q ? ?.
    repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
    - apply H0. symmetry. eapply separate_sep_conj_perm_l; eauto.
    - symmetry. eapply separate_sep_conj_perm_r; eauto.
  Qed.
  Lemma sep_step_sep_conj_r : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (q * p1) (q * p2).
  Proof.
    intros p1 p2 q ? ?.
    repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
    - symmetry. eapply separate_sep_conj_perm_l; eauto.
    - apply H0. symmetry. eapply separate_sep_conj_perm_r; eauto.
    - symmetry. auto.
  Qed.

  Variant typing_perm_gen typing (p : perm) (t : itree E R) : Prop :=
  | cond : (forall c, dom p c ->
                 forall t' c',
                   step t c t' c' ->
                   (
                     (* we step to configs that satisfy the perm *)
                     (upd p c c') /\
                     (* we step to machines that are well-typed by some other perm that maintains separation *)
                     (exists p', typing p' t' /\ sep_step p p' /\ dom p' c'))) ->
           typing_perm_gen typing p t.

  Definition typing_perm p t := paco2 typing_perm_gen bot2 p t.

  Lemma typing_perm_gen_mon : monotone2 typing_perm_gen.
  Proof.
    repeat intro.
    inversion IN. econstructor. intros. specialize (H _ H0 _ _ H1).
    destruct H as [? [? [? ?]]]. split; eauto.
  Qed.
  Hint Resolve typing_perm_gen_mon : paco.

  Lemma rewrite_spin : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.

  Lemma typing_perm_lte : forall p q t, typing_perm p t -> p <= q -> typing_perm q t.
  Proof.
    intros. pcofix CIH. pstep. constructor; intros.
    pinversion H. edestruct H3; eauto. split; eauto.
    destruct H5 as [p' [? [? ?]]]. exists p'. split; [| split]; auto.
    - pclearbot. left. eapply paco2_mon_bot; eauto.
    - eapply sep_step_lte; eauto.
  Qed.

  Definition typing P t := forall p, p ∈ P -> typing_perm p t.

  Lemma type_lte : forall P Q t, typing P t -> P ⊑ Q -> typing Q t.
  Proof.
    repeat intro. specialize (H p (H0 _ H1)). auto.
  Qed.

  Lemma type_spin : forall P, typing P ITree.spin.
  Proof.
    pcofix CIH. intros. pstep. constructor. intros. rewrite rewrite_spin in H1.
    inversion H1; subst. split; try reflexivity.
    exists p. split; eauto; intuition.
  Qed.

  Lemma type_ret : forall P r, typing P (Ret r).
  Proof.
    repeat intro.
    pstep. constructor. intros. inversion H1.
  Qed.

  Lemma type_top : forall t, typing top_Perms t.
  Proof.
    repeat intro. pstep. constructor. intros. inversion H.
  Qed.

  Lemma type_tau : forall P t, typing P t -> typing P (Tau t).
  Proof.
    repeat intro. specialize (H _ H0). pinversion H.
    pfold. econstructor. intros.
    inversion H3; subst.
    split; intuition.
    exists p. split; intuition.
  Qed.

  Lemma frame : forall P1 P2 t, typing P1 t -> typing (P1 ** P2) t.
  Proof.
    intros. eapply type_lte; eauto. apply lte_l_sep_conj_Perms.
  Qed.
  (* todo get proper instance working *)
  Lemma frame' : forall P1 P2 t, typing P2 t -> typing (P1 ** P2) t.
  Proof.
    intros. eapply type_lte; eauto. apply lte_r_sep_conj_Perms.
  Qed.

  Require Import Coq.Program.Equality.

  Lemma parallel_perm : forall p1 p2 t1 t2,
      typing_perm p1 t1 -> typing_perm p2 t2 -> typing_perm (p1 * p2) (par t1 t2).
  Proof.
    pcofix CIH. intros p1 p2 t1 t2 Ht1 Ht2.
    pstep. econstructor. intros c [Hdom1 [Hdom2 Hsep]] t' c' Hstep.
    rewrite rewrite_par in Hstep. unfold par_match in Hstep.
    dependent destruction Hstep; split; try reflexivity.
    { destruct (observe t1) eqn:?.
      - exists p2. split; [left; eapply paco2_mon_bot; eauto | split]; auto.
        repeat intro. symmetry. symmetry in H. eapply separate_sep_conj_perm_r; eauto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht1.
        pinversion Ht1. destruct (H _ Hdom1 _ _ (step_tau _ _)) as [? [p [? [? ?]]]].
        exists (p * p2). pclearbot. split; [| split].
        + left. pstep. constructor. intros. inversion H5; subst.
          split; intuition. exists (p * p2). split; [| split]; intuition.
        + apply sep_step_sep_conj_l; auto.
        + split; [| split]; auto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht1.
        destruct e; [destruct s | destruct n]; pinversion Ht1; exists (p1 * p2);
          (split; intuition; [| split; [| split]]; auto);
          left; pstep; constructor; intros ? [Hdom1' [Hdom2' Hsep']] ? ? Hstep;
            inversion Hstep; auto_inj_pair2; subst.
        + destruct (H _ Hdom1' _ _ (step_get _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
        + destruct (H _ Hdom1' _ _ (step_put _ _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
            rewrite dom_respects. 2: { symmetry. apply Hsep'. apply H0. } auto.
        + destruct (H _ Hdom1' _ _ (step_nondet_true _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
        + destruct (H _ Hdom1' _ _ (step_nondet_false _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
    }
    { symmetry in Hsep. destruct (observe t2) eqn:?.
      - exists p1. split; [left; eapply paco2_mon_bot; eauto | split]; auto.
        repeat intro. symmetry. symmetry in H. eapply separate_sep_conj_perm_l; eauto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht2.
        pinversion Ht2. destruct (H _ Hdom2 _ _ (step_tau _ _)) as [? [p [? [? ?]]]].
        exists (p1 * p). pclearbot. split; [| split].
        + left. pstep. constructor. intros. inversion H5; subst.
          split; intuition. exists (p1 * p). split; [| split]; intuition.
        + apply sep_step_sep_conj_r; auto.
        + split; [| split]; auto. symmetry. apply H2; auto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht2. symmetry in Hsep.
        destruct e; [destruct s | destruct n]; pinversion Ht2; exists (p1 * p2);
          (split; intuition; [| split; [| split]]; auto);
          left; pstep; constructor; intros ? [Hdom1' [Hdom2' Hsep']] ? ? Hstep;
            inversion Hstep; auto_inj_pair2; subst; symmetry in Hsep.
        + destruct (H _ Hdom2' _ _ (step_get _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. symmetry. apply H2; auto.
        + destruct (H _ Hdom2' _ _ (step_put _ _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. 2: symmetry; apply H2; auto.
            rewrite dom_respects. 2: { symmetry. apply Hsep'. apply H0. } auto.
        + destruct (H _ Hdom2' _ _ (step_nondet_true _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. symmetry. apply H2; auto.
        + destruct (H _ Hdom2' _ _ (step_nondet_false _ _)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. symmetry. apply H2; auto.
      }
  Qed.

  Lemma parallel : forall P1 P2 t1 t2,
      typing P1 t1 -> typing P2 t2 -> typing (P1 ** P2) (par t1 t2).
  Proof.
    intros P1 P2 t1 t2 Ht1 Ht2 p [p1 [p2 [? [? ?]]]].
    assert (Hp1: p ∈ P1).
    { eapply Perms_upwards_closed; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm. }
    assert (Hp2: p ∈ P2).
    { eapply Perms_upwards_closed; eauto. etransitivity; eauto. apply lte_r_sep_conj_perm. }
    specialize (Ht1 _ H).
    specialize (Ht2 _ H0). eapply typing_perm_lte; eauto. eapply parallel_perm; eauto.
  Qed.
End ts.

Import ITreeNotations.
Import ITree.Basics.Basics.Monads.

Definition test : itree (stateE config +' _) unit :=
  par
    (x <- (trigger (Get _)) ;; (trigger (Put _ x)))
    (par (vis (Get _) (fun x => Ret tt))
         (Ret tt)).

(* Compute (burn 10 test). *)

(* Eval cbv in (burn 10 (step (trigger (Put _ 0)) 1)). *)
(* Eval cbn in (burn 10 (step test 1)). *)
(* Eval cbn in (burn 10 (run_state test 1)). *)
