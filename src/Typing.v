From Heapster Require Import
     Permissions
     Config.

From Coq Require Import
     Structures.Equalities
     Ensembles
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     Program.Equality.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.
(* Import CatNotations. *)
(* Import MonadNotation. *)
Open Scope monad_scope.

Definition sep_step p q : Prop :=
  forall r, p ⊥ r -> q ⊥ r.

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

Lemma sep_step_lte' : forall p q, q <= p -> sep_step p q.
Proof.
  repeat intro. symmetry. eapply separate_antimonotone; eauto. symmetry; auto.
Qed.

Lemma sep_step_view : forall p q x y, sep_step p q -> view p x y -> view q x y.
Proof.
  intros. specialize (H (sym_upd_perm p) (separate_self_sym _)).
  apply H; auto.
Qed.

Lemma sep_step_upd : forall p q x y, sep_step p q ->
                                upd q x y ->
                                upd p x y.
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

Section ts.
  Variant MemoryE : Type -> Type :=
  | Load : forall (p : SByte), MemoryE SByte
  | Store : forall (p v : SByte) , MemoryE unit
  .

  (* Definition E := (stateE config +' nondetE). *)
  Definition E := (MemoryE +' nondetE).

  Context {R : Type}.
  (* Definition R := SByte. *)

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

  Lemma rewrite_spin : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.

  Variant step : itree E R -> config -> itree E R -> config -> Prop :=
  | step_tau : forall t c, step (Tau t) c t c
  | step_nondet_true : forall k c, step (vis Or k) c (k true) c
  | step_nondet_false : forall k c, step (vis Or k) c (k false) c
  | step_load : forall k c p v, read c p = Some v ->
                           step (vis (Load (Ptr p)) k) c (k v) c
  | step_store : forall k c c' p v, write c p v = Some c' ->
                               step (vis (Store (Ptr p) v) k) c (k tt) c'
  | step_load_fail : forall k c p, read c p = None ->
                                step (vis (Load (Ptr p)) k) c (k (Byte 0)) (error_config c)
  | step_store_fail : forall k c p v, write c p v = None ->
                                    step (vis (Store (Ptr p) v) k) c (k tt) (error_config c)
  (* | step_get : forall k c, step (vis (Get _) k) c (k c) c *)
  (* | step_put : forall k c c', step (vis (Put _ c') k) c (k tt) c' *)
  .

  Inductive multistep : itree E R -> config -> itree E R -> config -> Prop :=
  | multistep_refl : forall t c, multistep t c t c
  | multistep_step : forall t c t' c' t'' c'',
      multistep t c t' c' -> step t' c' t'' c'' -> multistep t c t'' c''
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
    - pose proof (bind_vis _ _ (subevent _ (Load (Ptr p))) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis.
      (* constructor doesn't work here for some reason *)
      apply (step_load (fun v => x <- k0 v;; k x) _ _ _ H0).
    - pose proof (bind_vis _ _ (subevent _ (Store (Ptr p) v)) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor; auto.
    - pose proof (bind_vis _ _ (subevent _ (Load (Ptr p))) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor; auto.
    - pose proof (bind_vis _ _ (subevent _ (Store (Ptr p) v)) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor 7; auto.
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
      try solve [rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor; auto].
    (* as above, load case needs its constructor manually applied... *)
    rewrite rewrite_par; unfold par_match; simpl; repeat eexists. constructor.
    apply (step_load (fun x => par (k x) t') _ _ _ H0).
  Qed.
  Lemma par_step_right : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'', step (par t' t1) c t'' c /\ step t'' c (par t' t2) c'.
  Proof.
    inversion 1; subst;
      try solve [rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor; auto].
    rewrite rewrite_par; unfold par_match; simpl; repeat eexists. constructor 3.
    apply (step_load (fun x => par t' (k x)) _ _ _ H0).
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

  Definition no_error (c : config) :=
    e c = false.

  (* use instead of no_upd_error? *)
  Program Definition no_error_perm : perm :=
    {|
    dom := no_error;
    view := fun c c' => no_error c -> no_error c';
    upd := eq;
    |}.
  Next Obligation.
    constructor; auto.
  Qed.

  Lemma typing_perm_multistep : forall p t,
      typing_perm p t ->
      forall c, dom p c ->
           forall t' c', multistep t c t' c' ->
                    exists p', dom p' c' /\ sep_step p p' /\ typing_perm p' t'.
  Proof.
    intros. induction H1.
    - eexists; split; [| split]; eauto; reflexivity.
    - destruct IHmultistep as (? & ? & ? & ?); eauto. pinversion H5.
      edestruct H6 as (? & ? & ? & ? & ?); eauto. pclearbot.
      exists x0; split; [| split]; eauto. etransitivity; eauto.
  Qed.

  Lemma typing_perm_soundness_step : forall p t,
      typing_perm p t ->
      forall c, dom (p * no_error_perm) c ->
           forall t' c', step t c t' c' -> no_error c'.
  Proof.
    intros. destruct H0 as (? & ? & ?).
    pinversion H. specialize (H4 _ H0 _ _ H1). decompose [ex and] H4; clear H4.
    eapply H3; eauto.
  Qed.

  Lemma typing_perm_soundness : forall p t,
      typing_perm p t ->
      forall c, dom (p * no_error_perm) c ->
           forall t' c', multistep t c t' c' -> no_error c'.
  Proof.
    intros.
    destruct H0 as (? & ? & ?).
    generalize dependent p. induction H1; intros; auto.
    destruct (typing_perm_multistep _ _ H0 _ H3 _ _ H1) as (? & ? & ? & ?).
    specialize (IHmultistep H2 _ H0 H3 H4).
    apply H6 in H4.
    eapply typing_perm_soundness_step; eauto. split; [| split]; auto.
  Qed.

  Lemma typing_perm_lte : forall p q t, typing_perm p t -> p <= q -> typing_perm q t.
  Proof.
    intros. pcofix CIH. pstep. constructor; intros.
    pinversion H. edestruct H3; eauto. split; eauto.
    destruct H5 as [p' [? [? ?]]]. exists p'. split; [| split]; auto.
    - pclearbot. left. eapply paco2_mon_bot; eauto.
    - eapply sep_step_lte; eauto.
  Qed.

  Lemma typing_perm_ret : forall p r, typing_perm p (Ret r).
  Proof.
    pstep. constructor. intros. inversion H0.
  Qed.

  Lemma typing_perm_spin : forall p, typing_perm p ITree.spin.
  Proof.
    pcofix CIH. pstep. constructor. intros. rewrite rewrite_spin in H0.
    inversion H0; subst; split; try reflexivity.
    exists p. split; eauto; intuition.
  Qed.

  (* Lemma typing_perm_load' ptr val : *)
  (*   typing_perm (read_perm_p ptr val) (trigger (Load (Ptr ptr))). *)
  (* Proof. *)
  (*   pcofix CIH. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. *)
  (*   split; intuition. *)
  (*   eexists. split; [| split]; eauto; intuition. *)
  (*   left. eapply paco2_mon_bot; eauto. apply typing_perm_ret. *)
  (* Qed. *)

  (* Lemma typing_perm_store ptr val : *)
  (*   typing_perm (write_p ptr) (trigger (Store (Ptr ptr) val)). *)
  (* Proof. *)
  (*   pcofix CIH. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. *)
  (*   split; simpl; auto. *)
  (*   - intros. admit. *)
  (*   - exists (write_p ptr). split; [| split]. *)
  (*     + left. eapply paco2_mon_bot; eauto. apply typing_perm_ret. *)
  (*     + reflexivity. *)
  (*     + admit. *)
  (* Abort. *)

  Definition typing P t := forall p, p ∈ P -> typing_perm p t.

  Lemma typing_soundness : forall P t,
      typing P t -> forall p c, p ∈ (P ** singleton_Perms no_error_perm) ->
                          dom p c ->
                          forall t' c', multistep t c t' c' ->
                                   no_error c'.
  Proof.
    intros. simpl in *.
    destruct H0 as (? & ? & ? & ? & ?).
    eapply typing_perm_soundness; eauto.
    split; [| split]; auto.
    - apply H4; auto.
    - apply H3; apply H4; auto.
    - eapply separate_antimonotone; eauto. destruct H4 as [? _ _]. apply (dom_inc0 _ H1).
  Qed.

  Lemma type_lte : forall P Q t, typing P t -> P ⊑ Q -> typing Q t.
  Proof.
    repeat intro. specialize (H p (H0 _ H1)). auto.
  Qed.
  Lemma type_spin : forall P, typing P ITree.spin.
  Proof.
    repeat intro. apply typing_perm_spin.
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
        destruct e; [destruct m | destruct n]; pinversion Ht1; exists (p1 * p2);
          (split; intuition; [| split; [| split]]; auto);
          left; pstep; constructor; intros ? [Hdom1' [Hdom2' Hsep']] ? ? Hstep;
            inversion Hstep; auto_inj_pair2; subst.
        + (* load success *)
          destruct (H _ Hdom1' _ _ (step_load _ _ _ _ H5)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
        + (* load error *)
          destruct (H _ Hdom1' _ _ (step_load_fail _ _ _ H5)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
            eapply dom_respects. apply Hsep'. apply H0. auto.
        + destruct (H _ Hdom1' _ _ (step_store _ _ _ _ _ H6)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
            eapply dom_respects. apply Hsep'. apply H0. auto.
        + destruct (H _ Hdom1' _ _ (step_store_fail _ _ _ _ H6)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p * p2). split; [| split]; auto.
          * apply sep_step_sep_conj_l; auto.
          * split; [| split]; auto.
            eapply dom_respects. apply Hsep'. apply H0. auto.
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
        destruct e; [destruct m | destruct n]; pinversion Ht2; exists (p1 * p2);
          (split; intuition; [| split; [| split]]; auto);
          left; pstep; constructor; intros ? [Hdom1' [Hdom2' Hsep']] ? ? Hstep;
            inversion Hstep; auto_inj_pair2; subst; symmetry in Hsep.
        + destruct (H _ Hdom2' _ _ (step_load _ _ _ _ H5)) as [? [p [? [? ?]]]]. pclearbot.
          split; intuition.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. symmetry. apply H2; auto.
        + destruct (H _ Hdom2' _ _ (step_load_fail _ _ _ H5)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. 2: symmetry; apply H2; auto.
            eapply dom_respects. apply Hsep'. apply H0. auto.
        + destruct (H _ Hdom2' _ _ (step_store _ _ _ _ _ H6)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. 2: symmetry; apply H2; auto.
            eapply dom_respects. apply Hsep'. apply H0. auto.
        + destruct (H _ Hdom2' _ _ (step_store_fail _ _ _ _ H6)) as [? [p [? [? ?]]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p1 * p). split; [| split]; auto.
          * apply sep_step_sep_conj_r; auto.
          * split; [| split]; auto. 2: symmetry; apply H2; auto.
            eapply dom_respects. apply Hsep'. apply H0. auto.
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

Lemma typing_perm_load p ptr :
  typing_perm p (trigger (Load (Ptr ptr))).
Proof.
  pcofix CIH. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst.
  split; intuition.
  eexists. split; [| split]; eauto; intuition.
  left. eapply paco2_mon_bot; eauto. apply typing_perm_ret.
Abort.

Lemma typing_load ptr P :
  typing P (trigger (Load (Ptr ptr))).
Proof.
  repeat intro. apply typing_perm_load.
Qed.

(* Load an addr from ptr, and store val into it *)
Definition load_store ptr val : itree E _ :=
  vis (Load (Ptr ptr)) (fun ptr' => vis (Store ptr' val) (fun _ => Ret tt)).

(* TODO GET THESE TO WORK *)
Lemma bind_trigger' {R} X (e : E X) k :
  x <- trigger e ;; k x = (Vis e (fun x => k x) : itree E R).
Proof.
  apply bisimulation_is_eq. apply bind_trigger.
Qed.

Lemma unfold_bind' {R S : Type} (t : itree E R) (k : R -> itree E S) :
    x <- t;; k x = ITree._bind k (fun t0 : itree E R => x <- t0;; k x) (observe t).
Proof.
  apply bisimulation_is_eq. apply unfold_bind.
Qed.

Lemma typing_perm_store ptr v1 v2 :
  typing_perm (write_perm ptr v1) (vis (Store (Ptr ptr) v2) (fun _ => Ret tt)).
Proof.
  pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. split.
  - split; intros; simpl.
    + eapply write_success_other_ptr; eauto.
    + eapply write_success_allocation; eauto.
  - exists (write_perm ptr v2); split; [| split].
    + left. apply typing_perm_ret.
    + repeat intro. destruct H1. constructor; auto.
    + simpl. eapply write_success_ptr; eauto.
Qed.

Lemma typing_perm_load_store ptr ptr' v v' :
  typing_perm (read_perm ptr (Ptr ptr') * write_perm ptr' v) (load_store ptr v').
Proof.
  intros. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. split; intuition.
  eexists. split; [| split]; eauto; intuition.
  left. simpl in H. destruct H. rewrite H in H6. inversion H6; subst.
  eapply typing_perm_lte. apply typing_perm_store. apply lte_r_sep_conj_perm.
Qed.

Lemma typing_load_store ptr val :
  typing (read_Perms ptr (fun val' => match val' with
                                   | Ptr ptr' => write_Perms ptr' (fun _ => bottom_Perms)
                                   | _ => bottom_Perms
                                   end))
         (load_store ptr val).
Proof.
  repeat intro. simpl in H. decompose [ex and] H; clear H.
  subst. simpl in H2. decompose [ex and] H2; clear H2.
  destruct x0 eqn:?.
  - pstep. constructor. intros. unfold load_store in *.
    inversion H2; auto_inj_pair2.
    split; intuition.
    assert (x0 = v).
    { subst.
      destruct H3. specialize (dom_inc0 _ H1). destruct dom_inc0. destruct H.
      specialize (dom_inc0 _ H3). simpl in dom_inc0. rewrite dom_inc0 in H9. inversion H9. auto.
    }
    subst.
    eexists. split; [| split]; eauto. left. pstep. constructor. intros. inversion H5. reflexivity.
  - simpl in *. decompose [ex and] H0; clear H0; subst. simpl in H4.
    decompose [ex and] H4; clear H4.
    eapply typing_perm_lte. apply typing_perm_load_store.
    etransitivity; eauto. apply sep_conj_perm_monotone; eauto.
    etransitivity; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

(* Store an addr into ptr, and then use it by loading and storing into it. *)
Definition store_load_store ptr ptr' : itree E _ :=
  vis (Store (Ptr ptr) ptr') (fun _ => load_store ptr (Byte 1)).

Lemma typing_perm_store_load_store ptr ptr' v v' :
  typing_perm (write_perm ptr v * write_perm ptr' v') (store_load_store ptr (Ptr ptr')).
Proof.
  pstep. constructor. intros. unfold store_load_store in H0.
  inversion H0; auto_inj_pair2; subst.
  (* destruct H as (? & ? & ?). simpl in H. *)
  split.
  - constructor. left. simpl.
    split; [eapply write_success_other_ptr | eapply write_success_allocation]; eauto.
  - exists (read_perm ptr (Ptr ptr') * write_perm ptr' v'). split; [| split].
    + left. apply typing_perm_load_store.
    + (* TODO: factor out this more general version of sep_step_lte' *)
      repeat intro. destruct H1. constructor; auto. intros.
      apply sep_r0. clear sep_l0 sep_r0. induction H1.
      * destruct H1; constructor; [left | right]; simpl in *; subst; auto. split; reflexivity.
      * econstructor 2; eauto.
    + destruct H as (? & ? & ?).
      split; [| split]; simpl in *; auto.
      * eapply write_success_ptr; eauto.
      * apply write_write_separate_neq_ptr in H2. erewrite <- write_success_other_ptr; eauto.
      * rewrite read_write_separate_neq_ptr. apply write_write_separate_neq_ptr in H2; auto.
Qed.

Lemma typing_store_load_store ptr ptr' :
  typing (write_Perms ptr (fun _ => bottom_Perms) **
          write_Perms ptr' (fun _ => bottom_Perms))
         (store_load_store ptr (Ptr ptr')).
Proof.
  repeat intro. simpl in H. decompose [ex and] H; clear H. subst.
  simpl in H3, H5. decompose [ex and] H3; clear H3.
  decompose [ex and] H5; clear H5. clear H0 H3.
  eapply typing_perm_lte. apply typing_perm_store_load_store.
  etransitivity; eauto.
  apply sep_conj_perm_monotone; etransitivity; eauto;
    etransitivity; eauto; apply lte_l_sep_conj_perm.
Qed.
