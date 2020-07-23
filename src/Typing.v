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

Definition sep_step_Perms P Q : Prop :=
  forall p, p ∈ P -> exists q, q ∈ Q /\ sep_step p q.

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

  (* todo: q : R -> perm *)
  Variant typing_perm_gen typing (p : perm) (q : perm) : itree E R -> Prop :=
  | cond : forall t, (exists c t' c', step t c t' c') /\ (* we can step *)
                (forall c, dom p c -> (* and everything we can step to... *)
                      forall t' c',
                        step t c t' c' ->
                        (
                          (* we step to configs that satisfy the perm *)
                          (upd p c c') /\
                          (* we step to machines that are well-typed by some other perm that maintains separation *)
                          (exists p', typing p' q t' /\ sep_step p p' /\ dom p' c'))) ->
                typing_perm_gen typing p q t
  | ret : forall r, q <= p -> typing_perm_gen typing p q (Ret r).

  Definition typing_perm := paco3 typing_perm_gen bot3.

  Lemma typing_perm_gen_mon : monotone3 typing_perm_gen.
  Proof.
    repeat intro.
    inversion IN; subst.
    - econstructor. destruct H. split; auto.
      intros. edestruct H0; eauto. split; eauto.
      destruct H4 as [? [? [? ?]]]. eexists. split; [| split]; eauto.
    - constructor 2; auto.
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

  Lemma typing_perm_multistep : forall p q t,
      typing_perm p q t ->
      forall c, dom p c ->
           forall t' c', multistep t c t' c' ->
                    exists p', dom p' c' /\ sep_step p p' /\ typing_perm p' q t'.
  Proof.
    intros. induction H1.
    - eexists; split; [| split]; eauto; reflexivity.
    - destruct IHmultistep as (? & ? & ? & ?); eauto. pinversion H5; subst.
      + edestruct H6 as (? & ? & ? & ? & ? & ?); eauto. pclearbot.
        exists x0; split; [| split]; eauto. etransitivity; eauto.
      + inversion H2.
  Qed.

  Lemma typing_perm_soundness_step : forall p q t,
      typing_perm p q t ->
      forall c, dom (p * no_error_perm) c ->
           forall t' c', step t c t' c' -> no_error c'.
  Proof.
    intros. destruct H0 as (? & ? & ?).
    pinversion H; subst.
    - destruct H4. specialize (H5 _ H0 _ _ H1). decompose [ex and] H5; clear H4.
      eapply H3; eauto.
    - inversion H1.
  Qed.

  Lemma typing_perm_soundness : forall p q t,
      typing_perm p q t ->
      forall c, dom (p * no_error_perm) c ->
           forall t' c', multistep t c t' c' -> no_error c'.
  Proof.
    intros. destruct H0 as (? & ? & ?).
    generalize dependent p. induction H1; intros; auto.
    destruct (typing_perm_multistep _ _ _ H0 _ H3 _ _ H1) as (? & ? & ? & ?).
    specialize (IHmultistep H2 _ H0 H3 H4).
    apply H6 in H4.
    eapply typing_perm_soundness_step; eauto. split; [| split]; auto.
  Qed.

  Lemma typing_perm_lte : forall p q p' t, typing_perm p q t -> p <= p' -> typing_perm p' q t.
  Proof.
    intros. pcofix CIH. pstep.
    pinversion H; subst.
    - constructor 1. destruct H1 as ((? & ? & ? & ?) & ?).
      split; eauto. intros.
      edestruct H2; eauto. split; eauto.
      destruct H6 as [p'' [? [? ?]]].
      exists p''. split; [| split]; auto.
      + pclearbot. left. eapply paco3_mon_bot; eauto.
      + eapply sep_step_lte; eauto.
    - constructor 2. etransitivity; eauto.
  Qed.

  (* Lemma typing_perm_ret : forall p q r, typing_perm p q (Ret r). *)
  (* Proof. *)
  (*   pstep. constructor 2. intros. inversion H0. *)
  (* Qed. *)

  Lemma typing_perm_spin : forall p q, typing_perm p q ITree.spin.
  Proof.
    pcofix CIH. pstep. constructor 1. split.
    - exists start_config. eexists. exists start_config. rewrite rewrite_spin. constructor.
    - intros. rewrite rewrite_spin in H0.
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

  Lemma typing_perm_bind : forall p q r t1 t2,
      typing_perm p q t1 ->
      typing_perm q r t2 ->
      typing_perm p r (t1 ;; t2).
  Proof.
    pcofix CIH. intros. pinversion H0; subst.
    - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor. split; auto.
      + do 3 eexists. apply step_bind; eauto.
      + intros.
  Qed.

  Lemma typing_perm_frame : forall p q r t, typing_perm p q t -> typing_perm (p * r) (q * r) t.
  Proof.
    pcofix CIH. intros. pinversion H0; subst.
    - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor 1. split; [do 3 eexists; eauto |].
      intros. edestruct H1; eauto; [apply H2 |]. clear H1.
      split; [constructor; auto |]. destruct H5 as (p' & ? & ? & ?).
      exists (p' * r0). split; [| split]; auto.
      + right. apply CIH. pclearbot. auto.
      + apply sep_step_sep_conj_l; auto. apply H2.
      + split; [| split]; auto.
        * destruct H2 as (? & ? & ?). apply H8 in H4. eapply dom_respects; eauto.
        * apply H5. apply H2.
    - pstep. constructor 2. apply sep_conj_perm_monotone; intuition.
  Qed.

  Lemma parallel_perm : forall p1 p2 q1 q2 t1 t2,
      typing_perm p1 q1 t1 -> typing_perm p2 q2 t2 -> typing_perm (p1 * p2) (q1 * q2) (par t1 t2).
  Proof.
    pcofix CIH. intros p1 p2 q1 q2 t1 t2 Ht1 Ht2.
    pstep. econstructor.
    rewrite rewrite_par. unfold par_match. split.
    simpl. exists start_config. eexists. exists start_config. constructor.
    intros c (Hdom1 & Hdom2 & Hsep) t' c' Hstep.
    inversion Hstep; auto_inj_pair2; subst; clear Hstep; split; try reflexivity.
    { pinversion Ht1; subst.
      - destruct H as ((? & ? & ? & ?) & ?).
        inversion H; subst; clear H.
        + (* tau *) clear x1. simpl.
          exists (p1 * p2). split; [| split]; intuition.
          * left. pstep. constructor. split.
            -- exists start_config; eexists; exists start_config; constructor.
            -- intros. inversion H1; subst.
               split; intuition. destruct H as (Hdom1' & Hdom2' & Hsep').
               destruct (H0 _ Hdom1' _ _ (step_tau _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p * p2). split; [| split]; auto.
               ++ apply sep_step_sep_conj_l; auto.
               ++ split; [| split]; auto.
          * split; [| split]; auto.
        + (* nondet *) clear x1. simpl.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- exists start_config; eexists; exists start_config; constructor.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom1' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
               }
               {
                 split; intuition.
                 destruct (H0 _ Hdom1' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
               }
          * split; [| split]; auto.
        + (* same as previous case *) clear x1. simpl.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- exists start_config; eexists; exists start_config; constructor.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom1' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
               }
               {
                 split; intuition.
                 destruct (H0 _ Hdom1' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
               }
          * split; [| split]; auto.
        + (* load *) clear H1 x1. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom1' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
               }
               {
                 destruct (H0 _ Hdom1' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 split. constructor 1. auto.
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
               }
          * split; [| split]; auto.
        + (* store *) clear H1 x1 x. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
               inversion H1; auto_inj_pair2; subst.
               {
                 destruct (H0 _ Hdom1' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
               }
               {
                 destruct (H0 _ Hdom1' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
               }
          * split; [| split]; auto.
        + (* load *) clear H1 x. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom1' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
               }
               {
                 destruct (H0 _ Hdom1' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 split. constructor 1. auto.
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
               }
          * split; [| split]; auto.
        + (* store *) clear H1 x. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
               inversion H1; auto_inj_pair2; subst.
               {
                 destruct (H0 _ Hdom1' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
               }
               {
                 destruct (H0 _ Hdom1' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p * p2). split; [| split]; auto.
                 - apply sep_step_sep_conj_l; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
               }
          * split; [| split]; auto.
      - simpl. exists (q1 * p2). split; [| split].
        + left. replace (q1 * p2) with (p2 * q1). 2: admit.
           replace (q1 * q2) with (q2 * q1). 2: admit.
          eapply paco3_mon_bot; eauto.
          apply typing_perm_frame. auto.
        + apply sep_step_sep_conj_l. auto.
          apply sep_step_lte'; auto.
        + split; [| split]; auto.
          respects; intuition. symmetry. eapply separate_antimonotone; eauto. symmetry. auto.
    }
    { pinversion Ht2; subst.
      - destruct H as ((? & ? & ? & ?) & ?).
        inversion H; subst; clear H.
        + (* tau *) clear x1. simpl.
          exists (p1 * p2). split; [| split]; intuition.
          * left. pstep. constructor. split.
            -- exists start_config; eexists; exists start_config; constructor.
            -- intros. inversion H1; subst.
               split; intuition. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
               destruct (H0 _ Hdom2' _ _ (step_tau _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p1 * p). split; [| split]; auto.
               ++ apply sep_step_sep_conj_r; auto.
               ++ split; [| split]; auto. symmetry; apply H3; auto.
          * split; [| split]; auto.
        + (* nondet *) clear x1. simpl.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- exists start_config; eexists; exists start_config; constructor.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom2' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto. symmetry; apply H3; auto.
               }
               {
                 split; intuition.
                 destruct (H0 _ Hdom2' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto. symmetry; apply H3; auto.
               }
          * split; [| split]; auto.
        + (* same as previous case *) clear x1. simpl.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- exists start_config; eexists; exists start_config; constructor.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom2' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto. symmetry; apply H3; auto.
               }
               {
                 split; intuition.
                 destruct (H0 _ Hdom2' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto. symmetry; apply H3; auto.
               }
          * split; [| split]; auto.
        + (* load *) clear H1 x1. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom2' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto. symmetry. apply H3; auto.
               }
               {
                 destruct (H0 _ Hdom2' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 split. constructor 1. auto.
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
                   symmetry. apply H3; auto.
               }
          * split; [| split]; auto.
        + (* store *) clear H1 x1 x. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
               inversion H1; auto_inj_pair2; subst.
               {
                 destruct (H0 _ Hdom2' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
                   symmetry. apply H3; auto.
               }
               {
                 destruct (H0 _ Hdom2' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
                   symmetry. apply H3; auto.
               }
          * split; [| split]; auto.
        + (* load *) clear H1 x. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
               inversion H1; auto_inj_pair2; subst.
               {
                 split; intuition.
                 destruct (H0 _ Hdom2' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto. symmetry. apply H3; auto.
               }
               {
                 destruct (H0 _ Hdom2' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
                 split. constructor 1. auto.
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
                   symmetry. apply H3; auto.
               }
          * split; [| split]; auto.
        + (* store *) clear H1 x. simpl. rename p into l.
          exists (p1 * p2). split; [| split]; auto; intuition.
          * left. pstep. constructor. split.
            -- admit.
            -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
               inversion H1; auto_inj_pair2; subst.
               {
                 destruct (H0 _ Hdom2' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
                   symmetry. apply H3; auto.
               }
               {
                 destruct (H0 _ Hdom2' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
                 split. constructor 1; auto.
                 pclearbot. exists (p1 * p). split; [| split]; auto.
                 - apply sep_step_sep_conj_r; auto.
                 - split; [| split]; auto.
                   respects. apply Hsep. auto.
                   symmetry. apply H3; auto.
               }
          * split; [| split]; auto.
      - simpl. exists (p1 * q2). split; [| split].
        + left.
          eapply paco3_mon_bot; eauto.
          apply typing_perm_frame. auto.
        + apply sep_step_sep_conj_r. symmetry; auto.
          apply sep_step_lte'; auto.
        + split; [| split]; auto.
          respects; intuition. eapply separate_antimonotone; eauto.
    }
  Admitted.

  Definition typing P Q t := forall p, p ∈ P -> exists q, q ∈ Q /\ typing_perm p q t.

  Lemma typing_soundness : forall P Q t,
      (* (exists q, q ∈ Q) /\ (* change to something involving top_Perms? *) *)
      typing P Q t -> forall p c, p ∈ (P ** singleton_Perms no_error_perm) ->
                            dom p c ->
                            forall t' c', multistep t c t' c' ->
                                     no_error c'.
  Proof.
    intros. simpl in *.
    destruct H0 as (? & ? & ? & ? & ?).
    destruct (H _ H0) as (? & ? & ?). (* as ((? & ?) & ?). *)
    eapply typing_perm_soundness; eauto.
    split; [| split]; auto.
    - apply H4; auto.
    - apply H3; apply H4; auto.
    - eapply separate_antimonotone; eauto. destruct H4 as [? _ _]. apply (dom_inc0 _ H1).
  Qed.

  Lemma typing_lte : forall P P' Q t, typing P Q t -> P ⊑ P' -> typing P' Q t.
  Proof.
    repeat intro; auto.
  Qed.
  Lemma typing_ret : forall P Q r, Q ⊑ P -> typing P Q (Ret r).
  Proof.
    repeat intro. specialize (H _ H0). exists p. split; auto.
    pstep. constructor 2. reflexivity.
  Qed.
  Lemma typing_spin : forall P Q, Q ⊑ P -> typing P Q ITree.spin.
  Proof.
    repeat intro. specialize (H _ H0). exists p. split; auto.
    apply typing_perm_spin.
  Qed.
  Lemma typing_top : forall P t, typing top_Perms P t.
  Proof.
    repeat intro. inversion H.
  Qed.
  Lemma typing_tau : forall P Q t, typing P Q t -> typing P Q (Tau t).
  Proof.
    repeat intro. specialize (H _ H0). destruct H as (? & ? & ?). pinversion H1; subst.
    - exists x. split; auto. pstep. constructor.
      split; [exists start_config; eexists; exists start_config; constructor |].
      intros. inversion H4; subst. split; intuition. eexists; split; [| split]; eauto; intuition.
    - exists x. split; auto. pstep. constructor.
      split; [exists start_config; eexists; exists start_config; constructor |].
      intros. inversion H4; subst. split; intuition. eexists; split; [| split]; eauto; intuition.
  Qed.
  Lemma typing_frame : forall P Q R t, typing P Q t -> typing (P ** R) (Q ** R) t.
  Proof.
    repeat intro. rename p into p'. destruct H0 as (p & r & ? & ? & ?).
    destruct (H _ H0) as (q & ? & ?).
    exists (q * r). split.
    - exists q, r. split; [| split]; intuition.
    - eapply typing_perm_lte; eauto. apply typing_perm_frame; auto.
  Qed.
  (* (* todo get proper instance working *) *)
  (* Lemma frame' : forall P1 P2 t, typing P2 t -> typing (P1 ** P2) t. *)
  (* Proof. *)
  (*   intros. eapply type_lte; eauto. apply lte_r_sep_conj_Perms. *)
  (* Qed. *)

  Lemma typing_parallel : forall P1 P2 Q1 Q2 t1 t2,
      typing P1 Q1 t1 -> typing P2 Q2 t2 -> typing (P1 ** P2) (Q1 ** Q2) (par t1 t2).
  Proof.
    intros P1 P2 Q1 Q2 t1 t2 Ht1 Ht2 p [p1 [p2 [? [? ?]]]].
    destruct (Ht1 _ H) as (q1 & ? & ?). specialize (Ht2 _ H0) as (q2 & ? & ?).
    exists (q1 * q2). split.
    - exists q1, q2. split; [| split]; intuition.
    - eapply typing_perm_lte; eauto. eapply parallel_perm; eauto.
  Qed.
End ts.

Definition fun_typing {R1} (P : Perms) (t : itree E R1) (P': R1 -> Perms) : Prop :=
  forall R2 (k : R1 -> itree E R2), (forall (r : R1), typing (P' r) (k r)) -> typing P (bind t k).

Lemma bind_ret_r' {E R} (t : itree E R) :
  x <- t;; Ret x = t.
Proof.
  apply bisimulation_is_eq. apply bind_ret_r.
Qed.

Lemma bind_ret_l' {E R1 R2} (r : R1) (k : R1 -> itree E R2) :
  x <- Ret r;; k x = k r.
Proof.
  apply bisimulation_is_eq. apply bind_ret_l.
Qed.

Lemma bind_bind' {E R1 R2 R3} (t : itree E R1) (k1 : R1 -> itree E R2) (k2 : R2 -> itree E R3) :
  x <- (x <- t;; k1 x);; k2 x = x1 <- t;; x2 <- k1 x1;; k2 x2.
Proof.
  apply bisimulation_is_eq. apply bind_bind.
Qed.

Lemma bind_trigger' {E' R} `{E' -< E} X (e : E' X) k :
  x <- trigger e ;; k x = (vis e (fun x => k x) : itree E R).
Proof.
  apply bisimulation_is_eq. apply bind_trigger.
Qed.

Lemma unfold_bind' {R S : Type} (t : itree E R) (k : R -> itree E S) :
    x <- t;; k x = ITree._bind k (fun t0 : itree E R => x <- t0;; k x) (observe t).
Proof.
  apply bisimulation_is_eq. apply unfold_bind.
Qed.

Lemma read_perm_read_succeed p ptr c v v' :
  read_perm ptr v <= p ->
  dom p c ->
  read c ptr = Some v' ->
  v = v'.
Proof.
  intros. apply H in H0. simpl in H0. rewrite H0 in H1. inversion H1; auto.
Qed.
Lemma read_perm_read_fail p ptr c v :
  read_perm ptr v <= p ->
  dom p c ->
  read c ptr = None ->
  False.
Proof.
  intros. apply H in H0. simpl in H0. rewrite H0 in H1. inversion H1.
Qed.
Lemma write_perm_write_fail p ptr c v v' :
  write_perm ptr v <= p ->
  dom p c ->
  write c ptr v' = None ->
  False.
Proof.
  intros. apply H in H0. simpl in H0. destruct ptr as [b o].
  unfold read, write in *. simpl in *.
  destruct (m c b); try solve [inversion H1]; try solve [inversion H0]. destruct l.
  destruct (PeanoNat.Nat.ltb o size); destruct (bytes o); simpl in *;
    try solve [inversion H1]; try solve [inversion H0].
Qed.

Lemma fun_typing_consequence {R} P (t : itree E R) P' Q Q' :
  fun_typing P t P' ->
  P ⊑ Q ->
  (forall r, Q' r ⊑ P' r) ->
  fun_typing Q t Q'.
Proof.
  red. intros. eapply type_lte; eauto. apply H. intros. eapply type_lte; eauto.
Qed.

Lemma fun_typing_ret {R} (r : R) P : fun_typing (P r) (Ret r) P.
Proof.
  repeat intro. simpl. rewrite bind_ret_l'. apply H; auto.
Qed.

Lemma fun_typing_ret_invert {R} (r : R) P P' :
  fun_typing P (Ret r) P' -> forall p p', p ∈ P -> p' ∈ P' r ->
                                    sep_step p p'.
Proof.
  repeat intro. unfold fun_typing in H. simpl in H.
  setoid_rewrite bind_ret_l' in H.
Admitted.

Lemma fun_typing_bind {R1 R2} (P1 : Perms) (t1 : itree E R1) (P2 : R1 -> Perms) (k : R1 -> itree E R2) (P3 : R2 -> Perms) :
  fun_typing P1 t1 P2 ->
  (forall r, fun_typing (P2 r) (k r) P3) ->
  fun_typing P1 (bind t1 k) P3.
Proof.
  repeat intro. simpl. rewrite bind_bind'. apply H; auto.
  repeat intro. apply H0; auto.
Qed.

Lemma fun_typing_pre {R} P (t : itree E R) P' :
  fun_typing P t P' ->
  typing P t.
Proof.
  intros. rewrite <- bind_ret_r'. apply H. intros. apply type_ret.
Qed.

Program Definition eq_p {T} (y x : T) :=
  {|
    in_Perms := fun _ => x = y;
  |}.

Lemma fun_typing_load ptr P : fun_typing
                                (read_Perms ptr P)
                                (trigger (Load (Ptr ptr)))
                                (fun x => (read_Perms ptr (fun y => eq_p x y)) ** P x).
Proof.
  repeat intro. pstep. constructor. intros.
  destruct H0 as (? & (v & ?) & ?); subst.
  destruct H3 as (pr & p' & (? & ? & ?)).

  simpl in *. rewrite bind_trigger' in H2.
  inversion H2; auto_inj_pair2; subst; clear H2.
  - eapply read_perm_read_succeed in H10; eauto. subst.
    2: { eapply dom_inc; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm. }
    split; intuition. exists (pr * p'). split; [| split].
    + left. apply H; auto. simpl. do 2 eexists. split; [| split]; eauto. 2: reflexivity.
      simpl. eexists; split; eauto. simpl. do 2 eexists. split; [ | split]; eauto.
      rewrite sep_conj_perm_bottom. reflexivity.
    + apply sep_step_lte'. auto.
    + eapply dom_inc; eauto.
  - exfalso. eapply read_perm_read_fail; [| eauto | eauto].
    etransitivity. apply H0. etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma fun_typing_store ptr val P P' : fun_typing
                                        (write_Perms ptr P ** P' val)
                                        (trigger (Store (Ptr ptr) val))
                                        (fun _ => write_Perms ptr P').
Proof.
  repeat intro. pstep. constructor. intros.
  destruct H0 as (? & p' & (? & (v & ?) & ?) & ? & ?). subst.
  destruct H3 as (pw & ? & ? & ? & ?). simpl in *.
  rewrite bind_trigger' in H2.
  inversion H2; auto_inj_pair2; subst; clear H2.
  - split. {
      apply (upd_inc (write_perm ptr v)).
      - etransitivity; eauto. etransitivity; eauto.
        etransitivity. 2: apply lte_l_sep_conj_perm.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      - split; [eapply write_success_other_ptr |
                split; [eapply write_success_allocation | eapply write_success_others]]; eauto.
    }
    exists (write_perm ptr val * p'). split; [| split].
    + left. apply H. simpl. eexists. split; eauto.
      simpl. exists (write_perm ptr val), p'. split; [| split]; eauto; intuition.
    + repeat intro. symmetry in H2. eapply separate_antimonotone in H2; eauto.
      eapply separate_antimonotone in H2.
      2: { apply sep_conj_perm_monotone. 2: reflexivity.
           etransitivity. 2: eauto. etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
      constructor; apply H2.
    + assert (write_perm ptr val ⊥ p'). {
        eapply dom_inc in H1; eauto. destruct H1 as (_ & _ & ?).
        symmetry in H1. eapply separate_antimonotone in H1; eauto.
        eapply separate_antimonotone in H1; eauto. 2: apply lte_l_sep_conj_perm.
        eapply separate_antimonotone in H1; eauto. constructor; apply H1.
      }
      split; [| split]; auto.
      * eapply write_read; eauto.
      * respects. 2: { eapply dom_inc. apply lte_r_sep_conj_perm. eapply dom_inc; eauto. }
        apply H2. simpl.
        split; [eapply write_success_other_ptr |
                split; [eapply write_success_allocation | eapply write_success_others]]; eauto.
  - exfalso. eapply write_perm_write_fail. 2, 3: eauto. etransitivity; eauto.
    etransitivity. apply lte_l_sep_conj_perm. etransitivity; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma in_Perms_lte p P Q : p ∈ P -> Q ⊑ P -> p ∈ Q.
Proof.
  intros. eapply Perms_upwards_closed; eauto; intuition.
Qed.

Lemma fun_typing_frame {R} P (t : itree E R) P' Q :
  fun_typing P t P' ->
  fun_typing (P ** Q) t (fun x => P' x ** Q).
Proof.
  repeat intro. red in H0. red in H.

  generalize dependent P.
  generalize dependent P'.
  generalize dependent Q.
  generalize dependent p.
  pcofix CIH. intros. simpl in H1. simpl.
  setoid_rewrite unfold_bind' in H1.
  rewrite unfold_bind'.
  simpl in CIH. rewrite unfold_bind' in CIH.

  destruct (observe t) eqn:?; simpl; simpl in H1.
  - assert (exists p', p' ∈ P' r0) by admit. destruct H.
    destruct H2 as (? & ? & ? & ? & ?).
    assert (sep_step x0 x) by admit.
    assert (x * x1 ∈ P' r0 ** Q). apply sep_conj_Perms_perm; auto.

    specialize (H0 _ _ H6). pinversion H0; eauto.

      pstep. constructor. intros. split. admit.
    exists (x * x1). split; [| split].
    + admit. admit.
    + repeat intro. admit.
    + simpl.
      (* split; [admit |]. eexists. split; [| split]. *)
    (* + right. simpl in CIH. apply CIH. *)

    (* eapply paco2_mon_bot; eauto. apply H1; eauto. *)
    (* 2: { destruct H2 as (? & ? & ? & ? & ?). eapply Perms_upwards_closed; eauto. *)
    (*      etransitivity; eauto. apply lte_l_sep_conj_perm. } *)
    (* repeat intro. apply H0. simpl. do 2 eexists. split; [| split]; eauto. *)

  (* eapply Perms_upwards_closed; eauto. *)
    admit.
  - eapply paco2_mon_bot; eauto. apply H1. 2: {
      eapply in_Perms_lte; eauto. apply lte_l_sep_conj_Perms.
    }
    repeat intro. apply H0.

    simpl in CIH. pstep. constructor. intros. inversion H3; subst.
    split; intuition.
Qed.

Lemma typing_perm_load p ptr :
  typing_perm p (trigger (Load (Ptr ptr))).
Proof.
  pcofix CIH. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst.
  - split; intuition.
    eexists. split; [| split]; eauto; intuition.
    left. eapply paco2_mon_bot; eauto. apply typing_perm_ret.
  -
Abort.

Lemma typing_load ptr P :
  typing P (trigger (Load (Ptr ptr))).
Proof.
  repeat intro. (* apply typing_perm_load. *)
Abort.

(* Load an addr from ptr, and store val into it *)
Definition load_store ptr val : itree E _ :=
  vis (Load (Ptr ptr)) (fun ptr' => vis (Store ptr' val) (fun _ => Ret tt)).

Lemma typing_perm_store ptr v1 v2 :
  typing_perm (write_perm ptr v1) (vis (Store (Ptr ptr) v2) (fun _ => Ret tt)).
Proof.
  pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. split.
  - split; [| split]; intros; simpl.
    + eapply write_success_other_ptr; eauto.
    + eapply write_success_allocation; eauto.
    + admit.
  - exists (write_perm ptr v2); split; [| split].
    + left. apply typing_perm_ret.
    + repeat intro. destruct H1. constructor; auto.
    + simpl. eapply write_success_ptr; eauto.
  - simpl in H. admit.
Admitted.

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
