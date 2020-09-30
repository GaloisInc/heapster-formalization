From Heapster Require Import
     Permissions
     Config
     Step.

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

(* Lemma bind_ret_r' {E R} (t : itree E R) : *)
(*   x <- t;; Ret x = t. *)
(* Proof. *)
(*   apply bisimulation_is_eq. apply bind_ret_r. *)
(* Qed. *)

(* Lemma bind_ret_l' {E R1 R2} (r : R1) (k : R1 -> itree E R2) : *)
(*   x <- Ret r;; k x = k r. *)
(* Proof. *)
(*   apply bisimulation_is_eq. apply bind_ret_l. *)
(* Qed. *)

(* Lemma bind_tau' {E R1 R2} (t : itree E R1) (k : R1 -> itree E R2) : *)
(*   x <- Tau t;; k x = Tau (x <- t;; k x). *)
(* Proof. *)
(*   apply bisimulation_is_eq. apply bind_tau. *)
(* Qed. *)

(* Lemma bind_vis' {E R1 R2 R3} (e : E R1) (k1 : R1 -> itree E R2) (k2 : R2 -> itree E R3) : *)
(*   x <- Vis e k1;; k2 x = Vis e (fun x => x' <- k1 x;; k2 x'). *)
(* Proof. *)
(*   apply bisimulation_is_eq. apply bind_vis. *)
(* Qed. *)

(* Lemma bind_bind' {E R1 R2 R3} (t : itree E R1) (k1 : R1 -> itree E R2) (k2 : R2 -> itree E R3) : *)
(*   x <- (x <- t;; k1 x);; k2 x = x1 <- t;; x2 <- k1 x1;; k2 x2. *)
(* Proof. *)
(*   apply bisimulation_is_eq. apply bind_bind. *)
(* Qed. *)

(* Lemma bind_trigger' {E E' R} `{E' -< E} X (e : E' X) k : *)
(*   x <- trigger e ;; k x = (vis e (fun x => k x) : itree E R). *)
(* Proof. *)
(*   apply bisimulation_is_eq. apply bind_trigger. *)
(* Qed. *)

(* Lemma unfold_bind' {E R S} (t : itree E R) (k : R -> itree E S) : *)
(*   x <- t;; k x = ITree._bind k (fun t0 : itree E R => x <- t0;; k x) (observe t). *)
(* Proof. *)
(*   apply bisimulation_is_eq. apply unfold_bind. *)
(* Qed. *)

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
  (* Variant MemoryE : Type -> Type := *)
  (* | Load : forall (p : SByte), MemoryE SByte *)
  (* | Store : forall (p v : SByte) , MemoryE unit *)
  (* . *)

  Context {R : Type}.

  Definition par_match {R1 R2}
             (par : itree E R1 -> itree E R2 -> itree E (R1 * R2))
             (t1 : itree E R1)
             (t2 : itree E R2)
    : itree E (R1 * R2) :=
    vis Or (fun b : bool =>
              if b then
                match (observe t1) with
                | RetF r1 => fmap (fun r2 => (r1, r2)) t2
                | TauF t => Tau (par t t2)
                | VisF o k => vis o (fun x => par (k x) t2)
                end
              else
                match (observe t2) with
                | RetF r2 => fmap (fun r1 => (r1, r2)) t1
                | TauF t => Tau (par t1 t)
                | VisF o k => vis o (fun x => par t1 (k x))
                end).

  CoFixpoint par {R1 R2} (t1 : itree E R1) (t2 : itree E R2) := par_match par t1 t2.

  Lemma rewrite_par : forall {R1 R2} (t1 : itree E R1) (t2 : itree E R2),
      par t1 t2 = par_match par t1 t2.
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

  (* Variant typing_perm_gen typing (p : perm) (q : R -> perm) : itree E R -> Prop := *)
  (* | cond : forall t, (exists c t' c', step t c t' c') /\ (* we can step *) *)
  (*               (forall c, dom p c -> (* and everything we can step to... *) *)
  (*                     forall t' c', *)
  (*                       step t c t' c' -> *)
  (*                       ( *)
  (*                         (* we step to configs that satisfy the perm *) *)
  (*                         (upd p c c') /\ *)
  (*                         (* we step to machines that are well-typed by some other perm that maintains separation *) *)
  (*                         (exists p', typing p' q t' /\ sep_step p p' /\ dom p' c'))) -> *)
  (*               typing_perm_gen typing p q t *)
  (* | ret : forall r, q r <= p -> typing_perm_gen typing p q (Ret r). *)

  Variant typing_gen typing (P : Perms) (Q : R -> Perms) : itree E R -> Prop :=
  | cond : forall t, (exists c t' c', step t c t' c') /\ (* we can step *)
                (forall p c, p ∈ P ->
                        dom p c ->
                        forall t' c',
                          step t c t' c' -> (* and everything we can step to... *)
                          (
                            (* we step to configs that satisfy the perm *)
                            (upd p c c') /\
                            (* we step to machines that are well-typed by some other perm that maintains separation *)
                            (exists P', typing P' Q t' /\ exists p', p' ∈ P' /\ sep_step p p' /\ dom p' c'))) ->
                typing_gen typing P Q t
  | ret : forall r, Q r ⊑ P -> typing_gen typing P Q (Ret r).

  (* Definition typing_perm := paco3 typing_perm_gen bot3. *)
  Definition typing := paco3 typing_gen bot3.

  Lemma typing_gen_mon : monotone3 typing_gen.
  Proof.
    repeat intro.
    inversion IN; subst.
    - econstructor. destruct H. split; auto.
      intros. edestruct H0; eauto. split; eauto.
      destruct H5 as (? & ? & (? & ? & ? & ?)). eexists. split; eauto.
    - constructor 2; auto.
  Qed.
  Hint Resolve typing_gen_mon : paco.

  Lemma typing_lte : forall P P' Q Q' t, typing P Q t ->
                                    P ⊑ P' ->
                                    (forall r, Q' r ⊑ Q r) ->
                                    typing P' Q' t.
  Proof.
    pcofix CIH. intros. pstep. pinversion H0; subst.
    - constructor 1. destruct H. split; auto. intros.
      edestruct H3; eauto. split; auto.
      destruct H8 as (? & ? & (? & ? & ? & ?)). pclearbot.
      eexists; split.
      + right. eapply CIH; eauto. reflexivity.
      + eexists. split; [| split]; eauto.
    - constructor 2. etransitivity; eauto. etransitivity; eauto.
  Qed.

  Lemma typing_ret : forall P Q r, Q r ⊑ P -> typing P Q (Ret r).
  Proof.
    intros. pstep. constructor 2. auto.
  Qed.

  Lemma typing_spin : forall P Q, typing P Q ITree.spin.
  Proof.
    pcofix CIH. intros. pstep. constructor 1. split.
    - exists start_config. eexists. exists start_config. rewrite rewrite_spin. constructor.
    - intros. rewrite rewrite_spin in H1. inversion H1; subst; split; intuition.
      exists P. split.
      + right. auto.
      + exists p; split; [| split]; intuition.
  Qed.

  Lemma typing_top : forall P Q t, typing P Q t -> typing top_Perms Q t.
  Proof.
    intros. pstep. pinversion H; subst.
    - constructor 1. destruct H0. split; auto. intros. inversion H2.
    - constructor 2; auto. apply top_Perms_is_top.
  Qed.
  Lemma typing_top_step : forall Q t, (exists c t' c', step t c t' c') -> typing top_Perms Q t.
  Proof.
    intros. pstep. constructor. split; auto. inversion 1.
  Qed.

  Lemma typing_bottom : forall P Q t, typing P Q t -> typing P (fun _ => bottom_Perms) t.
  Proof.
    pcofix CIH. intros. pstep. pinversion H0; subst.
    - destruct H. constructor 1. split; auto. intros.
      edestruct H1; eauto. split; auto. destruct H6 as (? & ? & (? & ? & ? & ?)).
      pclearbot. eexists. split; eauto.
    - constructor 2. apply bottom_Perms_is_bottom.
  Qed.

  (* converse not true, e.g. bottom can type Tau t since Tau t steps to t, but
     bottom cannot type t if t doesn't step. *)
  Lemma typing_tau : forall P Q t, typing P Q t -> typing P Q (Tau t).
    intros. pstep. pinversion H; subst.
    - constructor 1. destruct H0 as ((? & ? & ? & ?) & ?). split.
      + exists start_config. eexists. exists start_config. constructor.
      + intros. inversion H4; subst.
        split; intuition.
        exists P. split; auto. exists p. split; [| split]; intuition.
    - constructor 1. split.
      + exists start_config. eexists. exists start_config. constructor.
      + intros. inversion H3; subst.
        split; intuition.
        exists P. split; auto. exists p. split; [| split]; intuition.
  Qed.

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

  Lemma typing_multistep : forall P Q t,
      typing P Q t ->
      forall p c, p ∈ P ->
             dom p c ->
             forall t' c',
               multistep t c t' c' ->
               exists P', typing P' Q t' /\ exists p', p' ∈ P' /\ sep_step p p' /\ dom p' c'.
  Proof.
    intros. induction H2.
    - eexists; split; eauto. eexists; split; [| split]; eauto; reflexivity.
    - destruct IHmultistep as (P' & ? & p' & ? & ? & ?); eauto. pinversion H4; subst.
      + destruct H8 as (_ & ?). edestruct H8 as (? & P'' & ? & p'' & ? & ? & ?); eauto. pclearbot.
        exists P''; split; eauto. exists p''; split; [| split]; eauto. etransitivity; eauto.
      + inversion H3.
  Qed.

  Lemma typing_soundness_step : forall P Q t,
      typing P Q t ->
      forall p c, p ∈ (P ** singleton_Perms no_error_perm) ->
             dom p c ->
             forall t' c', step t c t' c' -> no_error c'.
  Proof.
    intros. rename p into p'. destruct H0 as (p & no_error & ? & ? & ?).
    apply H4 in H1. destruct H1 as (? & ? & ?).
    pinversion H; subst.
    - destruct H7. specialize (H8 _ _ H0 H1 _ _ H2) as (? & _).
      apply H3. respects. apply H6. auto.
    - inversion H2.
  Qed.

  Lemma typing_soundness : forall P Q (t : itree E R),
      (* (exists q, q ∈ Q) /\ (* change to something involving top_Perms? *) *)
      typing P Q t ->
      forall p c, p ∈ (P ** singleton_Perms no_error_perm) ->
             dom p c ->
             forall t' c', multistep t c t' c' -> no_error c'.
  Proof.
    intros P Q t Htyping p0 c (p & no_err & Hp & Hno_err & Hlte) Hdom t' c' Hmultistep.
    induction Hmultistep.
    - apply Hno_err. apply Hlte. auto.
    - pose proof Hdom as H'. rename H into Hstep.
      apply Hlte in H'. destruct H' as (Hdomp & Hdomno_err & Hsep).
      destruct (typing_multistep _ _ _ Htyping _ _ Hp Hdomp _ _ Hmultistep) as (P' & Htyping' & p' & Hp' & Hsep_step & Hdomp').
      eapply (typing_soundness_step _ _ _ Htyping').
      3: apply Hstep. (* apply H10 in H7. simpl. *)
      exists p', no_error_perm. split; [| split]; simpl; auto; reflexivity.
      split; [| split]; auto.
      2: { apply Hsep_step in Hsep. eapply separate_antimonotone; eauto. }
      apply IHHmultistep; eauto.
  Qed.

(*   Inductive Returns (r : R) : itree E R -> Prop := *)
(*   | ReturnsRet: Returns r (Ret r) *)
(*   | ReturnsTau: forall t, Returns r t -> Returns r (Tau t) *)
(*   | ReturnsVis: forall {X} (e : E X) (x : X) k, Returns r (k x) -> Returns r (Vis e k) *)
(*   . *)

(*   (* Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop := *) *)
(*   (* | ReturnsRet: forall t, t ≈ Ret a -> Returns a t *) *)
(*   (* | ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t *) *)
(*   (* | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t *) *)
(*   (* . *) *)

End ts.

Hint Resolve typing_gen_mon : paco.

Lemma typing_bind {R1 R2} : forall P Q R (t : itree E R1) (k : R1 -> itree E R2),
    typing P Q t ->
    (forall r1, typing (Q r1) R (k r1)) ->
    typing P R (x <- t;; k x).
Proof.
  pcofix CIH. intros. pinversion H0; subst.
  - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor. split; auto.
    do 3 eexists. apply step_bind; eauto.
    intros. inversion H5; subst.
    + pose proof @eqitree_inv_bind_tau.
      edestruct H6 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H7; reflexivity | |];
        apply bisimulation_is_eq in H8; apply bisimulation_is_eq in H9; subst;
          [| inversion H].
      destruct (H2 _ _ H3 H4 _ _ (step_tau _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H6 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H7; reflexivity | |];
        apply bisimulation_is_eq in H8; subst; [| inversion H].
      rewritebisim_in @bind_vis H7. inversion H7; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_nondet_true _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H6 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H7; reflexivity | |];
        apply bisimulation_is_eq in H8; subst; [| inversion H].
      rewritebisim_in @bind_vis H7. inversion H7; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_nondet_false _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H8 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
        apply bisimulation_is_eq in H9; subst; [| inversion H].
      rewritebisim_in @bind_vis H6. inversion H6; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_load _ _ _ _ H7)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H8 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
        apply bisimulation_is_eq in H9; subst; [| inversion H].
      rewritebisim_in @bind_vis H6. inversion H6; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_store _ _ _ _ _ H7)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H8 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
        apply bisimulation_is_eq in H9; subst; [| inversion H].
      rewritebisim_in @bind_vis H6. inversion H6; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_load_fail _ _ _ H7)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H8 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
        apply bisimulation_is_eq in H9; subst; [| inversion H].
      rewritebisim_in @bind_vis H6. inversion H6; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_store_fail _ _ _ _ H7)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H6 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H7; reflexivity | |];
        apply bisimulation_is_eq in H8; subst; [| inversion H].
      rewritebisim_in @bind_vis H5. inversion H5; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_load_invalid _ _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
    + pose proof @eqitree_inv_bind_vis.
      edestruct H6 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H7; reflexivity | |];
        apply bisimulation_is_eq in H8; subst; [| inversion H].
      rewritebisim_in @bind_vis H5. inversion H5; auto_inj_pair2; subst.
      destruct (H2 _ _ H3 H4 _ _ (step_store_invalid _ _ _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
      pclearbot. split; auto. exists P'. split; eauto.
  - rewritebisim @bind_ret_l. eapply paco3_mon_bot; eauto. eapply typing_lte; eauto.
    reflexivity.
Qed.

(* Lemma return_map1 {R1 R2} : forall (t1 : itree E R1) (r1 : R1) (r2 r2' : R2), *)
(*     Returns (r1, r2) (ITree.map (fun r1 : R1 => (r1, r2')) t1) -> *)
(*     Returns r1 t1 /\ r2 = r2'. *)
(* Proof. *)
(*   intros. remember (r1, r2). remember (ITree.map _ _). *)
(*   generalize dependent t1. unfold ITree.map. *)
(*   induction H; intros; subst. *)
(*   - edestruct @eqitree_inv_bind_ret as (? & ? & ?); [rewrite Heqi; reflexivity |]. *)
(*     apply bisimulation_is_eq in H0. inversion H0. *)
(*     rewritebisim H. subst. *)
(*     split; [constructor |]; auto. *)
(*   - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)]; *)
(*       [rewrite Heqi; reflexivity | |]. *)
(*     + rewritebisim H0. apply bisimulation_is_eq in H1. *)
(*       split; [constructor |]; eapply IHReturns; eauto. *)
(*     + apply bisimulation_is_eq in H1. inversion H1. *)
(*   - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)]; *)
(*       [rewrite Heqi; reflexivity | |]. *)
(*     + rewritebisim H0. split; [econstructor; eapply IHReturns; eauto; rewritebisim H1; eauto |]. *)
(*       specialize (H1 x). apply bisimulation_is_eq in H1. eapply IHReturns; eauto. *)
(*     + apply bisimulation_is_eq in H1. inversion H1. *)
(* Qed. *)

(* Lemma return_map2 {R1 R2} : forall (t2 : itree E R2) (r1 r1' : R1) (r2 : R2), *)
(*     Returns (r1, r2) (ITree.map (fun r2 : R2 => (r1', r2)) t2) -> *)
(*     Returns r2 t2 /\ r1 = r1'. *)
(* Proof. *)
(*   intros. remember (r1, r2). remember (ITree.map _ _). *)
(*   generalize dependent t2. unfold ITree.map. *)
(*   induction H; intros; subst. *)
(*   - edestruct @eqitree_inv_bind_ret as (? & ? & ?); [rewrite Heqi; reflexivity |]. *)
(*     apply bisimulation_is_eq in H0. inversion H0. *)
(*     rewritebisim H. subst. *)
(*     split; [constructor |]; auto. *)
(*   - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)]; *)
(*       [rewrite Heqi; reflexivity | |]. *)
(*     + rewritebisim H0. apply bisimulation_is_eq in H1. *)
(*       split; [constructor |]; eapply IHReturns; eauto. *)
(*     + apply bisimulation_is_eq in H1. inversion H1. *)
(*   - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)]; *)
(*       [rewrite Heqi; reflexivity | |]. *)
(*     + rewritebisim H0. split; [econstructor; eapply IHReturns; eauto; rewritebisim H1; eauto |]. *)
(*       specialize (H1 x). apply bisimulation_is_eq in H1. eapply IHReturns; eauto. *)
(*     + apply bisimulation_is_eq in H1. inversion H1. *)
(* Qed. *)

(* Lemma return_par_helper {R1 R2} (t1 : itree E R1) (t2 : itree E R2) r1 r2 t : *)
(*   Returns (r1, r2) t -> *)
(*   (t = (par t1 t2) \/ *)
(*    t = Tau (par t1 t2) \/ *)
(*    (exists X (e : E X) k, t1 = Vis e k /\ t = Vis (subevent X e) (fun x => par (k x) t2)) \/ *)
(*    (exists X (e : E X) k, t2 = Vis e k /\ t = Vis (subevent X e) (fun x => par t1 (k x)))) -> *)
(*   Returns r1 t1 /\ Returns r2 t2. *)
(* Proof. *)
(*   intros. *)
(*   revert H0. generalize dependent t1. generalize dependent t2. *)
(*   induction H; intros. *)
(*   - destruct H0 as [? | [? | [? | ?]]]. *)
(*     + rewrite rewrite_par in H. unfold par_match in H. inversion H. *)
(*     + inversion H. *)
(*     + destruct H as (? & ? & ? & ? & ?). inversion H0. *)
(*     + destruct H as (? & ? & ? & ? & ?). inversion H0. *)
(*   - destruct H0 as [? | [? | [? | ?]]]. *)
(*     + rewrite rewrite_par in H0. unfold par_match in H0. inversion H0. *)
(*     + inversion H0. eapply IHReturns; eauto. *)
(*     + destruct H0 as (? & ? & ? & ? & ?). inversion H1. *)
(*     + destruct H0 as (? & ? & ? & ? & ?). inversion H1. *)
(*   - destruct H0 as [? | [? | [? | ?]]]. *)
(*     + rewrite rewrite_par in H0. unfold par_match in H0. *)
(*       inversion H0; subst; auto_inj_pair2; subst; clear H0. *)
(*       destruct x. *)
(*       { *)
(*         destruct (observe t1) eqn:?. *)
(*         - apply return_map2 in H. destruct H. split; auto. *)
(*           rewrite itree_eta_. rewrite Heqi. subst. constructor. *)
(*         - rewrite (itree_eta_ t1). rewrite Heqi. split; [constructor |]; eapply IHReturns; eauto. *)
(*         - rewrite (itree_eta_ t1). rewrite Heqi. eapply IHReturns. *)
(*           right. right. left. do 3 eexists. split; reflexivity. *)
(*       } *)
(*       { *)
(*         destruct (observe t2) eqn:?. *)
(*         - apply return_map1 in H. destruct H. split; auto. *)
(*           rewrite itree_eta_. rewrite Heqi. subst. constructor. *)
(*         - rewrite (itree_eta_ t2). rewrite Heqi. split; [| constructor]; eapply IHReturns; eauto. *)
(*         - rewrite (itree_eta_ t2). rewrite Heqi. eapply IHReturns. *)
(*           right. right. right. do 3 eexists. split; reflexivity. *)
(*       } *)
(*     + inversion H0. *)
(*     + destruct H0 as (? & ? & ? & ? & ?). inversion H1; subst; auto_inj_pair2; subst; clear H1. *)
(*       split; [econstructor |]; eapply IHReturns; left; eauto. *)
(*     + destruct H0 as (? & ? & ? & ? & ?). inversion H1; subst; auto_inj_pair2; subst; clear H1. *)
(*       split; [| econstructor]; eapply IHReturns; left; eauto. *)
(* Qed. *)

(* Lemma return_par {R1 R2} (t1 : itree E R1) (t2 : itree E R2) r1 r2 : *)
(*   Returns (r1, r2) (par t1 t2) -> *)
(*   Returns r1 t1 /\ Returns r2 t2. *)
(* Proof. *)
(*   intros. eapply return_par_helper; eauto. *)
(* Qed. *)


(* TODO Generalize these lemmas *)
Lemma fmap_fst {R1 R2 : Type} (t' : itree E R1) (t : itree E (R1 * R2)) (r2 : R2) :
  t = fmap (fun x => (x, r2)) t' ->
  t = fmap (fun x => (x, r2)) (fmap fst t).
Proof.
  intros. apply bisimulation_is_eq. generalize dependent H. revert t' t r2.
  pcofix CIH. intros.
  pstep. unfold eqit_. simpl in *. unfold ITree.map in H0.
  destruct (observe t0) eqn:?.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    rewritebisim @map_map.
    rewritebisim @map_ret.
    constructor.
    edestruct @eqitree_inv_bind_ret as (? & ? & ?);
      [rewrite H in H0; rewrite H0; reflexivity |].
    destruct r0 as [r1 r2']. apply bisimulation_is_eq in H2. inversion H2. reflexivity.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    do 2 rewritebisim @map_tau.
    edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. right. eapply CIH; eauto. apply bisimulation_is_eq. symmetry. apply H2.
    + apply bisimulation_is_eq in H1. subst. rewritebisim_in @bind_ret_l H. inversion H.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    unfold ITree.map. rewritebisim @bind_vis. rewritebisim @bind_vis.
    edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. intros. right. subst. eapply CIH.
      specialize (H2 v). apply bisimulation_is_eq in H2. symmetry. apply H2.
    + apply bisimulation_is_eq in H2. inversion H2.
Qed.

Lemma fmap_snd {R1 R2 : Type} (t' : itree E R2) (t : itree E (R1 * R2)) (r1 : R1) :
  t = fmap (fun x => (r1, x)) t' ->
  t = fmap (fun x => (r1, x)) (fmap snd t).
Proof.
  intros. apply bisimulation_is_eq. generalize dependent H. revert t' t r1.
  pcofix CIH. intros.
  pstep. unfold eqit_. simpl in *. unfold ITree.map in H0.
  destruct (observe t0) eqn:?.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    rewritebisim @map_map.
    rewritebisim @map_ret.
    constructor.
    edestruct @eqitree_inv_bind_ret as (? & ? & ?);
      [rewrite H in H0; rewrite H0; reflexivity |].
    destruct r0 as [r1' r2]. apply bisimulation_is_eq in H2. inversion H2. reflexivity.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    do 2 rewritebisim @map_tau.
    edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. right. eapply CIH; eauto. apply bisimulation_is_eq. symmetry. apply H2.
    + apply bisimulation_is_eq in H1. subst. rewritebisim_in @bind_ret_l H. inversion H.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    unfold ITree.map. rewritebisim @bind_vis. rewritebisim @bind_vis.
    edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. intros. right. subst. eapply CIH.
      specialize (H2 v). apply bisimulation_is_eq in H2. symmetry. apply H2.
    + apply bisimulation_is_eq in H2. inversion H2.
Qed.

Lemma typing_frame1 {R1 R2 : Type} : forall P Q R (r1 : R1) (t : itree E R2),
    typing P Q t ->
    typing (R r1 ** P) (fun '(r1, r2) => R r1 ** Q r2) (fmap (fun r2 => (r1, r2)) t).
Proof.
  pcofix CIH. intros. pinversion H0; subst.
  - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor.
    split. {
      simpl. do 3 eexists. eapply step_fmap; eauto.
    }
    intros. pose proof (step_fmap_fst _ _ _ _ _ H4).
    rename p into rp.
    destruct H2 as (r' & p & Hr & Hp & Hle).
    edestruct H1. eauto. apply Hle; eauto. eauto. split.
    apply Hle. constructor. auto.
    destruct H6 as (P' & ? & (p' & ? & ? & ?)). pclearbot.
    exists (R r1 ** P'). split; [| exists (r' * p'); split; [| split]]; eauto.
    + right.
      simpl in H4. unfold ITree.map in H4.
      pose proof @step_fmap_inv. simpl in H10. unfold ITree.map in H10.
      specialize (H10 _ _ _ _ _ _ _ H4). destruct H10.
      erewrite fmap_snd; eauto.
    + apply sep_conj_Perms_perm; auto.
    + eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto. symmetry.
      apply Hle in H3. apply H3.
    + apply Hle in H3. destruct H3 as (? & ? & ?).
      split; [| split]; auto.
      * eapply dom_respects; eauto. apply H11; auto.
      * symmetry. apply H8. symmetry. auto.
  - simpl. pstep. unfold ITree.map. rewritebisim @bind_ret_l.
    constructor 2. apply sep_conj_Perms_monotone; intuition.
Qed.

Lemma typing_frame2 {R1 R2 : Type} : forall P Q R (r2 : R2) (t : itree E R1),
    typing P Q t ->
    typing (P ** R r2) (fun '(r1, r2) => Q r1 ** R r2) (fmap (fun r1 => (r1, r2)) t).
Proof.
  pcofix CIH. intros. pinversion H0; subst.
  - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor.
    split. {
      simpl. do 3 eexists. eapply step_fmap; eauto.
    }
    intros. pose proof (step_fmap_snd _ _ _ _ _ H4).
    rename p into rp.
    destruct H2 as (p & r' & Hr & Hp & Hle).
    edestruct H1. eauto. apply Hle; eauto. eauto. split.
    apply Hle. constructor. auto.
    destruct H6 as (P' & ? & (p' & ? & ? & ?)). pclearbot.
    exists (P' ** R r2). split; [| exists (p' * r'); split; [| split]]; eauto.
    + right.
      simpl in H4. unfold ITree.map in H4.
      pose proof @step_fmap_inv. simpl in H10. unfold ITree.map in H10.
      specialize (H10 _ _ _ _ _ _ _ H4). destruct H10.
      erewrite fmap_fst; eauto.
    + apply sep_conj_Perms_perm; auto.
    + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
      apply Hle in H3. apply H3.
    + apply Hle in H3. destruct H3 as (? & ? & ?).
      split; [| split]; auto.
      eapply dom_respects; eauto. apply H11; auto.
  - simpl. pstep. unfold ITree.map. rewritebisim @bind_ret_l.
    constructor 2. apply sep_conj_Perms_monotone; intuition.
Qed.

Lemma parallel_perm : forall {R1 R2} P1 P2 Q1 Q2 (t1 : itree E R1) (t2 : itree E R2),
    typing P1 Q1 t1 ->
    typing P2 Q2 t2 ->
    typing (P1 ** P2) (fun '(r1, r2) => Q1 r1 ** Q2 r2) (par t1 t2).
Proof.
  intros R1 R2.
  pcofix CIH. intros P1 P2 Q1 Q2 t1 t2 Ht1 Ht2.
  pstep. econstructor.
  rewrite rewrite_par. unfold par_match. split.
  { simpl. exists start_config. eexists. exists start_config. constructor. }
  intros p c (p1 & p2 & Hp1 & Hp2 & Hp) Hdom t' c' Hstep.
  inversion Hstep; auto_inj_pair2; subst; clear Hstep; split; try reflexivity.
  { pinversion Ht1; subst.
    - destruct H as ((? & ? & ? & ?) & ?).
      inversion H; subst; clear H.
      + (* tau *) clear x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             inversion Hstep; subst. split; intuition.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
             specialize (H0 _ _ Hp1' Hdom1 _ _ (step_tau _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
             pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
             ++ apply sep_conj_Perms_perm; auto.
             ++ eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
             ++ split; [| split]; auto.
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* nondet *) clear x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_nondet_true _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_nondet_false _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* nondet again, exactly the same as prev case. *) clear x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_nondet_true _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_nondet_false _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* load *) clear H1 x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor; auto. apply read_config_mem.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_load _ _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split; intuition.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_load_fail _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto. respects. apply Hsep. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* store *) clear H1 x1 x. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor. apply write_config_mem. Unshelve. apply (Byte 0).
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_store _ _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto. respects. apply Hsep. auto.
             }
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_store_fail _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto. respects. apply Hsep. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* load *) clear H1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor. apply (Byte 0). apply read_config_mem.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_load _ _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split; intuition.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_load_fail _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto. respects. apply Hsep. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* store *) clear H1 x. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor. apply write_config_mem. Unshelve. apply (Byte 0).
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_store _ _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto. respects. apply Hsep. auto.
             }
             {
               specialize (H0 _ _ Hp1' Hdom1 _ _ (step_store_fail _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto. respects. apply Hsep. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* load *) simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. Unshelve. apply start_config.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
             inversion Hstep; subst; auto_inj_pair2; subst.
             specialize (H0 _ _ Hp1' Hdom1 _ _ (step_load_invalid _ _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
             split. apply Hp'. constructor 1. auto.
             pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
             ++ apply sep_conj_Perms_perm; auto.
             ++ eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
             ++ split; [| split]; auto. respects. apply Hsep. auto.
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* store *) simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. Unshelve. apply start_config.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep).
             inversion Hstep; subst; auto_inj_pair2; subst.
             specialize (H0 _ _ Hp1' Hdom1 _ _ (step_store_invalid _ _ _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
             split. apply Hp'. constructor 1. auto.
             pclearbot. exists (P' ** P2). split; eauto. exists (p'' * p2'). split; [| split].
             ++ apply sep_conj_Perms_perm; auto.
             ++ eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
             ++ split; [| split]; auto. respects. apply Hsep. auto.
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
    - simpl. exists (Q1 r0 ** P2). split.
      + left.
        eapply paco3_mon_bot; eauto.
        apply typing_frame1; auto.
      + apply H in Hp1. exists (p1 * p2). split; [| split]; eauto.
        * apply sep_conj_Perms_perm; auto.
        * eapply sep_step_lte; eauto; reflexivity.
  }
  { pinversion Ht2; subst.
    - destruct H as ((? & ? & ? & ?) & ?).
      inversion H; subst; clear H.
      + (* tau *) clear x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             inversion Hstep; subst. split; intuition.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
             specialize (H0 _ _ Hp2' Hdom2 _ _ (step_tau _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
             pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
             ++ apply sep_conj_Perms_perm; auto.
             ++ eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
             ++ split; [| split]; auto. symmetry. auto.
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* nondet *) clear x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_nondet_true _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. auto.
             }
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_nondet_false _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* nondet again, exactly the same as prev case. *) clear x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_nondet_true _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. auto.
             }
             {
               split; intuition.
               apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_nondet_false _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* load *) clear H1 x1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor; auto. apply read_config_mem.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_load _ _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split; intuition.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. auto.
             }
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_load_fail _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* store *) clear H1 x1 x. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor; auto. apply write_config_mem. Unshelve. apply (Byte 0).
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_store _ _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
             }
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_store_fail _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* load *) clear H1. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor. apply (Byte 0). apply read_config_mem.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_load _ _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split; intuition.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. auto.
             }
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_load_fail _ _ _ H5)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* store *) clear H1 x. simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor; auto. apply write_config_mem. Unshelve. apply (Byte 0).
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_store _ _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
             }
             {
               specialize (H0 _ _ Hp2' Hdom2 _ _ (step_store_fail _ _ _ _ H6)) as (? & (P' & ? & (p'' & ? & ? & ?))).
               split. apply Hp'. constructor 1. auto.
               pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
               - apply sep_conj_Perms_perm; auto.
               - eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
             }
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* load *) simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. Unshelve. apply start_config.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             specialize (H0 _ _ Hp2' Hdom2 _ _ (step_load_invalid _ _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
             split. apply Hp'. constructor 1. auto.
             pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
             ++ apply sep_conj_Perms_perm; auto.
             ++ eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
             ++ split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
      + (* store *) simpl.
        exists (P1 ** P2). split.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. Unshelve. apply start_config.
          -- intros p' c (p1' & p2' & Hp1' & Hp2' & Hp') Hdom' t' c'' Hstep.
             apply Hp' in Hdom'. destruct Hdom' as (Hdom1 & Hdom2 & Hsep). symmetry in Hsep.
             inversion Hstep; subst; auto_inj_pair2; subst.
             specialize (H0 _ _ Hp2' Hdom2 _ _ (step_store_invalid _ _ _ _)) as (? & (P' & ? & (p'' & ? & ? & ?))).
             split. apply Hp'. constructor 1. auto.
             pclearbot. exists (P1 ** P'). split; eauto. exists (p1' * p''). split; [| split].
             ++ apply sep_conj_Perms_perm; auto.
             ++ eapply sep_step_lte; eauto. apply sep_step_sep_conj_r; auto.
             ++ split; [| split]; auto. respects. apply Hsep. auto. symmetry. auto.
        * exists p. split; [| split]; intuition. exists p1, p2. split; [| split]; auto.
    - simpl. exists (P1 ** Q2 r0). split.
      + left.
        eapply paco3_mon_bot; eauto.
        apply typing_frame2; auto.
      + apply H in Hp2. exists (p1 * p2). split; [| split]; eauto.
        * apply sep_conj_Perms_perm; auto.
        * eapply sep_step_lte; eauto; reflexivity.
  }
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

Program Definition eq_p {T} (y x : T) :=
  {|
  in_Perms := fun _ => x = y;
  |}.

Lemma typing_load ptr (Q : SByte -> Perms) :
  typing
    (read_Perms ptr Q)
    (fun x => (read_Perms ptr (fun y => eq_p x y)) ** Q x)
    (trigger (Load (Ptr ptr))).
Proof.
  pstep. constructor 1. split.
  - do 3 eexists. constructor. apply read_config_mem. Unshelve. apply (Byte 0).
  - intros p' c (P & (v & ?) & Hp) Hdom t' c' Hstep. subst.
    destruct Hp as (p & q & Hp & Hq & Hlte). simpl in Hp.
    inversion Hstep; subst; auto_inj_pair2; subst.
    + split; intuition. assert (v = v0). {
        apply Hlte in Hdom. destruct Hdom as (Hdom & _). apply Hp in Hdom.
        rewrite Hdom in H4. inversion H4. auto.
      } subst. eexists. split.
      * left. pstep. constructor 2. reflexivity.
      * exists (p * q). split; [| split]; eauto.
        2: { eapply sep_step_lte. 2: reflexivity. auto. }
        exists p, q. split; [| split]; intuition.
        eexists. split. eexists. reflexivity. simpl. eexists. exists bottom_perm.
        split; [| split]; eauto. apply sep_conj_perm_bottom.
    + apply Hlte in Hdom. destruct Hdom as (Hdom & _). apply Hp in Hdom.
      rewrite Hdom in H4. inversion H4.
Qed.

(* Lemma fun_typing_load ptr P : fun_typing *)
(*                                 (read_Perms ptr P) *)
(*                                 (trigger (Load (Ptr ptr))) *)
(*                                 (fun x => (read_Perms ptr (fun y => eq_p x y)) ** P x). *)
(* Proof. *)
(*   repeat intro. pstep. constructor. intros. *)
(*   destruct H0 as (? & (v & ?) & ?); subst. *)
(*   destruct H3 as (pr & p' & (? & ? & ?)). *)

(*   simpl in *. rewrite bind_trigger' in H2. *)
(*   inversion H2; auto_inj_pair2; subst; clear H2. *)
(*   - eapply read_perm_read_succeed in H10; eauto. subst. *)
(*     2: { eapply dom_inc; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm. } *)
(*     split; intuition. exists (pr * p'). split; [| split]. *)
(*     + left. apply H; auto. simpl. do 2 eexists. split; [| split]; eauto. 2: reflexivity. *)
(*       simpl. eexists; split; eauto. simpl. do 2 eexists. split; [ | split]; eauto. *)
(*       rewrite sep_conj_perm_bottom. reflexivity. *)
(*     + apply sep_step_lte'. auto. *)
(*     + eapply dom_inc; eauto. *)
(*   - exfalso. eapply read_perm_read_fail; [| eauto | eauto]. *)
(*     etransitivity. apply H0. etransitivity; eauto. apply lte_l_sep_conj_perm. *)
(* Qed. *)

Lemma typing_store ptr val' P Q :
  typing
    (write_Perms ptr P ** Q val')
    (fun _ => write_Perms ptr Q)
    (trigger (Store (Ptr ptr) val')).
Proof.
  pstep. constructor 1. split.
  - do 3 eexists. constructor. apply write_config_mem. Unshelve. apply (Byte 0).
  - intros p'' c (p' & q & (? & (val & ?) & Hp') & Hq & Hlte'') Hdom t' c' Hstep. subst.
    destruct Hp' as (pw & p & Hwrite & Hp & Hlte'). simpl in Hwrite.
    inversion Hstep; subst; auto_inj_pair2; subst.
    {
      assert (upd p' c c').
      { apply Hlte'. constructor 1. left. apply Hwrite.
        split; [eapply write_success_other_ptr |
                split; [eapply write_success_allocation | eapply write_success_others]]; eauto. }
      split.
      { apply Hlte''. constructor 1. left. auto. }
      eexists. split.
      { left. pstep. constructor 2. reflexivity. }
      exists (write_perm ptr val' * q). split; [| split].
      - eexists. split; eauto.
        do 2 eexists. split; [| split; [apply Hq |]]; simpl; reflexivity.
      - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l.
        { apply Hlte'' in Hdom. apply Hdom. }
        eapply sep_step_lte; eauto. eapply sep_step_lte. apply lte_l_sep_conj_perm.
        eapply sep_step_lte; eauto.
        intros r []. constructor; auto.
      - simpl. split; [| split]; auto.
        + eapply write_read; eauto.
        + respects. 2: { apply Hlte'' in Hdom. apply Hdom. }
          apply Hlte'' in Hdom. apply Hdom. auto.
        + apply Hlte'' in Hdom. destruct Hdom as (_ & _ & Hsep). symmetry in Hsep.
          eapply separate_antimonotone in Hsep; eauto. apply separate_sep_conj_perm_l in Hsep.
          eapply separate_antimonotone in Hsep; eauto. destruct Hsep. constructor; auto.
    }
    {
      exfalso. eapply write_perm_write_fail; eauto. apply Hlte'. apply Hlte''. auto.
    }
Qed.

(* Lemma fun_typing_store ptr val P P' : fun_typing *)
(*                                         (write_Perms ptr P ** P' val) *)
(*                                         (trigger (Store (Ptr ptr) val)) *)
(*                                         (fun _ => write_Perms ptr P'). *)
(* Proof. *)
(*   repeat intro. pstep. constructor. intros. *)
(*   destruct H0 as (? & p' & (? & (v & ?) & ?) & ? & ?). subst. *)
(*   destruct H3 as (pw & ? & ? & ? & ?). simpl in *. *)
(*   rewrite bind_trigger' in H2. *)
(*   inversion H2; auto_inj_pair2; subst; clear H2. *)
(*   - split. { *)
(*       apply (upd_inc (write_perm ptr v)). *)
(*       - etransitivity; eauto. etransitivity; eauto. *)
(*         etransitivity. 2: apply lte_l_sep_conj_perm. *)
(*         etransitivity; eauto. apply lte_l_sep_conj_perm. *)
(*       - split; [eapply write_success_other_ptr | *)
(*                 split; [eapply write_success_allocation | eapply write_success_others]]; eauto. *)
(*     } *)
(*     exists (write_perm ptr val * p'). split; [| split]. *)
(*     + left. apply H. simpl. eexists. split; eauto. *)
(*       simpl. exists (write_perm ptr val), p'. split; [| split]; eauto; intuition. *)
(*     + repeat intro. symmetry in H2. eapply separate_antimonotone in H2; eauto. *)
(*       eapply separate_antimonotone in H2. *)
(*       2: { apply sep_conj_perm_monotone. 2: reflexivity. *)
(*            etransitivity. 2: eauto. etransitivity. 2: apply lte_l_sep_conj_perm. eauto. } *)
(*       constructor; apply H2. *)
(*     + assert (write_perm ptr val ⊥ p'). { *)
(*         eapply dom_inc in H1; eauto. destruct H1 as (_ & _ & ?). *)
(*         symmetry in H1. eapply separate_antimonotone in H1; eauto. *)
(*         eapply separate_antimonotone in H1; eauto. 2: apply lte_l_sep_conj_perm. *)
(*         eapply separate_antimonotone in H1; eauto. constructor; apply H1. *)
(*       } *)
(*       split; [| split]; auto. *)
(*       * eapply write_read; eauto. *)
(*       * respects. 2: { eapply dom_inc. apply lte_r_sep_conj_perm. eapply dom_inc; eauto. } *)
(*         apply H2. simpl. *)
(*         split; [eapply write_success_other_ptr | *)
(*                 split; [eapply write_success_allocation | eapply write_success_others]]; eauto. *)
(*   - exfalso. eapply write_perm_write_fail. 2, 3: eauto. etransitivity; eauto. *)
(*     etransitivity. apply lte_l_sep_conj_perm. etransitivity; eauto. *)
(*     etransitivity; eauto. apply lte_l_sep_conj_perm. *)
(* Qed. *)

(* Load an addr from ptr, and store val into it *)
Definition load_store ptr val : itree E _ :=
  ptr' <- trigger (Load (Ptr ptr)) ;;
  trigger (Store ptr' val) ;;
  Ret tt.

(* TODO move to permissions.v *)
Instance Proper_eq_Perms_eq_perm_in_Perms : Proper (eq_Perms ==> eq_perm ==> flip impl) in_Perms.
Proof.
  repeat intro; subst. apply H. eapply Perms_upwards_closed; eauto.
Qed.

(* TODO clean up *)
Instance Proper_eq_Perms_typing {R} : Proper (eq_Perms ==> (pointwise_relation _ eq_Perms) ==> eq ==> flip impl) (@typing R).
Proof.
  pcofix CIH. repeat intro. subst. pstep. pinversion H3; subst.
  - constructor 1. destruct H. split; auto. intros.
    edestruct H2; eauto. rewrite <- H0; auto. split; auto.
    destruct H8 as (? & ? & ? & ? & ? & ?). eexists. split.
    right. pclearbot. eapply CIH. 3: reflexivity. 3: apply H8.
    reflexivity. auto. eauto.
  - constructor 2; eauto. rewrite H0. rewrite H1. auto.
Qed.

Lemma typing_load_store ptr val P Q :
  typing
    (read_Perms ptr (fun ptr => match ptr with
                             | Byte _ => top_Perms
                             | Ptr ptr' => write_Perms ptr' P ** Q val
                             end))
    (fun _ => bottom_Perms)
    (load_store ptr val).
Proof.
  eapply typing_bind.
  - apply typing_load.
  - intros. destruct r1.
    + rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_top_absorb.
      eapply typing_top_step.
      rewritebisim @bind_trigger. do 3 eexists. constructor. Unshelve. apply start_config.
    + eapply typing_bind.
      2: { intros. apply typing_ret. apply bottom_Perms_is_bottom.
           Unshelve. intros. apply bottom_Perms. }
      eapply typing_lte.
      3: { intros. apply bottom_Perms_is_bottom. }
      eapply typing_store; eauto.
      apply lte_r_sep_conj_Perms.
Qed.

(* below is old stuff *)

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
