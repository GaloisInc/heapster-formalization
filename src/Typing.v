From Heapster Require Import
     Permissions
     Config
     PropT.

From Coq Require Import
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
     Events.State
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.
Import ITree.Basics.Basics.Monads.

Global Instance EqM_Prop : EqM Ensembles.Ensemble := Ensembles.Same_set.

Global Instance Functor_Prop : Functor.Functor Ensembles.Ensemble :=
  {| fmap := fun _ _ f Pa b => exists a, Pa a /\ f a = b |}.

Global Instance Monad_Prop : Monad Ensembles.Ensemble :=
  {|
  ret := fun _ x y => x = y;
  bind := fun _ _ Pa K b => exists a, In _ Pa a /\ In _ (K a) b
  |}.

Lemma bind_ret_l_Prop : forall A B (f : A -> Ensembles.Ensemble B) a,
    eqm (bind (ret a) f) (f a).
Proof.
  split; repeat intro; simpl in *.
  - destruct H as (? & ? & ?). red in H. subst; auto.
  - eexists; split; eauto. reflexivity.
Qed.

Lemma bind_ret_r_Prop : forall (A : Type) (Pa : Ensembles.Ensemble A),
    eqm (bind Pa (fun a => ret a)) Pa.
Proof.
  split. repeat intro; simpl in *.
  - destruct H as (? & ? & ?). red in H0; subst; auto.
  - red. repeat intro. eexists; split; eauto. reflexivity.
Qed.

Lemma bind_bind_Prop :
  forall A B C (Pa : Ensembles.Ensemble A)
    (f : A -> Ensembles.Ensemble B) (g : B -> Ensembles.Ensemble C),
    eqm (bind (bind Pa f) g) (bind Pa (fun y => bind (f y) g)).
Proof.
  intros. split; repeat intro; simpl in *;
            [destruct H as (? & (? & ? & ?) & ?) | destruct H as (? & ? & (? & ? & ?))];
            do 2 (eexists; split; eauto).
Qed.

Definition PropM (T : Type) (R : Type) := Ensembles.Ensemble (T * R).
Global Instance EqM_PropM T : EqM (PropM T) := fun _ => Ensembles.Same_set _.

Global Instance Functor_PropM T : Functor.Functor (PropM T) :=
  {|
  fmap := fun A B (f : A -> B) (Pa : PropM T A) (pb : T * B) =>
            exists (pa : T * A), Pa pa /\ (fst pa, f (snd pa)) = pb
  |}.

Global Instance Monad_PropM T : Monad (PropM T) :=
  {|
  ret := fun A a pa => a = snd pa;
  bind := fun A B (Pa : PropM T A) (K : A -> PropM T B) (pb : T * B) =>
            exists (a : A), In _ Pa (fst pb, a) /\ In _ (K a) pb
  |}.

Lemma bind_ret_l_PropM : forall T A B (f : A -> PropM T B) a,
    eqm (bind (ret a) f) (f a).
Proof.
  split; repeat intro; simpl in *.
  - destruct H as (? & ? & ?). red in H. subst. auto.
  - exists a; split; [split |]; auto.
Qed.

Lemma bind_ret_r_PropM : forall T (A : Type) (Pa : PropM T A),
    eqm (bind Pa (fun a => ret a)) Pa.
Proof.
  split; repeat intro; simpl in *.
  - destruct H as (? & ? & ?). red in H0. destruct x; subst; auto.
  - exists (snd x); split; auto; destruct x; red; auto.
Qed.

Lemma bind_bind_PropM :
  forall T A B C (Pa : PropM T A)
    (f : A -> PropM T B) (g : B -> PropM T C),
    eqm (bind (bind Pa f) g) (bind Pa (fun y => bind (f y) g)).
Proof.
  intros. split; repeat intro; simpl in *;
            [destruct H as (? & (? & ? & ?) & ?) | destruct H as (? & ? & (? & ? & ?))];
            do 2 (eexists; split; eauto).
Qed.

Section ts.

  Definition E := (stateE config +' nondetE).

  (* Context {R : Type}. *)
  Definition R := nat.

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

  CoInductive iter_PropM_perm {R I : Type} (step : I -> PropM perm (I + R)) (i : I) (pr : perm * R)
    : Prop :=
  | iter_done
    : step i (fst pr, (inr (snd pr))) -> iter_PropM_perm step i pr
  | iter_step i'
    : let p := fst pr in
      let r := snd pr in
      step i (p, (inl i')) ->
      (exists p', sep_step p p' /\
             iter_PropM_perm step i' (p', r)) ->
      iter_PropM_perm step i pr
  .
  Global Instance MonadIter_PropM : MonadIter (PropM perm) := @iter_PropM_perm.

  Definition h_nondet : nondetE ~> stateT config (PropM perm) :=
    fun R e c =>
      fun (pcr : perm * (config * R)) =>
        let p := fst pcr in
        let c' := fst (snd pcr) in
        let r := snd (snd pcr) in
        dom p c ->
        c = c' /\
        match e in (nondetE bool) return bool -> Prop with
        | Or => fun r => r = true \/ r = false
        end r.

  Definition h_state : stateE config ~> stateT config (PropM perm) :=
    fun R e c =>
      fun (pcr : perm * (config * R)) =>
        let p := fst pcr in
        let c' := fst (snd pcr) in
        let r := snd (snd pcr) in
        dom p c ->
        match e in (stateE _ X) return X -> Prop with
        | Get _ => fun r => c' = c /\ r = c
        | Put _ c'' => fun r =>
                        upd p c c' /\ (* true for all other cases since c = c' there *)
                        c' = c'' /\
                        r = tt
        end r.


  Lemma h_nondet_lte R e c p q r :
    p <= q -> h_nondet R e c (p, r) -> h_nondet R e c (q, r).
  Proof.
    intros. destruct e; repeat intro; simpl in *.
    apply H0; auto. apply H; auto.
  Qed.
  Lemma h_state_lte R e c p q r :
    p <= q -> h_state R e c (p, r) -> h_state R e c (q, r).
  Proof.
    intros. destruct e; repeat intro; simpl in *.
    - apply H0; auto. apply H; auto.
    - destruct H0 as (? & ? & ?).
      + apply H; auto.
      + split; auto. apply H; auto.
  Qed.

  Definition handler : E ~> stateT config (PropM perm) := case_ h_state h_nondet.

  Definition test1 := par (Ret 0) (Ret 1).
  Definition test2 : itree E R := Ret 1.
  Definition test_interp := interp handler test2.

  Definition empty_config := Build_config nil.
  Eval cbv in test_interp empty_config.

  Goal forall p c (n : R), interp handler (Ret n) c (p, (c, n)).
  Proof.
    intros. repeat red. constructor. repeat red. cbn. eexists. split; auto.
  Qed.

  Goal forall p q (t : itree E R) c n,
      interp handler t c (p, (c, n)) -> p <= q -> interp handler t c (q, (c, n)).
  Proof.
    intros. repeat red in H. destruct H; auto.
    - constructor 1. simpl in *. decompose [ex and] H; clear H.
      exists x; split; auto. destruct x. repeat red. repeat red in H3; simpl in *.
      destruct s; inversion H3. subst.
      unfold observe in H2. destruct (_observe t0); simpl; auto.
      red in H2. decompose [ex and] H2; clear H2. inversion H4.
    - simpl in p0, r. replace p0 with p in H, H1; auto. clear p0.
      replace r with (c, n) in H1; auto. clear r.
      econstructor 2.
      + repeat red. clear H1. repeat red in H. decompose [ex and] H; clear H.
        exists x. destruct x. split; auto.
        * clear H3. simpl in *. destruct (observe t0); simpl in *; auto. repeat red in H2 |- *.
          decompose [ex and] H2; clear H2. destruct x as (? & ? & ?).
          inversion H3; clear H3; subst.
          exists (q, (c0, x)). split; auto.
          destruct e; [eapply h_state_lte | eapply h_nondet_lte]; eauto.
        * clear H2. repeat red in H3 |- *; simpl in *. destruct s; inversion H3.
          f_equal.
      + decompose [ex and] H1; clear H1. exists x. split; auto. eapply sep_step_lte; eauto.
  Qed.

  Goal forall p c n,
      interp handler (ITree.spin : itree E R) c (p, (c, n)).
  Proof.
    repeat red. cofix CIH.
    econstructor 2.
    - repeat red. eexists; split; repeat red; simpl.
      + rewrite rewrite_spin. simpl. auto.
      + simpl. auto.
    - exists p. split; simpl; intuition.
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

  Lemma typing_perm_lte : forall p q t, typing_perm p t -> p <= q -> typing_perm q t.
  Proof.
    intros. pcofix CIH. pstep. constructor; intros.
    pinversion H. edestruct H3; eauto. split; eauto.
    destruct H5 as [p' [? [? ?]]]. exists p'. split; [| split]; auto.
    - pclearbot. left. eapply paco2_mon_bot; eauto.
    - eapply sep_step_lte; eauto.
  Qed.

  Lemma typing_perm_spin : forall p, typing_perm p ITree.spin.
  Proof.
    pcofix CIH. pstep. constructor. intros. rewrite rewrite_spin in H0.
    inversion H0; subst; split; try reflexivity.
    exists p. split; eauto; intuition.
  Qed.

  Definition typing P t := forall p, p ∈ P -> typing_perm p t.

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

Definition test : itree (stateE config +' _) unit :=
  par
    (x <- (trigger (Get _)) ;; (trigger (Put _ x)))
    (par (vis (Get _) (fun x => Ret tt))
         (Ret tt)).

(* Compute (burn 10 test). *)

(* Eval cbv in (burn 10 (step (trigger (Put _ 0)) 1)). *)
(* Eval cbn in (burn 10 (step test 1)). *)
(* Eval cbn in (burn 10 (run_state test 1)). *)
