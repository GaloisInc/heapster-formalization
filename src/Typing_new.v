From Coq Require Import
     Structures.Equalities
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     Program.Equality.

From Heapster Require Import
     Permissions
     NoEvent
     SepStep.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.

Import SumNotations.
Open Scope sum_scope.

Section bisim.

  Variant modifyE C : Type -> Type :=
  | Modify : forall (f : C -> C), modifyE C C.
  Global Arguments Modify {C} f.

  Definition sceE (C : Type) := (exceptE unit +' modifyE C +' nondetE).

  Definition CompM S R := itree (sceE S) R.
  Definition CompM' S R := itree' (sceE S) R.


  (** * `no_errors` **)

  Inductive no_errors_genF {S R : Type} no_errors : CompM' S R -> S -> Prop :=
  | no_errors_gen_ret r s : no_errors_genF no_errors (RetF r) s
  | no_errors_gen_tau t s : no_errors t s -> no_errors_genF no_errors (TauF t) s
  | no_errors_gen_modify f k s :
      no_errors (k s) (f s) ->
      no_errors_genF no_errors (VisF (subevent _ (Modify f)) k) s
  | no_errors_gen_choice k s :
      (forall b, no_errors (k b) s) ->
      no_errors_genF no_errors (VisF (subevent _ Or) k) s
  .

  Definition no_errors_gen {S R} no_errors t s :=
    @no_errors_genF S R no_errors (observe t) s.
  Hint Unfold no_errors_gen : core.

  Definition no_errors {S R} : CompM S R -> S -> Prop := paco2 no_errors_gen bot2.

  Lemma no_errors_gen_mon {S R} : monotone2 (@no_errors_gen S R).
  Proof.
    repeat intro. unfold no_errors_gen in *.
    inversion IN; subst; try solve [constructor; auto].
  Qed.
  Hint Resolve no_errors_gen_mon : paco.

  Instance Proper_observing_paco2_no_errors_gen {S R} r :
    Proper (observing eq ==> eq ==> iff) (paco2 (@no_errors_gen S R) r).
  Proof.
    repeat intro; destruct H, H0.
    split; intro; punfold H0; pfold; unfold no_errors_gen in *;
      [ rewrite <- H | rewrite H ]; eauto.
  Qed.

  Instance Proper_observing_no_errors {S R} :
    Proper (observing eq ==> eq ==> iff) (@no_errors S R).
  Proof. apply Proper_observing_paco2_no_errors_gen. Qed.

  Lemma no_errors_Tau {S R} (t : CompM S R) s :
    no_errors t s <-> no_errors (Tau t) s.
  Proof.
    split; intro H.
    - pfold; cbn.
      constructor; left; eauto.
    - punfold H; cbn in H.
      inv H; pclearbot; eauto.
  Qed.

  Lemma no_errors_Modify {S R} f (k : S -> CompM S R) s :
    no_errors (k s) (f s) <-> no_errors (vis (Modify f) k) s.
  Proof.
    split; intro H.
    - pfold; cbn.
      constructor; left; eauto.
    - punfold H; cbn in H.
      inv H; pclearbot.
      auto_inj_pair2; subst; eauto.
  Qed.

  Lemma no_errors_Choice {S R} (k : bool -> CompM S R) s :
    (forall b, no_errors (k b) s) <-> no_errors (vis Or k) s.
  Proof.
    split; intro H.
    - pfold; cbn.
      constructor; left; eauto.
      apply H.
    - punfold H; cbn in H.
      inv H; pclearbot.
      auto_inj_pair2; subst; eauto.
  Qed.


  (** * `steps` and `step` **)

  (* The proposition that an itree has a next step *)

  Inductive stepsF {S R} : CompM' S R -> S -> Prop :=
  | steps_tau t s : stepsF (TauF t) s
  | steps_modify f k s : stepsF (VisF (|Modify f|) k) s
  | steps_choice k s : stepsF (VisF (||Or) k) s.
  Hint Constructors stepsF : core.

  Definition steps {S R} : CompM S R -> S -> Prop :=
    fun t s => @stepsF S R (observe t) s.
  Hint Unfold steps : core.

  (* A single step from an itree *)

  Inductive stepF {S R} : CompM' S R -> S -> CompM' S R -> S -> Type :=
  | step_tau t s : stepF (TauF t) s (observe t) s
  | step_modify f k s : stepF (VisF (|Modify f|) k) s (observe (k s)) (f s)
  | step_choice b k s : stepF (VisF (||Or) k) s (observe (k b)) s.
  Hint Constructors stepF : core.

  Definition step {S R} : CompM S R -> S -> CompM S R -> S -> Type :=
    fun t s t' s' => stepF (observe t) s (observe t') s'.
  Hint Unfold step : core.

  Definition step_no_errors {S R} t1 s1 t2 s2 :
    @step S R t1 s1 t2 s2 -> no_errors t1 s1 -> no_errors t2 s2.
  Proof.
    intro; unfold step in X; dependent destruction X.
    - rewrite <- (observing_intros _ (Tau t) _ x0), <- (observing_intros _ _ _ x).
      apply no_errors_Tau.
    - rewrite <- (observing_intros _ (vis (Modify f) k) _ x0), <- (observing_intros _ _ _ x).
      apply no_errors_Modify.
    - rewrite <- (observing_intros _ (vis Or k) _ x0), <- (observing_intros _ _ _ x).
      rewrite <- no_errors_Choice; eauto.
  Qed.

  (* If `steps t s` then there exists a step from `(t,s)` *)

  Lemma stepsF_impl_stepF {S R} (t : CompM' S R) s :
    stepsF t s -> exists t' s', inhabited (stepF t s (observe t') s').
  Proof.
    destruct 1; unshelve (repeat econstructor). exact false.
  Qed.

  Lemma steps_impl_step {S R} (t : CompM S R) s :
    steps t s -> exists t' s', inhabited (step t s t' s').
  Proof. apply stepsF_impl_stepF. Qed.

  (* If there exists a step from `(t,s)` then `steps t s` *)

  Lemma stepF_impl_stepsF {S R} (t : CompM' S R) s t' s' :
    stepF t s t' s' -> stepsF t s.
  Proof. destruct 1; constructor. Qed.

  Lemma step_impl_steps {S R} (t : CompM S R) s t' s' :
    step t s t' s' -> steps t s.
  Proof. apply stepF_impl_stepsF. Qed.

  (* Deconstructing `step t s` *)

  Lemma stepF_tau_inv {S R t t' s s'} :
    @stepF S R (TauF t) s (observe t') s' ->
    observe t' = observe t /\ s' = s.
  Proof. intro; dependent destruction X; easy. Qed.

  Lemma stepF_modify_inv {S R f k s t' s'} :
    @stepF S R (VisF (|Modify f|) k) s (observe t') s' ->
    observe t' = observe (k s) /\ s' = (f s).
  Proof. intro; dependent destruction X; easy. Qed.

  Lemma stepF_choice_inv {S R k s t' s'} :
    @stepF S R (VisF (||Or) k) s (observe t') s' ->
    { b | observe t' = observe (k b) /\ s' = s }.
  Proof. intro; dependent destruction X; exists b; easy. Qed.

  Lemma stepF_err {S R s t' s'} :
    @stepF S R (observe (throw tt)) s (observe t') s' -> False.
  Proof. inversion 1. Qed.

  Lemma stepF_vis_eq2 {S R X e k1 k2 s t1' t2' s1' s2'} :
    @stepF S R (VisF (X:=X) e k1) s (observe t1') s1' ->
    @stepF S R (VisF (X:=X) e k2) s (observe t2') s2' ->
    s1' = s2'.
  Proof.
    destruct e as [? | [? | ?]]; intros;
      dependent destruction X0; try dependent destruction X1; easy.
  Qed.


  (** * `sbuter` **)

  Inductive sbuter_genF {S1 S2 R1 R2} sbuter p (Q : R1 -> R2 -> Perms)
                        (t1 : CompM' S1 R1) s1 (t2 : CompM' S2 R2) s2 : Prop :=
  | sbuter_gen_ret p' r1 r2 :
      pre p (s1, s2) -> sep_step p p' ->
      p' ∈ Q r1 r2 ->
      RetF r1 = t1 -> RetF r2 = t2 ->
      sbuter_genF sbuter p Q t1 s1 t2 s2
  | sbuter_gen_err k :
      pre p (s1, s2) ->
      VisF (Throw tt|) k = t2 ->
      sbuter_genF sbuter p Q t1 s1 t2 s2
  | sbuter_gen_step_l p' :
      pre p (s1, s2) -> sep_step p p' ->
      stepsF t1 s1 ->
      (forall t1' s1', stepF t1 s1 (observe t1') s1' ->
         guar p (s1, s2) (s1', s2)) ->
      (forall t1' s1', stepF t1 s1 (observe t1') s1' ->
         sbuter_genF sbuter p' Q (observe t1') s1' t2 s2) ->
      sbuter_genF sbuter p Q t1 s1 t2 s2
  | sbuter_gen_step_r p' :
      pre p (s1, s2) -> sep_step p p' ->
      stepsF t2 s2 ->
      (forall t2' s2', stepF t2 s2 (observe t2') s2' ->
         guar p (s1, s2) (s1, s2')) ->
      (forall t2' s2', stepF t2 s2 (observe t2') s2' ->
         sbuter_genF sbuter p' Q t1 s1 (observe t2') s2') ->
      sbuter_genF sbuter p Q t1 s1 t2 s2
  | sbuter_gen_step p' :
      pre p (s1, s2) -> sep_step p p' ->
      stepsF t1 s1 -> stepsF t2 s2 ->
      (forall t1' s1', stepF t1 s1 (observe t1') s1' ->
       exists t2' s2' (_ : stepF t2 s2 (observe t2') s2'),
         guar p (s1, s2) (s1', s2') /\ sbuter p' Q t1' s1' t2' s2') ->
      (forall t2' s2', stepF t2 s2 (observe t2') s2' ->
       exists t1' s1'(_ : stepF t1 s1 (observe t1') s1'),
         guar p (s1, s2) (s1', s2') /\ sbuter p' Q t1' s1' t2' s2') ->
      sbuter_genF sbuter p Q t1 s1 t2 s2.

  Lemma sbuter_genF_mon {S1 S2 R1 R2} p Q t1 s1 t2 s2 r r' :
    @sbuter_genF S1 S2 R1 R2 r p Q t1 s1 t2 s2 ->
    (forall p Q t1 s1 t2 s2, r p Q t1 s1 t2 s2 -> r' p Q t1 s1 t2 s2 : Prop) ->
    @sbuter_genF S1 S2 R1 R2 r' p Q t1 s1 t2 s2.
  Proof.
    induction 1; intros; subst; try solve [econstructor; eauto]; auto.
    eapply sbuter_gen_step; eauto; intros.
    - destruct (H3 t1' s1' X) as [t2' [s2' [X' [? ?]]]].
      exists t2', s2', X'; eauto.
    - destruct (H4 t2' s2' X) as [t1' [s1' [X' [? ?]]]].
      exists t1', s1', X'; eauto.
  Qed.

  Definition sbuter_gen {S1 S2 R1 R2} sbuter p Q :
    CompM S1 R1 -> S1 -> CompM S2 R2 -> S2 -> Prop :=
    fun t1 s1 t2 s2 => sbuter_genF sbuter p Q (observe t1) s1 (observe t2) s2.
  Hint Unfold sbuter_gen : core.

  Definition sbuter {S1 S2 R1 R2} := paco6 (@sbuter_gen S1 S2 R1 R2) bot6.

  Lemma sbuter_gen_mon {S1 S2 R1 R2} : monotone6 (@sbuter_gen S1 S2 R1 R2).
  Proof.
    repeat intro. unfold sbuter_gen in *.
    eapply sbuter_genF_mon; eauto.
  Qed.
  Hint Resolve sbuter_gen_mon : paco.

  Instance Proper_observing_paco6_sbuter_gen {S1 S2 R1 R2} r p Q :
    Proper (observing eq ==> eq ==> observing eq ==> eq ==> iff)
           (paco6 (@sbuter_gen S1 S2 R1 R2) r p Q).
  Proof.
    repeat intro; destruct H, H1.
    split; intro; punfold H3; pfold; unfold sbuter_gen in *;
      [ rewrite <- H, <- H0, <- H1, <- H2 | rewrite H, H0, H1, H2 ]; eauto.
  Qed.

  Instance Proper_observing_sbuter {S1 S2 R1 R2} p Q :
    Proper (observing eq ==> eq ==> observing eq ==> eq ==> iff)
           (@sbuter S1 S2 R1 R2 p Q).
  Proof. apply Proper_observing_paco6_sbuter_gen. Qed.


  (** * alternate constructors for `sbuter` **)

  Definition sbuter_gen_tau_l {S1 S2 R1 R2 sbuter p Q} t1 s1 t2 s2 :
    pre p (s1, s2) ->
    sbuter_genF sbuter p Q (observe t1) s1 t2 s2 ->
    @sbuter_genF S1 S2 R1 R2 sbuter p Q (TauF t1) s1 t2 s2.
  Proof.
    econstructor 3 with (p':=p); intuition.
    all: try rewrite (proj1 (stepF_tau_inv X));
         now rewrite (proj2 (stepF_tau_inv X)).
  Defined.

  Definition sbuter_gen_tau_r {S1 S2 R1 R2 sbuter p Q} t1 s1 t2 s2 :
    pre p (s1, s2) ->
    sbuter_genF sbuter p Q t1 s1 (observe t2) s2 ->
    @sbuter_genF S1 S2 R1 R2 sbuter p Q t1 s1 (TauF t2) s2.
  Proof.
    econstructor 4 with (p':=p); intuition.
    all: try rewrite (proj1 (stepF_tau_inv X));
         now rewrite (proj2 (stepF_tau_inv X)).
  Defined.

  Definition sbuter_gen_modify_l {S1 S2 R1 R2 sbuter p Q} p' f k s1 t2 s2 :
      pre p (s1, s2) ->
      sep_step p p' -> guar p (s1, s2) (f s1, s2) ->
      sbuter_genF sbuter p' Q (observe (k s1)) (f s1) t2 s2 ->
      @sbuter_genF S1 S2 R1 R2 sbuter p Q (VisF (|Modify f|) k) s1 t2 s2.
  Proof.
    econstructor 3 with (p':=p'); intuition; try inv H3.
    all: try rewrite (proj1 (stepF_modify_inv X));
         now rewrite (proj2 (stepF_modify_inv X)).
  Defined.

  Definition sbuter_gen_modify_r {S1 S2 R1 R2 sbuter p Q} p' t1 s1 f k s2 :
      pre p (s1, s2) ->
      sep_step p p' -> guar p (s1, s2) (s1, f s2) ->
      sbuter_genF sbuter p' Q t1 s1 (observe (k s2)) (f s2) ->
      @sbuter_genF S1 S2 R1 R2 sbuter p Q t1 s1 (VisF (|Modify f|) k) s2.
  Proof.
    econstructor 4 with (p':=p'); intuition. try inv H3.
    all: try rewrite (proj1 (stepF_modify_inv X));
         now rewrite (proj2 (stepF_modify_inv X)).
  Defined.

  Definition sbuter_gen_choice_l {S1 S2 R1 R2 sbuter p Q} p' k s1 t2 s2 :
      pre p (s1, s2) ->
      sep_step p p' ->
      (forall b, sbuter_genF sbuter p' Q (observe (k b)) s1 t2 s2) ->
      @sbuter_genF S1 S2 R1 R2 sbuter p Q (VisF (||Or) k) s1 t2 s2.
  Proof.
    econstructor 3 with (p':=p'); intuition; try inv H2.
    all: apply stepF_choice_inv in X; destruct X as [? []];
         try rewrite H2; rewrite H3; easy.
  Defined.

  Definition sbuter_gen_choice_r {S1 S2 R1 R2 sbuter p Q} p' t1 s1 k s2 :
      pre p (s1, s2) ->
      sep_step p p' ->
      (forall b, sbuter_genF sbuter p' Q t1 s1 (observe (k b)) s2) ->
      @sbuter_genF S1 S2 R1 R2 sbuter p Q t1 s1 (VisF (||Or) k) s2.
  Proof.
    econstructor 4 with (p':=p'); intuition; try inv H2.
    all: apply stepF_choice_inv in X; destruct X as [? []];
         try rewrite H2; rewrite H3; easy.
  Defined.


  (** * basic lemmas about `sbuter` **)

  Lemma sep_step_sbuter_genF {S1 R1 S2 R2 r p Q t1 s1 t2 s2} p' :
    pre p (s1,s2) -> sep_step p p' ->
    @sbuter_genF S1 R1 S2 R2 r p' Q t1 s1 t2 s2 ->
    @sbuter_genF S1 R1 S2 R2 r p Q t1 s1 t2 s2.
  Proof.
    intros. dependent induction H1; subst.
    - econstructor 1 with (p':=p'); eauto.
      transitivity p0; eauto.
    - econstructor 2; eauto.
    - econstructor 3 with (p':=p'); eauto; intros.
      + transitivity p0; eauto.
      + eapply (sep_step_guar _ p0); eauto.
    - econstructor 4 with (p':=p'); eauto; intros.
      + transitivity p0; eauto.
      + eapply (sep_step_guar _ p0); eauto.
    - econstructor 5 with (p':=p'); eauto; intros.
      + transitivity p0; eauto.
      + specialize (H5 _ _ X); destruct H5 as [?t2' [?s2' [? []]]].
        exists t2', s2', x; split; eauto.
        eapply (sep_step_guar _ p0); eauto.
      + specialize (H6 _ _ X); destruct H6 as [?t1' [?s1' [? []]]].
        exists t1', s1', x; split; eauto.
        eapply (sep_step_guar _ p0); eauto.
  Qed.

  Lemma sep_step_sbuter {S1 R1 S2 R2 p Q t1 s1 t2 s2} p' :
    pre p (s1,s2) -> sep_step p p' ->
    @sbuter S1 R1 S2 R2 p' Q t1 s1 t2 s2 ->
    @sbuter S1 R1 S2 R2 p Q t1 s1 t2 s2.
  Proof.
    intros. pfold; red; punfold H1; red in H1.
    eapply sep_step_sbuter_genF; eauto.
  Qed.

  Lemma sbuter_genF_pre {S1 R1 S2 R2 r p Q t1 s1 t2 s2} :
    @sbuter_genF S1 R1 S2 R2 r p Q t1 s1 t2 s2 ->
    pre p (s1, s2) \/ exists k, VisF (Throw tt|) k = t2.
  Proof.
    inversion 1; eauto.
  Qed.

  Lemma sbuter_pre {S1 R1 S2 R2 p Q t1 s1 t2 s2} :
    @sbuter S1 R1 S2 R2 p Q t1 s1 t2 s2 ->
    pre p (s1, s2) \/ exists k, vis (Throw tt) k = t2.
  Proof.
    intro; punfold H; red in H; inversion H; eauto.
  Qed.

  Lemma sbuter_inv_tau_l {S1 S2 R1 R2} p Q t1 s1 t2 s2 :
    @sbuter S1 S2 R1 R2 p Q (Tau t1) s1 t2 s2 ->
    @sbuter S1 S2 R1 R2 p Q t1 s1 t2 s2.
  Proof.
    intro; pfold; red; punfold H; red in H.
    dependent induction H.
    - destruct x; econstructor 2; eauto.
    - eapply sep_step_sbuter_genF; eauto.
      eapply H3; constructor.
    - econstructor 4; eauto.
    - econstructor 4; eauto; intros.
      + specialize (H4 _ _ X); destruct H4 as [?t1' [?s1' [? []]]].
        inv x; eauto.
      + specialize (H4 _ _ X); destruct H4 as [?t1' [?s1' [? []]]].
        inv x; rewrite H9.
        destruct H5; [|inv H5].
        pfold_reverse; eauto.
  Qed.

  Lemma sbuter_inv_tau_r {S1 S2 R1 R2} p Q t1 s1 t2 s2 :
    @sbuter S1 S2 R1 R2 p Q t1 s1 (Tau t2) s2 ->
    @sbuter S1 S2 R1 R2 p Q t1 s1 t2 s2.
  Proof.
    intro; pfold; red; punfold H; red in H.
    dependent induction H.
    - econstructor 3; eauto.
    - eapply sep_step_sbuter_genF; eauto.
      eapply H3; constructor.
    - econstructor 3; eauto; intros.
      + specialize (H3 _ _ X); destruct H3 as [?t2' [?s2' [? []]]].
        inv x; eauto.
      + specialize (H3 _ _ X); destruct H3 as [?t1' [?s1' [? []]]].
        inv x; rewrite H9.
        destruct H5; [|inv H5].
        pfold_reverse; eauto.
  Qed.

  Lemma Proper_eutt_sbuter_l {S1 S2 R1 R2} p Q t1 t1' s1 t2 s2 :
    t1 ≈ t1' -> @sbuter S1 S2 R1 R2 p Q t1 s1 t2 s2 ->
                @sbuter S1 S2 R1 R2 p Q t1' s1 t2 s2.
  Proof.
    revert p Q t1 t1' s1 t2 s2; pcofix CIH; intros.
    pfold; red; punfold H1; red in H1.
    revert t1' H0; dependent induction H1; intros.
    5: punfold H5; red in H5; dependent destruction H1; destruct x.
    (* sbuter_gen_ret *)
    - punfold H2; red in H2.
      destruct x0, x.
      dependent induction H2.
      + destruct x; econstructor; eauto.
      + destruct x; apply sbuter_gen_tau_l; eauto.
    (* sbuter_gen_err *)
    - destruct x; econstructor 2; eauto.
    (* sbuter_gen_step_l *)
    - punfold H5; red in H5; dependent induction H5; pclearbot.
      all: destruct x; try destruct x0; eauto.
      3: destruct e as [e | [e | e]]; destruct e; inversion H1.
      + inversion H1.
      + apply sbuter_gen_tau_l; eauto.
        eapply sep_step_sbuter_genF; eauto.
      + eapply sbuter_gen_modify_l; eauto.
      + eapply sbuter_gen_choice_l; eauto.
      + eapply sep_step_sbuter_genF; eauto.
      + apply sbuter_gen_tau_l; eauto.
    (* sbuter_gen_step_r *)
    - econstructor 4; eauto.
    (* sbuter_gen_step, step_tau *)
    - dependent induction H5; pclearbot; try destruct x.
      + econstructor 5; eauto; intros.
        * inv X.
          specialize (H3 _ _ (step_tau _ _)); destruct H3 as [?t1' [?s1' [? []]]].
          exists t1'1, s1'0, x; split; eauto.
          destruct H3; [|inv H3].
          right; eapply CIH; eauto.
          rewrite <- (observing_intros _ _ _ H7); eauto.
        * specialize (H4 _ _ X); destruct H4 as [?t2' [?s2' [? []]]].
          inv x.
          exists m2, s2'0, (step_tau _ _); split; eauto.
          destruct H4; [|inv H4].
          right; eapply (CIH _ _ t2'0); eauto.
          rewrite <- (observing_intros _ _ _ H8); eauto.
      + eapply IHeqitF; eauto.
        admit. (* Hunh? Why?? *)
      + eapply sbuter_gen_tau_l; eauto.
    (* sbuter_gen_step, step_modify *)
    - dependent induction H5; pclearbot; try destruct x.
      + econstructor 5; eauto; intros.
        * apply stepF_modify_inv in X; destruct X; subst.
          specialize (H3 _ _ (step_modify _ _ _)); destruct H3 as [?t2' [?s2' [? []]]].
          exists t2', s2', x; split; eauto.
          destruct H5; [|inv H5].
          right; eapply CIH; eauto.
          rewrite (observing_intros _ _ _ H1); eauto.
        * specialize (H4 _ _ X); destruct H4 as [?t1' [?s1' [? []]]].
          apply stepF_modify_inv in x; destruct x; subst.
          exists (k2 s), (f s), (step_modify _ _ _); split; eauto.
          destruct H4; [|inv H4].
          right; eapply (CIH _ _ t1'0); eauto.
          rewrite (observing_intros _ _ _ H5); eauto.
      + eapply sbuter_gen_tau_l; eauto.
    (* sbuter_gen_step, step_choice *)
    - dependent induction H5; pclearbot; try destruct x.
      + econstructor 5; eauto; intros.
        * apply stepF_choice_inv in X; destruct X as [b []]; subst.
          specialize (H3 _ _ (step_choice b _ _)); destruct H3 as [?t2' [?s2' [? []]]].
          exists t2', s2', x; split; eauto.
          destruct H5; [|inv H5].
          right; eapply CIH; eauto.
          rewrite (observing_intros _ _ _ H1); eauto.
        * specialize (H4 _ _ X); destruct H4 as [?t1' [?s1' [? []]]].
          apply stepF_choice_inv in x; destruct x as [b []]; subst.
          exists (k2 b), s, (step_choice b _ _); split; eauto.
          destruct H4; [|inv H4].
          right; eapply (CIH _ _ t1'0); eauto.
          rewrite (observing_intros _ _ _ H5); eauto.
  Admitted.

  Lemma Proper_eutt_sbuter_r {S1 S2 R1 R2} p Q t1 s1 t2 t2' s2 :
    t2 ≈ t2' -> @sbuter S1 S2 R1 R2 p Q t1 s1 t2 s2 ->
                @sbuter S1 S2 R1 R2 p Q t1 s1 t2' s2.
  Proof.
    revert p Q t1 s1 t2 t2' s2; pcofix CIH; intros.
    pfold; red; punfold H1; red in H1.
    revert t2' H0; dependent induction H1; intros.
    5: punfold H5; red in H5; dependent destruction H2; destruct x.
    (* sbuter_gen_ret *)
    - punfold H2; red in H2.
      destruct x0, x.
      dependent induction H2.
      + destruct x; econstructor; eauto.
      + destruct x; apply sbuter_gen_tau_r; eauto.
    (* sbuter_gen_err *)
    - rewrite <- (observing_intros eq (vis (Throw tt) k) _ x) in H0.
      punfold H0; red in H0; dependent induction H0; intros.
      + destruct x; econstructor 2; eauto.
      + destruct x; eapply sbuter_gen_tau_r; eauto.
    (* sbuter_gen_step_l *)
    - econstructor 3; eauto.
    (* sbuter_gen_step_r *)
    - punfold H5; red in H5; dependent induction H5; pclearbot.
      all: destruct x; try destruct x0; eauto.
      3: destruct e as [e | [e | e]]; destruct e; inversion H1.
      + inversion H1.
      + apply sbuter_gen_tau_r; eauto.
        eapply sep_step_sbuter_genF; eauto.
      + eapply sbuter_gen_modify_r; eauto.
      + eapply sbuter_gen_choice_r; eauto.
      + eapply sep_step_sbuter_genF; eauto.
      + apply sbuter_gen_tau_r; eauto.
    (* sbuter_gen_step, step_tau *)
    - dependent induction H5; pclearbot; try destruct x.
      + econstructor 5; eauto; intros.
        * specialize (H3 _ _ X); destruct H3 as [?t2' [?s2' [? []]]].
          inv x.
          exists m2, s2', (step_tau _ _); split; eauto.
          destruct H3; [|inv H3].
          right; eapply (CIH _ _ _ _ t2'0); eauto.
          rewrite <- (observing_intros _ _ _ H8); eauto.
        * inv X.
          specialize (H4 _ _ (step_tau _ _)); destruct H4 as [?t2' [?s2' [? []]]].
          exists t2'1, s2'0, x; split; eauto.
          destruct H4; [|inv H4].
          right; eapply CIH; eauto.
          rewrite <- (observing_intros _ _ _ H7); eauto.
      + eapply IHeqitF; eauto.
        admit. (* Hunh? Why?? *)
      + eapply sbuter_gen_tau_r; eauto.
    (* sbuter_gen_step, step_modify *)
    - dependent induction H5; pclearbot; try destruct x.
      + econstructor 5; eauto; intros.
        * specialize (H3 _ _ X); destruct H3 as [?t2' [?s2' [? []]]].
          apply stepF_modify_inv in x; destruct x; subst.
          exists (k2 s), (f s), (step_modify _ _ _); split; eauto.
          destruct H3; [|inv H3].
          right; eapply (CIH _ _ _ _ t2'0); eauto.
          rewrite (observing_intros _ _ _ H5); eauto.
        * apply stepF_modify_inv in X; destruct X; subst.
          specialize (H4 _ _ (step_modify _ _ _)); destruct H4 as [?t1' [?s1' [? []]]].
          exists t1', s1', x; split; eauto.
          destruct H5; [|inv H5].
          right; eapply CIH; eauto.
          rewrite (observing_intros _ _ _ H2); eauto.
      + eapply sbuter_gen_tau_r; eauto.
    (* sbuter_gen_step, step_choice *)
    - dependent induction H5; pclearbot; try destruct x.
      + econstructor 5; eauto; intros.
        * specialize (H3 _ _ X); destruct H3 as [?t2' [?s2' [? []]]].
          apply stepF_choice_inv in x; destruct x as [b []]; subst.
          exists (k2 b), s, (step_choice b _ _); split; eauto.
          destruct H3; [|inv H3].
          right; eapply (CIH _ _ _ _ t2'0); eauto.
          rewrite (observing_intros _ _ _ H5); eauto.
        * apply stepF_choice_inv in X; destruct X as [b []]; subst.
          specialize (H4 _ _ (step_choice b _ _)); destruct H4 as [?t1' [?s1' [? []]]].
          exists t1', s1', x; split; eauto.
          destruct H5; [|inv H5].
          right; eapply CIH; eauto.
          rewrite (observing_intros _ _ _ H2); eauto.
  Admitted.

  Instance Proper_eutt_sbuter {S1 S2 R1 R2} p Q :
    Proper (eutt eq ==> eq ==> eutt eq ==> eq ==> iff)
           (@sbuter S1 S2 R1 R2 p Q).
  Proof.
    repeat intro; split; intro; destruct H0, H2.
    - eapply Proper_eutt_sbuter_l; eauto.
      eapply Proper_eutt_sbuter_r; eauto.
    - eapply Proper_eutt_sbuter_l; [symmetry|]; eauto.
      eapply Proper_eutt_sbuter_r; [symmetry|]; eauto.
  Qed.

End bisim.
