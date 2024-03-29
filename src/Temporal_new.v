From Heapster Require Import
     Permissions
     Typing_new.

From Coq Require Import
     Program
     Program.Equality
     Relations
     Morphisms
     Streams
     Vector.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     ITree
     Basics.Basics
     Basics.MonadState
     Basics.CategoryTheory
     Events.Exception
     Events.Nondeterminism
     Events.Writer
     Events.State
     Events.StateFacts
     Eq.Eqit
     Eq.Shallow
     Interp.Interp
     Interp.InterpFacts.

From Paco Require Import
     paco.

Import ITreeNotations.
Import SumNotations.
Open Scope sum_scope.

#[local] Hint Constructors stepsF stepF : core.
#[local] Hint Resolve no_errors_gen_mon : paco.
#[local] Hint Resolve sbuter_gen_mon : paco.


(** * `eq_sat_sep_sbuter` **)

Definition TPred S R := CompM S R -> S -> Prop.
Definition TPred' S R := CompM' S R -> S -> Prop.

Definition eq_sat_sep_sbuter {S1 S2 R1 R2} (q:@perm (S1*S2)) Q
  (P1:TPred S1 R1) (P2:TPred S2 R2) :=
  forall p t1 s1 t2 s2, pre q (s1,s2) -> p ⊥ q ->
    sbuter p Q t1 s1 t2 s2 -> no_errors t2 s2 ->
    (P1 t1 s1 <-> P2 t2 s2).
#[local] Hint Unfold eq_sat_sep_sbuter : core.


(** * `eq_sat_sep_sbuter` for state predicates **)

Definition state_pred {S} R P : TPred S R := fun '_ s => P s.

Definition q_similar {S1 S2} q (P1 : S1 -> Prop) (P2 : S2 -> Prop): Prop :=
  forall s1 s2, pre q (s1,s2) -> (P1 s1 <-> P2 s2).

Lemma eq_sat_state_preds {S1 S2 R1 R2} q Q (P1 : S1 -> Prop) (P2 : S2 -> Prop)
  : q_similar q P1 P2 ->
    eq_sat_sep_sbuter q Q (state_pred R1 P1) (state_pred R2 P2).
Proof. intros; eauto. Qed.


(** * `eq_sat_sep_sbuter` for logical connectives **)

Lemma eq_sat_and {S1 S2 R1 R2} q Q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q Q TP1 TP2 -> eq_sat_sep_sbuter q Q TP1' TP2' ->
    eq_sat_sep_sbuter q Q (TP1 /2\ TP1') (TP2 /2\ TP2').
Proof.
  intros esss esss' p t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.

Lemma eq_sat_or {S1 S2 R1 R2} q Q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q Q TP1 TP2 -> eq_sat_sep_sbuter q Q TP1' TP2' ->
    eq_sat_sep_sbuter q Q (TP1 \2/ TP1') (TP2 \2/ TP2').
Proof.
  intros esss esss' p t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.

Notation "p -2> q" :=
  (fun x0 x1 => p x0 x1 -> q x0 x1)
  (at level 50, no associativity).

Lemma eq_sat_impl {S1 S2 R1 R2} q Q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q Q TP1 TP2 -> eq_sat_sep_sbuter q Q TP1' TP2' ->
    eq_sat_sep_sbuter q Q (TP1 -2> TP1') (TP2 -2> TP2').
Proof.
  intros esss esss' p t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.


(** * `eq_sat_sep_sbuter` for `EU`  **)

Inductive EU {S R} (P P' : TPred S R) t0 s0 : Prop :=
| EU_here : P' t0 s0 -> EU P P' t0 s0
| EU_step : P t0 s0 -> forall t1 s1, step t0 s0 t1 s1 -> EU P P' t1 s1 -> EU P P' t0 s0.
Arguments EU_here {S R P P' t0 s0}.
Arguments EU_step {S R P P' t0 s0}.

Lemma eq_sat_EU {S1 S2 R1 R2} q Q (P1 P1' : TPred S1 R1) (P2 P2' : TPred S2 R2) :
    eq_sat_sep_sbuter q Q P1 P2 -> eq_sat_sep_sbuter q Q P1' P2' ->
    eq_sat_sep_sbuter q Q (EU P1 P1') (EU P2 P2').
Proof.
  intros eq_sat_Ps eq_sat_P's; split; intros.
  - revert p t2 s2 H H0 H1 H2; dependent induction H3; intros.
    + eapply EU_here, eq_sat_P's; eauto.
    + punfold H2; red in X, H2; dependent induction H2.
      * destruct x0; inv X.
      * punfold H2; red in H2; destruct x; inv H2.
      * eapply (IHEU p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H6; eauto.
      * destruct (stepsF_impl_stepF _ _ H8) as [?t2' [?s2' []]].
        eapply EU_step; eauto.
        -- eapply eq_sat_Ps; eauto.
           pfold; red; econstructor 4; eauto.
        -- eapply H4; eauto.
           ++ respects; eapply sep_r; eauto.
           ++ eapply step_no_errors; eauto.
      * destruct (H6 _ _ X) as [?t2' [?s2' [? []]]].
        eapply EU_step; eauto.
        -- eapply eq_sat_Ps; eauto.
           pfold; red; econstructor 5; eauto.
        -- eapply (IHEU p'); pclearbot; eauto.
           ++ respects; eapply sep_r; eauto.
           ++ eapply step_no_errors; eauto.
  - revert p t1 s1 H H0 H1 H2; dependent induction H3; intros.
    + eapply EU_here, eq_sat_P's; eauto.
    + punfold H2; red in X, H2; dependent induction H2.
      1-2: destruct x; inv X.
      * destruct (stepsF_impl_stepF _ _ H8) as [?t1' [?s1' []]].
        eapply EU_step; eauto.
        -- eapply eq_sat_Ps; eauto.
           pfold; red; econstructor 3; eauto.
        -- eapply H4; eauto.
           respects; eapply sep_r; eauto.
      * eapply (IHEU p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H6; eauto.
        -- eapply step_no_errors; eauto.
      * destruct (H4 _ _ X) as [?t1' [?s1' [? []]]].
        eapply EU_step; eauto.
        -- eapply eq_sat_Ps; eauto.
           pfold; red; econstructor 5; eauto.
        -- eapply (IHEU p'); pclearbot; eauto.
           ++ respects; eapply sep_r; eauto.
           ++ eapply step_no_errors; eauto.
Qed.


(** * `eq_sat_sep_sbuter` for `EF`  **)

Notation True2 := (fun _ _ => True).

Notation EF := (EU True2).
Notation EF_here := (@EU_here _ _ True2 _ _ _).
Notation EF_step := (@EU_step _ _ True2 _ _ _ I).

Lemma eq_sat_EF {S1 S2 R1 R2} q Q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q Q P1 P2 ->
    eq_sat_sep_sbuter q Q (EF P1) (EF P2).
Proof. eapply eq_sat_EU; easy. Qed.


(** * `eq_sat_sep_sbuter` for `AF`  **)

Definition AG_gen {S R} (P : TPred S R) (AG : TPred S R) t0 s0 :=
  P t0 s0 /\ (forall t1 s1, step t0 s0 t1 s1 -> AG t1 s1).

Definition AG {S R} P := paco2 (@AG_gen S R P) bot2.

Lemma is_path_gen_mon {S R P} : monotone2 (@AG_gen S R P).
Proof. repeat intro; induction IN; econstructor; eauto. Qed.
#[local] Hint Resolve is_path_gen_mon : paco.

Lemma eq_sat_AG {S1 S2 R1 R2} q Q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q Q P1 P2 ->
    eq_sat_sep_sbuter q Q (AG P1) (AG P2).
Proof.
  intros eq_sat_Ps; split; intros.
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    punfold H4; destruct H4; pfold; split; intros.
    + eapply eq_sat_Ps; eauto.
    + punfold H2; red in X, H2; dependent induction H2.
      1-2: destruct x; inv X.
      * destruct (stepsF_impl_stepF _ _ H6) as [?t1' [?s1' []]].
        specialize (H9 _ _ X0); pclearbot; punfold H9; destruct H9.
        eapply H4; eauto.
        respects; eapply sep_r; eauto.
      * right; eapply (CIH p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H3; eauto.
        -- eapply step_no_errors; eauto.
        -- pfold; constructor; eauto.
      * destruct (H4 _ _ X) as [?t1' [?s1' [? []]]].
        right; eapply (CIH p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- destruct H11; [|inversion b]; eauto.
        -- eapply step_no_errors; eauto.
        -- specialize (H9 _ _ x); pclearbot; eauto.
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    punfold H4; destruct H4; pfold; split; intros.
    + eapply eq_sat_Ps; eauto.
    + punfold H2; red in X, H2; dependent induction H2.
      * destruct x0; inv X.
      * punfold H3; red in H3; destruct x; inv H3.
      * right; eapply (CIH p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H3; eauto.
        -- pfold; constructor; eauto.
      * destruct (stepsF_impl_stepF _ _ H6) as [?t2' [?s2' []]].
        specialize (H9 _ _ X0); pclearbot; punfold H9; destruct H9.
        eapply H4; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
      * destruct (H3 _ _ X) as [?t2' [?s2' [? []]]].
        right; eapply (CIH p' _ _ t2' s2'); eauto.
        -- respects; eapply sep_r; eauto.
        -- destruct H11; [|inversion H11]; eauto.
        -- eapply step_no_errors; eauto.
        -- specialize (H9 _ _ x); pclearbot; eauto.
Qed.


(** * `eq_sat_sep_sbuter` for `AU` **)

Inductive AU {S R} (P P' : TPred S R) t0 s0 : Prop :=
| AU_here : P' t0 s0 -> AU P P' t0 s0
| AU_step : P t0 s0 -> steps t0 s0 ->
            (forall t1 s1, step t0 s0 t1 s1 -> AU P P' t1 s1) ->
            AU P P' t0 s0.
Arguments AU_here {S R P P' t0 s0}.
Arguments AU_step {S R P P' t0 s0}.

Lemma eq_sat_AU {S1 S2 R1 R2} q Q (P1 P1' : TPred S1 R1) (P2 P2' : TPred S2 R2) :
    eq_sat_sep_sbuter q Q P1 P2 -> eq_sat_sep_sbuter q Q P1' P2' ->
    eq_sat_sep_sbuter q Q (AU P1 P1') (AU P2 P2').
Proof.
  intros eq_sat_Ps eq_sat_P's; split; intros.
  - revert p t2 s2 H H0 H1 H2; dependent induction H3; intros.
    { apply AU_here; eapply eq_sat_P's; eauto. }
    punfold H5; red in H5; dependent induction H5.
    + red in H0; destruct x0; inv H0.
    + punfold H6; red in H6; destruct x; inv H6.
    + destruct (stepsF_impl_stepF _ _ H0) as [?t1' [?s1' []]].
      eapply (H2 _ _ X p'); eauto.
      * respects; eapply sep_r; eauto.
      * pfold; red; eapply H9; eauto.
    + apply AU_step; eauto; intros.
      * eapply eq_sat_Ps; eauto.
        pfold; red; econstructor 4; eauto.
      * eapply H10; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
    + apply AU_step; eauto; intros.
      * eapply eq_sat_Ps; eauto.
        pfold; red; econstructor 5; eauto.
      * specialize (H10 _ _ X); destruct H10 as [?t1' [?s1' [? []]]].
        change (step t0 s1 t1' s1') in x.
        eapply (H2 _ _ x p'); pclearbot; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
  - revert p t1 s1 H H0 H1 H2; dependent induction H3; intros.
    { apply AU_here; eapply eq_sat_P's; eauto. }
    punfold H5; red in H5; dependent induction H5.
    + red in H0; destruct x; inv H0.
    + punfold H6; red in H6; destruct x; inv H6.
    + apply AU_step; eauto; intros.
      * eapply eq_sat_Ps; eauto.
        pfold; red; econstructor 3; eauto.
      * eapply H10; eauto.
        respects; eapply sep_r; eauto.
    + destruct (stepsF_impl_stepF _ _ H0) as [?t2' [?s2' []]].
      eapply (H2 _ _ X p'); eauto.
      * respects; eapply sep_r; eauto.
      * pfold; red; eapply H9; eauto.
      * eapply step_no_errors; eauto.
    + apply AU_step; eauto; intros.
      * eapply eq_sat_Ps; eauto.
        pfold; red; econstructor 5; eauto.
      * specialize (H9 _ _ X); destruct H9 as [?t2' [?s2' [? []]]].
        change (step t0 s2 t2' s2') in x.
        eapply (H2 _ _ x p'); pclearbot; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
Qed.


(** * `eq_sat_sep_sbuter` for `AF` **)

Notation AF := (AU True2).
Notation AF_here := (@AU_here _ _ True2 _ _ _).
Notation AF_step := (@AU_step _ _ True2 _ _ _ I).

Lemma eq_sat_AF {S1 S2 R1 R2} q Q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q Q P1 P2 ->
    eq_sat_sep_sbuter q Q (AF P1) (AF P2).
Proof. apply eq_sat_AU; easy. Qed.


(** * `eq_sat_sep_sbuter` for `EG` **)

Inductive EG_gen {S R} (P : TPred S R) EG t0 s0 : Prop :=
| EG_step t1 s1 : P t0 s0 -> step t0 s0 t1 s1 -> EG t1 s1 -> EG_gen P EG t0 s0
| EG_stop : P t0 s0 -> ~ (steps t0 s0) -> EG_gen P EG t0 s0.
Arguments EG_step {S R P EG t0 s0} t1 s1.
Arguments EG_stop {S R P EG t0 s0}.

Definition EG {S R} P := paco2 (@EG_gen S R P) bot2.

Lemma EG_gen_mon {S R P} : monotone2 (@EG_gen S R P).
Proof. repeat intro; induction IN; subst; solve [econstructor; eauto]. Qed.
#[local] Hint Resolve EG_gen_mon : paco.

Definition EG_pf {S R P t0 s0} : @EG S R P t0 s0 -> P t0 s0.
Proof. intro; punfold H; destruct H; eauto. Defined.

Lemma eq_sat_EG {S1 S2 R1 R2} q Q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q Q P1 P2 ->
    eq_sat_sep_sbuter q Q (EG P1) (EG P2).
Proof.
  intro eq_sat_Ps; split; intros.
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    punfold H2; red in H2; dependent induction H2.
    + pfold; apply EG_stop.
      * apply EG_pf in H2.
        eapply eq_sat_Ps; eauto.
        pfold; red; econstructor 1; eauto.
      * intro; red in H6; destruct x; inv H6.
    + punfold H3; red in H3; destruct x; inv H3.
    + punfold H8; destruct H8; [| exfalso; apply H9; red; eauto ].
      eapply H4; pclearbot; eauto.
      respects; eapply sep_r; eauto.
    + destruct (stepsF_impl_stepF _ _ H6) as [?t2' [?s2' []]].
      change (step t2 s2 t2' s2') in X.
      pfold; apply (EG_step t2' s2'); eauto.
      * apply EG_pf in H8.
        eapply eq_sat_Ps; eauto.
        pfold; econstructor 4; eauto.
      * left; eapply H4; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
    + punfold H8; destruct H8; [| exfalso; apply H9; red; eauto ].
      destruct (H3 _ _ X) as [?t2' [?s2' [? []]]].
      pclearbot; destruct H11; [|inv H11].
      pfold; apply (EG_step t2' s2'); eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 5; eauto.
      * right; eapply (CIH p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    punfold H2; red in H2; dependent induction H2.
    + pfold; apply EG_stop.
      * apply EG_pf in H2.
        eapply eq_sat_Ps; eauto.
        pfold; red; econstructor 1; eauto.
      * intro; red in H6; destruct x0; inv H6.
    + punfold H3; red in H3; destruct x; inv H3.
    + destruct (stepsF_impl_stepF _ _ H6) as [?t1' [?s1' []]].
      change (step t1 s1 t1' s1') in X.
      pfold; apply (EG_step t1' s1'); eauto.
      * apply EG_pf in H8.
        eapply eq_sat_Ps; eauto.
        pfold; econstructor 3; eauto.
      * left; eapply H4; eauto.
        -- respects; eapply sep_r; eauto.
    + punfold H8; destruct H8; [| exfalso; apply H9; red; eauto ].
      eapply H4; pclearbot; eauto.
      -- respects; eapply sep_r; eauto.
      -- eapply step_no_errors; eauto.
    + punfold H8; destruct H8; [| exfalso; apply H9; red; eauto ].
      destruct (H4 _ _ X) as [?t1' [?s1' [? []]]].
      pclearbot; destruct H11; [|inv H11].
      pfold; apply (EG_step t1' s1'); eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 5; eauto.
      * right; eapply (CIH p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
Qed.


(** * `eq_sat_sep_sbuter` for termination predicates **)

Definition RetPred S R := R -> S -> Prop.

Definition AReturns {S R} (P : RetPred S R) : TPred S R :=
  AF (fun t s => exists r, observing eq (Ret r) t /\ P r s).

Definition eq_sat_sep_ret {S1 S2 R1 R2} q Q
  (P1 : RetPred S1 R1) (P2 : RetPred S2 R2) :=
  forall p r1 r2 s1 s2, pre q (s1,s2) -> p ⊥ q ->
    p ∈ Q r1 r2 -> (P1 r1 s1 <-> P2 r2 s2).

Lemma eq_sat_AReturns {S1 S2 R1 R2} q Q (P1 : RetPred S1 R1) (P2 : RetPred S2 R2) :
  eq_sat_sep_ret q Q P1 P2 ->
  eq_sat_sep_sbuter q Q (AReturns P1) (AReturns P2).
Proof.
  intro eq_sat_Ps; unfold AReturns; split; intros.
  - revert p t2 s2 H H0 H1 H2; dependent induction H3; intros.
    + destruct H as [? [[]]].
      punfold H2; red in H2; destruct observing_observe.
      dependent induction H2; try solve [ inv H7 ].
      * eapply AF_here; exists r2; split; eauto.
        eapply (eq_sat_Ps p'); eauto.
      * punfold H2; red in H2; destruct x; inv H2.
      * eapply AF_step; eauto; intros.
        eapply H4; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
    + punfold H5; red in H5; dependent induction H5.
      * red in H0; destruct x0; inv H0.
      * punfold H5; red in H5; destruct x; inv H5.
      * destruct (stepsF_impl_stepF _ _ H8) as [?t1' [?s1' []]].
        eapply (H2 _ _ X p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H10; eauto.
      * apply AF_step; eauto; intros.
        eapply H5; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
      * apply AF_step; eauto; intros.
        specialize (H5 _ _ X); destruct H5 as [?t1' [?s1' [? []]]].
        eapply (H2 _ _ x p'); pclearbot; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
  - revert p t1 s1 H H0 H1 H2; dependent induction H3; intros.
    + destruct H as [? [[]]].
      punfold H2; red in H2; destruct observing_observe.
      dependent induction H2; try solve [ inv H2 | inv H7 ].
      * eapply AF_here; exists r1; split; eauto.
        eapply (eq_sat_Ps p'); eauto.
      * eapply AF_step; eauto; intros.
        eapply H4; eauto.
        respects; eapply sep_r; eauto.
    + punfold H5; red in H5; dependent induction H5.
      * red in H0; destruct x; inv H0.
      * punfold H5; red in H5; destruct x; inv H5.
      * apply AF_step; eauto; intros.
        eapply H5; eauto.
        respects; eapply sep_r; eauto.
      * destruct (stepsF_impl_stepF _ _ H8) as [?t2' [?s2' []]].
        eapply (H2 _ _ X p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H10; eauto.
        -- eapply step_no_errors; eauto.
      * apply AF_step; eauto; intros.
        specialize (H10 _ _ X); destruct H10 as [?t2' [?s2' [? []]]].
        eapply (H2 _ _ x p'); pclearbot; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
Qed.

Definition EReturns {S R} (P : RetPred S R) : TPred S R :=
  EF (fun t s => exists r, observing eq (Ret r) t /\ P r s).

Lemma eq_sat_EReturns {S1 S2 R1 R2} q Q (P1 : RetPred S1 R1) (P2 : RetPred S2 R2) :
  eq_sat_sep_ret q Q P1 P2 ->
  eq_sat_sep_sbuter q Q (EReturns P1) (EReturns P2).
Proof.
  intros eq_sat_Ps; unfold EReturns; split; intros.
  - revert p t2 s2 H H0 H1 H2; dependent induction H3; intros.
    + destruct H as [r1 []]; eapply Proper_observing_sbuter in H2; eauto.
      punfold H2; red in H2; dependent induction H2; try solve [ inv H8 ].
      * eapply EF_here; exists r2; split; eauto.
        eapply (eq_sat_Ps p'); eauto.
      * punfold H3; red in H3; destruct x; inv H3.
      * destruct (stepsF_impl_stepF _ _ H8) as [?t2' [?s2' []]].
        eapply EF_step; eauto.
        eapply H6; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
    + punfold H2; red in X, H2; dependent induction H2.
      * destruct x0; inv X.
      * punfold H4; red in H4; destruct x; inv H4.
      * eapply (IHEU p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H4; eauto.
      * destruct (stepsF_impl_stepF _ _ H2) as [?t2' [?s2' []]].
        eapply EF_step; eauto.
        eapply H5; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
      * destruct (H4 _ _ X) as [?t2' [?s2' [? []]]].
        eapply EF_step; eauto.
        eapply (IHEU p'); pclearbot; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
  - revert p t1 s1 H H0 H1 H2; dependent induction H3; intros.
    + destruct H as [r2 []]; eapply Proper_observing_sbuter in H2; eauto.
      punfold H2; red in H2; dependent induction H2; try solve [ inv H2 | inv H8 ].
      * eapply EF_here; exists r1; split; eauto.
        eapply (eq_sat_Ps p'); eauto.
      * destruct (stepsF_impl_stepF _ _ H8) as [?t2' [?s2' []]].
        eapply EF_step; eauto.
        eapply H6; eauto.
        respects; eapply sep_r; eauto.
    + punfold H2; red in X, H2; dependent induction H2.
      1-2: destruct x; inv X.
      * destruct (stepsF_impl_stepF _ _ H2) as [?t1' [?s1' []]].
        eapply EF_step; eauto.
        eapply H5; eauto.
        respects; eapply sep_r; eauto.
      * eapply (IHEU p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- pfold; red; eapply H4; eauto.
        -- eapply step_no_errors; eauto.
      * destruct (H5 _ _ X) as [?t1' [?s1' [? []]]].
        eapply EF_step; eauto.
        eapply (IHEU p'); pclearbot; eauto.
        -- respects; eapply sep_r; eauto.
        -- eapply step_no_errors; eauto.
Qed.


(** * Definition of our fragment of CTL **)

Inductive CTLformula {S R} : Type :=
| CTL_st (P:S -> Prop)
| CTL_and (tp1 tp2:CTLformula)
| CTL_or (tp1 tp2:CTLformula)
| CTL_impl (tp1 tp2:CTLformula)
| CTL_EF (tp:CTLformula)
| CTL_EG (tp:CTLformula)
| CTL_AF (tp:CTLformula)
| CTL_AG (tp:CTLformula)
| CTL_EU (tp1 tp1:CTLformula)
| CTL_AU (tp1 tp1:CTLformula)
| CTL_EReturns (P : RetPred S R)
| CTL_AReturns (P : RetPred S R).

Fixpoint CTLsats {S R} (tp:@CTLformula S R): TPred S R :=
  match tp with
  | CTL_st P => state_pred _ P
  | CTL_and tp1 tp2 => (CTLsats tp1) /2\ (CTLsats tp2)
  | CTL_or tp1 tp2 => (CTLsats tp1) \2/ (CTLsats tp2)
  | CTL_impl tp1 tp2 => (CTLsats tp1) -2> (CTLsats tp2)
  | CTL_EF tp => EF (CTLsats tp)
  | CTL_EG tp => EG (CTLsats tp)
  | CTL_AF tp => AF (CTLsats tp)
  | CTL_AG tp => AG (CTLsats tp)
  | CTL_EU tp1 tp2 => EU (CTLsats tp1) (CTLsats tp2)
  | CTL_AU tp1 tp2 => AU (CTLsats tp1) (CTLsats tp2)
  | CTL_EReturns P => EReturns P
  | CTL_AReturns P => AReturns P
  end.

Inductive CTLsim {S1 S2 R1 R2} q Q: @CTLformula S1 R1 -> @CTLformula S2 R2 -> Prop :=
| CTLsim_st P1 P2 : q_similar q P1 P2 -> CTLsim q Q (CTL_st P1) (CTL_st P2)
| CTLsim_and tp1 tp2 tp1' tp2' : CTLsim q Q tp1 tp2 -> CTLsim q Q tp1' tp2' ->
                                CTLsim q Q (CTL_and tp1 tp1') (CTL_and tp2 tp2')
| CTLsim_or tp1 tp2 tp1' tp2' : CTLsim q Q tp1 tp2 -> CTLsim q Q tp1' tp2' ->
                               CTLsim q Q (CTL_or tp1 tp1') (CTL_or tp2 tp2')
| CTLsim_impl tp1 tp2 tp1' tp2' : CTLsim q Q tp1 tp2 -> CTLsim q Q tp1' tp2' ->
                                 CTLsim q Q (CTL_impl tp1 tp1') (CTL_impl tp2 tp2')
| CTLsim_EF tp1 tp2 : CTLsim q Q tp1 tp2 -> CTLsim q Q (CTL_EF tp1) (CTL_EF tp2)
| CTLsim_EG tp1 tp2 : CTLsim q Q tp1 tp2 -> CTLsim q Q (CTL_EG tp1) (CTL_EG tp2)
| CTLsim_AF tp1 tp2 : CTLsim q Q tp1 tp2 -> CTLsim q Q (CTL_AF tp1) (CTL_AF tp2)
| CTLsim_AG tp1 tp2 : CTLsim q Q tp1 tp2 -> CTLsim q Q (CTL_AG tp1) (CTL_AG tp2)
| CTLsim_EU tp1 tp2 tp1' tp2' : CTLsim q Q tp1 tp2 -> CTLsim q Q tp1' tp2' ->
                               CTLsim q Q (CTL_EU tp1 tp1') (CTL_EU tp2 tp2')
| CTLsim_AU tp1 tp2 tp1' tp2' : CTLsim q Q tp1 tp2 -> CTLsim q Q tp1' tp2' ->
                               CTLsim q Q (CTL_AU tp1 tp1') (CTL_AU tp2 tp2')
| CTLsim_EReturns P1 P2 : eq_sat_sep_ret q Q P1 P2 ->
                         CTLsim q Q (CTL_EReturns P1) (CTL_EReturns P2)
| CTLsim_AReturns P1 P2 : eq_sat_sep_ret q Q P1 P2 ->
                         CTLsim q Q (CTL_AReturns P1) (CTL_AReturns P2)
.

Lemma tpsim_implies_eq_sat_sep_sbuter {S1 S2 R1 R2} q Q TP1 TP2:
  CTLsim q Q TP1 TP2 -> @eq_sat_sep_sbuter S1 S2 R1 R2 q Q (CTLsats TP1) (CTLsats TP2).
Proof.
  intro tp_sim; induction tp_sim.
  - apply eq_sat_state_preds; eauto.
  - apply eq_sat_and; eauto.
  - apply eq_sat_or; eauto.
  - apply eq_sat_impl; eauto.
  - apply eq_sat_EF; eauto.
  - apply eq_sat_EG; eauto.
  - apply eq_sat_AF; eauto.
  - apply eq_sat_AG; eauto.
  - apply eq_sat_EU; eauto.
  - apply eq_sat_AU; eauto.
  - apply eq_sat_EReturns; eauto.
  - apply eq_sat_AReturns; eauto.
Qed.

Theorem sbuter_preserves_tpreds {S1 R1 S2 R2} p q Q t1 s1 t2 s2 TP1 TP2:
  @sbuter S1 R1 S2 R2 p Q t1 s1 t2 s2 -> no_errors t2 s2 ->
  CTLsim q Q TP1 TP2 -> pre (p ** q) (s1, s2) ->
  CTLsats TP1 t1 s1 <-> CTLsats TP2 t2 s2.
Proof.
  intros sb ne tp_sim pre_pq. destruct pre_pq as [ pre_p [ pre_q sep ]].
  eapply (tpsim_implies_eq_sat_sep_sbuter q Q TP1 TP2 tp_sim); eauto.
Qed.
