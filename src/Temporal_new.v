From Heapster Require Import
     Permissions
     Config
     NoEvent
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
     Eq.Eq
     Interp.Interp
     Interp.InterpFacts.

From Paco Require Import
     paco.

Import ITreeNotations.

Hint Resolve no_errors_gen_mon : paco.
Hint Resolve sbuter_gen_mon : paco.


(** * `eq_sat_sep_sbuter` **)

Definition TPred S R := CompM S R -> S -> Prop.
Definition TPred' S R := CompM' S R -> S -> Prop.

Definition eq_sat_sep_sbuter {S1 S2 R1 R2} (q:@perm (S1*S2))
  (P1:TPred S1 R1) (P2:TPred S2 R2) :=
  forall p Q t1 s1 t2 s2, pre q (s1,s2) -> p ⊥ q ->
    sbuter p Q t1 s1 t2 s2 -> no_errors t2 s2 ->
    (P1 t1 s1 <-> P2 t2 s2).
Hint Unfold eq_sat_sep_sbuter.


(** * `eq_sat_sep_sbuter` for state predicates **)

Definition state_pred {S} R P : TPred S R := fun '_ s => P s.

Definition q_similar {S1 S2} q (P1 : S1 -> Prop) (P2 : S2 -> Prop): Prop :=
  forall s1 s2, pre q (s1,s2) -> (P1 s1 <-> P2 s2).

Lemma eq_sat_state_preds {S1 S2 R1 R2} q (P1 : S1 -> Prop) (P2 : S2 -> Prop)
  : q_similar q P1 P2 ->
    eq_sat_sep_sbuter q (state_pred R1 P1) (state_pred R2 P2).
Proof. intros; eauto. Qed.


(** * `eq_sat_sep_sbuter` for logical connectives **)

Lemma eq_sat_and {S1 S2 R1 R2} q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q TP1 TP2 -> eq_sat_sep_sbuter q TP1' TP2' ->
    eq_sat_sep_sbuter q (TP1 /2\ TP1') (TP2 /2\ TP2').
Proof.
  intros esss esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.

Lemma eq_sat_or {S1 S2 R1 R2} q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q TP1 TP2 -> eq_sat_sep_sbuter q TP1' TP2' ->
    eq_sat_sep_sbuter q (TP1 \2/ TP1') (TP2 \2/ TP2').
Proof.
  intros esss esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.

Notation "p -2> q" :=
  (fun x0 x1 => p x0 x1 -> q x0 x1)
  (at level 50, no associativity).

Lemma eq_sat_impl {S1 S2 R1 R2} q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q TP1 TP2 -> eq_sat_sep_sbuter q TP1' TP2' ->
    eq_sat_sep_sbuter q (TP1 -2> TP1') (TP2 -2> TP2').
Proof.
  intros esss esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.


(** * `eq_sat_sep_sbuter` for `EU`  **)

Inductive EU {S R} (P P' : TPred S R) t0 s0 : Prop :=
| EU_here : P' t0 s0 -> EU P P' t0 s0
| EU_step t1 s1 : P t0 s0 -> step t0 s0 t1 s1 -> EU P P' t1 s1 -> EU P P' t0 s0.

Lemma eq_sat_EU {S1 S2 R1 R2} q (P1 P1' : TPred S1 R1) (P2 P2' : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 -> eq_sat_sep_sbuter q P1' P2' ->
    eq_sat_sep_sbuter q (EU P1 P1') (EU P2 P2').
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

Definition EF {S R} := @EU S R (fun _ _ => True).

Lemma eq_sat_EF {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (EF P1) (EF P2).
Proof. eapply eq_sat_EU; easy. Qed.


(** * `eq_sat_sep_sbuter` for `AF`  **)

Definition AG_gen {S R} (P : TPred S R) (AG : TPred S R) t0 s0 :=
  P t0 s0 /\ (forall t1 s1, step t0 s0 t1 s1 -> AG t1 s1).

Definition AG {S R} P := paco2 (@AG_gen S R P) bot2.

Lemma is_path_gen_mon {S R P} : monotone2 (@AG_gen S R P).
Proof. repeat intro; induction IN; econstructor; eauto. Qed.
Hint Resolve is_path_gen_mon : paco.

Lemma eq_sat_AG {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (AG P1) (AG P2).
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
