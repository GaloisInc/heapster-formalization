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

Section bisim.

  (** * `sceE` and `CompM` **)

  Variant modifyE C : Type -> Type :=
  | Modify : forall (f : C -> C), modifyE C C.
  Global Arguments Modify {C} f.

  Definition sceE (C : Type) := (exceptE unit +' modifyE C +' nondetE).

  Definition CompM S R := itree (sceE S) R.
  Definition CompM' S R := itree' (sceE S) R.

  Definition TPred S R := CompM S R -> S -> Prop.
  Definition TPred' S R := CompM' S R -> S -> Prop.

  (** * `no_errors` **)

  Inductive no_errors_genF {S R : Type} no_errors : TPred' S R :=
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

  Definition no_errors {S R} : TPred S R := paco2 no_errors_gen bot2.

  Lemma no_errors_gen_mon {S R} : monotone2 (@no_errors_gen S R).
  Proof.
    repeat intro. unfold no_errors_gen in *.
    inversion IN; subst; try solve [constructor; auto].
  Qed.
  Hint Resolve no_errors_gen_mon : paco.

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

  (** * `steps` and `stops` **)

  (* The proposition that an itree has a next step *)

  Inductive stepsF {S R} : TPred' S R :=
  | steps_tau t s : stepsF (observe t) s -> stepsF (TauF t) s
  | steps_modify f k s : stepsF (VisF (subevent _ (Modify f)) k) s
  | steps_choice k s : stepsF (VisF (subevent _ Or) k) s.
  Hint Constructors stepsF : core.

  Definition steps {S R} : TPred S R :=
    fun t s => @stepsF S R (observe t) s.
  Hint Unfold steps : core.

  (* The proposition that an itree has no next step *)

  Inductive stops_genF {S R} stops : TPred' S R :=
  | stops_gen_tau t s : stops t s -> stops_genF stops (TauF t) s
  | stops_gen_ret r s : stops_genF stops (RetF r) s
  | stops_gen_err k s : stops_genF stops (VisF (subevent _ (Throw tt)) k) s.
  Hint Constructors stops_genF : core.

  Definition stops_gen {S R} stops t s := @stops_genF S R stops (observe t) s.
  Hint Unfold stops_gen : core.

  Definition stops {S R} : TPred S R := paco2 stops_gen bot2.

  Lemma stops_gen_mon {S R} : monotone2 (@stops_gen S R).
  Proof.
    repeat intro. unfold stops_gen in *.
    inversion IN; subst; try solve [constructor; auto].
  Qed.
  Hint Resolve stops_gen_mon : paco.

  (** * `step` **)

  Inductive stepF {S R} : CompM' S R -> S -> CompM' S R -> S -> Type :=
  | step_tau t s t' s' : stepF (observe t) s t' s' -> stepF (TauF t) s t' s'
  | step_modify f k s : stepF (VisF (subevent _ (Modify f)) k) s (observe (k s)) (f s)
  | step_choice b k s : stepF (VisF (subevent _ Or) k) s (observe (k b)) s.

  Definition step {S R} : CompM S R -> S -> CompM S R -> S -> Type :=
    fun t s t' s' => stepF (observe t) s (observe t') s'.
  Hint Unfold step : core.

  (* If `steps t s` then there exists a step from `(t,s)` *)
  Lemma steps_impl_step {S R} (t : CompM S R) s :
    steps t s -> exists t' s', inhabited (step t s t' s').
  Proof.
    intro; unfold steps, step in *.
    induction H.
    - destruct IHstepsF as [t' [s' []]].
      exists t', s'.
      apply inhabits; constructor; eauto.
    - exists (k s), (f s).
      apply inhabits; constructor.
    - exists (k false), s.
      apply inhabits; constructor.
  Qed.

  (* If `stops t s` then there exist no steps from `(t,s)` *)
  Lemma stops_impl_no_step {S R} (t : CompM S R) s :
    stops t s -> forall t' s', step t s t' s' -> False.
  Proof.
    intros; punfold H; unfold stops_gen, step in *.
    induction X; inv H.
    apply IHX.
    pclearbot; punfold H1.
  Qed.

  (* If there exists a step from `(t,s)` then `steps t s` *)
  Lemma step_impl_steps {S R} (t : CompM S R) s t' s' :
    step t s t' s' -> steps t s.
  Proof.
    intro; unfold step, steps in *.
    induction X; constructor; eauto.
  Qed.

  (* If there exists a step from `(t,s)` then `stops t s` does not hold *)
  Lemma step_impl_not_stops {S R} (t : CompM S R) s t' s' :
    step t s t' s' -> (stops t s -> False).
  Proof.
    intros; punfold H; unfold step, stops_gen in *.
    induction X; inv H.
    apply IHX.
    pclearbot; punfold H1.
  Qed.

  (** * `sbuter` **)

  Definition eutt' {E R} r (t : itree' E R) (t' : itree' E R) :=
    eqitF r true true id (eutt r) t t'.

  Lemma eutt_iff_eutt' {E R} r t t' :
    eutt r t t' <-> @eutt' E R r (observe t) (observe t').
  Proof.
    split; intro.
    - punfold H; induction H; pclearbot; constructor; eauto.
    - pfold; unfold eqit_; induction H; constructor; eauto.
      intro; specialize (REL v).
      unfold id in *; eauto.
   Qed.

  Inductive sbuter_genF {S1 S2 R1 R2 : Type} sbuter (p : perm)
            (Q : R1 -> R2 -> Perms) (t1 : CompM' S1 R1) s1 (t2 : CompM' S2 R2) s2 : Prop :=
  | sbuter_gen_ret r1 r2 :
      pre p (s1, s2) ->
      p ∈ Q r1 r2 ->
      eutt' eq t1 (RetF r1) ->
      eutt' eq t2 (RetF r2) ->
      sbuter_genF sbuter p Q t1 s1 t2 s2
  | sbuter_gen_err k :
      eutt' eq t2 (VisF (subevent _ (Throw tt)) k) ->
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

  Definition sbuter_gen {S1 S2 R1 R2} sbuter p Q :
    CompM S1 R1 -> S1 -> CompM S2 R2 -> S2 -> Prop :=
    fun t1 s1 t2 s2 => sbuter_genF sbuter p Q (observe t1) s1 (observe t2) s2.

  Definition sbuter {S1 S2 R1 R2} := paco6 (@sbuter_gen S1 S2 R1 R2) bot6.

  Lemma sbuter_gen_mon {S1 S2 R1 R2} : monotone6 (@sbuter_gen S1 S2 R1 R2).
  Proof.
    repeat intro. unfold sbuter_gen in *.
    induction IN; subst; try solve [econstructor; eauto]; auto.
    econstructor 5; eauto; intros.
    - destruct (H3 t1' s1' X) as [t2' [s2' [X' [? ?]]]].
      exists t2', s2', X'; eauto.
    - destruct (H4 t2' s2' X) as [t1' [s1' [X' [? ?]]]].
      exists t1', s1', X'; eauto.
  Qed.
  Hint Resolve sbuter_gen_mon : paco.
