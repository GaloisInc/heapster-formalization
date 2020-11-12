From Heapster Require Import
     Permissions
     Config
     NoEvent
     Functional.

From Coq Require Import
     Program
     Program.Equality
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

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.
Import SumNotations.
Import VectorNotations.

(** * things that should probably be in Functional.v **)

Hint Resolve no_errors_gen_mon : paco.
Hint Resolve sbuter_gen_mon : paco.

Global Instance Proper_eutt_no_errors {S R} :
  Proper (eq ==> eutt eq ==> impl) (@no_errors S R).
Admitted.

Global Instance Proper_eutt_sbuter {S1 S2 R1 R2} :
  Proper (eq ==> eq ==> eutt eq ==> eq ==> eutt eq ==> eq ==> impl) (@sbuter S1 S2 R1 R2).
Admitted.

Definition CompM S R := itree (sceE S) R.
Definition TPred S R := CompM S R -> S -> Prop.

Lemma no_errors_Tau {S R} (s : S) (t : CompM S R)
  : no_errors s t <-> no_errors s (Tau t).
Proof.
  split; intro H.
  - pfold.
    apply no_errors_tau.
    left; assumption.
  - punfold H; inv H; inv H1.
    + assumption.
    + inv H.
Qed.

Lemma no_errors_Modify {S R} (s : S) f (k : S -> CompM S R) :
  no_errors (f s) (k s) <-> no_errors s (vis (Modify f) k).
Proof.
  split; intro H.
  - pfold.
    apply no_errors_modify.
    left; assumption.
  - punfold H; inv H; inv H1.
    + admit. (* Hunh? Why can't I get rid of those `existT`s...? *)
    + inv H.
Admitted.

Lemma no_errors_Choice {S R} (s : S) (k : bool -> CompM S R) :
  (forall b, no_errors s (k b)) <-> no_errors s (vis Or k).
Proof.
  split; intros.
  - pfold.
    apply no_errors_choice.
    intro b; specialize (H b).
    left; assumption.
  - punfold H; inv H.
    specialize (H1 b); inv H1.
    + admit. (* Uh oh, I've got the same problem here... *)
    + inv H.
Admitted.


(** * `eutt_closure` and lemmas **)

Inductive eutt_closure {S R} r (t1 : itree (sceE S) R) (s1 : S)
                               (t2 : itree (sceE S) R) (s2 : S) : Prop :=
| eutt_closure_ex t1' t2' :
    t1 ≈ t1' -> t2 ≈ t2' -> r t1' s1 t2' s2 -> eutt_closure r t1 s1 t2 s2.
Arguments eutt_closure_ex {S R r t1 s1 t2 s2} t1' t2'.

Definition is_eutt_closed {S R} (r : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop) :=
  Proper (eutt eq ==> eq ==> eutt eq ==> eq ==> impl) r.

Global Instance eutt_closure_is_eutt_closed {S R} r :
  Proper (eutt eq ==> eq ==> eutt eq ==> eq ==> impl) (@eutt_closure S R r).
Proof.
  intros t1 t1' eqt1 s1 s1' eqs1 t2 t2' eqt2 s2 s2' eqs2 H.
  destruct H as [t1'' t2'' eqt1' eqt2'].
  rewrite eqt1 in eqt1'; rewrite eqt2 in eqt2'.
  apply (eutt_closure_ex t1'' t2'' eqt1' eqt2').
  rewrite eqs1, eqs2 in X; exact X.
Qed.

Lemma eutt_closure_rec {S R} (r r' : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop) :
  is_eutt_closed r' -> (forall t1 s1 t2 s2, r t1 s1 t2 s2 -> r' t1 s1 t2 s2) ->
  forall t1 s1 t2 s2, eutt_closure r t1 s1 t2 s2 -> r' t1 s1 t2 s2.
Proof.
  intros.
  destruct H1.
  apply H0 in H3.
  eapply H.
  5: exact H3.
  all: easy.
Qed.

Lemma eutt_closure_Tau_L {S R} r t1 s1 t2 s2 :
  @eutt_closure S R r t1 s1 t2 s2 <-> @eutt_closure S R r (Tau t1) s1 t2 s2.
Proof.
  split; rewrite tau_eutt; easy.
Qed.


(** * `eutt_or_closure` and lemmas **)

Inductive euttOr_closure' {S R} (r : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop) :
  itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop :=
| euttOr_closure'_rel t1 s1 t2 s2 :
    r t1 s1 t2 s2 -> euttOr_closure' r t1 s1 t2 s2
| euttOr_closure'_or b t1' t2' k s1 t2 s2 :
    k b ≈ t1' -> t2 ≈ t2' -> euttOr_closure' r t1' s1 t2' s2 -> euttOr_closure' r (vis Or k) s1 t2 s2.
Arguments euttOr_closure'_rel {S R r} t1 s1 t2 s2.
Arguments euttOr_closure'_or {S R r} b t1' t2' k s1 t2 s2.

Definition euttOr_closure {S R} r := @eutt_closure S R (euttOr_closure' r).

Global Instance euttOr_closure_is_eutt_closed {S R} r :
  Proper (eutt eq ==> eq ==> eutt eq ==> eq ==> impl) (@euttOr_closure S R r).
Proof. apply eutt_closure_is_eutt_closed. Qed.

Definition euttOr_closure_rel {S R} (r : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop)
                              t1 s1 t2 s2 :
  r t1 s1 t2 s2 -> @euttOr_closure S R r t1 s1 t2 s2.
Proof.
  intro.
  apply (eutt_closure_ex t1 t2); try reflexivity.
  apply euttOr_closure'_rel; assumption.
Defined.

Definition is_Or_closed {S R} (r : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop) :=
  forall b k s1 t2 s2, r (k b) s1 t2 s2 -> r (vis Or k) s1 t2 s2.

Definition euttOr_closure_or {S R r} b k s1 t2 s2 :
  euttOr_closure r (k b) s1 t2 s2 -> @euttOr_closure S R r (vis Or k) s1 t2 s2.
Proof.
  intro.
  apply (eutt_closure_ex (vis Or k) t2); try reflexivity.
  destruct H as [t1' t2'].
  apply (euttOr_closure'_or b t1' t2'); easy.
Defined.

Definition euttOr_closure_rec {S R}
           (r r' : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop) :
  is_eutt_closed r' -> is_Or_closed r' ->
  (forall t1 s1 t2 s2, r t1 s1 t2 s2 -> r' t1 s1 t2 s2) ->
  forall t1 s1 t2 s2, euttOr_closure r t1 s1 t2 s2 -> r' t1 s1 t2 s2.
Proof.
  intros euttC OrC H.
  apply eutt_closure_rec; [ assumption | intros ].
  induction H0.
  - apply H; assumption.
  - apply (OrC b).
    eapply euttC.
    5: exact IHeuttOr_closure'.
    all: easy.
Qed.

Lemma euttOr_closure_no_errors {S R}
      (r : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop)
      (Hr : forall t s t' s', r t s t' s' -> no_errors s t -> no_errors s' t')
      t s t' s' :
  euttOr_closure r t s t' s' -> no_errors s t -> no_errors s' t'.
Proof.
  revert t s t' s'.
  apply (euttOr_closure_rec r (fun t1 s1 t2 s2 => no_errors s1 t1 -> no_errors s2 t2)).
  - cbv - [eutt no_errors]; intros; rewrite H, H0, H1, H2 in H3; auto.
  - unfold is_Or_closed; intros.
    rewrite <- no_errors_Choice in H0.
    apply H, H0.
  - intros.
    eapply (Hr t1 s1); assumption.
Qed.

Lemma euttOr_closure_trans_eq_l {S R} {r} {t1 s1} t2 s2 {t3 s3} :
  @euttOr_closure S R (fun t1 s1 t2 s2 => t1 = t2 /\ s1 = s2) t1 s1 t2 s2 ->
  @euttOr_closure S R r t2 s2 t3 s3 ->
  @euttOr_closure S R r t1 s1 t3 s3.
Proof.
  intros [t1' t2' eqt1 eqt2] [t2'' t3' eqt2' eqt3].
  rewrite eqt1, eqt3; clear t1 eqt1 t3 eqt3.
  rewrite eqt2 in eqt2'; clear t2 eqt2.
  induction H.
  - destruct H0.
    + destruct H.
      rewrite H, eqt2', H1.
      apply euttOr_closure_rel; assumption.
    + destruct H.
      rewrite H, eqt2', H3.
      apply (euttOr_closure_or b).
      refine (eutt_closure_ex t1' t2' _ _ _); assumption.
  - apply (euttOr_closure_or b).
    rewrite H1 in eqt2'; clear t2 H1.
    rewrite H; clear H.
    apply IHeuttOr_closure'; assumption.
Qed.


(** * `steps_to` and lemmas **)

(* Inductive steps_to' {S R} : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop := *)
(* | steps_to'_modify f k s : steps_to' (vis (Modify f) k) s (k s) (f s) *)
(* | steps_to'_or b k s1 t2 s2 : steps_to' (k b) s1 t2 s2 -> steps_to' (vis Or k) s1 t2 s2. *)

(* Definition steps_to {S R} t1 s1 t2 s2 := *)
(*   exists t1' t2', t1 ≈ t1' /\ t2 ≈ t2' /\ @steps_to' S R t1' s1 t2' s2. *)

Inductive steps_to' {S R} : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop :=
| steps_to'_modify f k s : steps_to' (vis (Modify f) k) s (k s) (f s).

Definition steps_to {S R} := @euttOr_closure S R steps_to'.

Global Instance steps_to_is_eutt_closed {S R} :
  Proper (eutt eq ==> eq ==> eutt eq ==> eq ==> impl) (@steps_to S R).
Proof. apply euttOr_closure_is_eutt_closed. Qed.

Definition steps_to_modify {S R} f k s : @steps_to S R (vis (Modify f) k) s (k s) (f s).
Proof. apply euttOr_closure_rel; constructor. Defined.

Lemma no_errors_steps_to {S R} (t : CompM S R) s (t' : CompM S R) s' :
  steps_to t s t' s' -> no_errors s t -> no_errors s' t'.
Proof.
  revert t s t' s'; apply euttOr_closure_no_errors; intros.
  destruct H.
  apply no_errors_Modify; assumption.
Qed.


(** * `no_steps_to` and lemmas **)

(* The proposition that there are no steps between `(t0,s0)` and `(tf,sf)`,
   i.e. that `s0 = sf` and `t0` is different from `tf` only by `eutt` and `Or` events *)
Definition no_steps_to {S R} := @euttOr_closure S R (fun t1 s1 t2 s2 => t1 = t2 /\ s1 = s2).

Definition no_steps_to_refl {S R} t1 s1 : @no_steps_to S R t1 s1 t1 s1.
Proof. apply euttOr_closure_rel; easy. Defined.

Lemma no_steps_to_trans {S R} {t1 s1} t2 s2 {t3 s3} :
  @no_steps_to S R t1 s1 t2 s2 -> @no_steps_to S R t2 s2 t3 s3 -> @no_steps_to S R t1 s1 t3 s3.
Proof. apply euttOr_closure_trans_eq_l. Qed.

Lemma no_errors_no_steps_to {S R} (t : CompM S R) s (t' : CompM S R) s' :
  no_steps_to t s t' s' -> no_errors s t -> no_errors s' t'.
Proof.
  revert t s t' s'; apply euttOr_closure_no_errors; intros.
  destruct H.
  rewrite <- H, <- H1; assumption.
Qed.

Definition no_steps_to_eqs {S R t1 s1 t2 s2} : @no_steps_to S R t1 s1 t2 s2 -> s1 = s2.
Proof.
  destruct 1; clear H H0.
  revert t1' t2' H1; induction 1; intros; easy.
Qed.


(** * `is_path` and lemmas **)

(* The proposition that there are `n` or `n+1` steps from (t0,s0) to (tf,sf),
   i.e. `(t0,s0) steps_to ... (ti,si) ... steps_to (tn,sn) steps_to (tf,sf)` or
        `(t0,s0) steps_to ... (ti,si) ... steps_to (tn,sn) no_steps_to (tf,sf)`. *)
Fixpoint is_path {S R} n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :=
  match ts with
  | [] => no_steps_to t0 s0 tf sf \/ steps_to t0 s0 tf sf
  | (t,s) :: ts' => steps_to t0 s0 t s /\ is_path _ t s ts' tf sf
  end.

Lemma is_path_Tau_l {S R} n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  is_path n t0 s0 ts tf sf <-> is_path n (Tau t0) s0 ts tf sf.
Proof.
  destruct ts; [|destruct h]; simpl.
  - now unfold is_path, no_steps_to, steps_to, euttOr_closure; do 2 rewrite <- eutt_closure_Tau_L.
  - now unfold steps_to, euttOr_closure; rewrite <- eutt_closure_Tau_L.
Defined.

Lemma no_steps_is_path {S R} n t s t0 s0 ts tf sf :
  no_steps_to t s t0 s0 -> is_path n t0 s0 ts tf sf -> @is_path S R n t s ts tf sf.
Proof.
  destruct ts; [|destruct h]; simpl.
  - destruct 2.
    + now left; apply (no_steps_to_trans t0 s0).
    + now right; apply (euttOr_closure_trans_eq_l t0 s0).
  - intros ? [? ?]; split.
    + eapply euttOr_closure_trans_eq_l.
      apply H. apply H0.
    + assumption.
Qed.

Lemma no_errors_is_path {S R} n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  is_path n t0 s0 ts tf sf -> no_errors s0 t0 -> no_errors sf tf.
Proof.
  revert t0 s0; induction ts; [|destruct h]; simpl; intros; destruct H.
  - apply (no_errors_no_steps_to t0 s0); assumption.
  - apply (no_errors_steps_to t0 s0); assumption.
  - apply (IHts c s); try assumption.
    apply (no_errors_steps_to t0 s0); assumption.
Qed.


(** * `sbuter_ex` and lemmas **)

Definition sbuter_ex {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t2 s2 :=
  exists p', sep_step p p' /\ sbuter p' Q t1 s1 t2 s2.

Global Instance Proper_sbuter_ex {S1 S2 R1 R2} :
  Proper (sep_step --> eq ==> eutt eq ==> eq ==> eutt eq ==> eq ==> impl)
         (@sbuter_ex S1 S2 R1 R2).
Proof.
  intros p q step_p_q Q Q' eqQ t1 t1' eqt1 s1 s1'
         eqs1 t2 t2' eqt2 s2 s2' eqs2 [q' [step_q'_q' H]].
  exists q'; split.
  - now transitivity p.
  - now rewrite eqQ, eqt1, eqs1, eqt2, eqs2 in H.
Qed.


(** * `steps_to_sbuter_l` and `steps_to_sbuter_r`  **)

(* A picture for the following lemma, where the diagonal and horizontal lines in
   the middle are sbuter and the vertical lines on the sides are steps_to.
            (t4,s4)
          ⋰   ⋮
   (t2,s2)  (ti,si)
      |   ⋰   ⋮
   (t1,s1)~~(t3,s3)
 *)

Definition sbuter_impl_path_r {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms)
                              t1 s1 t2 s2 t3 s3 :=
  sbuter p Q t1 s1 t3 s3 ->
  exists n (ts : Vector.t (CompM S2 R2 * S2) n) t4 s4,
    is_path n t3 s3 ts t4 s4 /\
    (forall i, sbuter_ex p Q t1 s1 (fst ts[@i]) (snd ts[@i]) /\
               guar p (s1, s3) (s1, snd ts[@i])) /\
    sbuter_ex p Q t2 s2 t4 s4 /\ guar p (s1, s3) (s2, s4).

Lemma steps_to'_sbuter_l {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 -> steps_to' t1 s1 t2 s2 -> sbuter_impl_path_r p Q t1 s1 t2 s2 t3 s3.
Proof.
  intros ne3 Ht Hb; destruct Ht.
  punfold Hb; dependent induction Hb.
  (* sbuter_gen_err *)
  - punfold ne3; inv ne3.
  (* sbuter_gen_tau_R *)
  - apply no_errors_Tau in ne3.
    specialize (IHHb ne3 f k JMeq_refl eq_refl).
    destruct IHHb as [n [ts [t4 [s4 ?]]]].
    exists n; exists ts; exists t4; exists s4; split.
    + rewrite <- is_path_Tau_l; easy.
    + easy.
  (* sbuter_gen_modify_L *)
  - exists 0; exists []; exists t2; exists c2. split; [|split; [|split]].
    + left; apply no_steps_to_refl.
    + inversion i.
    + exists p'; split; [|pfold]; assumption.
    + assumption.
  (* sbuter_gen_modify_R *)
  - apply no_errors_Modify in ne3.
    specialize (IHHb ne3 f k JMeq_refl eq_refl).
    destruct IHHb as [n [ts [t4 [s4 [? [? [? ?]]]]]]].
    exists (S n); exists ((k0 c2, f0 c2) :: ts); exists t4; exists s4; split; [|split; [|split]].
    + split; try assumption.
      apply steps_to_modify.
    + dependent destruction i; simpl.
      * split.
        -- exists p'; split; try assumption.
           pfold; assumption.
        -- assumption.
      * specialize (H3 i); destruct H3; split.
        -- rewrite H1; assumption.
        -- rewrite H0.
           apply (sep_step_guar p p'); assumption.
     + rewrite H1; assumption.
     + rewrite H0.
       apply (sep_step_guar p p'); assumption.
   (* sbuter_gen_modify *)
  - exists 0; exists []; exists (k2 c2); exists (f2 c2); split; [|split; [|split]].
    + right; apply steps_to_modify.
    + inversion i.
    + exists p'; pclearbot; easy.
    + assumption.
  (* sbuter_gen_choice_R *)
  - rewrite <- no_errors_Choice in ne3.
    specialize (H1 false); specialize (ne3 false).
    specialize (H2 false ne3 f k JMeq_refl eq_refl).
    destruct H2 as [n [ts [t4 [s4 [? [? [? ?]]]]]]].
    exists n; exists ts; exists t4; exists s4; split; [|split; [|split]].
    + apply (no_steps_is_path _ _ _ (k0 false) c2); try assumption.
      apply (euttOr_closure_or false), no_steps_to_refl.
    + intro i; specialize (H3 i).
      destruct H3; split.
      * rewrite H0; assumption.
      * apply (sep_step_guar p p'); assumption.
    + rewrite H0; assumption.
    + apply (sep_step_guar p p'); assumption.
Qed.

Lemma steps_to_sbuter_l {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 -> steps_to t1 s1 t2 s2 -> sbuter_impl_path_r p Q t1 s1 t2 s2 t3 s3.
Proof.
  intro; revert t1 s1 t2 s2.
  eapply (euttOr_closure_rec _ (fun t1 s1 t2 s2 =>  sbuter_impl_path_r p Q t1 s1 t2 s2 t3 s3)).
  - cbv - [eutt sbuter_impl_path_r]; intros t1 t1' eqt1 s1 s1' eqs1 t2 t2' eqt2 s2 s2' eqs2 ?.
    rewrite <- eqs1, <- eqs2; clear s1' s2' eqs1 eqs2.
    admit.
  - unfold is_Or_closed; intros.
    admit.
  - intros; apply steps_to'_sbuter_l; assumption.
Admitted.

Definition sbuter_impl_path_l {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms)
                              t1 s1 t3 s3 t4 s4 :=
  sbuter p Q t1 s1 t3 s3 ->
  exists n (ts : Vector.t (CompM S1 R1 * S1) n) t2 s2,
    is_path n t1 s1 ts t2 s2 /\
    (forall i, sbuter_ex p Q (fst ts[@i]) (snd ts[@i]) t3 s3 /\
               guar p (s1, s3) (snd ts[@i], s3)) /\
    sbuter_ex p Q t2 s2 t4 s4 /\ guar p (s1, s3) (s2, s4).

Lemma steps_to_sbuter_r {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t3 s3 t4 s4 :
  no_errors s3 t3 -> steps_to t3 s3 t4 s4 -> sbuter_impl_path_l p Q t1 s1 t3 s3 t4 s4.
Admitted.


(** * `is_no_step_invariant` and basic facts  **)

Definition is_no_step_invariant {S R} (P : TPred S R) :=
  is_eutt_closed (fun t1 s1 t2 s2 => P t1 s1 <-> P t2 s2) /\
  is_Or_closed   (fun t1 s1 t2 s2 => P t1 s1 <-> P t2 s2).

Lemma is_no_step_invariant_no_steps {S R} (P : TPred S R) t1 s1 t2 s2 :
  is_no_step_invariant P ->
  no_steps_to t1 s1 t2 s2 -> P t1 s1 <-> P t2 s2.
Proof.
  intros [? ?]; revert t1 s1 t2 s2.
  apply (euttOr_closure_rec _ (fun t1 s1 t2 s2 => P t1 s1 <-> P t2 s2)).
  - assumption.
  - assumption.
  - intros ? ? ? ? [? ?].
    rewrite H1, H2; reflexivity.
Qed.


(** * `eq_sat_sep_sbuter` and basic facts  **)

Definition eq_sat_sep_sbuter {S1 S2 R1 R2} (q:@perm (S1*S2))
  (P1:TPred S1 R1) (P2:TPred S2 R2) :=
  forall p Q t1 s1 t2 s2, pre q (s1,s2) -> separate p q ->
    sbuter p Q t1 s1 t2 s2 -> no_errors s2 t2 ->
    (P1 t1 s1 <-> P2 t2 s2).

Definition state_pred {S} R P : TPred S R := fun _ s => P s.

Lemma eq_sat_state_preds {S1 S2 R1 R2} q (P1 : S1 -> Prop) (P2 : S2 -> Prop)
  : (forall s1 s2, pre q (s1,s2) -> (P1 s1 <-> P2 s2)) ->
    eq_sat_sep_sbuter q (state_pred R1 P1) (state_pred R2 P2).
Proof.
  unfold eq_sat_sep_sbuter; intros.
  apply H; assumption.
Qed.


(** * `EF` and lemmas  **)

Inductive EF {S R} (P : TPred S R) : TPred S R :=
| EF_refl t s : P t s -> EF P t s
| EF_step t s t' s' : steps_to t s t' s' -> EF P t' s' -> EF P t s.
Arguments EF_refl {S R P} t s.
Arguments EF_step {S R P t s} t' s'.

Lemma EF_path {S1 R1 P} n t0 s0 (ts : Vector.t (CompM S1 R1 * S1) n) tf sf :
  is_no_step_invariant P ->
  is_path n t0 s0 ts tf sf -> EF P tf sf -> EF P t0 s0.
Proof.
  intros.
  revert t0 s0 H0; induction ts; [|destruct h]; intros.
  - destruct H0, H1.
    + apply EF_refl.
      now rewrite (is_no_step_invariant_no_steps P t0 s0 t s).
    + apply (euttOr_closure_trans_eq_l (t1:=t0) (s1:=s0) t s) in H1; try assumption.
      apply (EF_step t' s'); assumption.
    + apply (EF_step t s); try assumption.
      apply EF_refl; assumption.
    + apply (EF_step t s); try assumption.
      apply (EF_step t' s'); assumption.
  - destruct H0.
    apply (EF_step c s); try assumption.
    apply IHts; assumption.
Qed.


(** * `eq_sat_EF`  **)

Lemma eq_sat_EF {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2)
  : is_no_step_invariant P1 -> is_no_step_invariant P2 ->
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (EF P1) (EF P2).
Proof.
  intros invar1 invar2; split; intros.
  - revert H4 p t2 s2 H0 H1 H2 H3.
    induction 1 as [t1 s1 | t1 s1 t1' s1']; intros.
    + apply (EF_refl t2 s2).
      apply (H p Q t1 s1 t2 s2); assumption.
    + pose proof (steps_to_sbuter_l _ _ _ _ _ _ _ _ H5 H0 H3).
      destruct H6 as [n [ts [t2' [s2' [? [? [? ?]]]]]]].
      apply (EF_path n t2 s2 ts t2' s2'); try assumption.
      destruct H8 as [p' [? ?]].
      apply (IHEF p').
      * admit. (* need lemma about steps_to, is_path, sbuter, and pre *)
      * apply H8; assumption.
      * assumption.
      * apply (no_errors_is_path _ t2 s2 ts t2' s2'); assumption.
  - revert H4 p t1 s1 H0 H1 H2 H3.
    induction 1 as [t2 s2 | t2 s2 t2' s2']; intros.
    + apply (EF_refl t1 s1).
      apply (H p Q t1 s1 t2 s2); assumption.
    + pose proof (steps_to_sbuter_r _ _ _ _ _ _ _ _ H5 H0 H3).
      destruct H6 as [n [ts [t1' [s1' [? [? [? ?]]]]]]].
      apply (EF_path n t1 s1 ts t1' s1'); try assumption.
      destruct H8 as [p' [? ?]].
      apply (IHEF p').
      * admit. (* need lemma about steps_to, is_path, sbuter, and pre *)
      * apply H8; assumption.
      * assumption.
      * apply (no_errors_steps_to t2 s2 t2' s2'); assumption.
Admitted.


(** * `AG` and lemmas  **)

Definition AG_gen {S R} (AG : TPred S R -> TPred S R) (P : TPred S R) : TPred S R :=
  fun t1 s1 => P t1 s1 /\ (forall t2 s2, steps_to t1 s1 t2 s2 -> AG P t2 s2).

Definition AG {S R} : TPred S R -> TPred S R := paco3 AG_gen bot3.

Lemma AG_gen_mon {S R} : monotone3 (@AG_gen S R).
Admitted.
Hint Resolve AG_gen_mon : paco.


(** * `eq_sat_AG`  **)

Lemma eq_sat_AG {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2)
  : eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (AG P1) (AG P2).
Proof.
  split.
  - pcofix CIH.
Admitted.


(*

Definition traceE S := (exceptE unit +' writerE S).

Definition trace S R := itree (traceE S) R.

(* Trivial instances for `trace` *)
Instance Functor_trace {S} : Functor (trace S) := Functor_itree.
Instance Monad_trace {S} : Monad (trace S) := Monad_itree.
Instance MonadIter_trace {S} : MonadIter (trace S) := MonadIter_itree.


Print subevent.


(** * old stuff with StTraceM and interpSet **)

Definition StTraceM S := stateT (S * Stream bool) (trace S).

(* Trivial instances for `StTraceM` *)
Instance Functor_StTraceM {S} : Functor (StTraceM S) := Functor_stateT.
Instance Monad_StTraceM {S} : Monad (StTraceM S) := Monad_stateT.
Instance MonadIter_StTraceM {S} : MonadIter (StTraceM S) := MonadIter_stateT0.

Open Scope sum_scope.

Definition handleTr {S} : sceE S ~> StTraceM S := fun _ e st =>
  match e with
  | ( t |)  => match t with
               | Throw _ => throw tt
               end
  | (| m |) => match m, st with
               | Modify f, (s, bs) => tell (f s) >>= fun _ => Ret (f s, bs, f s)
               end
  | (|| o ) => match o, st with
               | Or, (s, Cons b bs) => Ret (s, bs, b)
               end
  end.

Definition interpTr {S} : itree (sceE S) ~> StTraceM S := interp_state handleTr.

(* Unfolding of [interpTr] *)
Definition _interpTr {S} R (t : itreeF (sceE S) R _) : StTraceM S R :=
  match t with
  | RetF r => ret r
  | TauF t => fun s => Tau (interpTr R t s)
  | VisF e k => bind (handleTr _ e) (fun x s => Tau (interpTr R (k x) s))
  end.

(* Unfolding lemma for [interpTr] *)
Lemma unfold_interpTr {S} R (t : itree (sceE S) R) s :
  interpTr R t s ≅ _interpTr R (observe t) s.
Proof.
  rewrite (unfold_interp_state handleTr t s).
  destruct observe; reflexivity.
Qed.

Goal forall {S R} f k (s : S) o,
  interpTr R (vis (Modify f) k) (s,o) ≅
   vis (Tell (f s)) (fun _ => Tau (interpTr R (k (f s)) (f s, o))).
Proof.
  intros.
  rewrite unfold_interpTr; cbn.
  rewrite unfold_bind; cbn.
  apply eqit_Vis; intros [].
  rewrite unfold_bind; cbn.
  reflexivity.
Qed.

Definition interpSet {S R} t s (tr: trace S (S * R)) :=
  exists o, fmap (fun '(s',_,r) => (s',r)) (interpTr R t (s,o)) ≈ tr.

(* Unfolding of [fmap] on [trace]s *)
Definition _fmap_trace {S R R'} (f : R -> R') (tr : itree' (traceE S) R) :=
  match tr with
  | RetF r => Ret (f r)
  | TauF t => Tau (fmap f t)
  | VisF e k => Vis e (fun x => fmap f (k x))
  end.

(* Unfolding lemma for [fmap] on [trace]s *)
Definition unfold_fmap_trace {S R R'} (f : R -> R') (tr : trace S R) :
  fmap f tr ≅ _fmap_trace f (observe tr).
Proof.
  unfold fmap, Functor_trace, Functor_itree, ITree.map.
  rewrite unfold_bind.
  destruct observe; reflexivity.
Qed.

Lemma interpTr_Tau {S} R t (s:S) o :
  interpTr R (Tau t) (s,o) ≈ interpTr R t (s,o).
Proof.
  rewrite unfold_interpTr; cbn.
  apply eqit_tauL.
  reflexivity.
Qed.

Lemma interpSet_Tau {S R} t c (tr : trace S (S * R)) :
  interpSet (Tau t) c tr <-> interpSet t c tr.
Proof.
  split; intro.
  - destruct H as [o H]; exists o.
    rewrite interpTr_Tau in H.
    assumption.
  - destruct H as [o H]; exists o.
    rewrite <- interpTr_Tau in H.
    assumption.
Qed.


(** * new stuff with is_trace **)

Inductive is_trace_gen {S R} is_trace :
  itree (sceE S) R -> S -> trace S R -> Prop :=
| is_trace_ret r s :
    is_trace_gen is_trace (Ret r) s (Ret r)
| is_trace_tau_L t s tr :
    is_trace_gen is_trace t s tr ->
    is_trace_gen is_trace (Tau t) s tr
| is_trace_tau_R t s tr :
    is_trace_gen is_trace t s tr ->
    is_trace_gen is_trace t s (Tau tr)
| is_trace_tau t s tr :
    is_trace t s tr ->
    is_trace_gen is_trace (Tau t) s (Tau tr)
| is_trace_err s :
    is_trace_gen is_trace (throw tt) s (throw tt)
| is_trace_modify f kt s s' ktr :
    f s = s' -> is_trace (kt s) (f s) (ktr tt) ->
    is_trace_gen is_trace (vis (Modify f) kt) s (vis (Tell s') ktr)
| is_trace_choice kt b s tr :
    is_trace (kt b) s tr ->
    is_trace_gen is_trace (vis Or kt) s tr
.

Definition is_trace {S R} := paco3 (@is_trace_gen S R) bot3.

Lemma is_trace_gen_mon {S R} : monotone3 (@is_trace_gen S R).
Admitted.
Hint Resolve is_trace_gen_mon : paco.

(* This should hold - does the other direction also hold? *)
(* Lemma interpSet_impl_is_trace {S R} (t : itree (sceE S) R) s : *)
(*   (exists trM, interpSet t s trM) -> exists tr, is_trace t s tr. *)


Variant no_errors_tr_gen {S R : Type} no_errors_tr : trace S R -> Prop :=
| no_error_ret : forall r, no_errors_tr_gen no_errors_tr (Ret r)
| no_error_tau : forall t, no_errors_tr t -> no_errors_tr_gen no_errors_tr (Tau t)
| no_error_state : forall s k,
    no_errors_tr (k tt) ->
    no_errors_tr_gen no_errors_tr (vis (Tell s) k).

Definition no_errors_tr {R C : Type} :=
  paco1 (@no_errors_tr_gen R C) bot1.

Lemma no_errors_tr_gen_mon {S R} : monotone1 (@no_errors_tr_gen S R).
Proof.
  repeat intro. inversion IN; subst; try solve [constructor; auto].
Qed.
Hint Resolve no_errors_tr_gen_mon : paco.


Inductive ruts_gen {S1 S2 R1 R2} ruts (PS:S1 -> S2 -> Prop) (PR:S1 -> R1 -> S2 ->R2 -> Prop) :
  S1 -> trace S1 R1 -> S2 -> trace S2 R2 -> Prop :=
| ruts_ret s1 r1 s2 r2 :
    PR s1 r1 s2 r2 -> ruts_gen ruts PS PR s1 (Ret r1) s2 (Ret r2)
| ruts_tau_L s1 t1 s2 t2 :
    ruts_gen ruts PS PR s1 t1 s2 t2 ->
    ruts_gen ruts PS PR s1 (Tau t1) s2 t2
| ruts_tau_R s1 t1 s2 t2 :
    ruts_gen ruts PS PR s1 t1 s2 t2 ->
    ruts_gen ruts PS PR s1 t1 s2 (Tau t2)
| ruts_tau s1 t1 s2 t2 : ruts PS PR s1 t1 s2 t2 ->
    ruts_gen ruts PS PR s1 (Tau t1) s2 (Tau t2)
| ruts_st_L s1 s1' k1 s2 t2 :
    PS s1' s2 -> ruts_gen ruts PS PR s1' (k1 tt) s2 t2 ->
    ruts_gen ruts PS PR s1 (vis (Tell s1') k1) s2 t2
| ruts_st_R s1 t1 s2 s2' k2 :
    PS s1 s2' -> ruts_gen ruts PS PR s1 t1 s2' (k2 tt) ->
    ruts_gen ruts PS PR s1 t1 s2 (vis (Tell s2') k2)
| ruts_st s1 s1' k1 s2 s2' k2 :
    PS s1' s2' -> ruts PS PR s1' (k1 tt) s2' (k2 tt) ->
    ruts_gen ruts PS PR s1 (vis (Tell s1') k1)
                        s2 (vis (Tell s2') k2).

Definition ruts {S1 S2 R1 R2} := paco6 (@ruts_gen S1 S2 R1 R2) bot6.

Instance Proper_ruts {S1 S2 R1 R2} PS PR :
  Proper (eq ==> eutt eq ==> eq ==> eutt eq ==> impl) (@ruts S1 S2 R1 R2 PS PR).
Admitted.


Definition curry {A B C} (f:A*B->C) a b := f (a, b).

Definition outRel {S1 S2 R1 R2} Q (s1 : S1) (r1 : R1) (s2 : S2) (r2 : R2) : Prop :=
  exists q, q ∈ (Q r1 r2) /\ pre q (s1, s2).

(* is this what we want? hmm... *)
Lemma maybe_typing_soundness {S1 S2 R1 R2 : Type} (P: @Perms (S1*S2))
        (Q: R1 -> R2 -> @Perms (S1*S2)) s1 t1 s2 t2 p q :
  p ∈ P -> pre (p ** q) (s1,s2) ->
  sbuter p Q t1 s1 t2 s2 ->
  forall tr1 tr2, is_trace t1 s1 tr1 ->
                  is_trace t2 s2 tr2 ->
                  no_errors_tr tr2 ->
                  ruts (curry (pre q)) (outRel Q) s1 tr1 s2 tr2.
Proof.
  intros pInP prePQ H_sbuter tr1 tr2 IsTrace1 IsTrace2 NoErrors2.
Admitted.


(** * Old typing_soundness using interpSet **)

(*
Definition curry {A B C} (f:A*B->C) a b := f (a, b).

Definition outRel' {S1 S2 T R1 R2} (Q:R1 -> R2 -> Perms)
           (sr1:S1*T*R1) (sr2:S2*T*R2) : Prop :=
  exists q, q ∈ (Q (snd sr1) (snd sr2)) /\ pre q (fst (fst sr1), fst (fst sr2)).

Theorem typing_soundness_fwd_lem {S1 S2 R1 R2 : Type} (P : @Perms (S1*S2))
        (Q: R1 -> R2 -> @Perms (S1*S2)) s1 t1 s2 t2 p q :
  p ∈ P -> pre (p ** q) (s1,s2) ->
  (forall tr2, interpSet t2 s2 tr2 -> no_errors_tr tr2) ->
  sbuter p Q t1 s1 t2 s2 ->
  forall o1, exists o2,
      ruts (curry (pre q)) (outRel' Q) s1 (interpTr _ t1 (s1,o1))
                                       s2 (interpTr _ t2 (s2,o2)).
Proof.
  intros pInP prePQ no_errors_r H_sbuter o1.
  punfold H_sbuter; [induction H_sbuter | apply sbuter_gen_mon].
  (* sbuter_gen_ret *)
  - exists o1.
    repeat rewritebisim @unfold_interpTr; cbn.
    pstep; constructor.
    exists p; split; assumption.
  (* sbuter_gen_err - this case is impossible *)
  - exists o1.
    pose (tr2 := throw (E:=traceE S2) (X:=S2*R2) tt).
    assert (interpSet (throw tt) c2 tr2).
    + exists (Streams.const false).
      rewrite unfold_interpTr, unfold_fmap_trace; cbn.
      apply eqit_Vis.
      inversion u.
    + apply (fun no_errors_r => no_errors_r tr2 H) in no_errors_r.
      punfold no_errors_r; inversion no_errors_r.
  (* sbuter_gen_tau_L *)
  - apply (fun H => H pInP prePQ no_errors_r) in IHH_sbuter.
    destruct IHH_sbuter as [o IHH_sbuter]; exists o.
    rewrite @interpTr_Tau.
    assumption.
  (* sbuter_gen_tau_R *)
  - assert (no_errors_r' : forall tr2, interpSet t2 c2 tr2 -> no_errors_tr tr2).
    + intros.
      rewrite <- interpSet_Tau in H0.
      apply no_errors_r; assumption.
    + apply (fun H => H pInP prePQ no_errors_r') in IHH_sbuter.
      destruct IHH_sbuter as [o IHH_sbuter]; exists o.
      rewrite @interpTr_Tau.
      assumption.
  (* sbuter_gen_tau *)
  - admit. (* wait... I need to induct here? *)
Admitted.


Definition outRel {S1 S2 R1 R2} (Q:R1 -> R2 -> Perms)
           (sr1:S1*R1) (sr2:S2*R2) : Prop :=
  exists q, q ∈ (Q (snd sr1) (snd sr2)) /\ pre q (fst sr1, fst sr2).

Theorem typing_soundness {S1 S2 R1 R2 : Type} (P: @Perms (S1*S2))
        (Q: R1 -> R2 -> @Perms (S1*S2)) s1 t1 s2 t2 p q :
  p ∈ P -> pre (p ** q) (s1,s2) ->
  (forall tr2, interpSet t2 s2 tr2 -> no_errors_tr tr2) ->
  sbuter p Q t1 s1 t2 s2 ->
  (forall tr1, interpSet t1 s1 tr1 ->
   exists tr2, interpSet t2 s2 tr2
          /\ ruts (curry (pre q)) (outRel Q) s1 tr1 s2 tr2) /\
  (forall tr2, interpSet t2 s2 tr2 ->
   exists tr1, interpSet t1 s1 tr1
          /\ ruts (curry (pre q)) (outRel Q) s1 tr1 s2 tr2).
Proof.
  intros pInP prePQ no_errors_r H_sbuter; split; intros.
  all: destruct H as [o1 H].
  - pose (H0 := typing_soundness_fwd_lem _ _ _ _ _ _ _ _ pInP prePQ no_errors_r H_sbuter o1).
    destruct H0 as [o2 H0].
    exists (fmap (fun '(s', _, r) => (s', r)) (interpTr R2 t2 (s2, o2))).
    split.
    + exists o2.
      reflexivity.
    + rewrite <- H.
      admit.
  - admit.
Admitted.
*) *)
