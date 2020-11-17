From Heapster Require Import
     Permissions
     Config
     NoEvent
     Functional.

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

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.
Import SumNotations.
Import VectorNotations.

Hint Resolve no_errors_gen_mon : paco.
Hint Resolve sbuter_gen_mon : paco.

Definition CompM S R := itree (sceE S) R.
Definition TPred S R := CompM S R -> S -> Prop.

Fixpoint zip {A B : Type} {n : nat} (a : Vector.t A n) (b : Vector.t B n) : Vector.t (A * B) n :=
match a in Vector.t _ n return Vector.t B n -> Vector.t (A * B) n  with
| ha :: ta => fun b => (ha, Vector.hd b) :: zip ta (Vector.tl b)
| [] => fun _ => []
end b.


(** * basic facts about `no_errors` and `sbuter` **)

Global Instance Proper_eutt_no_errors {S R} :
  Proper (eq ==> eutt eq ==> impl) (@no_errors S R).
Admitted.

Global Instance Proper_eutt_sbuter {S1 S2 R1 R2} :
  Proper (eq ==> eq ==> eutt eq ==> eq ==> eutt eq ==> eq ==> impl) (@sbuter S1 S2 R1 R2).
Admitted.

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

Lemma sbuter_tau_L {S1 S2 R1 R2} p Q t1 s1 t2 s2 :
  sbuter p Q (Tau t1) s1 t2 s2 -> @sbuter S1 S2 R1 R2 p Q t1 s1 t2 s2.
Proof.
  intro; punfold H.
  dependent induction H; pfold; try econstructor; eauto.
  + specialize (IHsbuter_gen t1 JMeq_refl eq_refl).
    punfold IHsbuter_gen.
  + pclearbot; punfold H0.
  + specialize (IHsbuter_gen t1 JMeq_refl eq_refl).
    punfold IHsbuter_gen.
  + intro b; specialize (H2 b t1 JMeq_refl eq_refl).
    punfold H2.
Qed.

Lemma sbuter_tau_R {S1 S2 R1 R2} p Q t1 s1 t2 s2 :
  sbuter p Q t1 s1 (Tau t2) s2 -> @sbuter S1 S2 R1 R2 p Q t1 s1 t2 s2.
Proof.
  intro; punfold H.
  dependent induction H; pfold; try econstructor; eauto.
  + specialize (IHsbuter_gen t2 JMeq_refl eq_refl).
    punfold IHsbuter_gen.
  + pclearbot; punfold H0.
  + specialize (IHsbuter_gen t2 JMeq_refl eq_refl).
    punfold IHsbuter_gen.
  + intro b; specialize (H2 b t2 JMeq_refl eq_refl).
    punfold H2.
Qed.

Lemma sbuter_inv_tau_L {S1 S2 R1 R2} p Q t1 s1 t2 s2 (ne2 : no_errors s2 t2) :
  sbuter p Q t1 s1 t2 s2 -> @sbuter S1 S2 R1 R2 p Q (Tau t1) s1 t2 s2.
Proof.
  intro; punfold H; pfold; econstructor; eauto.
  apply sbuter_gen_pre in H; destruct H; eauto.
  rewrite H in ne2; punfold ne2; inv ne2.
Qed.

Lemma sbuter_inv_tau_R {S1 S2 R1 R2} p Q t1 s1 t2 s2 (ne2 : no_errors s2 t2) :
  sbuter p Q t1 s1 t2 s2 -> @sbuter S1 S2 R1 R2 p Q t1 s1 (Tau t2) s2.
Proof.
  intro; punfold H; pfold; econstructor; eauto.
  apply sbuter_gen_pre in H; destruct H; eauto.
  rewrite H in ne2; punfold ne2; inv ne2.
Qed.


(** * `sbuter_ex` and lemmas **)

Definition sbuter_ex {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t2 s2 :=
  exists p', sep_step p p' /\ sbuter p' Q t1 s1 t2 s2.

Definition sbuter_to_sbuter_ex {S1 S2 R1 R2} p Q t1 s1 t2 s2 :
  sbuter p Q t1 s1 t2 s2 -> @sbuter_ex S1 S2 R1 R2 p Q t1 s1 t2 s2.
Proof. intro; exists p; split; [ reflexivity | assumption ]. Defined.

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

Lemma sbuter_ex_tau_L {S1 S2 R1 R2} p Q t1 s1 t2 s2 :
  sbuter_ex p Q (Tau t1) s1 t2 s2 -> @sbuter_ex S1 S2 R1 R2 p Q t1 s1 t2 s2.
Proof.
  intros [p' [? ?]]; exists p'; split; try apply sbuter_tau_L; eauto.
Qed.

Lemma sbuter_ex_tau_R {S1 S2 R1 R2} p Q t1 s1 t2 s2 :
  sbuter_ex p Q t1 s1 (Tau t2) s2 -> @sbuter_ex S1 S2 R1 R2 p Q t1 s1 t2 s2.
Proof.
  intros [p' [? ?]]; exists p'; split; try apply sbuter_tau_R; eauto.
Qed.


(** * definitions of steps and paths **)

Inductive tau_step {S R} : relation (CompM S R * S) :=
| tau_step_Tau t s : tau_step (Tau t, s) (t, s).

Inductive choice_step {S R} : relation (CompM S R * S) :=
| choice_step_Choice b k s : choice_step (vis Or k, s) (k b, s).

Definition tau_or_choice_step {S R} : relation (CompM S R * S) :=
  tau_step \2/ choice_step.

Inductive modify_step {S R} : relation (CompM S R * S) :=
| modify_step_Modify f k s : modify_step (vis (Modify f) k, s) (k s, f s).

Definition small_step {S R} : relation (CompM S R * S) :=
  tau_step \2/ choice_step \2/ modify_step.

(* Finite paths with a special case for the length 0 case *)
Fixpoint is_gen_finite_path0 {A} (r0 r : relation A) n x ys z :=
  match ys with
  | [] => r0 x z
  | y :: ys' => r x y /\ is_gen_finite_path0 r0 r _ y ys' z
  end.

(* Finite paths of a single relation *)
Definition is_gen_finite_path {A} (r : relation A) := @is_gen_finite_path0 A r r.
Arguments is_gen_finite_path /.

Definition is_finite_path {S R} := is_gen_finite_path0 (eq \2/ small_step) (@small_step S R).

Definition is_big_step {S R} := is_gen_finite_path0 (@modify_step S R) (tau_step \2/ choice_step).

Definition big_step {S R} ts0 tsf :=
  { n & { ts : Vector.t (CompM S R * S) n | is_big_step n ts0 ts tsf } }.


(** * lemmas about steps and paths **)

Definition tau_step_no_errors {S R} t1 s1 t2 s2 :
  @tau_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof. intros; dependent destruction H; apply no_errors_Tau; eauto. Qed.

Definition choice_step_no_errors {S R} t1 s1 t2 s2 :
  @choice_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof. intros; dependent destruction H; apply no_errors_Choice; eauto. Qed.

Definition tau_or_choice_step_no_errors {S R} t1 s1 t2 s2 :
  @tau_or_choice_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof.
  intros [?|?].
  - apply tau_step_no_errors; eauto.
  - apply choice_step_no_errors; eauto.
Qed.

Definition modify_step_no_errors {S R} t1 s1 t2 s2 :
  @modify_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof. intros; dependent destruction H; apply no_errors_Modify; eauto. Qed.

Definition small_step_no_errors {S R} t1 s1 t2 s2 :
  @small_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof.
  intros [?|?].
  - apply tau_or_choice_step_no_errors; eauto.
  - apply modify_step_no_errors; eauto.
Qed.

Lemma is_gen_finite_path0_no_errors {S R} (r0 r : relation (CompM S R * S))
      n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  (forall t s t' s', r0 (t,s) (t',s') -> no_errors s t -> no_errors s' t') ->
  (forall t s t' s', r (t,s) (t',s') -> no_errors s t -> no_errors s' t') ->
  is_gen_finite_path0 r0 r n (t0,s0) ts (tf,sf) -> no_errors s0 t0 -> no_errors sf tf.
Proof.
  intros r0_no_errors r_no_errors; revert t0 s0.
  induction ts; [|destruct h]; simpl; intros.
  - eapply (r0_no_errors t0 s0); eauto.
  - apply (IHts c s); try easy.
    eapply (r_no_errors t0 s0); easy.
Qed.

Lemma is_gen_finite_path_no_errors {S R} (r : relation (CompM S R * S))
      n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  (forall t s t' s', r (t,s) (t',s') -> no_errors s t -> no_errors s' t') ->
  is_gen_finite_path r n (t0,s0) ts (tf,sf) -> no_errors s0 t0 -> no_errors sf tf.
Proof. intro; apply is_gen_finite_path0_no_errors; eauto. Qed.

Lemma is_finite_path_no_errors {S R} n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  is_finite_path n (t0,s0) ts (tf,sf) -> no_errors s0 t0 -> no_errors sf tf.
Proof.
  apply is_gen_finite_path0_no_errors; intros.
  - destruct H.
    + injection H as Ht Hs.
      rewrite <- Ht, <- Hs; easy.
    + apply (small_step_no_errors t s); easy.
  - eapply small_step_no_errors; eauto.
Qed.

Lemma is_big_step_no_errors {S R} n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  is_big_step n (t0,s0) ts (tf,sf) -> no_errors s0 t0 -> no_errors sf tf.
Proof.
  apply is_gen_finite_path0_no_errors; intros.
  - eapply modify_step_no_errors; eauto.
  - destruct H.
    + eapply tau_step_no_errors; eauto.
    + eapply choice_step_no_errors; eauto.
Qed.

Lemma big_step_no_errors {S R} t1 s1 t2 s2 :
  @big_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof. intros [? [? ?]]; eapply is_big_step_no_errors; eauto. Qed.

Definition tau_step_snd_eq {S R} t1 s1 t2 s2 : @tau_step S R (t1,s1) (t2,s2) -> s1 = s2.
Proof. intro; dependent induction H; eauto. Qed.

Definition choice_step_snd_eq {S R} t1 s1 t2 s2 : @choice_step S R (t1,s1) (t2,s2) -> s1 = s2.
Proof. intro; dependent induction H; eauto. Qed.


(** * `sbuter_path_r`, `exists_sbuter_path_r`, and `sbuter_impl_path_r`  **)

(* An impressionistic picture of `sbuter_impl_path_r`, where the solid line is
   assumed, the dotted lines are shown to exist, and all the center lines
   represent `sbuter_ex`.

   (t2,s2) ⋯⋯ (t4,s4)          --
                  ⋮ any_step      | all dotted lines:
               (ti,si)           | sbuter_path_r ((t1,s1), (t3,s3))
            ⋰    ⋮ any_step      |               ((t2,s2), (t4,s4))
   (t1,s1) --- (t3,s3)          --
        sbuter_ex

   In words, this picture states that if `sbuter_ex t1 s1 t3 s3` then there
   exists some `(t4,s4)` which satisfies `sbuter_ex t2 s2 t4 s4` and for which
   there exists a finite path of `any_step`s from `(t3,s3)`, where each
   intermediate point along the path satisfies `sbuter_ex t1 s1 ti si`.
*)

(* `sbuter_path_r ((t1,s1), (t3,s3)) ((t2,s2), (t4,s4))` represents all the
   dotted lines in the picture above. *)
Inductive sbuter_path_r {S1 S2 R1 R2} p Q :
  relation ((CompM S1 R1 * S1) * (CompM S2 R2 * S2)) :=
| ex_path_r t1 s1 t2 s2 t3 s3 t4 s4 n (ts : Vector.t (CompM S2 R2 * S2) n) :
    is_finite_path n (t3,s3) ts (t4,s4) ->
    (forall i, sbuter_ex p Q t1 s1 (fst ts[@i]) (snd ts[@i]) /\
               guar p (s1, s3) (s1, snd ts[@i])) ->
    sbuter_ex p Q t2 s2 t4 s4 -> guar p (s1, s3) (s2, s4) ->
    sbuter_path_r p Q ((t1,s1),(t3,s3)) ((t2,s2),(t4,s4)).
Arguments ex_path_r {S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3 t4 s4} n ts.

(* Like `sbuter_path_r` but with the endpoints on the right existentially
   quantified and the arguments curried. *)
Definition exists_sbuter_path_r {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :=
  exists t4 s4, @sbuter_path_r S1 S2 R1 R2 p Q ((t1,s1),(t3,s3)) ((t2,s2),(t4,s4)).

Definition sbuter_impl_path_r {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :=
  sbuter_ex p Q t1 s1 t3 s3 -> @exists_sbuter_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3.


(** * `step_sbuter_l` *)

(* We start with some lemmas about `sbuter_path_r` and `exists_sbuter_path_r`. *)

Lemma rel_sbuter_path_r_no_errors {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 t4 s4 :
  @sbuter_path_r S1 S2 R1 R2 p Q ((t1,s1),(t3,s3)) ((t2,s2),(t4,s4)) ->
  no_errors s3 t3 -> no_errors s4 t4.
Proof. intro; dependent destruction H; eapply is_finite_path_no_errors; eauto. Qed.

Lemma exists_path_r_tau_R {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :
  sbuter_ex p Q t1 s1 t3 s3 ->
  exists_sbuter_path_r p Q t1 s1 t2 s2 t3 s3 ->
  @exists_sbuter_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 (Tau t3) s3.
Proof.
  intros Hb [t4 [s4 H]]; dependent destruction H.
  exists t4, s4; apply (ex_path_r (S n) ((t3,s3) :: ts)); eauto.
  - split; try assumption.
    left; left; constructor.
  - intro i; dependent destruction i; [split|]; eauto.
    reflexivity.
Qed.

Lemma exists_path_r_modify_R {S1 S2 R1 R2} p p' Q t1 s1 t2 s2 f k s3 :
  guar p (s1, s3) (s1, f s3) ->
  sep_step p p' ->
  sbuter_gen (upaco6 sbuter_gen bot6) p' Q t1 s1 (k s3) (f s3) ->
  exists_sbuter_path_r p Q t1 s1 t2 s2 (k s3) (f s3) ->
  @exists_sbuter_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 (vis (Modify f) k) s3.
Proof.
  intros ? ? Hb [t4 [s4 H]]; dependent destruction H.
  exists t4, s4; apply (ex_path_r (S n) ((k s3, f s3) :: ts)); eauto.
  - split; try assumption.
    right; apply modify_step_Modify.
  - dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; try assumption.
      pfold; assumption.
    + specialize (H2 i); destruct H2; split; eauto.
      * rewrite H0; assumption.
   - rewrite H0; assumption.
Qed.

Lemma exists_path_r_choice_R {S1 S2 R1 R2} b p p' Q t1 s1 t2 s2 k s3 :
  sep_step p p' ->
  sbuter_gen (upaco6 sbuter_gen bot6) p' Q t1 s1 (k b) s3 ->
  exists_sbuter_path_r p Q t1 s1 t2 s2 (k b) s3 ->
  @exists_sbuter_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 (vis Or k) s3.
Proof.
  intros ? Hb [t4 [s4 H]]; dependent destruction H.
  exists t4, s4; apply (ex_path_r (S n) ((k b, s3) :: ts)); eauto.
  - split; try assumption.
    left; right; constructor.
  - intro i; dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; try assumption.
      pfold; assumption.
    + specialize (H1 i); destruct H1; split; eauto.
Qed.

(* Next we prove `sbuter_impl_path_r` for each kind of small step. *)

Lemma tau_step_sbuter_impl_path_r {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :
  tau_step (t1,s1) (t2,s2) ->
  @sbuter_impl_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3.
Proof.
  intros H Hb.
  dependent destruction H.
  apply sbuter_ex_tau_L in Hb.
  exists t3, s3; apply (ex_path_r 0 []); try easy.
  left; reflexivity.
Qed.

Lemma modify_step_sbuter_impl_path_r {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 ->
  modify_step (t1,s1) (t2,s2) ->
  @sbuter_impl_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3.
Proof.
  intros ne3 H [q [step_q Hb]].
  dependent destruction H.
  punfold Hb; dependent induction Hb.
  (* sbuter_gen_err *)
  - punfold ne3; inv ne3.
  (* sbuter_gen_tau_R *)
  - apply no_errors_Tau in ne3.
    apply exists_path_r_tau_R; eauto.
    exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_modify_L *)
  - exists t2, c2; apply (ex_path_r 0 []); try easy.
    + left; reflexivity.
    + exists p'; split; [|pfold]; eauto.
      rewrite step_q; eauto.
    + apply (sep_step_guar p p0); eauto.
  (* sbuter_gen_modify_R *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    apply no_errors_Modify in ne3.
    apply (sep_step_guar p p0) in H0; eauto.
    eapply exists_path_r_modify_R; eauto.
  (* sbuter_gen_modify *)
  - exists (k2 c2), (f2 c2); apply (ex_path_r 0 []); try easy.
    + right; right; constructor.
    + exists p'; split; pclearbot; eauto.
      rewrite step_q; eauto.
    + apply (sep_step_guar p p0); eauto.
  (* sbuter_gen_choice_R *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    rewrite <- no_errors_Choice in ne3.
    eapply (exists_path_r_choice_R false); eauto.
Qed.

Lemma choice_step_sbuter_impl_path_r {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 ->
  choice_step (t1,s1) (t2,s2) ->
  @sbuter_impl_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3.
Proof.
  intros ne3 H [q [step_q Hb]].
  dependent destruction H.
  punfold Hb; dependent induction Hb.
  (* sbuter_gen_err *)
  - punfold ne3; inv ne3.
  (* sbuter_gen_tau_R *)
  - apply no_errors_Tau in ne3.
    apply exists_path_r_tau_R; eauto.
    exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_modify_R *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    apply no_errors_Modify in ne3.
    apply (sep_step_guar p p0) in H0; eauto.
    eapply exists_path_r_modify_R; eauto.
  (* sbuter_gen_choice_L *)
  - exists t2, c2; apply (ex_path_r 0 []); try easy.
    + left; reflexivity.
    + exists p'; split; [|pfold]; eauto.
      rewrite step_q; eauto.
  (* sbuter_gen_choice_R *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    rewrite <- no_errors_Choice in ne3.
    eapply (exists_path_r_choice_R false); eauto.
  (* sbuter_gen_choice *)
  - specialize (H1 b); destruct H1 as [b' H1].
    exists (k2 b'), c2; apply (ex_path_r 0 []); try easy.
    + right; left; right; constructor.
    + exists p'; split; pclearbot; eauto.
      rewrite step_q; eauto.
Qed.

(* Finally, we state and prove `sbuter_step_l` *)

Lemma sbuter_step_l {S1 S2 R1 R2} p Q n t1 s1 ts t2 s2 t3 s3 :
  no_errors s3 t3 ->
  is_big_step n (t1,s1) ts (t2,s2) ->
  sbuter_ex p Q t1 s1 t3 s3 ->
  exists ts' t4 s4,
    is_gen_finite_path (@sbuter_path_r S1 S2 R1 R2 p Q)
                       n ((t1,s1),(t3,s3)) (zip ts ts') ((t2,s2),(t4,s4)).
Proof.
  revert ts t1 s1 t3 s3.
  induction ts; [|destruct h]; intros; simpl in *.
  - exists [].
    apply modify_step_sbuter_impl_path_r; eauto.
  - destruct H0 as [? ?].
    assert (exists_sbuter_path_r p Q t1 s1 c s t3 s3).
    + destruct H0.
      * apply tau_step_sbuter_impl_path_r; eauto.
      * apply choice_step_sbuter_impl_path_r; eauto.
    + destruct H3 as [t4 [s4 ?]].
      assert (no_errors s4 t4) by (eapply rel_sbuter_path_r_no_errors; eauto).
      assert (sbuter_ex p Q c s t4 s4) by (dependent destruction H3; eauto).
      specialize (IHts c s t4 s4 H4 H2 H5).
      destruct IHts as [ts' [t5 [s5 ?]]].
      exists ((t4,s4) :: ts'), t5, s5; split; eauto.
Qed.


(** * `sbuter_path_l`, `exists_sbuter_path_l`, and `sbuter_impl_path_l`  **)

(* An impressionistic picture of `sbuter_impl_path_l`, analogous to that
   for `sbuter_impl_path_r`

          (t2,s2) ⋯⋯ (t4,s4)   --
   any_step  ⋮                     | all dotted lines:
          (ti,si)                 | sbuter_path_l ((t1,s1), (t3,s3))
   any_step  ⋮     ⋱              |               ((t2,s2), (t4,s4))
          (t1,s1) --- (t3,s3)   --
               sbuter_ex
*)

(* `sbuter_path_l ((t1,s1), (t3,s3)) ((t2,s2), (t4,s4))` represents all the
   dotted lines in the picture above. *)
Inductive sbuter_path_l {S1 S2 R1 R2} p Q :
  relation ((CompM S1 R1 * S1) * (CompM S2 R2 * S2)) :=
| ex_path_l t1 s1 t2 s2 t3 s3 t4 s4 n (ts : Vector.t (CompM S1 R1 * S1) n) :
    is_finite_path n (t1,s1) ts (t2,s2) ->
    (forall i, sbuter_ex p Q (fst ts[@i]) (snd ts[@i]) t3 s3 /\
               guar p (s1, s3) (snd ts[@i], s3)) ->
    sbuter_ex p Q t2 s2 t4 s4 -> guar p (s1, s3) (s2, s4) ->
    sbuter_path_l p Q ((t1,s1),(t3,s3)) ((t2,s2),(t4,s4)).
Arguments ex_path_l {S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3 t4 s4} n ts.

(* Like `sbuter_path_l` but with the endpoints on the left existentially
   quantified and the arguments curried. *)
Definition exists_sbuter_path_l {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :=
  exists t2 s2, @sbuter_path_l S1 S2 R1 R2 p Q ((t1,s1),(t3,s3)) ((t2,s2),(t4,s4)).

Definition sbuter_impl_path_l {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :=
  sbuter_ex p Q t1 s1 t3 s3 -> @exists_sbuter_path_l S1 S2 R1 R2 p Q t1 s1 t3 s3 t4 s4.


(** * `step_sbuter_r` *)

(* We start with some lemmas about `sbuter_path_l` and `exists_sbuter_path_l`.
   The proofs here are mostly identical to those for `step_sbuter_l` above. *)

Lemma exists_path_l_tau_L {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :
  sbuter_ex p Q t1 s1 t3 s3 ->
  exists_sbuter_path_l p Q t1 s1 t3 s3 t4 s4 ->
  @exists_sbuter_path_l S1 S2 R1 R2 p Q (Tau t1) s1 t3 s3 t4 s4.
Proof.
  intros Hb [t2 [s2 H]]; dependent destruction H.
  exists t2, s2; apply (ex_path_l (S n) ((t1,s1) :: ts)); eauto.
  - split; try assumption.
    left; left; constructor.
  - intro i; dependent destruction i; [split|]; eauto.
    reflexivity.
Qed.

Lemma exists_path_l_modify_L {S1 S2 R1 R2} p p' Q f k s1 t3 s3 t4 s4 :
  guar p (s1, s3) (f s1, s3) ->
  sep_step p p' ->
  sbuter_gen (upaco6 sbuter_gen bot6) p' Q (k s1) (f s1) t3 s3 ->
  exists_sbuter_path_l p Q (k s1) (f s1) t3 s3 t4 s4 ->
  @exists_sbuter_path_l S1 S2 R1 R2 p Q (vis (Modify f) k) s1 t3 s3 t4 s4.
Proof.
  intros ? ? Hb [t2 [s2 H]]; dependent destruction H.
  exists t2, s2; apply (ex_path_l (S n) ((k s1, f s1) :: ts)); eauto.
  - split; try assumption.
    right; apply modify_step_Modify.
  - dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; try assumption.
      pfold; assumption.
    + specialize (H2 i); destruct H2; split; eauto.
      * rewrite H0; assumption.
   - rewrite H0; assumption.
Qed.

Lemma exists_path_l_choice_L {S1 S2 R1 R2} b p p' Q k s1 t3 s3 t4 s4 :
  sep_step p p' ->
  sbuter_gen (upaco6 sbuter_gen bot6) p' Q (k b) s1 t3 s3 ->
  exists_sbuter_path_l p Q (k b) s1 t3 s3 t4 s4 ->
  @exists_sbuter_path_l S1 S2 R1 R2 p Q (vis Or k) s1 t3 s3 t4 s4.
Proof.
  intros ? Hb [t2 [s2 H]]; dependent destruction H.
  exists t2, s2; apply (ex_path_l (S n) ((k b, s1) :: ts)); eauto.
  - split; try assumption.
    left; right; constructor.
  - intro i; dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; try assumption.
      pfold; assumption.
    + specialize (H1 i); destruct H1; split; eauto.
Qed.

(* Next we prove `sbuter_impl_path_r` for each kind of small step. Again,
   the proofs here are mostly identical to those for `step_sbuter_l` above. *)

Lemma tau_step_sbuter_impl_path_l {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :
  tau_step (t3,s3) (t4,s4) ->
  @sbuter_impl_path_l S1 S2 R1 R2 p Q t1 s1 t3 s3 t4 s4.
Proof.
  intros H Hb.
  dependent destruction H.
  apply sbuter_ex_tau_R in Hb.
  exists t1, s1; apply (ex_path_l 0 []); try easy.
  left; reflexivity.
Qed.

Lemma modify_step_sbuter_impl_path_l {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :
  modify_step (t3,s3) (t4,s4) ->
  @sbuter_impl_path_l S1 S2 R1 R2 p Q t1 s1 t3 s3 t4 s4.
Proof.
  intros H [q [step_q Hb]].
  dependent destruction H.
  punfold Hb; dependent induction Hb.
  (* sbuter_gen_tau_R *)
  - apply exists_path_l_tau_L; eauto.
    exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_modify_L *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    apply (sep_step_guar p p0) in H0; eauto.
    eapply exists_path_l_modify_L; eauto.
  (* sbuter_gen_modify_R *)
  - exists t1, c1; apply (ex_path_l 0 []); try easy.
    + left; reflexivity.
    + exists p'; split; [|pfold]; eauto.
      rewrite step_q; eauto.
    + apply (sep_step_guar p p0); eauto.
  (* sbuter_gen_modify *)
  - exists (k1 c1), (f1 c1); apply (ex_path_l 0 []); try easy.
    + right; right; constructor.
    + exists p'; split; pclearbot; eauto.
      rewrite step_q; eauto.
    + apply (sep_step_guar p p0); eauto.
  (* sbuter_gen_choice_L *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    eapply (exists_path_l_choice_L false); eauto.
Qed.

Lemma choice_step_sbuter_impl_path_l {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :
  choice_step (t3,s3) (t4,s4) ->
  @sbuter_impl_path_l S1 S2 R1 R2 p Q t1 s1 t3 s3 t4 s4.
Proof.
  intros H [q [step_q Hb]].
  dependent destruction H.
  punfold Hb; dependent induction Hb.
  (* sbuter_gen_tau_R *)
  - apply exists_path_l_tau_L; eauto.
    exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_modify_R *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    apply (sep_step_guar p p0) in H0; eauto.
    eapply exists_path_l_modify_L; eauto.
  (* sbuter_gen_choice_L *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    eapply (exists_path_l_choice_L false); eauto.
  (* sbuter_gen_choice_R *)
  - exists t1, c1; apply (ex_path_l 0 []); try easy.
    + left; reflexivity.
    + exists p'; split; [|pfold]; eauto.
      rewrite step_q; eauto.
  (* sbuter_gen_choice *)
  - specialize (H2 b); destruct H2 as [b' H2].
    exists (k1 b'), c1; apply (ex_path_l 0 []); try easy.
    + right; left; right; constructor.
    + exists p'; split; pclearbot; eauto.
      rewrite step_q; eauto.
Qed.

(* Finally, we state and prove `sbuter_step_r` *)

Lemma sbuter_step_r {S1 S2 R1 R2} p Q n t1 s1 t3 s3 ts t4 s4 :
  is_big_step n (t3,s3) ts (t4,s4) ->
  sbuter_ex p Q t1 s1 t3 s3 ->
  exists ts' t2 s2,
    is_gen_finite_path (@sbuter_path_l S1 S2 R1 R2 p Q)
                       n ((t1,s1),(t3,s3)) (zip ts' ts) ((t2,s2),(t4,s4)).
Proof.
  revert ts t1 s1 t3 s3.
  induction ts; [|destruct h]; intros; simpl in *.
  - exists [].
    apply modify_step_sbuter_impl_path_l; eauto.
  - destruct H as [? ?].
    assert (exists_sbuter_path_l p Q t1 s1 t3 s3 c s).
    + destruct H.
      * apply tau_step_sbuter_impl_path_l; eauto.
      * apply choice_step_sbuter_impl_path_l; eauto.
    + destruct H2 as [t2 [s2 ?]].
      assert (sbuter_ex p Q t2 s2 c s) by (dependent destruction H2; eauto).
      specialize (IHts t2 s2 c s H1 H3).
      destruct IHts as [ts' [t5 [s5 ?]]].
      exists ((t2,s2) :: ts'), t5, s5; split; eauto.
Qed.


(* ----- end of new stuff for now ----- *)


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
| EF_step t1 s1 t2 s2 t3 s3 :
    or_tau_step t1 s1 t2 s2 -> modify_step t2 s2 t3 s3 ->
    EF P t3 s3 -> EF P t1 s1.
Arguments EF_refl {S R P} t s.
Arguments EF_step {S R P t1 s1} t2 s2 t3 s3.

Definition or_tau_step_invariant {S P} (P : TPred S P) :=
  forall t1 s1 t2 s2, or_tau_step t1 s1 t2 s2 -> P t1 s1 <-> P t2 s2.

Lemma EF_path {S1 R1 P} n t0 s0 (ts : Vector.t (CompM S1 R1 * S1) n) tf sf :
  or_tau_step_invariant P ->
  is_path n t0 s0 ts tf sf -> EF P tf sf -> EF P t0 s0.
Proof.
  intros P_invar.
  revert t0 s0; induction ts; [|destruct h]; intros.
  - destruct H, H0.
    + apply EF_refl.
      now rewrite (P_invar _ _ _ _ H).
    + apply (EF_step t2 s2 t3 s3); try assumption.
      apply (or_tau_step_trans t1 s1); assumption.
    + apply (EF_step t0 s0 t s); try assumption.
      * apply or_tau_step_refl.
      * apply EF_refl; assumption.
    + apply (EF_step t0 s0 t1 s1); try assumption.
      * apply or_tau_step_refl.
      * apply (EF_step t2 s2 t3 s3); assumption.
  - destruct H, H.
    + specialize (IHts c s H1 H0).
      destruct IHts.
      * apply EF_refl.
        apply (P_invar _ _ _ _ H); assumption.
      * apply (EF_step t2 s2 t3 s3); try assumption.
        apply (or_tau_step_trans t1 s1); assumption.
    + apply (EF_step t0 s0 c s); try assumption.
      * apply or_tau_step_refl.
      * apply IHts; assumption.
Qed.


(** * `eq_sat_EF`  **)

Lemma eq_sat_EF {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2)
  : or_tau_step_invariant P1 -> or_tau_step_invariant P2 ->
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (EF P1) (EF P2).
Proof.
  intros invar1 invar2; split; intros.
  - revert H4 p t2 s2 H0 H1 H2 H3.
    induction 1 as [t1 s1 | t1 s1 t1' s1' t1'' s1'']; intros.
    + apply (EF_refl t2 s2).
      apply (H p Q t1 s1 t2 s2); assumption.
    + apply sbuter_to_sbuter_ex in H5.
      pose proof (step_sbuter_l _ _ _ _ _ _ _ _ _ _ H6 H0 H1 H5).
      destruct H7 as [n [ts [t2' [s2' [? [? [? ?]]]]]]].
      apply (EF_path n t2 s2 ts t2' s2'); try assumption.
      destruct H9 as [p' [? ?]].
      apply (IHEF p').
      * apply or_tau_step_to_eq in H0; rewrite H0 in H2.
        apply (sep_r _ _ H3) in H10; respects.
      * apply H9; assumption.
      * assumption.
      * apply (is_path_no_errors _ t2 s2 ts t2' s2'); assumption.
  - revert H4 p t1 s1 H0 H1 H2 H3.
    induction 1 as [t2 s2 | t2 s2 t2' s2' t2'' s2'']; intros.
    + apply (EF_refl t1 s1).
      apply (H p Q t1 s1 t2 s2); assumption.
    + apply sbuter_to_sbuter_ex in H5.
      pose proof (step_sbuter_r _ _ _ _ _ _ _ _ _ _ H6 H0 H1 H5).
      destruct H7 as [n [ts [t1' [s1' [? [? [? ?]]]]]]].
      apply (EF_path n t1 s1 ts t1' s1'); try assumption.
      destruct H9 as [p' [? ?]].
      apply (IHEF p').
      * apply or_tau_step_to_eq in H0; rewrite H0 in H2.
        apply (sep_r _ _ H3) in H10; respects.
      * apply H9; assumption.
      * assumption.
      * apply (modify_step_no_errors t2' s2'); try assumption.
        apply (or_tau_step_no_errors t2 s2); assumption.
Qed.


(** * `AG` and lemmas  **)

Definition AG_gen {S R} (AG : TPred S R -> TPred S R) (P : TPred S R) : TPred S R :=
  fun t1 s1 => P t1 s1 /\ (forall t2 s2 t3 s3, or_tau_step t1 s1 t2 s2 ->
                                               modify_step t2 s2 t3 s3 -> AG P t3 s3).

Definition AG {S R} : TPred S R -> TPred S R := paco3 AG_gen bot3.

Lemma AG_gen_mon {S R} : monotone3 (@AG_gen S R).
Admitted.
Hint Resolve AG_gen_mon : paco.


(** * `eq_sat_AG`  **)

Lemma eq_sat_AG {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2)
  : eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (AG P1) (AG P2).
Proof.
  split; intro.
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
