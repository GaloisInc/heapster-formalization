From Heapster Require Import
     Permissions
     Config
     Typing.

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


(** * Basic facts about `no_errors` and `sbuter` **)

Lemma no_errors_Tau {S R} (s : S) (t : CompM S R) :
  no_errors s t <-> no_errors s (Tau t).
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
    + apply inj_pair2 in H2; subst. apply H.
    + inv H.
Qed.

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
    + apply inj_pair2 in H0; subst. apply H.
    + inv H.
Qed.

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


(** * Definitions of steps and finite paths **)

Inductive tau_step {S R} : relation (CompM S R * S) :=
| tau_step_Tau t s : tau_step (Tau t, s) (t, s).

Inductive choice_step {S R} : relation (CompM S R * S) :=
| choice_step_Choice b k s : choice_step (vis Or k, s) (k b, s).

Inductive modify_step {S R} : relation (CompM S R * S) :=
| modify_step_Modify f k s : modify_step (vis (Modify f) k, s) (k s, f s).

Inductive step {S R} : relation (CompM S R * S) :=
| step_Tau t s : step (Tau t, s) (t, s)
| step_Choice b k s : step (vis Or k, s) (k b, s)
| step_Modify f k s : step (vis (Modify f) k, s) (k s, f s).

Hint Extern 0 (step (Tau ?t, ?s) (?t, ?s)) => eapply step_Tau : core.
Hint Extern 0 (step (vis Or ?k, ?s) (?k ?b, ?s)) => eapply step_Choice : core.
Hint Extern 0 (step (vis (Modify ?f) ?k, ?s) (?k ?s, ?f ?s)) => eapply step_Modify : core.

(* Finite paths with a special case for the length 0 case *)
Fixpoint is_gen_finite_path0 {A} (r0 r : relation A) n x ys z :=
  match ys with
  | [] => r0 x z
  | y :: ys' => r x y /\ is_gen_finite_path0 r0 r _ y ys' z
  end.

(* Finite paths of a single relation *)
Definition is_gen_finite_path {A} (r : relation A) := @is_gen_finite_path0 A r r.
Arguments is_gen_finite_path /.

(* Finite paths (of steps) *)
Definition is_finite_path {S R} :=
  is_gen_finite_path0 (eq \2/ step) (@step S R).


(** * lemmas about steps and paths **)

Definition tau_step_no_errors {S R} t1 s1 t2 s2 :
  @tau_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof. intros; dependent destruction H; apply no_errors_Tau; eauto. Qed.

Definition choice_step_no_errors {S R} t1 s1 t2 s2 :
  @choice_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof. intros; dependent destruction H; apply no_errors_Choice; eauto. Qed.

Definition modify_step_no_errors {S R} t1 s1 t2 s2 :
  @modify_step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof. intros; dependent destruction H; apply no_errors_Modify; eauto. Qed.

Definition step_no_errors {S R} t1 s1 t2 s2 :
  @step S R (t1,s1) (t2,s2) -> no_errors s1 t1 -> no_errors s2 t2.
Proof.
  intros; dependent destruction H.
  - apply no_errors_Tau; eauto.
  - apply no_errors_Choice; eauto.
  - apply no_errors_Modify; eauto.
Qed.

Lemma is_gen_finite_path0_no_errors_end {S R} (r0 r : relation (CompM S R * S))
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

Lemma is_gen_finite_path0_no_errors_mid {S R} (r0 r : relation (CompM S R * S))
      n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  (forall t s t' s', r0 (t,s) (t',s') -> no_errors s t -> no_errors s' t') ->
  (forall t s t' s', r (t,s) (t',s') -> no_errors s t -> no_errors s' t') ->
  is_gen_finite_path0 r0 r n (t0,s0) ts (tf,sf) -> no_errors s0 t0 ->
  forall i, no_errors (snd ts[@i]) (fst ts[@i]).
Proof.
  intros r0_no_errors r_no_errors ? ne0 i.
  revert t0 s0 ne0 H; dependent induction i; intros.
  all: dependent destruction ts; destruct h.
  all: destruct H.
  - eapply r_no_errors; eauto.
  - apply (IHi ts c s); eauto.
Qed.

Lemma is_gen_finite_path_no_errors_end {S R} (r : relation (CompM S R * S))
      n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  (forall t s t' s', r (t,s) (t',s') -> no_errors s t -> no_errors s' t') ->
  is_gen_finite_path r n (t0,s0) ts (tf,sf) -> no_errors s0 t0 -> no_errors sf tf.
Proof. intro; apply is_gen_finite_path0_no_errors_end; eauto. Qed.

Lemma is_gen_finite_path_no_errors_mid {S R} (r : relation (CompM S R * S))
      n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  (forall t s t' s', r (t,s) (t',s') -> no_errors s t -> no_errors s' t') ->
  is_gen_finite_path r n (t0,s0) ts (tf,sf) -> no_errors s0 t0 ->
  forall i, no_errors (snd ts[@i]) (fst ts[@i]).
Proof. intro; apply is_gen_finite_path0_no_errors_mid; eauto. Qed.

Lemma is_finite_path_no_errors_end {S R} n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  is_finite_path n (t0,s0) ts (tf,sf) -> no_errors s0 t0 -> no_errors sf tf.
Proof.
  apply is_gen_finite_path0_no_errors_end; intros.
  - destruct H.
    + injection H; intros; subst; eauto.
    + eapply step_no_errors; eauto.
  - eapply step_no_errors; eauto.
Qed.

Lemma is_finite_path_no_errors_mid {S R} n t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :
  is_finite_path n (t0,s0) ts (tf,sf) -> no_errors s0 t0 ->
  forall i, no_errors (snd ts[@i]) (fst ts[@i]).
Proof.
  apply is_gen_finite_path0_no_errors_mid; intros.
  - destruct H.
    + injection H; intros; subst; eauto.
    + eapply step_no_errors; eauto.
  - eapply step_no_errors; eauto.
Qed.


(** * `sbuter_path_r`, `exists_sbuter_path_r`, and `sbuter_impl_path_r`  **)

(* An impressionistic picture of `sbuter_impl_path_r`, where the solid line is
   assumed, the dotted lines are shown to exist, and all the center lines
   represent `sbuter_ex`.

   (t2,s2) ⋯⋯ (t4,s4)      --
                  ⋮ step      | all dotted lines:
               (ti,si)       | sbuter_path_r ((t1,s1), (t3,s3))
            ⋰    ⋮ step      |               ((t2,s2), (t4,s4))
   (t1,s1) --- (t3,s3)      --
        sbuter_ex

   In words, this picture states that if `sbuter_ex t1 s1 t3 s3` then there
   exists some `(t4,s4)` which satisfies `sbuter_ex t2 s2 t4 s4` and for which
   there exists a finite path from `(t3,s3)`, where each intermediate point
   along the path satisfies `sbuter_ex t1 s1 ti si`.
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

Lemma exists_path_r_tau_R {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :
  sbuter_ex p Q t1 s1 t3 s3 ->
  exists_sbuter_path_r p Q t1 s1 t2 s2 t3 s3 ->
  @exists_sbuter_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 (Tau t3) s3.
Proof.
  intros Hb [t4 [s4 H]]; dependent destruction H.
  exists t4, s4; apply (ex_path_r (S n) ((t3, s3) :: ts)); eauto.
  - split; eauto.
  - intro i; dependent destruction i; simpl; eauto.
    split; solve [ eauto; reflexivity ].
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
  - split; eauto.
  - dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; eauto.
      pfold; eauto.
    + specialize (H2 i); destruct H2; split; eauto.
      * rewrite H0; eauto.
   - rewrite H0; eauto.
Qed.

Lemma exists_path_r_choice_R {S1 S2 R1 R2} b p p' Q t1 s1 t2 s2 k s3 :
  sep_step p p' ->
  sbuter_gen (upaco6 sbuter_gen bot6) p' Q t1 s1 (k b) s3 ->
  exists_sbuter_path_r p Q t1 s1 t2 s2 (k b) s3 ->
  @exists_sbuter_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 (vis Or k) s3.
Proof.
  intros ? Hb [t4 [s4 H]]; dependent destruction H.
  exists t4, s4; apply (ex_path_r (S n) ((k b, s3) :: ts)); eauto.
  - split; eauto.
  - intro i; dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; eauto.
      pfold; eauto.
    + specialize (H1 i); destruct H1; split; eauto.
Qed.

(* Next we prove `sbuter_impl_path_r` for `step`. *)

Lemma tau_step_sbuter_impl_path_r {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 ->
  tau_step (t1,s1) (t2,s2) ->
  @sbuter_impl_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3.
Proof.
  intros ne3 H [q [step_q Hb]].
  dependent destruction H.
  punfold Hb; dependent induction Hb.
  (* sbuter_gen_err *)
  - punfold ne3; inv ne3.
  (* sbuter_gen_tau_L *)
  - exists t0, c2; apply (ex_path_r 0 []); try easy.
    + left; reflexivity.
    + exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_tau_R *)
  - apply no_errors_Tau in ne3.
    apply exists_path_r_tau_R; eauto.
    exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_tau *)
  - exists t0, c2; apply (ex_path_r 0 []); try easy.
    + right; apply step_Tau.
    + exists p0; split; pclearbot; eauto.
  (* sbuter_gen_modify_R *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    apply no_errors_Modify in ne3.
    apply (sep_step_guar p p0) in H0; eauto.
    eapply exists_path_r_modify_R; eauto.
  (* sbuter_gen_choice_R *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    rewrite <- no_errors_Choice in ne3.
    eapply (exists_path_r_choice_R false); eauto.
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
    + right; apply step_Modify.
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
    + right; apply step_Choice.
    + exists p'; split; pclearbot; eauto.
      rewrite step_q; eauto.
Qed.

Lemma sbuter_step_l {S1 S2 R1 R2} p Q t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 ->
  step (t1,s1) (t2,s2) ->
  @sbuter_impl_path_r S1 S2 R1 R2 p Q t1 s1 t2 s2 t3 s3.
Proof.
  intros ne3 H; dependent destruction H.
  - apply tau_step_sbuter_impl_path_r, tau_step_Tau; eauto.
  - apply choice_step_sbuter_impl_path_r, choice_step_Choice; eauto.
  - apply modify_step_sbuter_impl_path_r, modify_step_Modify; eauto.
Qed.


(** * `sbuter_path_l`, `exists_sbuter_path_l`, and `sbuter_impl_path_l`  **)

(* An impressionistic picture of `sbuter_impl_path_l`, analogous to that
   for `sbuter_impl_path_r`

      (t2,s2) ⋯⋯ (t4,s4)   --
   step  ⋮                     | all dotted lines:
      (ti,si)                 | sbuter_path_l ((t1,s1), (t3,s3))
   step  ⋮     ⋱              |               ((t2,s2), (t4,s4))
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
  exists t2, s2; apply (ex_path_l (S n) ((t1, s1) :: ts)); eauto.
  - split; eauto.
  - intro i; dependent destruction i; simpl; eauto.
    split; solve [ eauto; reflexivity ].
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
  - split; eauto.
  - dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; eauto.
      pfold; eauto.
    + specialize (H2 i); destruct H2; split; eauto.
      * rewrite H0; eauto.
   - rewrite H0; eauto.
Qed.

Lemma exists_path_l_choice_L {S1 S2 R1 R2} b p p' Q k s1 t3 s3 t4 s4 :
  sep_step p p' ->
  sbuter_gen (upaco6 sbuter_gen bot6) p' Q (k b) s1 t3 s3 ->
  exists_sbuter_path_l p Q (k b) s1 t3 s3 t4 s4 ->
  @exists_sbuter_path_l S1 S2 R1 R2 p Q (vis Or k) s1 t3 s3 t4 s4.
Proof.
  intros ? Hb [t2 [s2 H]]; dependent destruction H.
  exists t2, s2; apply (ex_path_l (S n) ((k b, s1) :: ts)); eauto.
  - split; eauto.
  - intro i; dependent destruction i; simpl.
    + split; try easy.
      exists p'; split; eauto.
      pfold; eauto.
    + specialize (H1 i); destruct H1; split; eauto.
Qed.

(* Next we prove `sbuter_impl_path_r` for `step`. Again, the proofs here are
   mostly identical to those for `step_sbuter_l` above. *)

Lemma tau_step_sbuter_impl_path_l {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :
  tau_step (t3,s3) (t4,s4) ->
  @sbuter_impl_path_l S1 S2 R1 R2 p Q t1 s1 t3 s3 t4 s4.
Proof.
  intros H [q [step_q Hb]].
  dependent destruction H.
  punfold Hb; dependent induction Hb.
  (* sbuter_gen_tau_L *)
  - apply exists_path_l_tau_L; eauto.
    exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_tau_R *)
  - exists t1, c1; apply (ex_path_l 0 []); try easy.
    + left; reflexivity.
    + exists p0; split; [|pfold]; eauto.
  (* sbuter_gen_tau *)
  - exists t1, c1; apply (ex_path_l 0 []); try easy.
    + right; apply step_Tau.
    + exists p0; split; pclearbot; eauto.
  (* sbuter_gen_modify_L *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    apply (sep_step_guar p p0) in H0; eauto.
    eapply exists_path_l_modify_L; eauto.
  (* sbuter_gen_choice_L *)
  - assert (sep_step p p') by (rewrite step_q; eauto).
    eapply (exists_path_l_choice_L false); eauto.
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
    + right; apply step_Modify.
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
    + right; apply step_Choice.
    + exists p'; split; pclearbot; eauto.
      rewrite step_q; eauto.
Qed.

Lemma sbuter_step_r {S1 S2 R1 R2} p Q t1 s1 t3 s3 t4 s4 :
  step (t3,s3) (t4,s4) ->
  @sbuter_impl_path_l S1 S2 R1 R2 p Q t1 s1 t3 s3 t4 s4.
Proof.
  intros H; dependent destruction H.
  - apply tau_step_sbuter_impl_path_l, tau_step_Tau; eauto.
  - apply choice_step_sbuter_impl_path_l, choice_step_Choice; eauto.
  - apply modify_step_sbuter_impl_path_l, modify_step_Modify; eauto.
Qed.


(** * `eq_sat_sep_sbuter` and basic facts  **)

Definition TPred S R := CompM S R * S -> Prop.

Definition eq_sat_sep_sbuter {S1 S2 R1 R2} (q:@perm (S1*S2))
  (P1:TPred S1 R1) (P2:TPred S2 R2) :=
  forall p Q t1 s1 t2 s2, pre q (s1,s2) -> separate p q ->
    sbuter p Q t1 s1 t2 s2 -> no_errors s2 t2 ->
    (P1 (t1,s1) <-> P2 (t2,s2)).


(** * `eq_sat_sep_sbuter` for state predicates **)

Definition state_pred {S} R P : TPred S R := fun '(_,s) => P s.

Definition q_similar {S1 S2} q (P1 : S1 -> Prop) (P2 : S2 -> Prop): Prop :=
  forall s1 s2, pre q (s1,s2) -> (P1 s1 <-> P2 s2).

Lemma eq_sat_state_preds {S1 S2 R1 R2} q (P1 : S1 -> Prop) (P2 : S2 -> Prop)
  : q_similar q P1 P2 ->
    eq_sat_sep_sbuter q (state_pred R1 P1) (state_pred R2 P2).
Proof.
  unfold eq_sat_sep_sbuter; intros.
  apply H; assumption.
Qed.


(** * `eq_sat_sep_sbuter` for logical connectives **)

Lemma eq_sat_and {S1 S2 R1 R2} q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q TP1 TP2 -> eq_sat_sep_sbuter q TP1' TP2' ->
    eq_sat_sep_sbuter q (fun ts => TP1 ts /\ TP1' ts) (fun ts => TP2 ts /\ TP2' ts).
Proof.
  intros esss esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.

Lemma eq_sat_or {S1 S2 R1 R2} q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q TP1 TP2 -> eq_sat_sep_sbuter q TP1' TP2' ->
    eq_sat_sep_sbuter q (fun ts => TP1 ts \/ TP1' ts) (fun ts => TP2 ts \/ TP2' ts).
Proof.
  intros esss esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.

Lemma eq_sat_impl {S1 S2 R1 R2} q (TP1 TP1' : TPred S1 R1) (TP2 TP2' : TPred S2 R2)
  : eq_sat_sep_sbuter q TP1 TP2 -> eq_sat_sep_sbuter q TP1' TP2' ->
    eq_sat_sep_sbuter q (fun ts => TP1 ts -> TP1' ts) (fun ts => TP2 ts -> TP2' ts).
Proof.
  intros esss esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs.
  rewrite (esss p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  rewrite (esss' p Q t1 s1 t2 s2 pre_q sep sb no_errs).
  reflexivity.
Qed.


(** * `eq_sat_sep_sbuter` for `EU`  **)

Inductive EU {S R} (P P' : TPred S R) (ts0 : CompM S R * S) : Prop :=
| EU_here : P' ts0 -> EU P P' ts0
| EU_step ts1 : P ts0 -> step ts0 ts1 -> EU P P' ts1 -> EU P P' ts0.

Lemma EU_path {S1 R1} (P P' : TPred S1 R1) n ts0 (ts : Vector.t _ n) tsf :
  P ts0 -> (forall i, P (ts [@i])) ->
  is_finite_path n ts0 ts tsf -> EU P P' tsf -> EU P P' ts0.
Proof.
  intros; revert ts0 H H0 H1.
  induction ts; intros.
  - destruct H1.
    + destruct ts0, tsf; injection H1; intros; subst; eauto.
    + eapply EU_step; eauto.
  - destruct H1.
    eapply EU_step, IHts; eauto.
    + apply (H0 Fin.F1).
    + intro i; apply (H0 (Fin.FS i)).
Qed.

Lemma eq_sat_EU {S1 S2 R1 R2} q (P1 P1' : TPred S1 R1) (P2 P2' : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 -> eq_sat_sep_sbuter q P1' P2' ->
    eq_sat_sep_sbuter q (EU P1 P1') (EU P2 P2').
Proof.
  intros eq_sat_Ps eq_sat_P's; split; intros.
  - revert p t2 s2 H H0 H1 H2; dependent induction H3; intros.
    + eapply EU_here, eq_sat_P's; eauto.
    + destruct ts1.
      pose proof (sbuter_to_sbuter_ex _ _ _ _ _ _ H4).
      pose proof (sbuter_step_l _ _ _ _ _ _ _ _ H5 H0 H6).
      destruct H7 as [t4 [s4 ?]]; dependent destruction H7.
      destruct H9 as [p' [? ?]].
      unshelve eapply EU_path, (IHEU q _ _ _ _ Q c s JMeq_refl p'); eauto.
      * eapply eq_sat_Ps; eauto.
      * intro i; specialize (H8 i); destruct H8 as [[p'' [? ?]] ?].
        pose proof (is_finite_path_no_errors_mid _ _ _ _ _ _ H7 H5 i).
        destruct (ts[@i]).
        eapply (eq_sat_Ps p''); eauto.
        respects; eapply sep_r; eauto.
      * respects; eapply sep_r; eauto.
      * eapply is_finite_path_no_errors_end; eauto.
  - revert p t1 s1 H H0 H1 H2; dependent induction H3; intros.
    + eapply EU_here, eq_sat_P's; eauto.
    + destruct ts1.
      pose proof (sbuter_to_sbuter_ex _ _ _ _ _ _ H4).
      pose proof (sbuter_step_r _ _ _ _ _ _ _ _ H0 H6).
      destruct H7 as [t3 [s3 ?]]; dependent destruction H7.
      destruct H9 as [p' [? ?]].
      unshelve eapply EU_path, (IHEU q _ _ _ _ Q c s JMeq_refl p'); eauto.
      * eapply eq_sat_Ps; eauto.
      * intro i; specialize (H8 i); destruct H8 as [[p'' [? ?]] ?].
        destruct (ts[@i]).
        eapply (eq_sat_Ps p''); eauto.
        respects; eapply sep_r; eauto.
      * respects; eapply sep_r; eauto.
      * eapply step_no_errors; eauto.
Qed.


(** * `eq_sat_sep_sbuter` for `EF`  **)

Definition EF {S R} := @EU S R (fun _ => True).

Lemma eq_sat_EF {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (EF P1) (EF P2).
Proof. eapply eq_sat_EU; easy. Qed.


(** * `eq_sat_sep_sbuter` for `AF`  **)

Definition AG_gen {S R} (P : TPred S R) (AG : TPred S R) ts0 :=
  P ts0 /\ (forall ts1, step ts0 ts1 -> AG ts1).

Definition AG {S R} P := paco1 (@AG_gen S R P) bot1.

Lemma is_path_gen_mon {S R P} : monotone1 (@AG_gen S R P).
Proof. repeat intro; induction IN; econstructor; eauto. Qed.
Hint Resolve is_path_gen_mon : paco.

Lemma AG_step {S1 R1} (P : TPred S1 R1) ts0 ts1 :
  step ts0 ts1 -> AG P ts0 -> AG P ts1.
Proof.
  intros.
  punfold H0; destruct H0.
  specialize (H1 _ H).
  pclearbot; punfold H1; destruct H1.
  pfold; split; eauto.
Qed.

Lemma AG_path {S1 R1} (P : TPred S1 R1) n ts0 (ts : Vector.t _ n) tsf :
  (forall i, P (ts [@i])) ->
  is_finite_path n ts0 ts tsf -> AG P ts0 -> AG P tsf.
Proof.
  intros; revert ts0 H0 H1.
  induction ts; [|destruct h]; intros; [destruct H0|].
  - destruct ts0, tsf; injection H0; intros; subst; eauto.
  - eapply AG_step; eauto.
  - destruct H0.
    eapply IHts; eauto.
    + intro; specialize (H (Fin.FS i)); eauto.
    + eapply AG_step; eauto.
Qed.

Lemma eq_sat_AG {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (AG P1) (AG P2).
Proof.
  intro eq_sat_Ps; split; intros.
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    pfold; split.
    + punfold H4; destruct H4; eauto.
      eapply eq_sat_Ps; eauto.
    + intros; destruct ts1.
      apply sbuter_to_sbuter_ex in H2.
      pose proof (sbuter_step_r _ _ _ _ _ _ _ _ H H2).
      destruct H5 as [t3 [s3 ?]]; dependent destruction H5.
      destruct H7 as [p' [? ?]].
      right; eapply (CIH p' t3 s3 c s); eauto.
      * respects; eapply sep_r; eauto.
      * eapply step_no_errors; eauto.
      * eapply AG_path; eauto; intro.
        specialize (H6 i); destruct H6.
        destruct H6 as [p'' [? ?]].
        destruct (ts[@i]); unfold fst, snd in *.
        eapply (eq_sat_Ps p'' Q); eauto.
        -- respects; apply (sep_r p q); eauto.
        -- punfold H4; destruct H4.
           destruct H2 as [p''' [? ?]].
           eapply (eq_sat_Ps p''' Q); eauto.
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    pfold; split.
    + punfold H4; destruct H4; eauto.
      eapply eq_sat_Ps; eauto.
    + intros; destruct ts1.
      apply sbuter_to_sbuter_ex in H2.
      pose proof (sbuter_step_l _ _ _ _ _ _ _ _ H3 H H2).
      destruct H5 as [t4 [s4 ?]]; dependent destruction H5.
      destruct H7 as [p' [? ?]].
      right; eapply (CIH p' c s t4 s4); eauto.
      * respects; eapply sep_r; eauto.
      * eapply is_finite_path_no_errors_end; eauto.
      * pose proof (is_finite_path_no_errors_mid _ _ _ _ _ _ H5 H3).
        eapply AG_path; eauto; intro.
        specialize (H6 i); destruct H6.
        specialize (H10 i).
        destruct H6 as [p'' [? ?]].
        destruct (ts[@i]); unfold fst, snd in *.
        eapply (eq_sat_Ps p'' Q); eauto.
        -- respects; apply (sep_r p q); eauto.
        -- punfold H4; destruct H4.
           destruct H2 as [p''' [? ?]].
           eapply (eq_sat_Ps p''' Q); eauto.
Qed.


(** * `stops` and `steps` **)

(* The proposition that an itree has a next step *)
Inductive steps {S R} : TPred S R :=
| steps_Tau t s : steps (Tau t, s)
| steps_Modify f k s : steps (vis (Modify f) k, s)
| steps_Choice k s : steps (vis Or k, s).

(* The proposition that an itree has no next step *)
Inductive stops {S R} : TPred S R :=
| stops_Ret r s : stops (Ret r, s)
| stops_Err k s : stops (vis (Throw tt) k, s).

Hint Constructors steps stops : core.

(* Every itree either stops or steps *)
Lemma steps_or_stops {S R} (t' : itree' (sceE R) S) s :
  steps (go t', s) \/ stops (go t', s).
Proof.
  dependent destruction t'; eauto.
  destruct e as [? | [? | ?]].
  + destruct e, u; right; constructor.
  + destruct m; left; constructor.
  + destruct n; left; constructor.
Qed.


(** * `eq_sat_sep_sbuter` for `EG` **)

Inductive EG_gen {S R} (P : TPred S R) EG ts0 : Prop :=
| EG_step ts1 : P ts0 -> step ts0 ts1 -> EG ts1 -> EG_gen P EG ts0
| EG_stop : P ts0 -> stops ts0 -> EG_gen P EG ts0.
Arguments EG_step {S R P EG ts0} ts1.
Arguments EG_stop {S R P EG ts0}.

Definition EG {S R} P := paco1 (@EG_gen S R P) bot1.

Lemma EG_gen_mon {S R P} : monotone1 (@EG_gen S R P).
Proof. repeat intro; induction IN; subst; solve [econstructor; eauto]. Qed.
Hint Resolve EG_gen_mon : paco.

Definition EG_gen_pf {S R P EG ts0} : @EG_gen S R P EG ts0 -> P ts0.
Proof. destruct 1; eauto. Defined.

Definition EG_pf {S R P ts0} : @EG S R P ts0 -> P ts0.
Proof. intro; punfold H; destruct H; eauto. Defined.

Lemma eq_sat_EG {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (EG P1) (EG P2).
Proof.
  intro eq_sat_Ps; split; intros.
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    punfold H2; dependent induction H2.
    (* sbuter_gen_ret *)
    + punfold H4; inv H4; [inv H6|].
      pfold; constructor; eauto.
      eapply eq_sat_Ps; eauto.
      pfold; constructor; eauto.
    (* sbuter_gen_err *)
    + punfold H3; inv H3.
    (* sbuter_gen_tau_L *)
    + punfold H4; inv H4; inv H6; pclearbot.
      apply IHsbuter_gen; eauto.
    (* sbuter_gen_tau_R *)
    + pfold; apply (EG_step (t2,c2)).
      * apply EG_pf in H4.
        eapply (eq_sat_Ps _ Q); eauto.
        pfold; econstructor; eauto.
      * constructor; eauto.
      * left; apply IHsbuter_gen; eauto.
        apply no_errors_Tau; eauto.
    (* sbuter_gen_tau *)
    + punfold H4; inv H4; inv H6; pclearbot.
      pfold; apply (EG_step (t2,c2)).
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 5; eauto.
      * constructor.
      * right; eapply CIH; eauto.
        apply no_errors_Tau; eauto.
    (* sbuter_gen_modify_L *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      apply IHsbuter_gen; eauto.
      respects; eapply sep_r; eauto.
    (* sbuter_gen_modify_R *)
    + pfold; apply (EG_step (k c2, f c2)).
      * apply EG_pf in H6.
        eapply (eq_sat_Ps p Q); eauto.
        pfold; econstructor 7; eauto.
      * constructor; eauto.
      * left; apply IHsbuter_gen; eauto.
        -- respects; eapply sep_r; eauto.
        -- apply no_errors_Modify; eauto.
    (* sbuter_gen_modify *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      pfold; apply (EG_step (k2 c2, f2 c2)).
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 8; eauto.
      * constructor.
      * right; eapply (CIH p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- apply no_errors_Modify; eauto.
    (* sbuter_gen_choice_L *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      apply (H4 b); eauto.
    (* sbuter_gen_choice_R *)
    + pfold; apply (EG_step (k false, c2)).
      * apply EG_pf in H6.
        eapply (eq_sat_Ps p Q); eauto.
        pfold; econstructor 10; eauto.
      * constructor; eauto.
      * left; apply (H4 false); eauto.
        apply no_errors_Choice; eauto.
    (* sbuter_gen_choice *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      pose proof (H3 b); destruct H6 as [b2].
      pfold; apply (EG_step (k2 b2, c2)).
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 11; eauto.
      * constructor.
      * right; eapply (CIH p'); eauto.
        -- destruct H6; [ eauto | inv H6 ].
        -- apply no_errors_Choice; eauto.
  (* The rest is basically identical to the above. *)
  - revert p t1 s1 t2 s2 H H0 H1 H2 H3; pcofix CIH; intros.
    punfold H2; dependent induction H2.
    (* sbuter_gen_ret *)
    + punfold H4; inv H4; [inv H6|].
      pfold; constructor; eauto.
      eapply eq_sat_Ps; eauto.
      pfold; constructor; eauto.
    (* sbuter_gen_err *)
    + punfold H3; inv H3.
    (* sbuter_gen_tau_L *)
    + pfold; apply (EG_step (t1,c1)).
      * apply EG_pf in H4.
        eapply (eq_sat_Ps _ Q); eauto.
        pfold; econstructor; eauto.
      * constructor; eauto.
      * left; apply IHsbuter_gen; eauto.
    (* sbuter_gen_tau_R *)
    + punfold H4; inv H4; inv H6; pclearbot.
      apply IHsbuter_gen; eauto.
      apply no_errors_Tau; eauto.
    (* sbuter_gen_tau *)
    + punfold H4; inv H4; inv H6; pclearbot.
      pfold; apply (EG_step (t1,c1)).
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 5; eauto.
      * constructor.
      * right; eapply CIH; eauto.
        apply no_errors_Tau; eauto.
    (* sbuter_gen_modify_L *)
    + pfold; apply (EG_step (k c1, f c1)).
      * apply EG_pf in H6.
        eapply (eq_sat_Ps p Q); eauto.
        pfold; econstructor 6; eauto.
      * constructor; eauto.
      * left; apply IHsbuter_gen; eauto.
        respects; eapply sep_r; eauto.
    (* sbuter_gen_modify_R *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      apply IHsbuter_gen; eauto.
      -- respects; eapply sep_r; eauto.
      -- apply no_errors_Modify; eauto.
    (* sbuter_gen_modify *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      pfold; apply (EG_step (k1 c1, f1 c1)).
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 8; eauto.
      * constructor.
      * right; eapply (CIH p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- apply no_errors_Modify; eauto.
    (* sbuter_gen_choice_L *)
    + pfold; apply (EG_step (k false, c1)).
      * apply EG_pf in H6.
        eapply (eq_sat_Ps p Q); eauto.
        pfold; econstructor 9; eauto.
      * constructor; eauto.
      * left; apply (H4 false); eauto.
    (* sbuter_gen_choice_R *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      apply (H4 b); eauto.
      apply no_errors_Choice; eauto.
    (* sbuter_gen_choice *)
    + punfold H6; inv H6; dependent destruction H8; pclearbot.
      pose proof (H4 b); destruct H6 as [b1].
      pfold; apply (EG_step (k1 b1, c1)).
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 11; eauto.
      * constructor.
      * right; eapply (CIH p' _ _ (k2 b) c2); eauto.
        -- destruct H6; [ eauto | inv H6 ].
        -- apply no_errors_Choice; eauto.
Qed.


(** * `eq_sat_sep_sbuter` for `AU` **)

Inductive AU {S R} (P P' : TPred S R) ts0 : Prop :=
| AU_here : P' ts0 -> AU P P' ts0
| AU_step : P ts0 -> steps ts0 ->
            (forall t1 s1, step ts0 (t1,s1) -> AU P P' (t1,s1)) ->
            AU P P' ts0.

Lemma eq_sat_AU {S1 S2 R1 R2} q (P1 P1' : TPred S1 R1) (P2 P2' : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 -> eq_sat_sep_sbuter q P1' P2' ->
    eq_sat_sep_sbuter q (AU P1 P1') (AU P2 P2').
Proof.
  intros eq_sat_Ps eq_sat_P's; split; intros.
  - revert p t2 s2 H H0 H1 H2; dependent induction H3; intros.
    eapply AU_here, eq_sat_P's; eauto.
    punfold H5; dependent induction H5; intros.
    (* sbuter_gen_ret *)
    + inv H0.
    (* sbuter_gen_err *)
    + punfold H6; inv H6.
    (* sbuter_gen_tau_L *)
    + eapply (H2 t1 c1); eauto.
      pfold; eauto.
    (* sbuter_gen_tau_R *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor; eauto.
      * intros; inv H8.
        eapply IHsbuter_gen; eauto.
        apply no_errors_Tau; eauto.
    (* sbuter_gen_tau *)
    + apply AU_step; eauto; pclearbot.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 5; eauto.
      * intros; inv H9.
        eapply (H2 t1 c1); eauto.
        apply no_errors_Tau; eauto.
    (* sbuter_gen_modify_L *)
    + unshelve eapply (H2 (k c1) (f c1) _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
      * respects; eapply sep_r; eauto.
      * pfold; eauto.
    (* sbuter_gen_modify_R *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor; eauto.
      * intros; inv H10; apply inj_pair2 in H13; subst.
        eapply IHsbuter_gen; eauto.
        -- respects; eapply sep_r; eauto.
        -- apply no_errors_Modify; eauto.
    (* sbuter_gen_modify *)
    + apply AU_step; eauto; pclearbot.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 8; eauto.
      * intros; inv H11; apply inj_pair2 in H13; subst.
        unshelve eapply (H2 (k1 c1) (f1 c1) _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- apply no_errors_Modify; eauto.
    (* sbuter_gen_choice_L *)
    + unshelve eapply (H2 (k false) c1 _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
      pfold; apply H7.
    (* sbuter_gen_choice_R *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor; eauto.
      * intros; inv H10; apply inj_pair2 in H12; subst.
        eapply H8; eauto.
        apply no_errors_Choice; eauto.
    (* sbuter_gen_choice *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 11; eauto.
      * intros; inv H10; apply inj_pair2 in H12; subst.
        specialize (H8 b); destruct H8 as [b1].
        pclearbot.
        unshelve eapply (H2 (k1 b1) c1 _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
        apply no_errors_Choice; eauto.
  (* The rest is basically identical to the above. *)
  - revert p t1 s1 H H0 H1 H2; dependent induction H3; intros.
    eapply AU_here, eq_sat_P's; eauto.
    punfold H5; dependent induction H5; intros.
    (* sbuter_gen_ret *)
    + inv H0.
    (* sbuter_gen_err *)
    + punfold H6; inv H6.
    (* sbuter_gen_tau_L *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor; eauto.
      * intros; inv H8.
        eapply IHsbuter_gen; eauto.
    (* sbuter_gen_tau_R *)
    + eapply (H2 t2 c2); eauto.
      * pfold; eauto.
      * apply no_errors_Tau; eauto.
    (* sbuter_gen_tau *)
    + apply AU_step; eauto; pclearbot.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 5; eauto.
      * intros; inv H9.
        eapply (H2 t2 c2); eauto.
        apply no_errors_Tau; eauto.
    (* sbuter_gen_modify_L *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor; eauto.
      * intros; inv H10; apply inj_pair2 in H13; subst.
        eapply IHsbuter_gen; eauto.
        respects; eapply sep_r; eauto.
    (* sbuter_gen_modify_R *)
    + unshelve eapply (H2 (k c2) (f c2) _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
      * respects; eapply sep_r; eauto.
      * pfold; eauto.
      * apply no_errors_Modify; eauto.
    (* sbuter_gen_modify *)
    + apply AU_step; eauto; pclearbot.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 8; eauto.
      * intros; inv H11; apply inj_pair2 in H13; subst.
        unshelve eapply (H2 (k2 c2) (f2 c2) _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
        -- respects; eapply sep_r; eauto.
        -- apply no_errors_Modify; eauto.
    (* sbuter_gen_choice_L *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor; eauto.
      * intros; inv H10; apply inj_pair2 in H12; subst.
        eapply H8; eauto.
    (* sbuter_gen_choice_R *)
    + unshelve eapply (H2 (k false) c2 _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
      * pfold; apply H7.
      * apply no_errors_Choice; eauto.
    (* sbuter_gen_choice *)
    + apply AU_step; eauto.
      * eapply eq_sat_Ps; eauto.
        pfold; econstructor 11; eauto.
      * intros; inv H10; apply inj_pair2 in H12; subst.
        specialize (H7 b); destruct H7 as [b2].
        pclearbot.
        unshelve eapply (H2 (k2 b2) c2 _ q _ _ _ _ _ _ _ JMeq_refl p'); eauto.
        apply no_errors_Choice; eauto.
Qed.


(** * `eq_sat_sep_sbuter` for `AF` **)

Definition AF {S R} := @AU S R (fun _ => True).

Lemma eq_sat_AF {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2) :
    eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (AF P1) (AF P2).
Proof. apply eq_sat_AU; easy. Qed.


(** * Definition of our fragment of CTL **)

Inductive CTLformula {S} : Type :=
| CTL_st (P:S -> Prop)
| CTL_and (tp1 tp2:CTLformula)
| CTL_or (tp1 tp2:CTLformula)
| CTL_impl (tp1 tp2:CTLformula)
| CTL_EF (tp:CTLformula)
| CTL_EG (tp:CTLformula)
| CTL_AF (tp:CTLformula)
| CTL_AG (tp:CTLformula)
| CTL_EU (tp1 tp1:CTLformula)
| CTL_AU (tp1 tp1:CTLformula).

Fixpoint CTLsats {S R} (tp:@CTLformula S): TPred S R :=
  match tp with
  | CTL_st P => state_pred _ P
  | CTL_and tp1 tp2 => fun ts => CTLsats tp1 ts /\ CTLsats tp2 ts
  | CTL_or tp1 tp2 => fun ts => CTLsats tp1 ts \/ CTLsats tp2 ts
  | CTL_impl tp1 tp2 => fun ts => CTLsats tp1 ts -> CTLsats tp2 ts
  | CTL_EF tp => EF (CTLsats tp)
  | CTL_EG tp => EG (CTLsats tp)
  | CTL_AF tp => AF (CTLsats tp)
  | CTL_AG tp => AG (CTLsats tp)
  | CTL_EU tp1 tp2 => EU (CTLsats tp1) (CTLsats tp2)
  | CTL_AU tp1 tp2 => AU (CTLsats tp1) (CTLsats tp2)
  end.

Inductive CTLsim {S1 S2} q: @CTLformula S1 -> @CTLformula S2 -> Prop :=
| CTLsim_st P1 P2 : q_similar q P1 P2 -> CTLsim q (CTL_st P1) (CTL_st P2)
| CTLsim_and tp1 tp2 tp1' tp2' : CTLsim q tp1 tp2 -> CTLsim q tp1' tp2' ->
                                CTLsim q (CTL_and tp1 tp1') (CTL_and tp2 tp2')
| CTLsim_or tp1 tp2 tp1' tp2' : CTLsim q tp1 tp2 -> CTLsim q tp1' tp2' ->
                               CTLsim q (CTL_or tp1 tp1') (CTL_or tp2 tp2')
| CTLsim_impl tp1 tp2 tp1' tp2' : CTLsim q tp1 tp2 -> CTLsim q tp1' tp2' ->
                                 CTLsim q (CTL_impl tp1 tp1') (CTL_impl tp2 tp2')
| CTLsim_EF tp1 tp2 : CTLsim q tp1 tp2 -> CTLsim q (CTL_EF tp1) (CTL_EF tp2)
| CTLsim_EG tp1 tp2 : CTLsim q tp1 tp2 -> CTLsim q (CTL_EG tp1) (CTL_EG tp2)
| CTLsim_AF tp1 tp2 : CTLsim q tp1 tp2 -> CTLsim q (CTL_AF tp1) (CTL_AF tp2)
| CTLsim_AG tp1 tp2 : CTLsim q tp1 tp2 -> CTLsim q (CTL_AG tp1) (CTL_AG tp2)
| CTLsim_EU tp1 tp2 tp1' tp2' : CTLsim q tp1 tp2 -> CTLsim q tp1' tp2' ->
                               CTLsim q (CTL_EU tp1 tp1') (CTL_EU tp2 tp2')
| CTLsim_AU tp1 tp2 tp1' tp2' : CTLsim q tp1 tp2 -> CTLsim q tp1' tp2' ->
                               CTLsim q (CTL_AU tp1 tp1') (CTL_AU tp2 tp2')
.

Lemma tpsim_implies_eq_sat_sep_sbuter {S1 S2 R1 R2} q TP1 TP2:
  CTLsim q TP1 TP2 -> @eq_sat_sep_sbuter S1 S2 R1 R2 q (CTLsats TP1) (CTLsats TP2).
Proof.
  intro tp_sim; induction tp_sim.
  - apply eq_sat_state_preds; assumption.
  - apply eq_sat_and; assumption.
  - apply eq_sat_or; assumption.
  - apply eq_sat_impl; assumption.
  - apply eq_sat_EF; assumption.
  - apply eq_sat_EG; assumption.
  - apply eq_sat_AF; assumption.
  - apply eq_sat_AG; assumption.
  - apply eq_sat_EU; assumption.
  - apply eq_sat_AU; assumption.
Qed.

Theorem sbuter_preserves_tpreds {S1 R1 S2 R2} p q Q t1 s1 t2 s2 TP1 TP2:
  @sbuter S1 R1 S2 R2 p Q t1 s1 t2 s2 -> no_errors s2 t2 ->
  CTLsim q TP1 TP2 -> pre (p ** q) (s1, s2) ->
  CTLsats TP1 (t1, s1) <-> CTLsats TP2 (t2, s2).
Proof.
  intros sb ne tp_sim pre_pq. destruct pre_pq as [ pre_p [ pre_q sep ]].
  eapply (tpsim_implies_eq_sat_sep_sbuter q TP1 TP2 tp_sim); eassumption.
Qed.
