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


(** * `steps_to` and lemmas **)

Inductive steps_to' {S R} : itree (sceE S) R -> S -> itree (sceE S) R -> S -> Prop :=
| steps_to'_modify f k s : steps_to' (vis (Modify f) k) s (k s) (f s)
| steps_to'_or b k s1 t2 s2 : steps_to' (k b) s1 t2 s2 -> steps_to' (vis Or k) s1 t2 s2.

Definition steps_to {S R} t1 s1 t2 s2 :=
  exists t1' t2', t1 ≈ t1' /\ t2 ≈ t2' /\ @steps_to' S R t1' s1 t2' s2.

Global Instance Proper_steps_to {S R} :
  Proper (eutt eq ==> eq ==> eutt eq ==> eq ==> impl) (@steps_to S R).
Proof.
  intros t1 t1' eqt1 s1 s1' eqs1 t2 t2' eqt2 s2 s2' eqs2 H.
  destruct H as [t1'' [t2'' [eqt1' [eqt2' H]]]].
  exists t1''; exists t2''; split; [|split].
  - rewrite <- eqt1; assumption.
  - rewrite <- eqt2; assumption.
  - rewrite <- eqs1, <- eqs2; assumption.
Qed.

Definition steps_to_modify {S R} f k s  : @steps_to S R (vis (Modify f) k) s (k s) (f s).
Proof.
  esplit; esplit; split; [|split].
  - reflexivity.
  - reflexivity.
  - apply steps_to'_modify.
Qed.

Lemma steps_to_Tau_L {S R} t1 s1 t2 s2 :
  @steps_to S R t1 s1 t2 s2 <-> @steps_to S R (Tau t1) s1 t2 s2.
Proof.
  split; rewrite tau_eutt; easy.
Qed.

Lemma no_errors_steps_to {S R} (t : CompM S R) s (t' : CompM S R) s' :
  steps_to t s t' s' -> no_errors s t -> no_errors s' t'.
Proof.
  intros [t1' [t2' [eq_t1 [eq_t2 Ht]]]] ne_t.
  induction Ht.
  - punfold ne_t; induction ne_t.
    + punfold eq_t1; inversion eq_t1.
    + rewrite eq_t2.
Admitted.


(** * `is_path` and lemmas **)

(* The proposition that `(t0,s0) steps_to ... (ti,si) ... steps_to (tf,sf)` *)
Fixpoint steps_between {S R} {n} t0 s0 (ts : Vector.t (CompM S R * S) n) tf sf :=
  match ts with
  | [] => steps_to t0 s0 tf sf
  | (t,s) :: ts => steps_to t0 s0 t s /\ steps_between t s ts tf sf
  end.

(* The proposition that there are `n` steps from (t0,s0) to (tf,sf),
   i.e. `t0 ≈ tf /\ s0 = sf` or `(t0,s0) steps_to ... (ti,si) ... steps_to (tf,sf)` *)
Definition is_path {S R} n t0 s0 (ts : Vector.t (CompM S R * S) (pred n)) tf sf :=
  match n return Vector.t _ (pred n) -> Prop with
  | 0 => fun _ => t0 ≈ tf /\ s0 = sf
  | S n' => fun ts => steps_between t0 s0 ts tf sf
  end ts.

Lemma is_path_Tau_l {S R} n t0 s0 (ts : Vector.t (CompM S R * S) (pred n)) tf sf :
  is_path n t0 s0 ts tf sf <-> is_path n (Tau t0) s0 ts tf sf.
Proof.
  destruct n; simpl.
  - split; intros [eqt eqs].
    + now apply eqit_tauL in eqt.
    + now apply eqit_inv_tauL in eqt.
  - simpl in ts; destruct ts; [|destruct h]; simpl.
    all: now rewrite steps_to_Tau_L.
Defined.

Lemma no_errors_is_path {S R} n t0 s0 (ts : Vector.t (CompM S R * S) (pred n)) tf sf :
  is_path n t0 s0 ts tf sf -> no_errors s0 t0 -> no_errors sf tf.
Proof.
  destruct n; simpl.
  - intros [? ?].
    now rewrite H, H0.
  - revert t0 s0 tf sf.
    simpl in ts; induction ts; [|destruct h]; simpl.
    + apply no_errors_steps_to.
    + intros; destruct H.
      apply (IHts c s tf sf); try assumption.
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
Lemma steps_to'_sbuter_l {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 -> steps_to' t1 s1 t2 s2 -> sbuter p Q t1 s1 t3 s3 ->
  exists n (ts : Vector.t (CompM S2 R2 * S2) (pred n)) t4 s4,
    is_path n t3 s3 ts t4 s4 /\
    (forall i, sbuter_ex p Q t1 s1 (fst ts[@i]) (snd ts[@i]) /\
               guar p (s1, s3) (s1, snd ts[@i])) /\
    sbuter_ex p Q t2 s2 t4 s4 /\ guar p (s1, s3) (s2, s4).
Proof.
  intros ne3 Ht Hb.
  induction Ht.
  - punfold Hb; dependent induction Hb.
    (* sbuter_gen_err *)
    + punfold ne3; inv ne3.
    (* sbuter_gen_tau_R *)
    + apply no_errors_Tau in ne3.
      specialize (IHHb ne3 f k JMeq_refl eq_refl).
      destruct IHHb as [n [ts [t4 [s4 ?]]]].
      exists n; exists ts; exists t4; exists s4; split.
      * rewrite <- is_path_Tau_l; easy.
      * easy.
    (* sbuter_gen_modify_L *)
    + exists 0; exists []; exists t2; exists c2; split; [|split; [|split]].
      * split; reflexivity.
      * inversion i.
      * exists p'; split; try assumption.
        pfold; assumption.
      * assumption.
    (* sbuter_gen_modify_R *)
    + apply no_errors_Modify in ne3.
      specialize (IHHb ne3 f k JMeq_refl eq_refl).
      destruct IHHb as [n [ts [t4 [s4 [? [? [? ?]]]]]]].
      destruct n; [destruct H2|].
      * exists 1; exists []; exists (k0 c2); exists (f0 c2); split; [|split; [|split]].
        -- apply steps_to_modify.
        -- inversion i.
        -- rewrite H1, H2, H6; easy.
        -- rewrite <- H6 in H5.
           rewrite H0.
           apply (sep_step_guar p p'); easy.
      * exists (S (S n));exists ((k0 c2, f0 c2) :: ts); exists t4; exists s4; split; split.
        -- apply steps_to_modify.
        -- assumption.
        -- dependent destruction i; simpl.
           ++ split.
              ** exists p'; split; try assumption.
                 pfold; assumption.
              ** assumption.
           ++ specialize (H3 i); destruct H3; split.
              ** rewrite H1; assumption.
              ** rewrite H0.
                 apply (sep_step_guar p p'); assumption.
        -- split.
           ++ rewrite H1; assumption.
           ++ rewrite H0.
              apply (sep_step_guar p p'); assumption.
    (* sbuter_gen_modify *)
    + exists 1; exists []; exists (k2 c2); exists (f2 c2); split; [|split].
      * apply steps_to_modify.
      * inversion i.
      * pclearbot.
        split; [ exists p'; split |]; assumption.
    (* sbuter_gen_choice_R *)
    + admit.
  - admit.
Admitted.

Lemma steps_to_sbuter_l {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t2 s2 t3 s3 :
  no_errors s3 t3 -> steps_to t1 s1 t2 s2 -> sbuter p Q t1 s1 t3 s3 ->
  exists n (ts : Vector.t (CompM S2 R2 * S2) (pred n)) t4 s4,
    is_path n t3 s3 ts t4 s4 /\
    (forall i, sbuter_ex p Q t1 s1 (fst ts[@i]) (snd ts[@i]) /\
               guar p (s1, s3) (s1, snd ts[@i])) /\
    sbuter_ex p Q t2 s2 t4 s4 /\ guar p (s1, s3) (s2, s4).
Admitted.

Lemma steps_to_sbuter_r {S1 S2 R1 R2} (p:@perm (S1*S2)) (Q: R1 -> R2 -> Perms) t1 s1 t3 s3 t4 s4 :
  no_errors s3 t3 -> steps_to t3 s3 t4 s4 -> sbuter p Q t1 s1 t3 s3 ->
  exists n (ts : Vector.t (CompM S1 R1 * S1) (pred n)) t2 s2,
    is_path n t1 s1 ts t2 s2 /\
    (forall i, sbuter_ex p Q (fst ts[@i]) (snd ts[@i]) t3 s3 /\
               guar p (s1, s3) (snd ts[@i], s3)) /\
    sbuter_ex p Q t2 s2 t4 s4 /\ guar p (s1, s3) (s2, s4).
Admitted.


(** * `eq_sat_sep_sbuter` and basic facts  **)

Definition TPred S R := CompM S R -> S -> Prop.
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
| EF_eutt t s t' s' : t ≈ t' -> s = s' -> P t' s' -> EF P t s
| EF_step t s t' s' : steps_to t s t' s' -> EF P t' s' -> EF P t s.
Arguments EF_eutt {S R P t s} t' s'.
Arguments EF_step {S R P t s} t' s'.

Definition EF_refl {S R} {P : TPred S R} t s :=
 @EF_eutt S R P t s t s (reflexivity _) (reflexivity _).

Global Instance Proper_EF {S R P} : Proper (eutt eq ==> eq ==> impl) (@EF S R P).
Proof.
  intros t1 t2 eqt s1 s2 eqs H.
  induction H.
  - apply (EF_eutt t' s').
    + now rewrite <- eqt.
    + now rewrite <- eqs.
    + assumption.
  - apply (EF_step t' s').
    + now rewrite <- eqt, <- eqs.
    + assumption.
Qed.

Lemma EF_path {S1 R1 P} n t0 s0 (ts : Vector.t (CompM S1 R1 * S1) (pred n)) tf sf :
  is_path n t0 s0 ts tf sf -> EF P tf sf -> EF P t0 s0.
Proof.
  destruct n.
  - intros [eqt eqs].
    now rewrite eqt, eqs.
  - revert t0 s0.
    simpl in ts; induction ts; intros.
    + now apply (EF_step tf sf).
    + destruct h, H.
      apply (EF_step c s); try assumption.
      now apply IHts.
Qed.


(** * `eq_sat_EF`  **)

Lemma eq_sat_EF {S1 S2 R1 R2} q (P1 : TPred S1 R1) (P2 : TPred S2 R2)
  : eq_sat_sep_sbuter q P1 P2 ->
    eq_sat_sep_sbuter q (EF P1) (EF P2).
Proof.
  split; intro.
  - revert H4 p t2 s2 H0 H1 H2 H3.
    induction 1 as [t1 s1 | t1 s1 t1' s1']; intros.
    + apply (EF_refl t2 s2).
      rewrite H0 in H5.
      rewrite H1 in H3, H5.
      apply (H p Q t' s' t2 s2); assumption.
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
      rewrite H0 in H5, H6.
      rewrite H1 in H3, H5, H6.
      rewrite (H p Q t1 s1 t' s'); assumption.
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
