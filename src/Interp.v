From Heapster Require Import
     Permissions
     Config
     NoEvent
     Functional.

From Coq Require Import
     Program
     Morphisms
     Streams.

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


Definition traceE S := (exceptE unit +' writerE S).

Definition trace S R := itree (traceE S) R.

Definition StTraceM S := stateT (S * Stream bool) (trace S).

(* Trivial instances for `trace` and `StTraceM` *)
Instance Functor_trace {S} : Functor (trace S) := Functor_itree.
Instance Functor_StTraceM {S} : Functor (StTraceM S) := Functor_stateT.
Instance Monad_trace {S} : Monad (trace S) := Monad_itree.
Instance Monad_StTraceM {S} : Monad (StTraceM S) := Monad_stateT.
Instance MonadIter_trace {S} : MonadIter (trace S) := MonadIter_itree.
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


Inductive ruts_gen {S1 S2 R1 R2} ruts (PS:S1 -> S2 -> Prop) (PR:R1 -> R2 -> Prop) :
  S1 -> trace S1 R1 -> S2 -> trace S2 R2 -> Prop :=
| ruts_ret s1 r1 s2 r2 :
    PR r1 r2 -> ruts_gen ruts PS PR s1 (Ret r1) s2 (Ret r2)
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
