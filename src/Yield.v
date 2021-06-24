From Coq Require Import
     List
     Logic.FunctionalExtensionality.

From Heapster Require Import
     Permissions
     SepStep.

From ITree Require Import
     ITree
     Basics.Basics
     ITreeFacts
     Events.State
     Events.StateFacts
     Events.Nondeterminism
     Events.Exception
     Eq.EqAxiom.

Require Import Paco.paco.

Import ITreeNotations.
Import ListNotations.
Import ITree.Basics.Basics.Monads.

Local Open Scope itree_scope.

Ltac rewritebisim lem := pose proof lem as bisim;
                         eapply bisimulation_is_eq in bisim;
                         rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply bisimulation_is_eq in bisim;
                              rewrite bisim in H;
                              clear bisim.

Variant yieldE S : Type -> Type :=
| Yield : S -> yieldE S S.

Section parallel.
  Parameter config : Type.

  Definition thread := stateT config (itree (yieldE config)) unit.

  Definition choose {E} `{nondetE -< E} {X}
    : X -> list X -> list X -> itree E (X * list X)
    := fix choose1' x xs rest : itree E (X * list X) :=
         match xs with
         | [] => Ret (x, rest)
         | x' :: xs => or (Ret (x, (x' :: xs) ++ rest)) (choose1' x' xs (x :: rest))
         end.

  Definition par_match par (curr : thread) (rest : list thread)
    : stateT config (itree nondetE) unit :=
    fun s =>
      match (observe (curr s)) with
      | RetF (s', _) => match rest with
                       | nil => Ret (s', tt)
                       | cons h t => Tau (par h t s')
                       end
      | TauF t => Tau (par (fun _ => t) rest s)
      | VisF (Yield _ s') k =>
        '(curr', rest') <- choose k rest [];;
        Tau (par curr' rest' s')
      end.
  CoFixpoint par := par_match par.
  Lemma rewrite_par curr rest : par curr rest = par_match par curr rest.
  Proof.
  Admitted.

  (* Lemma par_unit : *)
  (*   forall t, par (fun s => Ret (s, tt)) [t] = par t [fun s => Ret (s, tt)]. *)
  (* Proof. *)
  (*   intros. do 2 rewrite rewrite_par. *)
  (*   unfold par_match. apply functional_extensionality. intros. simpl. *)
  (*   destruct (observe (t x)) eqn:?. *)
  (*   - destruct r. admit. *)
  (*   - admit. *)
  (*   - destruct e. *)
  (* Qed. *)
End parallel.

Definition E config := yieldE config +' nondetE.

Variant typing_gen {config R} typing (p : perm) (Q : R -> Perms) :
  config -> itree (E config) (config * R) -> Prop :=
  (* stateT config (itree (yieldE config)) R -> Prop := *)
| typing_gen_ret r c c' :
    pre p c ->
    p ∈ Q r ->
    guar p c c' ->
    typing_gen typing p Q c (Ret (c', r))
| typing_gen_tau t c :
    pre p c ->
    typing p Q c t ->
    typing_gen typing p Q c (Tau t)
| typing_gen_vis k c c' p' :
    pre p c ->
    guar p c c' ->
    sep_step p p' ->
    (forall c'', rely p c' c'' -> typing p' Q c'' (k c'')) ->
    typing_gen typing p Q c (vis (Yield _ c') k).

Lemma typing_gen_mon {config R} : monotone4 (@typing_gen config R).
Proof.
  repeat intro. inversion IN; subst; econstructor; eauto.
Qed.
Hint Resolve typing_gen_mon : paco.

Definition typing_ {config R} := paco4 (@typing_gen config R) bot4.

Lemma typing__lte {config R} p (Q Q' : R -> Perms) (c : config) t :
  typing_ p Q c t ->
  (forall r, Q r ⊨ Q' r) ->
  typing_ p Q' c t.
Proof.
  revert p Q Q' c t. pcofix CIH. intros p Q Q' c t Htyping Hlte.
  punfold Htyping. pstep.
  inversion Htyping; pclearbot; subst; econstructor; eauto.
  - apply Hlte; eauto.
  - intros. specialize (H2 _ H3). pclearbot. right. eapply CIH; eauto.
Qed.

Definition typing {config R} P Q (t : stateT config (itree (E config)) R) :=
  forall p c c', p ∈ P -> pre p c -> guar p c c' -> typing_ p Q c (t c').
(* also pre p c'? *)

Lemma typing_lte {config R} P P' Q Q' (t : stateT config (itree (E config)) R) :
  typing P Q t ->
  P' ⊨ P ->
  (forall r, Q r ⊨ Q' r) ->
  typing P' Q' t.
Proof.
  repeat intro. eapply typing__lte; eauto.
Qed.

Lemma typing__bind {config R S} p (Q1 : R -> Perms) (Q2 : S -> Perms) (c : config) t1 t2 r' :
  pre p c ->
  typing_ p Q1 c t1 ->
  (forall r p c c', p ∈ Q1 r ->
               pre p c ->
               guar p c c' ->
               paco4 typing_gen r' p Q2 c (t2 r c')) ->
  paco4 typing_gen r' p Q2 c (x <- t1;; t2 (snd x) (fst x)).
Proof.
  revert p Q1 Q2 c t1 t2. pcofix CIH. intros p Q1 Q2 c t1 t2 Hpre Htyping1 Htyping2.
  pinversion Htyping1; subst.
  - rewritebisim @bind_ret_l. eapply paco4_mon; eauto.
  - rewritebisim @bind_tau. pstep. econstructor; eauto.
  - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
    specialize (H2 _ H3). pclearbot. right. eapply CIH; eauto.
    pinversion H2; auto.
Qed.

Lemma typing_bind {config R S} P Q1 Q2 (t1 : stateT config (itree (E config)) R) (t2 : R -> stateT config (itree (E config)) S) :
  typing P Q1 t1 ->
  (forall r, typing (Q1 r) Q2 (t2 r)) ->
  typing P Q2 (bind t1 t2).
Proof.
  repeat intro. unfold bind. unfold Monad_stateT. red.
  eapply typing__bind; eauto.
Qed.
