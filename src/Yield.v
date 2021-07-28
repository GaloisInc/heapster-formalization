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

(** return one of the elements in [x :: xs], as well as the complete list of unchosen elements *)
Fixpoint choose' {E} `{nondetE -< E} {X} (x : X) (xs : list X) (rest : list X) :
  itree E (X * list X)
  := match xs with
     | [] => Ret (x, rest)
     | x' :: xs => or
                   (Ret (x, (x' :: xs) ++ rest)) (* [x] *)
                   (choose' x' xs (x :: rest)) (* not [x] *)
     end.
Definition choose {E} `{nondetE -< E} {X} x xs : itree E (X * list X) :=
  choose' x xs [].

Definition E config := yieldE config +' nondetE.

Section parallel.
  Parameter config : Type.

  Definition thread := stateT config (itree (E config)) unit.

  (** Interprets away yields *)
  Definition par_match par (curr : thread) (rest : list thread)
    : thread :=
    fun s =>
      match (observe (curr s)) with
      | RetF (s', _) => match rest with
                       | [] => Ret (s', tt)
                       | h :: t => Tau (par h t s')
                       end
      | TauF t => Tau (par (fun _ => t) rest s)
      | VisF (inl1 e) k =>
        match e in yieldE _ C return (C -> itree (E config) (config * unit)) -> _ with
        | Yield _ s' =>
          fun k' =>
          '(curr', rest') <- choose k' rest;;
          Tau (par curr' rest' s')
        end k
      | VisF (inr1 e) k =>
        vis e (fun b => par (fun _ => k b) rest s)
      end.
  CoFixpoint par := par_match par.
  Lemma rewrite_par curr rest : par curr rest = par_match par curr rest.
  Proof.
    apply functional_extensionality. intros. apply bisimulation_is_eq.
    revert x curr rest.
    ginit. gcofix CIH. intros. gstep. unfold par. red. reflexivity.
  Qed.

  Lemma par_single :
    forall t, par t [] = t.
  Proof.
    intro. apply functional_extensionality. intros. apply bisimulation_is_eq.
    revert t x. pcofix CIH. intros.
    rewrite rewrite_par. unfold par_match.
    destruct (observe (t x)) eqn:?; simpl; auto.
    - destruct r0. pstep. red. rewrite Heqi. simpl. destruct u. constructor; auto.
    - pstep. red. rewrite Heqi. constructor. right. apply CIH.
    - destruct e.
      + destruct y. pstep. unfold choose. unfold choose'.
        rewritebisim @bind_ret_l.
  Abort.

  (* Not true using ≅, need equivalence that involves nondeterminism: *)
  (* Lemma par_unit : *)
  (*   forall t s, par (fun s => Ret (s, tt)) [t] s ≅ par t [fun s => Ret (s, tt)] s. *)
  (* Proof. *)
  (*   intros. rewrite rewrite_par. unfold par_match. simpl. *)
  (*   (* do 2 rewrite rewrite_par. *) *)
  (*   rewrite (rewrite_par t [_]). *)
  (*   unfold par_match. simpl. *)
  (*   destruct (observe (t s)) eqn:?. *)
  (*   - destruct r. pstep. (* rewrite rewrite_par. unfold par_match. *) constructor. *)
  (*     left. *)
  (*     do 2 rewrite rewrite_par. unfold par_match. rewrite Heqi. simpl. *)
  (*     pstep. constructor; auto. *)
  (*   - pstep. constructor. left. revert Heqi. revert t t0 s. pcofix CIH. intros. *)
  (*     do 2 rewrite rewrite_par. unfold par_match. rewrite Heqi. *)
  (*     rewrite (rewrite_par (fun _ => t0) _). unfold par_match. rewrite Heqi. simpl. *)
  (*   - destruct e. *)
  (* Qed. *)
End parallel.

Variant typing_gen {R} typing (p : perm) (Q : config * R -> Perms) :
  config -> itree (E config) (config * R) -> Prop :=
| typing_gen_ret r c c' :
    pre p c ->
    p ∈ Q (c', r) ->
    guar p c c' ->
    typing_gen typing p Q c (Ret (c', r))
| typing_gen_tau t c p' :
    pre p c ->
    sep_step p p' -> (* Added since par turns vis into a tau, so the two cases need to be similar... *)
    typing p' Q c t ->
    typing_gen typing p Q c (Tau t)
| typing_gen_vis k c c' p' :
    pre p c ->
    guar p c c' ->
    sep_step p p' ->
    (forall c'', rely p c' c'' -> typing p' Q c (* c'? *) (k c'')) ->
    typing_gen typing p Q c (vis (Yield _ c') k).

Lemma typing_gen_mon {R} : monotone4 (@typing_gen R).
Proof.
  repeat intro. inversion IN; subst; econstructor; eauto.
Qed.
Hint Resolve typing_gen_mon : paco.

Definition typing_ {R} := paco4 (@typing_gen R) bot4.

Lemma typing__lte {R} p Q Q' c (t : itree (E config) (config * R)) :
  typing_ p Q c t ->
  (forall r, Q r ⊨ Q' r) ->
  typing_ p Q' c t.
Proof.
  revert p Q Q' c t. pcofix CIH. intros p Q Q' c t Htyping Hlte.
  pstep. pinversion Htyping; pclearbot; subst; econstructor; eauto.
  - apply Hlte; eauto.
  - intros. specialize (H2 _ H3). pclearbot. eauto.
Qed.

Definition typing {R} P Q (t : stateT config (itree (E config)) R) :=
  forall p c c', p ∈ P -> pre p c -> guar p c c' -> typing_ p Q c (t c').
(* also pre p c'? *)

Lemma typing_lte {R} P P' Q Q' (t : stateT config (itree (E config)) R) :
  typing P Q t ->
  P' ⊨ P ->
  (forall r, Q r ⊨ Q' r) ->
  typing P' Q' t.
Proof.
  repeat intro. eapply typing__lte; eauto.
Qed.

Lemma typing__bind {R S} p Q1 Q2 c
      (t1 : itree (E config) (config * R))
      (t2 : R -> stateT config (itree (E config)) S)
      r' :
  typing_ p Q1 c t1 ->
  (forall r p c c', p ∈ Q1 (c', r) ->
               pre p c ->
               guar p c c' ->
               paco4 typing_gen r' p Q2 c (t2 r c')) ->
  paco4 typing_gen r' p Q2 c (x <- t1;; t2 (snd x) (fst x)).
Proof.
  revert p Q1 Q2 c t1 t2. pcofix CIH. intros p Q1 Q2 c t1 t2 Htyping1 Htyping2.
  pinversion Htyping1; subst.
  - rewritebisim @bind_ret_l. eapply paco4_mon; eauto.
  - rewritebisim @bind_tau. pstep. econstructor; eauto.
  - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
    specialize (H2 _ H3). pclearbot. right. eapply CIH; eauto.
Qed.

Lemma typing_bind {R S} P Q1 Q2
      (t1 : stateT config (itree (E config)) R)
      (t2 : R -> stateT config (itree (E config)) S) :
  typing P Q1 t1 ->
  (forall c r, typing (Q1 (c, r)) Q2 (t2 r)) ->
  typing P Q2 (bind t1 t2).
Proof.
  repeat intro. unfold bind. unfold Monad_stateT. red.
  eapply typing__bind; eauto. intros. eapply H0; eauto.
Qed.

Lemma typing__sep_step p p' Q c (t : itree (E config) (config * unit)) :
  sep_step p p' ->
  typing_ p' Q c t ->
  typing_ p Q c t.
Proof.
  revert c t. pcofix CIH. intros c t Hstep Ht.
  punfold Ht. induction Ht.
  - pstep. constructor; auto.
Abort.

Lemma typing__par_empty p Q c c' t :
  typing_ p Q c (t c') ->
  typing_ p Q c (par t [] c').
Proof.
  revert p c c' t.
  pcofix CIH.
  intros p c c' t Ht. rewrite rewrite_par. unfold par_match.
  pinversion Ht; subst; simpl.
  - pstep. constructor; auto. destruct r0; auto.
  - pstep. econstructor; eauto.
  - pstep. unfold choose, choose'. rewritebisim @bind_ret_l. econstructor; eauto.
    right. eapply CIH; eauto.
    assert (rely p c'0 c'0) by reflexivity.
    specialize (H4 _ H3). pclearbot. eauto.
Qed.

Lemma typing_par_empty P Q t :
  typing P Q t ->
  typing P Q (par t []).
Proof.
  intros Ht p c c' Hp Hpre Hguar. apply typing__par_empty; auto.
Qed.

(* Lemma typing__par_empty' p Q Q' c c' t : *)
(*   p ∈ Q' tt -> *)
(*   typing_ p Q c (t c') -> *)
(*   typing_ p Q c (par t [] c'). *)
(* Proof. *)
(*   revert p c c' t. *)
(*   pcofix CIH. *)
(*   intros p c c' t Ht. rewrite rewrite_par. unfold par_match. *)
(*   pinversion Ht; subst; simpl. *)
(*   - pstep. constructor; auto. destruct r0; auto. *)
(*   - pstep. econstructor; eauto. *)
(*   - pstep. unfold choose, choose'. rewritebisim @bind_ret_l. econstructor; eauto. *)
(*     right. eapply CIH; eauto. *)
(*     assert (rely p c'0 c'0) by reflexivity. *)
(*     specialize (H4 _ H3). pclearbot. eauto. *)
(* Qed. *)

Lemma typing__frame p p' r (Q : config * unit -> Perms) R t c :
  typing_ p Q c t ->
  r ∈ R ->
  p ** r <= p' ->
  pre p' c ->
  typing_ p' (fun c => Q c * R) c t.
Proof.
  revert p p' r Q R t c.
  pcofix CIH. intros p p' r' Q R t c Ht Hr Hp' Hpre.
  pinversion Ht; subst.
  - pstep. constructor; auto.
    + eapply Perms_upwards_closed; eauto. apply sep_conj_Perms_perm; auto.
    + apply Hp'. constructor. left. auto.
  - pstep. econstructor; auto.
    + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_l.
      apply Hp' in Hpre. apply Hpre.
      apply H0.
    + right. eapply CIH; eauto. reflexivity.
      split; [| split]. pinversion H1; auto.
      apply Hp'. apply Hpre.
      apply H0. apply Hp' in Hpre. apply Hpre.
  - pstep. econstructor; eauto.
    + apply Hp'. constructor. left. auto.
    + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_l.
      apply Hp' in Hpre. apply Hpre.
      apply H1.
    + intros. right.
      assert (rely p c' c'').
      { apply Hp'. auto. }
      specialize (H2 _ H4). pclearbot.
      eapply CIH; eauto. reflexivity.
      split; [| split]. pinversion H2; auto.
      apply Hp'. apply Hpre.
      apply H1. apply Hp' in Hpre. apply Hpre.
Qed.

Lemma typing_frame P P' (Q : config * unit -> Perms) t :
  typing P Q t ->
  typing (P * P') (fun r => Q r * P') t.
Proof.
  repeat intro. destruct H0 as (? & ? & ? & ? & ?).
  eapply typing__frame; eauto. apply H; auto. apply H4. auto. inversion H4.
  (* intros Ht p c c' Hp Hpre Hguar. *)
  revert P P' Q t. pcofix CIH. intros P P' Q t Ht p c c' Hp Hpre Hguar.
  assert (Hp': p ∈ P).
  { destruct Hp as (? & ? & ? & ? & ?).
    eapply Perms_upwards_closed; eauto. etransitivity; eauto.
    apply lte_l_sep_conj_perm. }
  specialize (Ht _ _ _ Hp' Hpre Hguar).
  (* revert Ht Hp Hpre Hguar Hp'. revert P P' Q t p c c'. pcofix CIH. *)
  (* intros P P' Q t p c c' Ht Hpp' Hpre Hguar Hp. *)

  pinversion Ht; subst.
  - pstep. constructor; auto. admit.
  - pstep. econstructor. auto. reflexivity. right.
    change t0 with ((fun _ => t0) c'). eapply CIH; eauto.
    repeat intro.

Qed.

Lemma typing_par P1 P2 (Q1 Q2 : config * unit -> Perms) t1 t2 :
  typing P1 Q1 t1 ->
  typing P2 Q2 t2 ->
  typing (P1 * P2) (fun '(c, _) => Q1 (c, tt) * Q2 (c, tt)) (par t1 [t2]).
Proof.
  revert t1 t2 P1 P2 Q1 Q2.
  pcofix CIH. intros t1 t2 P1 P2 Q1 Q2.
  intros Ht1 Ht2 p c c' (p1 & p2 & Hp1 & Hp2 & Hlte) Hpre Hguar.
  rewrite rewrite_par. unfold par_match.
  assert (Hp1': p ∈ P1) by admit.
  specialize (Ht1 _ _ _ Hp1' Hpre Hguar). pinversion Ht1; subst; simpl.
  - destruct r0. pstep. econstructor; eauto. reflexivity. left.
    (* How do we push through the stronger post-condition here? p can change arbitrarily in the typing computation for t2, so why does this hold? *)
    eapply typing_par_empty in Ht2.
    red in Ht2.
    eapply paco4_mon_bot. apply Ht2; eauto. admit.
    intros. eauto.
  -
Qed.
