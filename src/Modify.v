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
                         setoid_rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply bisimulation_is_eq in bisim;
                              setoid_rewrite bisim in H;
                              clear bisim.

Variant modifyE S : Type -> Type :=
| Modify : (S -> S) -> modifyE S S.

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

Definition E config := modifyE config +' nondetE.

Section parallel.
  Parameter config : Type.

  Definition thread := stateT config (itree (E config)) unit.

  Definition par_match par (curr : itree (E config) (config * unit)) (rest : list thread)
    : itree (E config) (config * unit) :=
    (* fun s => *)
      match (observe curr) with
      | RetF (s', _) => match rest with
                       | [] => Ret (s', tt)
                       | h :: t => Tau (par (h s') t)
                       end
      | TauF t => Tau (par t rest)
      | VisF (inl1 e) k =>
        match e in modifyE _ C return (C -> itree (E config) (config * unit)) -> _ with
        | Modify _ f =>
          fun k' =>
          '(curr', rest') <- choose k' rest;;
          Vis (inl1 (Modify _ f)) (fun s' => (par (curr' s') rest'))
        end k
      | VisF (inr1 e) k =>
        vis e (fun b => par (k b) rest)
      end.
  CoFixpoint par := par_match par.
  Lemma rewrite_par curr rest : par curr rest = par_match par curr rest.
  Proof.
    apply bisimulation_is_eq.
    revert curr rest.
    ginit. gcofix CIH. intros. gstep. unfold par. red. reflexivity.
  Qed.

  Lemma par_single :
    forall t, par t [] = t.
  Proof.
    intros. apply bisimulation_is_eq.
    revert t. pcofix CIH. intros.
    rewrite rewrite_par. unfold par_match.
    destruct (observe t) eqn:?; simpl; auto.
    - destruct r0. pstep. red. rewrite Heqi. simpl. destruct u. constructor; auto.
    - pstep. red. rewrite Heqi. constructor. right. apply CIH.
    - destruct e.
      + destruct m. pstep. unfold choose. unfold choose'.
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
  config -> stateT config (itree (E config)) R -> Prop :=
| typing_gen_ret r c :
    pre p c ->
    (forall c', rely p c c' -> p ∈ Q (c', r)) ->
    typing_gen typing p Q c (fun c => Ret (c, r))
| typing_gen_tau t p' c :
    sep_step p p' ->
    typing p' Q c t ->
    typing_gen typing p Q c (fun c => Tau (t c))
| typing_gen_vis k f p' c :
    pre p c ->
    (forall c, pre p c -> guar p c (f c)) ->
    sep_step p p' ->
    (forall c', rely p (f c) c' -> typing p' Q c' (k)) ->
    typing_gen typing p Q c (fun c => Vis (inl1 (Modify _ f)) k)
(* (* other events. TODO: generalize E *) *)
| typing_gen_e X c p' (e : nondetE X) k :
    sep_step p p' ->
    (forall x, typing p' Q c (fun c => k x)) ->
    typing_gen typing p Q c (fun c => Vis (inr1 e) k)
.

Lemma typing_gen_mon {R} : monotone4 (@typing_gen R).
Proof.
  repeat intro. inversion IN; subst; econstructor; eauto.
Qed.
Hint Resolve typing_gen_mon : paco.

Definition typing_ {R} := paco4 (@typing_gen R) bot4.

Lemma typing__rely {R} p Q c c' (t : stateT config (itree (E config)) R) :
  rely p c c' ->
  typing_ p Q c t ->
  typing_ p Q c' t.
Proof.
  revert p Q c c' t. pcofix CIH. intros p Q c c' t Hrely Ht.
  pinversion Ht; subst.
  - pstep. constructor. respects. intros. apply H0; auto. etransitivity; eauto.
  - pstep. econstructor; eauto. right. eapply CIH; eauto. eapply sep_step_rely; eauto.
  - pstep. econstructor; eauto. right. eapply CIH; eauto. eapply sep_step_rely; eauto.
    assert (rely p (f c) (f c')) by admit.
    assert (rely p (f c) c'0) by (etransitivity; eauto).
    specialize (H2 _ H4). pclearbot. apply H2.
  - pstep. econstructor; eauto. right. eapply CIH; eauto. eapply sep_step_rely; eauto.
    apply H0.
Admitted.

Lemma typing__lte {R} p Q Q' c (t : stateT config (itree (E config)) R) :
  typing_ p Q c t ->
  (forall r, Q r ⊨ Q' r) ->
  typing_ p Q' c t.
Proof.
  revert p Q Q' c t. pcofix CIH. intros p Q Q' c t Htyping Hlte.
  pstep. pinversion Htyping; pclearbot; subst; econstructor; eauto.
  - intros. apply Hlte; eauto.
  - intros. specialize (H2 _ H3). pclearbot. eauto.
  - intros. specialize (H0 x). eauto.
Qed.

(* Lemma typing__lte' p p' Q c (t : itree (E config) (config * unit)) : *)
(*   typing_ p Q c t -> *)
(*   p <= p' -> *)
(*   typing_ p' Q c t. *)
(* Proof. *)
(*   revert p p' Q c t. pcofix CIH. intros p p' Q c t Ht Hlte. *)
(*   pinversion Ht; subst. *)
(*   - pstep. constructor; auto. *)
(*     + apply Hlte. *)
(*     + eapply Perms_upwards_closed; eauto. *)
(* Qed. *)

(* Definition typing {R} P Q (t : stateT config (itree (E config)) R) := *)
(*   forall p c, p ∈ P -> pre p c -> typing_ p Q (t c). *)
Definition typing {R} P Q (t : stateT config (itree (E config)) R) :=
  forall p c, p ∈ P -> pre p c -> typing_ p Q c t.

Lemma typing_lte {R} P P' (Q Q' : config * R -> Perms) t: (* (t : stateT config (itree (E config)) R) : *)
  typing P Q t ->
  P' ⊨ P ->
  (forall r, Q r ⊨ Q' r) ->
  typing P' Q' t.
Proof.
  repeat intro. eapply typing__lte; eauto.
Qed.

Lemma typing__bind {R S} p Q1 Q2 c
      (t1 : stateT config (itree (E config)) R)
      (t2 : R -> stateT config (itree (E config)) S)
      r' :
  typing_ p Q1 c t1 ->
  (forall r p c, (forall c', rely p c c' -> p ∈ Q1 (c', r)) ->
            pre p c ->
            paco4 typing_gen r' p Q2 c (t2 r)) ->
  paco4 typing_gen r' p Q2 c (fun c => x <- t1 c;; t2 (snd x) (fst x)).
Proof.
  revert p Q1 Q2 c t1 t2. pcofix CIH. intros p Q1 Q2 c t1 t2 Ht1 Ht2.
  pinversion Ht1; subst.
  - assert ((fun c0 => x <- Ret (c0, r0);; t2 (snd x) (fst x)) = (t2 r0)).
    { apply functional_extensionality. intros. rewritebisim @bind_ret_l. auto. }
    rewrite H1.
    eapply paco4_mon; eauto.
  - assert ((fun c0 : config => x <- Tau (t c0);; t2 (snd x) (fst x)) =
            (fun c0 => Tau (x <- (t c0);; t2 (snd x) (fst x)))).
    { apply functional_extensionality. intros. rewritebisim @bind_tau. auto. }
    rewrite H1. pstep. econstructor; eauto.
  - assert ((fun _ : config => x <- Vis (inl1 (Modify config f)) k;; t2 (snd x) (fst x)) =
            (fun _ => Vis (inl1 (Modify config f)) (fun s => x <- k s;; t2 (snd x) (fst x)))).
    { apply functional_extensionality. intros. rewritebisim @bind_vis. auto. }
    rewrite H3. pstep. econstructor; eauto. intros.
    right. eapply CIH; eauto.
    specialize (H2 _ H4). pclearbot. apply H2.
  - assert ((fun _ : config => x <- Vis (inr1 e) k;; t2 (snd x) (fst x)) =
            (fun _ => Vis (inr1 e) (fun x => x <- k x;; t2 (snd x) (fst x)))).
    { apply functional_extensionality. intros. rewritebisim @bind_vis. auto. }
    rewrite H1. pstep. econstructor; eauto. intros.
    right. eapply CIH; eauto. apply H0.
Qed.

Lemma typing_bind {R S} P Q1 Q2
      (t1 : stateT config (itree (E config)) R)
      (t2 : R -> stateT config (itree (E config)) S) :
  typing P Q1 t1 ->
  (forall c r, typing (Q1 (c, r)) Q2 (t2 r)) ->
  typing P Q2 (bind t1 t2).
Proof.
  intros Ht1 Ht2 p c Hp Hpre.
  eapply typing__bind; eauto. intros. eapply Ht2; eauto. apply H; reflexivity.
Qed.

Lemma typing__tau {R} p (Q : config * R -> Perms) c t :
  typing_ p Q c t ->
  typing_ p Q c (fun c => Tau (t c)).
Proof.
  intros Ht.
  pinversion Ht; subst; simpl; try solve [pstep; econstructor; try reflexivity; eauto].
Qed.

(* TODO after this point *)
Lemma typing__par_empty p Q c t :
  typing_ p Q c t ->
  typing_ p Q c (par t []).
Proof.
  revert p t.
  pcofix CIH.
  intros p t Ht. rewrite rewrite_par. unfold par_match.
  pinversion Ht; subst; simpl.
  - destruct r0. pstep. constructor; auto.
  - pstep. econstructor; eauto.
  - pstep. unfold choose, choose'. rewritebisim @bind_ret_l.
    econstructor; eauto.
    clear Ht H.
    right. eapply CIH; eauto.
    specialize (H1 _ _ H H2). pclearbot. eauto.
  - pstep. econstructor; eauto. intros. right. apply CIH. apply H0.
Qed.

Lemma typing_par_empty P Q t :
  typing P Q t ->
  typing P Q (par t []).
Proof.
  intros Ht p Hp. apply typing__par_empty; auto.
Qed.

Lemma typing__frame p p' r (Q : config * unit -> Perms) R t c :
  typing_ p Q (t c) ->
  r ∈ R ->
  p ** r <= p' ->
  pre p' c ->
  typing_ p' (fun c' => Q c' * R) (t c).
Proof.
(*   revert p p' r Q R t c. *)
(*   pcofix CIH. intros p p' r' Q R t c Ht Hr Hp' Hpre. *)
(*   pinversion Ht; subst. *)
(*   - destruct r0. pstep. constructor; auto. *)
(*     apply Hp'. *)
(*     eapply Perms_upwards_closed; eauto. apply sep_conj_Perms_perm; auto. *)
(*     apply H0; auto. apply Hp'; auto. *)
(*   - pstep. econstructor; auto. *)
(*     + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_l. *)
(*       apply Hp' in Hpre. apply Hpre. *)
(*       apply H0. *)
(*     + right. eapply CIH; eauto. reflexivity. *)
(*       split; [| split]. pinversion H1; auto. *)
(*       apply Hp'. apply Hpre. *)
(*       apply H0. apply Hp' in Hpre. apply Hpre. *)
(*   - pstep. econstructor; auto. *)
(*     + apply Hp'. constructor. left. auto. *)
(*     + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_l. *)
(*       apply Hp' in Hpre. apply Hpre. *)
(*       apply H1. *)
(*     + intros. right. *)
(*       assert (rely p c' c''). *)
(*       { apply Hp'. auto. } *)
(*       specialize (H2 _ H4). pclearbot. *)
(*       eapply CIH; eauto. reflexivity. *)
(*       split; [| split]. *)
(*       * pinversion H2; auto. *)
(*       * pose proof Hpre as Hpre'. apply Hp' in Hpre'. destruct Hpre' as (_ & _ & Hsep). *)
(*         apply Hsep in H0. respects. etransitivity; eauto. apply Hp'. auto. apply Hp'; auto. *)
(*       * apply H1. apply Hp' in Hpre. apply Hpre. *)
(*   - pstep. econstructor; eauto. *)
(*     + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_l. *)
(*       apply Hp' in Hpre. apply Hpre. *)
(*       apply H0. *)
(*     + intros. specialize (H1 x). right. eapply CIH; eauto. reflexivity. *)
(*       split; [| split]. pinversion H1; auto. *)
(*       apply Hp'. auto. *)
(*       apply Hp' in Hpre. apply H0. apply Hpre. *)
(* Qed. *)
Abort.

(* Lemma typing__frame' p p' r (Q R : config * unit -> Perms) t c : *)
(*   typing_ p Q c t -> *)
(*   (forall c', rely r c c' -> r ∈ R (c', tt)) -> *)
(*   r ** p <= p' -> *)
(*   pre p' c -> *)
(*   typing_ p' (fun c => R c * Q c) c t. *)
(* Proof. *)
(*   revert p p' r Q R t c. *)
(*   pcofix CIH. intros p p' r' Q R t c Ht Hr Hp' Hpre. *)
(*   pinversion Ht; subst. *)
(*   - pstep. constructor; auto. destruct r0. intros. *)
(*     eapply Perms_upwards_closed; eauto. apply sep_conj_Perms_perm; auto. *)
(*     + apply Hr; auto. apply Hp'; auto. *)
(*     + apply H0; auto. apply Hp'; auto. *)
(*   - pstep. econstructor; auto. *)
(*     + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_r. *)
(*       apply Hp' in Hpre. destruct Hpre as (_ & _ & Hpre). symmetry in Hpre. apply Hpre. *)
(*       apply H0. *)
(*     + right. eapply CIH; eauto. reflexivity. *)
(*       (* intros. apply Hr. apply Hp'. eapply sep_step_rely; eauto. *) *)

(*       split; [| split]. *)
(*       apply Hp'. apply Hpre. *)
(*       pinversion H1; auto. *)
(*       symmetry. apply H0. apply Hp' in Hpre. *)
(*       destruct Hpre as (_ & _ & Hpre). symmetry in Hpre. apply Hpre. *)
(*   - pstep. econstructor; eauto. *)
(*     + apply Hp'. constructor. right. auto. *)
(*     + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_r; eauto. *)
(*       apply Hp' in Hpre. destruct Hpre as (_ & _ & Hpre). symmetry in Hpre. apply Hpre. *)
(*     + intros. right. *)
(*       assert (rely p c' c''). *)
(*       { apply Hp'. auto. } *)
(*       specialize (H2 _ H4). pclearbot. *)
(*       eapply CIH; eauto. 2: reflexivity. *)

(*       intros. apply Hr. etransitivity; eauto. *)
(*       apply Hp' in Hpre. destruct Hpre as (_ & _ & Hsep). transitivity c'. *)
(*       apply Hsep; auto. apply Hp'; auto. *)

(*       split; [| split]. *)
(*       * pose proof Hpre as Hpre'. apply Hp' in Hpre'. destruct Hpre' as (_ & _ & Hsep). *)
(*         apply Hsep in H0. respects. etransitivity; eauto. apply Hp'. auto. apply Hp'; auto. *)
(*       * pinversion H2; auto. *)
(*       * symmetry. apply H1. apply Hp' in Hpre. *)
(*         destruct Hpre as (_ & _ & Hpre). symmetry in Hpre. apply Hpre. *)
(*   - pstep. econstructor; eauto. *)
(*     + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_r; eauto. *)
(*       apply Hp' in Hpre. destruct Hpre as (_ & _ & Hpre). symmetry in Hpre. apply Hpre. *)
(*     + intros. specialize (H1 x). right. eapply CIH; eauto. reflexivity. *)
(*       split; [| split]. *)
(*       apply Hp'. auto. *)
(*       pinversion H1; auto. *)
(*       symmetry. apply Hp' in Hpre. apply H0. *)
(*       destruct Hpre as (_ & _ & Hpre). symmetry in Hpre. apply Hpre. *)
(* Qed. *)

Lemma typing_frame P P' (Q : config * unit -> Perms) t :
  typing P Q t ->
  typing (P * P') (fun r => Q r * P') t.
Proof.
  intros Ht p'' (p & p' & Hp & Hp' & Hlte).
  specialize (Ht _ Hp).
  revert Ht Hp Hp' Hlte. revert P P' Q t p p'' p'.
  pcofix CIH. intros. pinversion Ht; subst; simpl.
  - destruct r0. pstep. constructor; auto.
    admit.
    intros. eapply Perms_upwards_closed; eauto.
    apply sep_conj_Perms_perm; auto. apply H0. apply Hlte; auto.
  - pstep. econstructor; auto.
    + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_l.
      apply Hp' in Hpre. apply Hpre.
      apply H0.

    2: {
      right. eapply CIH; eauto.

    eapply typing__frame; eauto. apply H; auto. apply H3. auto.
Qed.

Lemma typing_rely p (Q : config * unit -> Perms) t c c' :
  rely p c c' ->
  typing_ p Q c t ->
  typing_ p Q c' t.
Proof.
  revert p Q c c' t. pcofix CIH.
  intros p Q c c' t Hrely Ht. pinversion Ht; subst; simpl.
  - pstep. admit.
  - pstep. (* econstructor; eauto. right. eapply CIH; eauto. eapply sep_step_rely; eauto. *)
    admit.
  - pstep. econstructor. respects. admit. apply H1. intros. right. eapply CIH.
    reflexivity. admit.
  -
Abort.

Lemma typing__par p1 p2 p Q1 Q2 c t1 t2 :
  typing_ p1 Q1 c (t1 c) ->
  typing_ p2 Q2 c (t2 c) ->
  p1 ** p2 <= p ->
  pre p c ->
  typing_ p (fun c => Q1 c * Q2 c) c (par t1 [t2] c).
Proof.
  revert p1 p2 p c t1 t2. pcofix CIH. intros p1 p2 p c t1 t2 Ht1 Ht2 Hlte Hpre.
  rewrite rewrite_par. unfold par_match.
  (* assert (Hguar1: guar p1 c c) by reflexivity. specialize (Ht1 _ Hguar1). *)
  pinversion Ht1; subst; simpl.
  - destruct r0. pstep. econstructor; eauto. reflexivity. left.
    eapply paco4_mon_bot; eauto. eapply typing__frame'; eauto.
    apply typing__par_empty. apply Ht2; intuition.
    intros; eauto.
  - pstep. econstructor; eauto.
    2: { right. eapply CIH. apply H3. apply Ht2.
         reflexivity. split; [| split]; auto.
         pinversion H3; auto.
         apply Hlte; auto.
         apply H1. apply Hlte in Hpre. apply Hpre.
    }
    etransitivity; eauto. apply sep_step_lte'; eauto.
    apply sep_step_sep_conj_l; auto. apply Hlte in Hpre. apply Hpre.
  - unfold choose, choose', or. rewritebisim @bind_vis. simpl.
    pstep. econstructor; eauto. reflexivity.
    intros []; left; rewritebisim @bind_ret_l.
    + pstep. econstructor; auto.
      * apply Hlte. constructor 1; auto.
      * eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      * intros. right. eapply CIH; eauto.
        -- assert (Hrely : rely p1 c' c''). apply Hlte; auto.
           specialize (H4 _ Hrely). pclearbot. eauto.
        -- apply Hlte in H3. destruct H3.
           (* eapply typing_rely. transitivity c'; eauto. *)
           (* apply Hlte in Hpre. destruct Hpre as (_ & _ & Hsep). *)
        (* apply Hsep; eauto. auto. *)
           admit.
        -- reflexivity.
        -- split; [| split].
           ++ apply Hlte in H3. destruct H3. specialize (H4 _ H3).
              pclearbot. pinversion H4; auto.
           ++ respects; auto. apply Hlte; eauto.
              apply Hlte in Hpre. pose proof Hpre as (_ & _ & Hsep).
              respects; eauto. apply Hsep; eauto. apply Hpre.
           ++ apply H2; auto. apply Hlte in Hpre. apply Hpre.
    + admit.
  - pstep. econstructor; auto.
    2: { intros. specialize (H3 x). right. eapply CIH. apply H3. eauto. reflexivity.
         split; [| split].
         - pinversion H3; auto.
         - apply Hlte; auto.
         - apply H1. apply Hlte in Hpre. apply Hpre. }
    eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
    apply Hlte in Hpre. apply Hpre.
Admitted.

Lemma typing_par P1 P2 (Q1 Q2 : config * unit -> Perms) t1 t2 :
  typing P1 Q1 t1 ->
  typing P2 Q2 t2 ->
  typing (P1 * P2) (fun c => Q1 c * Q2 c) (par t1 [t2]).
Proof.

  repeat intro. destruct H1 as (? & ? & ? & ? & ?).
  eapply typing__par; eauto. unfold typing in *.
  apply H; auto. apply H4; auto.
  apply H0; auto. apply H4; auto.

  (* (* revert t1 t2 P1 P2 Q1 Q2. *) *)
  (* intros Ht1 Ht2 p c (p1 & p2 & Hp1 & Hp2 & Hlte) Hpre. *)
  (* assert (Hpre1 : pre p1 c). { apply Hlte; auto. } *)
  (* assert (Hpre2 : pre p2 c). { apply Hlte; auto. } *)
  (* specialize (Ht1 _ _ Hp1 Hpre1). *)
  (* specialize (Ht2 _ _ Hp2 Hpre2). *)
  (* revert Ht1 Ht2 Hp1 Hp2 Hlte Hpre Hpre1 Hpre2. revert t1 t2 c p1 p2 p (* P1 P2 Q1 Q2 *). *)
  (* (* pcofix CIH. *) intros t1 t2 c p1 p2 p (* P1 P2 Q1 Q2 *). *)
  (* intros Ht1 Ht2 Hp1 Hp2 Hlte Hpre Hpre1 Hpre2. *)
  (* rewrite rewrite_par. unfold par_match. pinversion Ht1; subst; simpl. *)
  (* - destruct r0. pstep. econstructor; eauto. reflexivity. left. *)
  (*   eapply paco4_mon_bot; eauto. eapply typing__frame'; eauto. *)
  (*   apply typing__par_empty. apply Ht2; auto. *)
  (*   intros; eauto. *)
  (* - pstep. econstructor; eauto. *)
  (*   2: { right. eapply CIH. apply H3. apply Ht2. all: auto. *)
  (*        admit. (* we need typing_ version... *) *)
  (*        reflexivity. split; [| split]; auto. *)
  (*        pinversion H3; auto. *)
  (*        apply H1. apply Hlte in Hpre. apply Hpre. *)
  (*        pinversion H3; auto. *)
  (*   } *)
  (*   etransitivity; eauto. apply sep_step_lte'; eauto. *)
  (*   apply sep_step_sep_conj_l; auto. apply Hlte in Hpre. apply Hpre. *)
  (* - unfold choose, choose', or. rewritebisim @bind_vis. simpl. *)
  (*   pstep. econstructor; eauto. reflexivity. *)
  (* - eapply typing_par_empty in Ht2. *)
  (*   red in Ht2. *)
  (*   eapply paco4_mon_bot. apply Ht2; eauto. admi.t *)
  (*   intros. eauto. *)
  (* - *)
Qed.
