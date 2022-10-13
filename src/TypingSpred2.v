(* begin hide *)
From Coq Require Import
     Structures.Equalities
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     ProofIrrelevance.

From Heapster Require Import
     Permissions
     PermissionsSpred2
     SepStepSpred2
     PermS.

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
     Eq.Eqit
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

(** * Bisimulation axiom *)
(** We make use of the [bisimulation_is_eq] axiom from the ITrees library.
    This axiom is used to avoid setoid rewriting up to strong bisimulation,
    [eq_itree eq]. This is used for convenience, we could also prove Proper
    instances for our definitions. *)
Ltac rewritebisim lem := pose proof lem as bisim;
                         eapply bisimulation_is_eq in bisim;
                         rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply bisimulation_is_eq in bisim;
                              rewrite bisim in H;
                              clear bisim.

Lemma throw_vis {E R} `{exceptE unit -< E} (k : void -> itree E R) :
  vis (Throw tt) k = throw tt.
Proof.
  apply bisimulation_is_eq. pstep. unfold throw.
  constructor. intros. inversion v.
Qed.

Lemma throw_bind {E R1 R2} `{exceptE unit -< E} (k : R1 -> itree E R2) :
  x <- throw tt;; k x = throw tt.
Proof.
  unfold throw. rewritebisim @bind_vis. apply throw_vis.
Qed.

(** * Stuttering bisimulation *)
Section bisim.
  Variant modifyE C : Type -> Type :=
  | Modify : forall (f : C -> C), modifyE C C.
  Global Arguments Modify {C} f.

  Definition sceE (C : Type) := (exceptE unit +' modifyE C +' nondetE).

  Context {config specConfig : Type}.

  Inductive bisim_gen {R1 R2 : Type}
            (bisim : forall (spred : config * specConfig -> Prop),
                @perm {x | spred x} ->
                (R1 -> R2 -> Perms2) ->
                itree (sceE config) R1 ->
                config ->
                itree (sceE specConfig) R2 ->
                specConfig ->
                Prop)
            (spred : config * specConfig -> Prop)
            (p : @perm {x | spred x})
            (Q : R1 -> R2 -> Perms2) :
    itree (sceE config) R1 ->
    config ->
    itree (sceE specConfig) R2 ->
    specConfig ->
    Prop :=
  | bisim_gen_ret r1 c1 r2 c2 (Hspred : spred (c1, c2)):
      pre p (exist _ (c1, c2) Hspred) ->
      in_Perms2 (Q r1 r2) p ->
      bisim_gen bisim spred p Q (Ret r1) c1 (Ret r2) c2
  | bisim_gen_err t1 c1 c2 :
      bisim_gen bisim spred p Q t1 c1 (throw tt) c2
  | bisim_gen_tau_L t1 c1 t2 c2 (Hspred : spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      bisim_gen bisim spred p Q t1 c1 t2 c2 ->
      bisim_gen bisim spred p Q (Tau t1) c1 t2 c2
  | bisim_gen_tau_R t1 c1 t2 c2 (Hspred : spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      bisim_gen bisim spred p Q t1 c1 t2 c2 ->
      bisim_gen bisim spred p Q t1 c1 (Tau t2) c2
  | bisim_gen_tau t1 c1 t2 c2 (Hspred : spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      bisim spred p Q t1 c1 t2 c2 ->
      bisim_gen bisim spred p Q (Tau t1) c1 (Tau t2) c2
  | bisim_gen_modify_L (spred' : config * specConfig -> Prop)
                       (Hspred' : forall x, spred' x -> spred x)
                       (f : config -> config) k c1 t2 c2
                       (p' : perm)
                       (Hspred : spred (c1, c2))
                       (Hf : spred' (f c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      guar p (exist _ (c1, c2) Hspred) (exist _ (f c1, c2) (Hspred' _ Hf)) ->
      sep_step _ _ _ Hspred' p p' ->
      bisim_gen bisim spred' p' Q (k c1) (f c1) t2 c2 ->
      bisim_gen bisim spred p Q (vis (Modify f) k) c1 t2 c2
  | bisim_gen_modify_R (spred' : config * specConfig -> Prop)
                        (Hspred' : forall x, spred' x -> spred x)
                        t1 c1 f k c2 p'
                        (Hspred : spred (c1, c2))
                        (Hf : spred' (c1, f c2)):
      pre p (exist _ (c1, c2) Hspred) ->
      guar p (exist _ (c1, c2) Hspred) (exist _ (c1, f c2) (Hspred' _ Hf)) ->
      sep_step _ _ _ Hspred' p p' ->
      bisim_gen bisim spred' p' Q t1 c1 (k c2) (f c2) ->
      bisim_gen bisim spred p Q t1 c1 (vis (Modify f) k) c2
  | bisim_gen_modify (spred' : config * specConfig -> Prop)
                      (Hspred' : forall x, spred' x -> spred x)
                      f1 k1 c1 f2 k2 c2 p'
                      (Hspred : spred (c1, c2))
                      (Hf : spred' (f1 c1, f2 c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      guar p (exist _ (c1, c2) Hspred) (exist _ (f1 c1, f2 c2) (Hspred' _ Hf)) ->
      sep_step _ _ _ Hspred' p p' ->
      bisim spred' p' Q (k1 c1) (f1 c1) (k2 c2) (f2 c2) ->
      bisim_gen bisim spred p Q (vis (Modify f1) k1) c1 (vis (Modify f2) k2) c2
  | bisim_gen_choice_L k c1 t2 c2 (Hspred : spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      (* sep_step p p' -> *)
      (forall b, bisim_gen bisim spred p Q (k b) c1 t2 c2) ->
      bisim_gen bisim spred p Q (vis Or k) c1 t2 c2
  | bisim_gen_choice_R t1 c1 k c2 (Hspred : spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      (* sep_step p p' -> *)
      (forall b, bisim_gen bisim spred p Q t1 c1 (k b) c2) ->
      bisim_gen bisim spred p Q t1 c1 (vis Or k) c2
  | bisim_gen_choice k1 c1 k2 c2 (Hspred : spred (c1, c2)):
      pre p (exist _ (c1, c2) Hspred) ->
      (* sep_step p p' -> *)
      (forall b1, exists b2, bisim spred p Q (k1 b1) c1 (k2 b2) c2) ->
      (forall b2, exists b1, bisim spred p Q (k1 b1) c1 (k2 b2) c2) ->
      bisim_gen bisim spred p Q (vis Or k1) c1 (vis Or k2) c2
  .

  Lemma bisim_gen_mon {R1 R2} : monotone7 (@bisim_gen R1 R2).
  Proof.
    repeat intro. induction IN; subst; try solve [econstructor; eauto]; auto.
    econstructor 11; eauto; intros.
    - destruct (H0 b1). eexists; eauto.
    - destruct (H1 b2). eexists; eauto.
  Qed.
  #[local] Hint Resolve bisim_gen_mon : paco.

  Definition bisim {R1 R2} := paco7 (@bisim_gen R1 R2) bot7.

  Lemma bisim_gen_pre {R1 R2} spred r p (Q : R1 -> R2 -> Perms2) t s c1 c2 Hspred :
    bisim_gen r spred p Q t c1 s c2 ->
    s = throw tt \/ pre p (exist _ (c1, c2) Hspred).
  Proof.
    inversion 1; subst; eauto; erewrite (proof_irrelevance _ Hspred); eauto.
  Qed.

  Lemma bisim_lte {R1 R2} spred p Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 :
    bisim spred p Q t c1 s c2 ->
    (forall r1 r2, lte_Perms2 (Q' r1 r2) (Q r1 r2)) ->
    bisim spred p Q' t c1 s c2.
  Proof.
    revert spred p Q Q' t s c1 c2. pcofix CIH. intros spred p Q Q' t s c1 c2 Htyping Hlte.
    punfold Htyping. pstep.
    induction Htyping; pclearbot; try solve [econstructor; eauto].
    - econstructor; eauto. apply Hlte. auto.
    - econstructor 11; eauto; intros.
      + destruct (H0 b1). eexists. right. eapply CIH; eauto. pclearbot. apply H2.
      + destruct (H1 b2). eexists. right. eapply CIH; eauto. pclearbot. apply H2.
  Qed.

  Lemma bisim_spred_lte {R1 R2} (spred spred' : config * specConfig -> Prop) p Q
        (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2)
        c1 c2 (Hspred': forall x, spred' x -> spred x) :
    bisim spred' (restrict _ _ _ Hspred' p) Q t c1 s c2 ->
    spred' (c1, c2) ->
    bisim spred
          p
          Q
          (* (fun spred'' Hspred'' r1 r2 => Restrict _ _ _ Hspred'' (Restrict _ _ _ Hspred' (Q r1 r2))) *)
                                                 (* Q spred'' (fun x Hx => (Hspred' x (Hspred'' x Hx)))) *)
          t c1 s c2.
  Proof.
    (* Set Printing All. *)
    revert spred p Q t s c1 c2 spred' Hspred'. pcofix CIH.
    intros spred p Q t s c1 c2 spred' Hspred' Hbisim Hc1c2.
    punfold Hbisim. pstep.
    remember (restrict _ _ _ _ p).
    revert spred p Hspred' Heqp0.
    revert Hc1c2 CIH.
    induction Hbisim; intros; subst.
    - econstructor 1. Unshelve. 3: auto.
      + cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H.
      + eapply Perms_upwards_closed1; eauto. unfold hlte_perm1. reflexivity.
    - constructor 2.
    - econstructor 3. apply H.
      eapply IHHbisim; eauto.
      (* erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    - econstructor 4. apply H.
      eapply IHHbisim; eauto.
    - econstructor 5.
      + cbn. apply H.
      + pclearbot. right. eapply CIH; eauto.
    - econstructor 6.
      + clear IHHbisim CIH. apply H.
      + clear IHHbisim CIH. apply H0.
      + clear IHHbisim. cbn. repeat intro. admit.
      + eapply IHHbisim. apply Hf. auto. admit.
    - econstructor 7.
      + clear IHHbisim CIH. apply H.
      + clear IHHbisim CIH. apply H0.
      + clear IHHbisim. cbn. repeat intro. admit.
      + eapply IHHbisim; auto. admit.
    - econstructor 8; eauto.
      + clear CIH. apply H.
      + clear CIH. apply H0.
      + cbn. repeat intro. admit.
      + pclearbot. right. eapply CIH; eauto. admit.
    - econstructor 9; eauto.
    (*   cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    (* - econstructor 10; eauto. *)
    (*   cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    (* - econstructor 11; eauto. *)
    (*   + cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    (*   + intros b. destruct (H0 b). pclearbot. eauto. *)
    (*   + intros b. destruct (H1 b). pclearbot. eauto. *)

    (*     Unshelve. all: auto. *)
  Admitted.

  (** * Typing *)
  Definition typing {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :=
    forall spred (p : @perm {x | spred x}) c1 c2 (Hspred : spred (c1, c2)),
      in_Perms2 P p ->
      pre p (exist _ (c1, c2) Hspred) ->
      bisim spred p Q t c1 s c2.

  Lemma typing_lte {R1 R2} (spred : config * specConfig -> Prop) P P' Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s ->
    lte_Perms2 P P' ->
    (forall r1 r2, lte_Perms2 (Q' r1 r2) (Q r1 r2)) ->
    typing P' Q' t s.
  Proof.
    repeat intro.
    eapply bisim_lte; eauto.
  Qed.

  Lemma typing_ret {R1 R2} P Q (r1 : R1) (r2 : R2) :
    lte_Perms2 (Q r1 r2) P -> typing P Q (Ret r1) (Ret r2).
  Proof.
    repeat intro. pstep. econstructor; eauto.
  Qed.

  Lemma rewrite_spin {E R} : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.


  Lemma typing_spin {R1 R2} P Q :
    typing P Q (ITree.spin : itree (sceE config) R1) (ITree.spin : itree (sceE specConfig) R2).
  Proof.
    repeat intro. pcofix CIH. pstep.
    rewrite (@rewrite_spin _ R1). rewrite (@rewrite_spin _ R2).
    econstructor 5; eauto.
  Qed.

  Lemma typing_top {R1 R2} Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing top_Perms2 Q t s.
  Proof.
    repeat intro. inversion H.
  Qed.

  Lemma bisim_bottom {R1 R2} spred p Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    bisim spred p Q t c1 s c2 -> bisim spred p (fun _ _ => bottom_Perms2) t c1 s c2.
  Proof.
    revert spred p Q t s c1 c2. pcofix CIH. intros. pstep. punfold H0.
    induction H0; pclearbot; try solve [econstructor; simpl; eauto].
    econstructor 11; eauto; intros.
    - destruct (H0 b1). eexists. right. eapply CIH; pclearbot. apply H2.
    - destruct (H1 b2). eexists. right. eapply CIH; pclearbot; apply H2.
  Qed.

  Lemma typing_bottom {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s -> typing P (fun _ _ => bottom_Perms2) t s.
  Proof.
    repeat intro. eapply bisim_bottom; eauto.
  Qed.

  Lemma bisim_bind {R1 R2 S1 S2} spred (p : perm)
        (Q : R1 -> S1 -> Perms2) (R : R2 -> S2 -> Perms2)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2)
        c1 c2 Hspred r :
    pre p (exist _ (c1, c2) Hspred) ->
    bisim spred p Q t1 c1 s1 c2 ->
    (forall r1 r2 c1 c2 spred' Hspred' p,
        in_Perms2 (Q r1 r2) p ->
        pre p (exist _ (c1, c2) Hspred') ->
        paco7 bisim_gen r spred' p R (t2 r1) c1 (s2 r2) c2) ->
    paco7 bisim_gen r spred p R (x <- t1 ;; t2 x) c1 (x <- s1 ;; s2 x) c2.
  Proof.
    revert spred p Q R t1 t2 s1 s2 c1 c2 Hspred. pcofix CIH.
    intros spred p Q R t1 t2 s1 s2 c1 c2 Hspred Hpre Htyping1 Htyping2.
    punfold Htyping1. induction Htyping1.
    - do 2 rewritebisim @bind_ret_l. specialize (Htyping2 _ _ c1 c2 spred Hspred0 _ H0 H).
      eapply paco7_mon; eauto.
    - rewrite throw_bind. pstep. constructor.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 _ Hpre Htyping2). punfold IHHtyping1.
      pstep. econstructor; eauto.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 _ Hpre Htyping2). punfold IHHtyping1.
      pstep. econstructor; eauto.
    - do 2 rewritebisim @bind_tau. pclearbot.
      pstep. econstructor 5; eauto.
    - rewritebisim @bind_vis. eapply bisim_gen_pre in Htyping1. destruct Htyping1; subst.
      + rewrite throw_bind. pstep. constructor.
      + pstep. econstructor; eauto. specialize (IHHtyping1 _ H2 Htyping2).
        punfold IHHtyping1.
    - rewritebisim @bind_vis. eapply bisim_gen_pre in Htyping1. destruct Htyping1; subst.
      + pstep. econstructor; eauto. rewrite H2. rewrite throw_bind. constructor.
      + pstep. econstructor; eauto. specialize (IHHtyping1 _ H2 Htyping2).
        punfold IHHtyping1.
    - do 2 rewritebisim @bind_vis. pclearbot.
      pose proof H2. punfold H2.
      pstep. econstructor 8; eauto.
      eapply bisim_gen_pre in H2. destruct H2; eauto.
      left. pstep. rewrite H2. rewrite throw_bind. constructor.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      specialize (H0 b). eapply bisim_gen_pre in H0. destruct H0.
      + rewrite H0. rewrite throw_bind. constructor.
      + specialize (H1 b _ H0 Htyping2). punfold H1.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      specialize (H0 b). eapply bisim_gen_pre in H0. destruct H0.
      + rewrite H0. rewrite throw_bind. constructor.
      + specialize (H1 b _ H0 Htyping2). punfold H1.
    - do 2 rewritebisim @bind_vis. pclearbot. pstep. econstructor 11; eauto; intros.
      + specialize (H0 b1). destruct H0. pclearbot.
        punfold H0. pose proof H0. eapply bisim_gen_pre in H0. destruct H0.
        * exists x. left. pstep. rewrite H0. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
      + specialize (H1 b2). destruct H1. pclearbot.
        punfold H1. pose proof H1. eapply bisim_gen_pre in H1. destruct H1.
        * exists x. left. pstep. rewrite H1. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.

          Unshelve. all: eauto.
  Qed.

  Lemma typing_bind {R1 R2 S1 S2} (P : Perms2) (Q : R1 -> S1 -> Perms2) (R : R2 -> S2 -> Perms2)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2) :
    typing P Q t1 s1 ->
    (forall r1 r2, typing (Q r1 r2) R (t2 r1) (s2 r2)) ->
    typing P R (x <- t1 ;; t2 x) (x <- s1 ;; s2 x).
  Proof.
    repeat intro.
    eapply bisim_bind; eauto.
    intros. eapply H0; eauto.
  Qed.

  Lemma bisim_frame {R1 R2} spred spred' Hspred' p r p' Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 Hc1c2:
    pre p' (exist _ (c1, c2) Hc1c2) ->
    in_Perms2 R r ->
    hlte_perm1 _ spred spred' Hspred' (p ** r) p' ->
    bisim spred p Q t c1 s c2 ->
    bisim spred' p' (fun r1 r2 => sep_conj_Perms2 (Q r1 r2) R) t c1 s c2.
  Proof.
  Admitted.
(*    revert spred p r p' Q R t s c1 c2 Hspred. pcofix CIH. rename r into r0.
    intros spred p r p' Q R t s c1 c2 Hspred Hpre Hr Hlte Hbisim. pstep. punfold Hbisim.
    revert p' Hlte Hpre. generalize dependent r.
    induction Hbisim; intros; pclearbot; try solve [econstructor; eauto].
    - econstructor; eauto.
      eapply Perms_upwards_closed1; eauto.
      do 4 eexists. split; [| split]; eauto.
      unfold hlte_perm1.
      rewrite restrict_same. apply Hlte.
      apply hlte_perm1_reflexive.
    - eapply bisim_gen_pre in Hbisim. destruct Hbisim; [subst; constructor |].
      econstructor; eauto.
      (* 2: { eapply sep_step_lte; eauto. *)
      + apply Hlte. constructor. left. erewrite (proof_irrelevance _ Hspred). apply H0.
      + (* eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto. *)
      (* apply Hlte in Hpre. apply Hpre. *)
        admit.
      + eapply IHHbisim. eapply Perms_upwards_closed1; eauto. admit.
        split; [| split]; auto.
        * apply Hlte in Hpre. destruct Hpre as (? & ? & ?). respects.
          apply H5. auto.
        * apply H1. apply Hlte in Hpre. apply Hpre.
    - econstructor; eauto.
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + apply sbuter_gen_pre in Hsbuter. destruct Hsbuter; [rewrite H2; constructor |].
        eapply IHHsbuter; eauto. reflexivity.
        split; [| split]; auto.
        * apply Hlte in Hpre. destruct Hpre as (? & ? & ?). respects.
          apply H5. auto.
        * apply H1. apply Hlte in Hpre. apply Hpre.
    - econstructor 8; eauto.
      3: { pose proof H2 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre in Hsbuter.
           destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H2. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
           respects. apply H6. auto.
      }
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
        apply Hlte in Hpre. apply Hpre.
    - econstructor; eauto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + intros. specialize (H1 b).
        apply sbuter_gen_pre in H1. destruct H1; [subst; constructor |].
        eapply H2; eauto. reflexivity.
        apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
        split; [| split]; auto.
    - econstructor; eauto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + intros. specialize (H1 b).
        apply sbuter_gen_pre in H1. destruct H1; [rewrite H1; constructor |].
        eapply H2; eauto. reflexivity.
        apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
        split; [| split]; auto.
    - econstructor 11; eauto.
      2: { intros. specialize (H1 b1). destruct H1 as (b2 & H1). pclearbot. exists b2.
           pose proof H1 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre in Hsbuter.
           destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H1. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
      }
      2: { intros. specialize (H2 b2). destruct H2 as (b1 & H2). pclearbot. exists b1.
           pose proof H2 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre in Hsbuter.
           destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H2. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
      }
      eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
      apply Hlte in Hpre. apply Hpre.
  Qed.
 *)

  Lemma typing_frame {R1 R2} P Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2):
    typing P Q t s ->
    typing (sep_conj_Perms2 P R) (fun r1 r2 => sep_conj_Perms2 (Q r1 r2) R) t s.
  Proof.
    (* repeat intro. *)
    intros Ht spred p' c1 c2 Hc1c2 (spred' & Hspred' & p & r & Hp & Hr & Hlte) Hpre.
    eapply bisim_frame; eauto.
    eapply Ht; eauto.
    destruct Hlte. cbn in pre_inc.
    apply pre_inc. cbn.
    erewrite (proof_irrelevance _ Hc1c2) in Hpre. apply Hpre.
    Unshelve.

    apply Hp.
    destruct H.
    pose proof Hpre as H. apply Hlte in H. destruct H as (Hprep & Hprer & Hsep).
    eapply sbuter_frame; eauto.
  Qed.

  Lemma typing_frame1 {R1 R2 R3 R4} P Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) (r3 : R3) (r4 : R4):
    typing P Q t s ->
    typing (R r3 r4 * P)
           (fun '(r1, r2) '(r3, r4) => R r1 r3 * Q r2 r4)
           (fmap (fun r1 => (r3, r1)) t)
           (fmap (fun r1 => (r4, r1)) s).
  Proof.
    revert P Q R t s r3 r4. pcofix CIH. rename r into r'.
    intros P Q R t s r3 r4 Ht p' c1 c2 (r & p & Hr & Hp & Hlte) Hpre.
    pose proof Hpre as H. apply Hlte in H. destruct H as (Hprer & Hprep & Hsep).
    specialize (Ht _ c1 c2 Hp Hprep). pstep. punfold Ht. induction Ht; simpl.
    - do 2 rewritebisim @map_ret. constructor; auto. exists r, p. auto.
    - unfold throw. unfold ITree.map. admit.
    - rewritebisim @map_tau. constructor 3; auto.
    - rewritebisim @map_tau. constructor 4; auto.
    - do 2 rewritebisim @map_tau. constructor 5; eauto. right. eapply CIH; eauto; admit.
    - unfold ITree.map. rewritebisim @bind_vis. econstructor 6; eauto; admit.
    - unfold ITree.map. rewritebisim @bind_vis. econstructor 7; eauto; admit.
    - unfold ITree.map. do 2 rewritebisim @bind_vis. econstructor 8; eauto.
      + apply Hlte. constructor 1. right. auto.
      + admit.
      + right. eapply CIH; eauto; admit.
    - unfold ITree.map. rewritebisim @bind_vis. econstructor 9; eauto; admit.
    - unfold ITree.map. rewritebisim @bind_vis. econstructor 10; eauto; admit.
    - unfold ITree.map. do 2 rewritebisim @bind_vis. econstructor 11; eauto.
      + admit.
      + intros. (* something with H1 *) admit.
      + intros. (* something with H2 *) admit.
  Admitted.

  Lemma typing_par {R1 R2 S1 S2} (P1 P2 : Perms) (Q1 : R1 -> S1 -> Perms) (Q2 : R2 -> S2 -> Perms)
        (t1 : itree (sceE config) R1) (s1 : itree (sceE specConfig) S1)
        (t2 : itree (sceE config) R2) (s2 : itree (sceE specConfig) S2) :
    typing P1 Q1 t1 s1 ->
    typing P2 Q2 t2 s2 ->
    typing (P1 * P2) (fun '(r1, r2) '(r3, r4) => Q1 r1 r3 * Q2 r2 r4) (par t1 t2) (par s1 s2).
  Proof.
    revert P1 P2 Q1 Q2 t1 s1 t2 s2. pcofix CIH.
    intros P1 P2 Q1 Q2 t1 s1 t2 s2 Ht1 Ht2 p c1 c2 Hp Hpre.
    pose proof Hp as H. destruct H as (p1 & p2 & Hp1 & Hp2 & Hlte).
    pose proof Hpre as H. apply Hlte in H. destruct H as (Hpre1 & Hpre2 & Hsep).
    specialize (Ht1 p1 c1 c2 Hp1 Hpre1).
    punfold Ht1.
    generalize dependent t2.
    generalize dependent s2.
    induction Ht1; intros; simpl.
    - specialize (Ht2 p2 c1 c2 Hp2 Hpre2). punfold Ht2. induction Ht2.
      + pstep. do 2 rewrite rewrite_par. unfold par_match.
        econstructor 9; eauto. reflexivity.
        intros. econstructor 10; eauto. reflexivity.
        intros. simpl. admit.
      + pstep. do 2 rewrite rewrite_par. unfold par_match.
        econstructor 9; eauto. reflexivity.
        intros. econstructor 10; eauto. reflexivity.
        intros. simpl. destruct b0.
        * unfold ITree.map. rewrite throw_bind. constructor.
        * admit.
      + pstep. do 2 rewrite rewrite_par. unfold par_match.
        econstructor 9; eauto. reflexivity.
        intros. econstructor 10; eauto. reflexivity.
        intros. simpl. admit.
      + pstep. do 2 rewrite rewrite_par. unfold par_match.
        econstructor 9; eauto. reflexivity.
        intros. econstructor 10; eauto. reflexivity.
        intros. simpl. admit.
      + pstep. do 2 rewrite rewrite_par. unfold par_match.
        econstructor 9; eauto. reflexivity.
        intros. econstructor 10; eauto. reflexivity.
        intros. simpl. admit.
      + pstep. do 2 rewrite rewrite_par. unfold par_match.
        econstructor 9; eauto. reflexivity.
        intros. econstructor 10; eauto. reflexivity.
        intros. simpl. admit.
      +

        (* apply IHHt2. *)
    (* econstructor 11; eauto. reflexivity. *)
    (* { *)
    (*   intros b; exists b; destruct b. *)
    (*   { *)
    (*     pose proof Hp as H. destruct H as (p1 & p2 & Hp1 & Hp2 & Hlte). *)
    (*     pose proof Hpre as H. apply Hlte in H. destruct H as (Hpre1 & Hpre2 & Hsep). *)
    (*     specialize (Ht1 p1 c1 c2 Hp1 Hpre1). *)
    (*     punfold Ht1. *)
    (*     generalize dependent t2. *)
    (*     generalize dependent s2. *)
    (*     induction Ht1; intros; simpl. *)
    (*     - admit. *)
    (*     - admit. *)
    (*     - left. pstep. constructor 3; auto. *)

    (*     - exists true. simpl. eapply typing_frame1 in Ht2. specialize (Ht2 p c1 c2 Hp Hpre). admit. *)
    (*     - exists true. simpl. admit. (* rewrite @throw_vis. econstructor 2. *) *)
    (*     - simpl. econstructor; auto. rewrite rewrite_par. unfold par_match. *)
    (*       left. pstep. econstructor; eauto. reflexivity. intros []. *)
    (*       + eapply IHHt1; auto. *)
    (*       + specialize (Ht2 p2 c1 c2 Hp2 Hpre2). punfold Ht2. induction Ht2. *)
    (*         * simpl. *)
  Abort.

  (** * [no_errors] *)
  Variant no_errors_gen {R C : Type} no_errors (c : C) : itree (sceE C) R -> Prop :=
  | no_errors_ret : forall r, no_errors_gen no_errors c (Ret r)
  | no_errors_tau : forall t, no_errors c t -> no_errors_gen no_errors c (Tau t)
  | no_errors_modify : forall f k,
      no_errors (f c) (k c) ->
      no_errors_gen no_errors c (vis (Modify f) k)
  | no_errors_choice : forall k,
      (forall b, no_errors c (k b)) ->
      no_errors_gen no_errors c (vis Or k)
  .
  Lemma no_errors_gen_mon {R C} : monotone2 (@no_errors_gen R C).
  Proof.
    repeat intro. inversion IN; subst; try solve [constructor; auto].
  Qed.
  #[local] Hint Resolve no_errors_gen_mon : paco.

  Definition no_errors {R C : Type} :=
    paco2 (@no_errors_gen R C) bot2.

  Lemma sbuter_no_errors {R1 R2} Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) p c1 c2 :
    sbuter p Q t c1 s c2 ->
    no_errors c2 s ->
    no_errors c1 t.
  Proof.
    revert Q t s p c1 c2. pcofix CIH. intros Q t s p c1 c2 Htyping Hs. pstep.
    punfold Htyping.
    induction Htyping;
      try solve [constructor; eauto];
      pinversion Hs;
      try (match goal with
           | [H : existT _ _ _ = existT _ _ _ |- _] => apply inj_pair2 in H
           end); subst; eauto;
        try solve [constructor; eauto].
    - subst. apply (H2 true). apply H4.
    - constructor. intros. right. destruct (H1 b). eapply CIH.
      + destruct H3; eauto. inversion b0.
      + inversion Hs. apply inj_pair2 in H5; subst.
        specialize (H6 x). pclearbot. eauto.
  Qed.

  Global Instance Proper_eq_Perms_typing {R1 R2} :
    Proper (eq_Perms ==>
           (pointwise_relation _ (pointwise_relation _ eq_Perms)) ==> eq ==> eq ==> flip impl) (@typing R1 R2).
  Proof.
    repeat intro. subst.
    eapply sbuter_lte; eauto. apply H3; auto. rewrite <- H; auto.
    intros. rewrite H0. reflexivity.
  Qed.
End bisim.
