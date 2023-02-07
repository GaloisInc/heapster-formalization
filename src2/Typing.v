(* begin hide *)
From Coq Require Import
     Structures.Equalities
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     ProofIrrelevance.

From Heapster2 Require Import
     Permissions
     PermissionsSpred2
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
  Context {Spred : Type}.
  Context {interp_spred : Spred -> config * specConfig -> Prop}.

  Inductive bisim_gen {R1 R2 : Type}
            (bisim : forall (spred : Spred),
                @perm {x | interp_spred spred x} ->
                (R1 -> R2 -> Perms2) ->
                itree (sceE config) R1 ->
                config ->
                itree (sceE specConfig) R2 ->
                specConfig ->
                Prop)
            (spred : Spred)
            (p : @perm {x | interp_spred spred x})
            (Q : R1 -> R2 -> Perms2) :
    itree (sceE config) R1 ->
    config ->
    itree (sceE specConfig) R2 ->
    specConfig ->
    Prop :=
  | bisim_gen_ret r1 c1 r2 c2 (Hspred : interp_spred spred (c1, c2)):
      pre p (exist _ (c1, c2) Hspred) ->
      in_Perms2 (Q r1 r2) p ->
      bisim_gen bisim spred p Q (Ret r1) c1 (Ret r2) c2
  | bisim_gen_err t1 c1 c2 :
      bisim_gen bisim spred p Q t1 c1 (throw tt) c2
  | bisim_gen_tau_L t1 c1 t2 c2 (Hspred : interp_spred spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      bisim_gen bisim spred p Q t1 c1 t2 c2 ->
      bisim_gen bisim spred p Q (Tau t1) c1 t2 c2
  | bisim_gen_tau_R t1 c1 t2 c2 (Hspred : interp_spred spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      bisim_gen bisim spred p Q t1 c1 t2 c2 ->
      bisim_gen bisim spred p Q t1 c1 (Tau t2) c2
  | bisim_gen_tau t1 c1 t2 c2 (Hspred : interp_spred spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      bisim spred p Q t1 c1 t2 c2 ->
      bisim_gen bisim spred p Q (Tau t1) c1 (Tau t2) c2
  | bisim_gen_modify_L (spred' : Spred)
                       (Hspred' : forall x, interp_spred spred' x -> interp_spred spred x)
                       (f : config -> config) k c1 t2 c2
                       (p' : perm)
                       (Hspred : interp_spred spred (c1, c2))
                       (Hf : interp_spred spred' (f c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      guar p (exist _ (c1, c2) Hspred) (exist _ (f c1, c2) (Hspred' _ Hf)) ->
      sep_step _ _ _ Hspred' p p' ->
      bisim_gen bisim spred' p' Q (k c1) (f c1) t2 c2 ->
      bisim_gen bisim spred p Q (vis (Modify f) k) c1 t2 c2
  | bisim_gen_modify_R (spred' : Spred)
                        (Hspred' : forall x, interp_spred spred' x -> interp_spred spred x)
                        t1 c1 f k c2 p'
                        (Hspred : interp_spred spred (c1, c2))
                        (Hf : interp_spred spred' (c1, f c2)):
      pre p (exist _ (c1, c2) Hspred) ->
      guar p (exist _ (c1, c2) Hspred) (exist _ (c1, f c2) (Hspred' _ Hf)) ->
      sep_step _ _ _ Hspred' p p' ->
      bisim_gen bisim spred' p' Q t1 c1 (k c2) (f c2) ->
      bisim_gen bisim spred p Q t1 c1 (vis (Modify f) k) c2
  | bisim_gen_modify (spred' : Spred)
                      (Hspred' : forall x, interp_spred spred' x -> interp_spred spred x)
                      f1 k1 c1 f2 k2 c2 p'
                      (Hspred : interp_spred spred (c1, c2))
                      (Hf : interp_spred spred' (f1 c1, f2 c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      guar p (exist _ (c1, c2) Hspred) (exist _ (f1 c1, f2 c2) (Hspred' _ Hf)) ->
      sep_step _ _ _ Hspred' p p' ->
      bisim spred' p' Q (k1 c1) (f1 c1) (k2 c2) (f2 c2) ->
      bisim_gen bisim spred p Q (vis (Modify f1) k1) c1 (vis (Modify f2) k2) c2
  | bisim_gen_choice_L k c1 t2 c2 (Hspred : interp_spred spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      (* sep_step p p' -> *)
      (forall b, bisim_gen bisim spred p Q (k b) c1 t2 c2) ->
      bisim_gen bisim spred p Q (vis Or k) c1 t2 c2
  | bisim_gen_choice_R t1 c1 k c2 (Hspred : interp_spred spred (c1, c2)) :
      pre p (exist _ (c1, c2) Hspred) ->
      (* sep_step p p' -> *)
      (forall b, bisim_gen bisim spred p Q t1 c1 (k b) c2) ->
      bisim_gen bisim spred p Q t1 c1 (vis Or k) c2
  | bisim_gen_choice k1 c1 k2 c2 (Hspred : interp_spred spred (c1, c2)):
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

  (*
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
   *)
  (* section variable: the spred lang and the interp function *)
  (** * Typing *)
  Definition typing {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :=
    (* forall "spreds" in the lang, apply interp to it *)
    forall spred (p : @perm {x | interp_spred spred x}) c1 c2 (Hspred : (interp_spred spred) (c1, c2)),
      in_Perms2 P p ->
      pre p (exist _ (c1, c2) Hspred) ->
      bisim spred p Q t c1 s c2.

  Lemma typing_lte {R1 R2} P P' Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
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
    (forall r1 r2 c1 c2 spred' Hspred' q,
        in_Perms2 (Q r1 r2) q ->
        pre q (exist _ (c1, c2) Hspred') ->
        paco7 bisim_gen r spred' q R (t2 r1) c1 (s2 r2) c2) ->
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

  Lemma restrict_rely C (spred spred' spred'' : C -> Prop) Hspred1 Hspred2
        (Hspred : forall x, spred' x -> spred x) r x y Hx Hy Hx' Hy' :
    rely (restrict C spred spred'' Hspred1 r)
         (exist _ x Hx) (exist _ y Hy) ->
    rely (restrict C spred' spred'' Hspred2 r)
         (exist _ x Hx') (exist _ y Hy').
  Proof.
    cbn. intros.
    erewrite (proof_irrelevance _ (Hspred2 x Hx')).
    erewrite (proof_irrelevance _ (Hspred2 y Hy')). apply H.
  Qed.
  Lemma restrict_pre C (spred spred' spred'' : C -> Prop) Hspred1 Hspred2
        (Hspred : forall x, spred' x -> spred x) r x Hx Hx' :
    pre (restrict C spred spred'' Hspred1 r) (exist _ x Hx) ->
    pre (restrict C spred' spred'' Hspred2 r) (exist _ x Hx').
  Proof.
    cbn. intros.
    erewrite (proof_irrelevance _ (Hspred2 x Hx')). apply H.
  Qed.

  Lemma bisim_frame {R1 R2} spred spred' Hspred p r p' Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 Hc1c2 Hrc1c2:
    pre p' (exist _ (c1, c2) Hc1c2) ->
    pre r (exist _ (c1, c2) Hrc1c2) ->
    @in_Perms2 (config * specConfig) R (interp_spred spred') r ->
    (p ** (restrict _ (interp_spred spred) (interp_spred spred') Hspred r)) <= p' ->
    bisim spred p Q t c1 s c2 ->
    bisim spred p' (fun r1 r2 => sep_conj_Perms2 (Q r1 r2) R) t c1 s c2.
  Proof.
    revert spred spred' p r p' Q R t s c1 c2 Hc1c2 Hrc1c2 Hspred.
    pcofix CIH. rename r into r0.
    intros spred spred' p r p' Q R t s c1 c2 Hc1c2 Hrc1c2 Hspred Hprep' Hprer Hr Hlte Hbisim.
    pstep. punfold Hbisim.
    revert p' Hlte Hprep' Hprer. generalize dependent r.
    induction Hbisim; intros; pclearbot; try solve [econstructor; eauto].
    - econstructor; eauto.
      eapply Perms2_upwards_closed; eauto. cbn.
      do 2 eexists. split; [| split]; eauto.
      + eapply Perms2_upwards_closed. apply Hr. red. reflexivity.
      + unfold hlte_perm2. rewrite restrict_same. reflexivity.
    - eapply bisim_gen_pre in Hbisim. destruct Hbisim; [subst; constructor |].
      Unshelve. 2: auto.
      econstructor.
      4: {
        eapply IHHbisim. apply Hr. reflexivity.
        Unshelve. all: auto.
        split; [| split]; eauto.
        - apply Hlte in Hprep'. destruct Hprep' as (? & ? & ?).
          destruct H5. specialize (sep_r _ _ H0). cbn in sep_r.
          cbn. eapply pre_respects. apply sep_r.
          eapply restrict_pre; eauto. cbn.
          erewrite (proof_irrelevance _ Hrc1c2) in Hprer. apply Hprer.
          Unshelve. auto. auto.
        - apply Hlte in Hprep'. destruct Hprep' as (_ & _ & ?). split.
          + intros. eapply H1. apply H3. rewrite <- restrict_restrict. apply H4.
          + intros. destruct x, y. eapply restrict_rely; eauto. apply H3.
            eapply sep_step_guar; eauto.
        - apply Hlte in Hprep'. destruct Hprep' as (? & ? & ?).
          respects. destruct H5. specialize (sep_r _ _ H0). cbn in sep_r.
          erewrite (proof_irrelevance _ Hrc1c2).
          erewrite (proof_irrelevance _ (Hspred _ _)). apply sep_r.
      }
      Unshelve. all: auto.
      + erewrite (proof_irrelevance _ Hspred0). apply Hprep'.
      + eapply Hlte. constructor. left.
        erewrite (proof_irrelevance _ Hspred0). apply H0.
      + eapply sep_step_lte; eauto.
        (* TODO *)
        eapply Proper_sep_step_eq_perm_2. reflexivity.
        erewrite (restrict_restrict _ _ _ _ r). reflexivity. eapply sep_step_sep_conj_l; eauto.
        apply Hlte in Hprep'. apply Hprep'.
    - econstructor.
      4: {
        eapply bisim_gen_pre in Hbisim. destruct Hbisim; [rewrite H2; constructor |].
        eapply IHHbisim. apply Hr. reflexivity.
        Unshelve. all: auto.
        split; [| split]; eauto.
        - apply Hlte in Hprep'. destruct Hprep' as (? & ? & ?).
          destruct H5. specialize (sep_r _ _ H0). cbn in sep_r.
          cbn. eapply pre_respects. apply sep_r.
          eapply restrict_pre; eauto. cbn.
          erewrite (proof_irrelevance _ Hrc1c2) in Hprer. apply Hprer.
          Unshelve. auto. auto.
        - apply Hlte in Hprep'. destruct Hprep' as (_ & _ & ?). split.
          + intros. eapply H1. apply H3. rewrite <- restrict_restrict. apply H4.
          + intros. destruct x, y. eapply restrict_rely; eauto. apply H3.
            eapply sep_step_guar; eauto.
        - apply Hlte in Hprep'. destruct Hprep' as (? & ? & ?).
          respects. destruct H5. specialize (sep_r _ _ H0). cbn in sep_r.
          erewrite (proof_irrelevance _ Hrc1c2).
          erewrite (proof_irrelevance _ (Hspred _ _)). apply sep_r.
      }
      Unshelve. all: auto.
      + erewrite (proof_irrelevance _ Hspred0). apply Hprep'.
      + eapply Hlte. constructor. left.
        erewrite (proof_irrelevance _ Hspred0). apply H0.
      + eapply sep_step_lte; eauto.
        (* TODO *)
        eapply Proper_sep_step_eq_perm_2. reflexivity.
        erewrite (restrict_restrict _ _ _ _ r). reflexivity. eapply sep_step_sep_conj_l; eauto.
        apply Hlte in Hprep'. apply Hprep'.
    - econstructor 8.
      4: {
        pose proof H2 as Hbisim.
        punfold Hbisim. eapply bisim_gen_pre in Hbisim.
        destruct Hbisim; [rewrite H3; left; pstep; constructor |].
        right. eapply CIH.
        5: { apply H2. }
        3: { apply Hr. }
        2: { respects. apply Hlte in Hprep'. destruct Hprep' as (? & ? & ?).
             destruct H6. specialize (sep_r _ _ H0). cbn in sep_r.
             erewrite (proof_irrelevance _ Hrc1c2). apply sep_r.
        }
        2: { reflexivity. }
        Unshelve. all: auto.
        split; [| split]; eauto.
        - apply Hlte in Hprep'. destruct Hprep' as (? & ? & ?).
          destruct H6. specialize (sep_r _ _ H0). cbn in sep_r.
          cbn. eapply pre_respects.
          erewrite (proof_irrelevance _ (Hspred _ (Hspred' _ _))) in sep_r. apply sep_r.

          eapply restrict_pre; eauto. cbn.
          erewrite (proof_irrelevance _ Hrc1c2) in Hprer. apply Hprer.
          Unshelve. auto. auto.
        - apply Hlte in Hprep'. destruct Hprep' as (_ & _ & ?). split.
          + intros. eapply H1. apply H4. rewrite <- restrict_restrict. apply H5.
          + intros. destruct x, y. eapply restrict_rely; eauto. apply H4.
            eapply sep_step_guar; eauto.
      }
      + erewrite (proof_irrelevance _ Hspred0). apply Hprep'.
      + eapply Hlte. constructor. left.
        erewrite (proof_irrelevance _ Hspred0). apply H0.
      + eapply sep_step_lte; eauto.
        (* TODO *)
        eapply Proper_sep_step_eq_perm_2. reflexivity.
        erewrite (restrict_restrict _ _ _ _ r). reflexivity. eapply sep_step_sep_conj_l; eauto.
        apply Hlte in Hprep'. apply Hprep'.
    - econstructor 11.
      2: { intros. specialize (H0 b1). destruct H0 as (b2 & H0). pclearbot. exists b2.
           pose proof H0 as Hbisim.
           punfold Hbisim.
      }
      2: { intros. specialize (H1 b2). destruct H1 as (b1 & H1). pclearbot. exists b1.
           pose proof H1 as Hbisim.
           punfold Hbisim.
      }
      apply Hprep'.
  Qed.

  Lemma typing_frame {R1 R2} P Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2):
    typing P Q t s ->
    typing (sep_conj_Perms2 P R) (fun r1 r2 => sep_conj_Perms2 (Q r1 r2) R) t s.
  Proof.
    intros Ht spred p' c1 c2 Hc1c2 (p & r & Hp & Hr & Hlte) Hpre.
    pose proof Hpre as Hpre'.
    apply Hlte in Hpre. destruct Hpre as (Hp' & Hr' & Hsep).
    eapply bisim_frame.
    - apply Hpre'.
    - apply Hr'.
    - apply Hr.
    - rewrite restrict_same. apply Hlte.
    - eapply Ht. apply Hp. apply Hp'.
      Unshelve. auto.
  Qed.


  (*
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
*)

  Global Instance Proper_eq_Perms_typing {R1 R2} :
    Proper (eq_Perms2 ==>
           (pointwise_relation _ (pointwise_relation _ eq_Perms2)) ==> eq ==> eq ==> flip impl) (@typing R1 R2).
  Proof.
    repeat intro. subst.
    eapply bisim_lte; eauto.
    eapply H3. eapply eq_Perms2_eq_perm_in_Perms2; eauto. reflexivity.
    apply H5. apply H0.
  Qed.
End bisim.
