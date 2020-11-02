From Heapster Require Import
     Permissions
     Config
     NoEvent.
     (* StepError. *)
     (* Typing. *)

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.

Ltac rewritebisim lem := pose proof lem as bisim;
                         eapply bisimulation_is_eq in bisim;
                         rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply bisimulation_is_eq in bisim;
                              rewrite bisim in H;
                              clear bisim.

Lemma throw_bind {E R1 R2} `{exceptE unit -< E} (k : R1 -> itree E R2) :
  x <- throw tt;; k x = throw tt.
Proof.
  apply bisimulation_is_eq. pcofix CIH.
  pstep. unfold throw. rewritebisim @bind_vis. constructor. intros. inversion v.
Qed.

Section bisim.
  Variant ModifyE {C : Type} : Type -> Type :=
  | Modify : forall (f : C -> C), ModifyE C
  .

  Definition E (C : Type) := (exceptE unit +' @ModifyE C +' nondetE).

  Context {config specConfig : Type}.

  Variant no_error_gen {R C : Type} no_error (c : C) : itree (E C) R -> Prop :=
  | no_error_ret : forall r, no_error_gen no_error c (Ret r)
  | no_error_tau : forall t, no_error c t -> no_error_gen no_error c (Tau t)
  | no_error_modify : forall f k,
      no_error (f c) (k c) ->
      no_error_gen no_error c (vis (Modify f) k)
  | no_error_choice : forall k,
      (forall b, no_error c (k b)) ->
      no_error_gen no_error c (vis Or k)
  .

  Definition no_error {R C : Type} :=
    paco2 (@no_error_gen R C) bot2.

  Lemma no_error_gen_mon {R C} : monotone2 (@no_error_gen R C).
  Proof.
    repeat intro. inversion IN; subst; try solve [constructor; auto].
  Qed.
  Hint Resolve no_error_gen_mon : paco.

  Program Definition eq_p {T : Type} (y x : T) : (@Perms (config * specConfig)) :=
  {|
  in_Perms := fun _ => x = y;
  |}.

  (* TODO: move somewhere else *)
  Definition sep_step (p q : @perm (config * specConfig)) : Prop :=
    forall r, p ⊥ r -> q ⊥ r.

  Inductive typing_gen {R1 R2 : Type} (typing : perm -> (R1 -> R2 -> Perms) -> itree (E config) R1 -> config -> itree (E specConfig) R2 -> specConfig -> Prop)
            (p : perm) (Q : R1 -> R2 -> Perms) :
    itree (E config) R1 -> config -> itree (E specConfig) R2 -> specConfig -> Prop :=
  | typing_gen_ret r1 c1 r2 c2 :
      pre p (c1, c2) ->
      p ∈ Q r1 r2 ->
      typing_gen typing p Q (Ret r1) c1 (Ret r2) c2
  | typing_gen_err t1 c1 c2 :
      typing_gen typing p Q t1 c1 (throw tt) c2
  | typing_gen_tau_L t1 c1 t2 c2 :
      pre p (c1, c2) ->
      typing_gen typing p Q t1 c1 t2 c2 ->
      typing_gen typing p Q (Tau t1) c1 t2 c2
  | typing_gen_tau_R t1 c1 t2 c2 :
      pre p (c1, c2) ->
      typing_gen typing p Q t1 c1 t2 c2 ->
      typing_gen typing p Q t1 c1 (Tau t2) c2
  | typing_gen_tau t1 c1 t2 c2 :
      pre p (c1, c2) ->
      typing p Q t1 c1 t2 c2 ->
      typing_gen typing p Q (Tau t1) c1 (Tau t2) c2
  | typing_gen_modify_L f k c1 t2 c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (f c1, c2) ->
      sep_step p p' ->
      typing_gen typing p' Q (k c1) (f c1) t2 c2 ->
      typing_gen typing p Q (vis (Modify f) k) c1 t2 c2
  | typing_gen_modify_R t1 c1 f k c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (c1, f c2) ->
      sep_step p p' ->
      typing_gen typing p' Q t1 c1 (k c2) (f c2) ->
      typing_gen typing p Q t1 c1 (vis (Modify f) k) c2
  | typing_gen_modify f1 k1 c1 f2 k2 c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (f1 c1, f2 c2) ->
      sep_step p p' ->
      typing p' Q (k1 c1) (f1 c1) (k2 c2) (f2 c2) ->
      typing_gen typing p Q (vis (Modify f1) k1) c1 (vis (Modify f2) k2) c2
  | typing_gen_choice_L k c1 t2 c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b, typing_gen typing p' Q (k b) c1 t2 c2) ->
      typing_gen typing p Q (vis Or k) c1 t2 c2
  | typing_gen_choice_R t1 c1 k c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b, typing_gen typing p' Q t1 c1 (k b) c2) ->
      typing_gen typing p Q t1 c1 (vis Or k) c2
  | typing_gen_choice k1 c1 k2 c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b1, exists b2, typing p' Q (k1 b1) c1 (k2 b2) c2) ->
      (forall b2, exists b1, typing p' Q (k1 b1) c1 (k2 b2) c2) ->
      typing_gen typing p Q (vis Or k1) c1 (vis Or k2) c2
  .

  Lemma typing_gen_mon {R1 R2} : monotone6 (@typing_gen R1 R2).
  Proof.
    repeat intro. induction IN; subst; try solve [econstructor; eauto]; auto.
    econstructor 11; eauto; intros.
    - destruct (H1 b1). eexists; eauto.
    - destruct (H2 b2). eexists; eauto.
  Qed.
  Hint Resolve typing_gen_mon : paco.

  Definition typing_ {R1 R2} := paco6 (@typing_gen R1 R2) bot6.

  Lemma typing_gen_pre {R1 R2} r p (Q : R1 -> R2 -> Perms) t s c1 c2 :
    typing_gen r p Q t c1 s c2 ->
    s = throw tt \/ pre p (c1, c2).
  Proof.
    inversion 1; auto.
  Qed.

  Definition typing {R1 R2} P Q (t : itree (E config) R1) (s : itree (E specConfig) R2) :=
    forall p c1 c2, p ∈ P -> pre p (c1, c2) -> typing_ p Q t c1 s c2.

  Lemma typing_lte' {R1 R2} p Q Q' (t : itree (E config) R1) (s : itree (E specConfig) R2) c1 c2 :
    typing_ p Q t c1 s c2 -> (forall r1 r2, Q r1 r2 ⊦ Q' r1 r2) -> typing_ p Q' t c1 s c2.
  Proof.
    revert p Q Q' t s c1 c2. pcofix CIH. intros p Q Q' t s c1 c2 Htyping Hlte.
    punfold Htyping. pstep.
    induction Htyping; pclearbot; try solve [econstructor; eauto].
    - constructor; eauto. apply Hlte. auto.
    - econstructor 11; eauto; intros.
      + destruct (H1 b1). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
      + destruct (H2 b2). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
  Qed.

  Lemma typing_lte {R1 R2} P P' Q Q' (t : itree (E config) R1) (s : itree (E specConfig) R2) :
    typing P Q t s ->
    P' ⊦ P ->
    (forall r1 r2, Q r1 r2 ⊦ Q' r1 r2) ->
    typing P' Q' t s.
  Proof.
    repeat intro.
    eapply typing_lte'; eauto.
  Qed.

  Lemma typing_ret {R1 R2} P Q (r1 : R1) (r2 : R2) :
    P ⊦ Q r1 r2 -> typing P Q (Ret r1) (Ret r2).
  Proof.
    repeat intro. pstep. constructor; auto.
  Qed.

  Lemma rewrite_spin {E R} : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.


  Lemma typing_spin {R1 R2} P Q :
    typing P Q (ITree.spin : itree (E config) R1) (ITree.spin : itree (E specConfig) R2).
  Proof.
    repeat intro. pcofix CIH. pstep.
    rewrite (@rewrite_spin _ R1). rewrite (@rewrite_spin _ R2).
    constructor 5; auto.
  Qed.

  Lemma typing_top {R1 R2} Q (t : itree (E config) R1) (s : itree (E specConfig) R2) :
    typing top_Perms Q t s.
  Proof.
    repeat intro. inversion H.
  Qed.

  Lemma typing_bottom' {R1 R2} p Q (t : itree (E config) R1) (s : itree (E specConfig) R2) c1 c2:
    typing_ p Q t c1 s c2 -> typing_ p (fun _ _ => bottom_Perms) t c1 s c2.
  Proof.
    revert p Q t s c1 c2. pcofix CIH. intros. pstep. punfold H0.
    induction H0; pclearbot; try solve [econstructor; simpl; eauto].
    econstructor 11; eauto; intros.
    - destruct (H1 b1). eexists. right. eapply CIH; pclearbot; apply H3.
    - destruct (H2 b2). eexists. right. eapply CIH; pclearbot; apply H3.
  Qed.

  Lemma typing_bottom {R1 R2} P Q (t : itree (E config) R1) (s : itree (E specConfig) R2) :
    typing P Q t s -> typing P (fun _ _ => bottom_Perms) t s.
  Proof.
    repeat intro. eapply typing_bottom'; eauto.
  Qed.

  Lemma typing_bind' {R1 R2 S1 S2} (p : perm) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (E config) R1) (t2 : R1 -> itree (E config) R2)
        (s1 : itree (E specConfig) S1) (s2 : S1 -> itree (E specConfig) S2)
        c1 c2 :
    pre p (c1, c2) ->
    typing_ p Q t1 c1 s1 c2 ->
    (forall r1 r2, typing (Q r1 r2) R (t2 r1) (s2 r2)) ->
    typing_ p R (x <- t1 ;; t2 x) c1 (x <- s1 ;; s2 x) c2.
  Proof.
    revert p Q R t1 t2 s1 s2 c1 c2. pcofix CIH.
    intros p Q R t1 t2 s1 s2 c1 c2 Hpre Htyping1 Htyping2.
    punfold Htyping1. induction Htyping1.
    - do 2 rewritebisim @bind_ret_l. specialize (Htyping2 _ _ _ c1 c2 H0 H).
      eapply paco6_mon_bot; eauto.
    - rewrite throw_bind. pstep. constructor.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - do 2 rewritebisim @bind_tau. pclearbot.
      pstep. constructor 5; auto. right. eapply CIH; eauto.
    - rewritebisim @bind_vis. apply typing_gen_pre in Htyping1. destruct Htyping1; subst.
      + rewrite throw_bind. pstep. constructor.
      + specialize (IHHtyping1 H2 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - rewritebisim @bind_vis. apply typing_gen_pre in Htyping1. destruct Htyping1; subst.
      + pstep. econstructor; eauto. rewrite H2. rewrite throw_bind. constructor.
      + specialize (IHHtyping1 H2 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - do 2 rewritebisim @bind_vis. pclearbot.
      pose proof H2. punfold H2.
      pstep. econstructor 8; eauto.
      destruct (typing_gen_pre _ _ _ _ _ _ _ H2); eauto.
      rewrite H4. rewrite throw_bind. left. pstep. constructor.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (typing_gen_pre _ _ _ _ _ _ _ (H1 b)).
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 Htyping2). punfold H2.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (typing_gen_pre _ _ _ _ _ _ _ (H1 b)).
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 Htyping2). punfold H2.
    - do 2 rewritebisim @bind_vis. pclearbot. pstep. econstructor 11; eauto; intros.
      + specialize (H1 b1). destruct H1. pclearbot.
        punfold H1. destruct (typing_gen_pre _ _ _ _ _ _ _ H1).
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
      + specialize (H2 b2). destruct H2. pclearbot.
        punfold H2. destruct (typing_gen_pre _ _ _ _ _ _ _ H2).
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
  Qed.

  Lemma typing_bind {R1 R2 S1 S2} (P : Perms) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (E config) R1) (t2 : R1 -> itree (E config) R2)
        (s1 : itree (E specConfig) S1) (s2 : S1 -> itree (E specConfig) S2) :
    typing P Q t1 s1 ->
    (forall r1 r2, typing (Q r1 r2) R (t2 r1) (s2 r2)) ->
    typing P R (x <- t1 ;; t2 x) (x <- s1 ;; s2 x).
  Proof.
    repeat intro.
    eapply typing_bind'; eauto.
  Qed.

  Lemma typing_soundness {R1 R2} Q (t : itree (E config) R1) (s : itree (E specConfig) R2) p c1 c2 :
    typing_ p Q t c1 s c2 ->
    no_error c2 s ->
    no_error c1 t.
  Proof.
    revert Q t s p c1 c2. pcofix CIH. intros Q t s p c1 c2 Htyping Hs. pstep.
    punfold Htyping.
    induction Htyping;
      try solve [constructor; eauto];
      pinversion Hs; auto_inj_pair2; subst; eauto;
        try solve [constructor; eauto].
    - apply (H2 true). apply H4.
    - constructor. intros. right. destruct (H1 b). eapply CIH.
      + destruct H3; eauto. inversion b0.
      + inversion Hs; auto_inj_pair2; subst.
        specialize (H6 x). pclearbot. eauto.
  Qed.

End bisim.

Definition load (v : Value) : itree (E config) Value :=
  c <- trigger (Modify id);;
  match v with
  | VNum _ => throw tt
  | VPtr p => match read c p with
            | None => throw tt
            | Some b => Ret b
            end
  end.

Definition store (l : Value) (v : Value) : itree (E config) config :=
  match l with
  | VNum _ => throw tt
  | VPtr l => c <- trigger (Modify (fun c => match write c l v with
                                       | None => c
                                       | Some c' => c'
                                       end)) ;;
            match write c l v with
            | None => throw tt
            | Some c' => Ret c'
            end
  end.

Example no_error_load : no_error (config_mem (0, 0) (VNum 1))
                                 (load (VPtr (0, 0))).
Proof.
  pstep. unfold load. rewritebisim @bind_trigger. constructor.
  left. pstep. constructor.
Qed.
Example no_error_store : no_error (config_mem (0, 0) (VNum 1))
                                  (store (VPtr (0, 0)) (VNum 2)).
Proof.
  pstep. unfold store. rewritebisim @bind_trigger. constructor.
  left. pstep. constructor.
Qed.

Lemma typing_load {R} ptr (Q : Value -> (@Perms (config * unit))) (r : R) :
  typing
    (read_Perms ptr Q)
    (fun x _ => (read_Perms ptr (eq_p x)) * Q x)
    (load (VPtr ptr))
    (Ret r).
Proof.
  repeat intro. pstep. unfold load. rewritebisim @bind_trigger.
  econstructor; eauto; try reflexivity.
  2: { destruct H as (? & (? & ?) & ?); subst.
       destruct i as (? & ? & ? & ? & ?). simpl in *.
       assert (read c1 ptr = Some x0).
       { apply H2 in H0. destruct H0 as (? & _). apply H in H0. auto. }
       rewrite H3. constructor; eauto.
       simpl. exists x, x1. split; [| split]; eauto. eexists. split; eauto.
       simpl. exists x, bottom_perm. split; [| split]; eauto.
       rewrite sep_conj_perm_bottom. reflexivity.
  }
  repeat intro; auto. (* TODO add sep_step properties *)
Qed.

Lemma typing_store {R} ptr val' P (Q : Value -> (@Perms (config * unit))) (r : R) :
  typing
    (write_Perms ptr P * Q val')
    (fun _ _ => write_Perms ptr Q)
    (store (VPtr ptr) val')
    (Ret r).
Proof.
  repeat intro. pstep. unfold store. rewritebisim @bind_trigger.
  destruct H as (? & ? & ? & ? & ?). destruct H as (? & (? & ?) & ?); subst.
  destruct H3 as (? & ? & ? & ? & ?). simpl in *.
  assert (exists val, read c1 ptr = Some val).
  {
    apply H2 in H0. destruct H0 as (? & _). apply H4 in H0. destruct H0 as (? & _).
    apply H in H0. simpl in H0. eexists. apply H0.
  }
  destruct H5 as (val & ?). eapply (read_success_write _ _ _ val') in H5. destruct H5.
  econstructor; eauto; try reflexivity.
  3: {
    rewrite H5. constructor; eauto.
    - admit.
    - simpl. eexists. split. exists val'. reflexivity.
      simpl. eexists. exists x0. split; [| split]; eauto.
      split; intros.
      + admit.
      + apply H; auto. apply H4. auto.
      + apply H4. constructor 1. left. apply H. apply H6.
  }
  rewrite H5. apply H2. constructor 1. left. apply H4. constructor 1. left. apply H.
  simpl. split; [| split].
  + eapply write_success_other_ptr; eauto.
  + eapply write_success_allocation; eauto.
  + eapply write_success_others; eauto.
  + repeat intro; auto. (* TODO *)
Abort.
