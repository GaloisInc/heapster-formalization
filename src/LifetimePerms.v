(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     FSets.FMaps.

From ITree Require Import
     ITree
     Eq.Eqit
     Events.Exception.

From Heapster Require Import
     Utils
     Permissions
     PermissionsSpred2
     Lifetime
     Typing.

From Paco Require Import
     paco.

Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.
Open Scope list_scope.
(* end hide *)

Section LifetimePerms.

  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  Definition nonLifetime (p : @perm (Si * Ss)) : Prop :=
    (forall x y, guar p x y -> lget (fst x) = lget (fst y)).

  Lemma clos_trans_nonLifetime p q (Hp : nonLifetime p) (Hq : nonLifetime q) x y :
    Relation_Operators.clos_trans (Si * Ss) (guar p \2/ guar q) x y ->
    lget (fst x) = lget (fst y).
  Proof.
    repeat intro. cbn in H. induction H.
    - destruct H; auto.
    - etransitivity; eauto.
  Qed.

  Lemma nonLifetime_sep_conj p q (Hp : nonLifetime p) (Hq : nonLifetime q) :
    nonLifetime (p ** q).
  Proof.
    repeat intro. apply (clos_trans_nonLifetime p q); auto.
  Qed.

  Lemma nonLifetime_bottom : nonLifetime bottom_perm.
  Proof.
    repeat intro; cbn in *; subst; auto.
  Qed.

  Lemma nonLifetime_lte p q :
    nonLifetime p -> q <= p -> nonLifetime q.
  Proof.
    repeat intro. apply H0 in H1. apply H; auto.
  Qed.

  (* Definition lifetime_invariant x y := *)
  (*   (forall n n', subsumes n' n (lget x) (lget x) -> *)
  (*            subsumes n' n (lget y) (lget y)) /\ *)
  (*     (forall n, lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n)). *)

  (* Instance lifetime_invariant_preorder : PreOrder lifetime_invariant. *)
  (* Proof. *)
  (*   split; [split; intuition |]. *)
  (*   - intros ? ? ? [] []. split; auto; etransitivity; eauto. *)
  (* Qed. *)

  (* Definition monotonic_at (p : @perm C) (n : nat) x y : Prop := *)
  (*   guar p x y -> lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n). *)

  (* Instance monotonic_at_reflexive p n : Reflexive (monotonic_at p n). *)
  (* Proof. *)
  (*   repeat intro. reflexivity. *)
  (* Qed. *)

  (* Lemma bottom_monotonic_at n : forall x y, monotonic_at bottom_perm n x y. *)
  (* Proof. *)
  (*   repeat intro. simpl in H. subst. reflexivity. *)
  (* Qed. *)

  (* Definition monotonic (P : Perms) (n : nat) : Prop := *)
  (*   forall p, p ∈ P -> exists p', p' <= p /\ p' ∈ P /\ forall x y, monotonic_at p' n x y. *)

  (* Lemma monotonic_bottom n : monotonic bottom_Perms n. *)
  (* Proof. *)
  (*   repeat intro. exists bottom_perm. split; [| split]. *)
  (*   apply bottom_perm_is_bottom. auto. apply bottom_monotonic_at. *)
  (* Qed. *)

  (* Program Definition restrict_monotonic_at (p : perm) (n : nat) : @perm C := *)
  (*   {| *)
  (*     pre := pre p; *)
  (*     rely := rely p; *)
  (*     guar := fun x y => guar p x y /\ monotonic_at p n x y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro. *)
  (*   - split; intuition. *)
  (*   - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   respects. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_monotone p p' n : *)
  (*   p <= p' -> restrict_monotonic_at p n <= restrict_monotonic_at p' n. *)
  (* Proof. *)
  (*   intros []. constructor; intros; simpl; auto. destruct H. *)
  (*   split; auto. intro. auto. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_lte p n : restrict_monotonic_at p n <= p. *)
  (* Proof. *)
  (*   constructor; intros; simpl in *; intuition. *)
  (* Qed. *)

  (* Definition invariant_at (p : perm) (n : nat) : Prop := *)
  (*   forall l1 l2 x y, guar p x y <-> guar p (replace_lifetime x n l1) (replace_lifetime y n l2). *)

  (* Lemma invariant_l p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime y n = Some l2 -> *)
  (*                guar p x y <-> guar p (replace_lifetime x n l1) y. *)
  (* Proof. *)
  (*   intros. *)
  (*   erewrite <- (replace_list_index_eq _ y n l2) at 2; auto. *)
  (* Qed. *)

  (* Lemma invariant_r p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime x n = Some l1 -> *)
  (*                guar p x y <-> guar p x (replace_lifetime y n l2). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite <- (replace_list_index_eq _ x n l1) at 2; auto. *)
  (* Qed. *)

  (* Note: does not have permission to start or end the lifetime [n] *)
  Program Definition when
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : perm :=
    {|
      pre x :=
      let '(si, _) := x in
      (statusOf l (lget si) = None \/ statusOf l (lget si) = Some current) ->
      pre p x;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
        Lifetimes_lte (lget si) (lget si') /\
          (* if the lifetime isn't starting or already started, the rely of p must hold *)
          ((statusOf l (lget si') = None \/ statusOf l (lget si') = Some current) ->
           rely p x y);

      guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          Lifetimes_lte (lget si) (lget si') /\
            statusOf l (lget si) = Some current /\
            statusOf l (lget si') = Some current /\
            guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros [].
      + etransitivity; eauto. apply H1. left. specialize (H0 l). rewrite H3 in H0.
        destruct (statusOf l (lget s1)); auto; inversion H0.
      + etransitivity; eauto. apply H1. specialize (H0 l). rewrite H3 in H0.
        destruct (statusOf l (lget s1)); [destruct s5 |]; auto; inversion H0.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; auto.
    decompose [and or] H; decompose [and or] H0; clear H H0.
    - inversion H1; inversion H2; subst; auto.
    - inversion H1. subst. auto.
    - inversion H4. subst. auto.
    - right. intuition. etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct x, y.
    destruct H. intros. respects. apply H0.
    specialize (H l).
    destruct H2.
    - rewrite H2 in H.
      destruct (statusOf l (lget s)); auto; inversion H.
    - rewrite H2 in H.
      destruct (statusOf l (lget s)); [destruct s3 |]; auto; inversion H.
  Qed.

  Lemma when_monotone n p1 p2 Hp1 Hp2 : p1 <= p2 -> when n p1 Hp1 <= when n p2 Hp2.
  Proof.
    intros. destruct H. constructor; simpl; intros.
    - destruct x. auto.
    - destruct x, y. destruct H; auto.
    - destruct x, y. intuition.
  Qed.

  (* Instance Proper_lte_perm_when : *)
  (*   Proper (eq ==> lte_perm ==> eq ==> lte_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. apply when_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_when : *)
  (*   Proper (eq ==> eq_perm ==> eq_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply when_monotone; auto. *)
  (* Qed. *)

  (* Gives us permission to end the lifetime [n], which gives us back [p] *)
  Program Definition owned
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : @perm (Si * Ss) :=
    {|
      (* TODO: probably need soemthing with subsumes *)
      pre x := let '(si, _) := x in
               statusOf l (lget si) = Some current;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      Lifetimes_lte (lget si) (lget si') /\
        statusOf l (lget si) = statusOf l (lget si') /\
        (statusOf l (lget si) = Some finished -> rely p x y);

      guar x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      x = y \/
        Lifetimes_lte (lget si) (lget si') /\
          statusOf l (lget si') = Some finished /\
          guar p x y; (* TODO: x and y can have different lifetimes! *)
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ? & ?), H0 as (? & ? & ?).
      split; [| split]; intros.
      + etransitivity; eauto.
      + etransitivity; eauto.
      + etransitivity; eauto. apply H4; auto. rewrite <- H1. auto.
  Qed.
  Next Obligation.
    constructor; repeat intro; auto.
    - destruct x. auto.
    - destruct x, y, z.
      decompose [and or] H; decompose [and or] H0; clear H H0.
      + inversion H1. inversion H2. subst; auto.
      + inversion H1. subst; auto.
      + inversion H3. subst; auto.
      + right. split; [| split]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct x, y.
    destruct H as (? & ? & ?). rewrite <- H1. auto.
  Qed.

  Lemma owned_monotone l p1 p2 Hp1 Hp2 :
    p1 <= p2 -> owned l p1 Hp1 <= owned l p2 Hp2.
  Proof.
    intros. destruct H.
    constructor; cbn; intros.
    - destruct x. decompose [and or] H; auto.
    - destruct x, y. decompose [and or] H; auto.
    - destruct x, y. decompose [and or] H; auto.
  Qed.

  (* Instance Proper_lte_perm_owned l ls Hls : *)
  (*   Proper (lte_perm ==> lte_perm) (owned l ls Hls). *)
  (* Proof. *)
  (*   repeat intro; subst. apply owned_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_owned l ls H : *)
  (*   Proper (eq_perm ==> eq_perm) (owned l ls H). *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply owned_monotone; auto. *)
  (* Qed. *)


  Program Definition lfinished
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : perm :=
    {|
      pre x :=
      let '(si, _) := x in
      statusOf l (lget si) = Some finished /\
        pre p x;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      Lifetimes_lte (lget si) (lget si') /\ (* TODO: what if it is ending at the moment *)
        (statusOf l (lget si) = Some finished ->
         rely p x y);

      guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          lget si = lget si' /\
            statusOf l (lget si) = Some finished /\
            statusOf l (lget si') = Some finished /\
            guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros. etransitivity; eauto. apply H2. specialize (H l). rewrite H3 in H.
        destruct (statusOf l (lget s1)); [destruct s5 |]; auto; inversion H.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; auto.
    decompose [and or] H; decompose [and or] H0; clear H H0.
    - inversion H1; inversion H2; subst; auto.
    - inversion H1. subst. auto.
    - inversion H4. subst. auto.
    - right. intuition. etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct x, y. intuition.
    specialize (H1 l). rewrite H in H1.
    destruct (statusOf l (lget s1)); [destruct s3 |]; auto; inversion H1.
  Qed.

  (* TODO: write lemma for proving Hpq *)
  Lemma lifetimes_sep_gen p q l Hp Hq :
    p ⊥ owned l q Hq ->
    when l p Hp ⊥ owned l (p ** q) (nonLifetime_sep_conj _ _ Hp Hq).
  Proof.
    split; intros.
    - destruct x, y. cbn in H0.
      decompose [and or] H0; [inversion H1; subst; intuition |]. clear H0.
      cbn. split; auto. intros [].
      + rewrite H0 in H1. inversion H1.
      + rewrite H0 in H1. inversion H1.
    - cbn in H0. destruct x, y.
      decompose [and or] H0; [inversion H1; subst; intuition |]; clear H0.
      cbn. split; [| split]; auto.
      + intros. rewrite H1, H3. auto.
      + intros. rewrite H1 in H0. discriminate H0.
  Qed.

  Lemma lifetimes_sep' l p Hp : when l p Hp ⊥ lfinished l p Hp.
  Proof.
    constructor; intros; cbn in H; auto.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split. rewrite H1. reflexivity.
      intro. rewrite H2 in H. destruct H; inversion H.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split; auto.
      intros. rewrite H in H0. inversion H0.
  Qed.

  (* not actually a special case of the above *)
  Lemma lifetimes_sep l p Hp : when l p Hp ⊥ owned l p Hp.
  Proof.
    constructor; intros; cbn in H; auto.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split; auto. intros. rewrite H0 in H. destruct H; inversion H.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      simpl. split; [| split]; auto.
      + rewrite H0, H2. auto.
      + intros. rewrite H in H0. discriminate H0.
  Qed.

  Lemma convert p q l Hp Hq :
    when l p Hp ** owned l (p ** q) (nonLifetime_sep_conj _ _ Hp Hq) <=
      p ** owned l q Hq.
  Proof.
    split; intros.
    - destruct x. cbn in *.
      decompose [and or] H; auto. split; auto. split; auto.
      eapply lifetimes_sep_gen; eauto.
    - destruct x, y. cbn in *.
      destruct H as (? & ? & ? & ?). split; [| split; [| split]]; auto.
    - destruct x, y. cbn in H.
      induction H. 2: econstructor 2; eauto.
      clear s s0 s1 s2.
      destruct x, y.
      decompose [and or] H; cbn; subst; try solve [constructor; auto]; clear H.
      rename H0 into Hlte, H1 into Hy, H3 into Hguar.
      apply Operators_Properties.clos_trans_t1n_iff.
      apply Operators_Properties.clos_trans_t1n_iff in Hguar.

      remember (s, s0). remember (s1, s2). revert s s0 s1 s2 Hlte Hy Heqp0 Heqp1.
      induction Hguar; intros; subst.
      + constructor 1. destruct H; [left | right]; auto.
      + econstructor 2.
        2: {
          destruct y.
          eapply (IHHguar s3 s4 s1 s2); eauto. clear H Hlte Hy IHHguar.
          rewrite <- Operators_Properties.clos_trans_t1n_iff in Hguar.
          apply clos_trans_nonLifetime in Hguar; auto.
          cbn in *; rewrite Hguar. reflexivity.
        }
        destruct H.
        left; auto.
        destruct y. right. right. split; [| split]; auto.
        * apply Hq in H. cbn in H. rewrite H. reflexivity.
        * clear Hlte H IHHguar.
          rewrite <- Operators_Properties.clos_trans_t1n_iff in Hguar.
          apply clos_trans_nonLifetime in Hguar; auto. cbn in *.
          rewrite Hguar. auto.
  Qed.

  (* special case of convert *)
  Lemma convert_bottom p n Hp :
    when n p Hp ** owned n p Hp <= p ** owned n bottom_perm nonLifetime_bottom.
  Proof.
  (*   rewrite <- (sep_conj_perm_bottom p) at 2. eapply convert; auto. *)
  (* Qed. *)
  Abort.

(* Lemma lcurrent_pre_trans' x n1 n2 n3 : *)
(*     lcurrent_pre x n1 n3 -> *)
(*     lcurrent_pre x n1 n2 /\ lcurrent_pre x n2 n3. *)
(* Proof. *)
(*   unfold lcurrent_pre. split. *)
(*   - split. *)
(*     + intro. apply H. *)
  (* Admitted. *)

  (** The naive defn is transitive, at least *)
(*    Program Definition lcurrent n1 n2 : @perm C :=
    {|
      pre x := subsumes n1 n2 (lget x) (lget x);
      rely x y := x = y \/
                    subsumes n1 n2 (lget x) (lget x) /\
                    subsumes n1 n2 (lget y) (lget y);
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; try solve [intuition].
    destruct H, H0; subst; auto.
    right. destruct H, H0. split; eapply subsumes_preorder; eauto; reflexivity.
  Qed.
  Next Obligation.
    constructor; repeat intro; subst; intuition.
  Qed.
  Next Obligation.
    destruct H; subst; auto. destruct H; intuition.
  Qed.

  Lemma lcurrent_transitive n1 n2 n3 :
    lcurrent n1 n3 <= lcurrent n1 n2 ** lcurrent n2 n3.
  Proof.
    constructor; intros; cbn; intuition.
    - destruct H as (? & ? & ?). simpl in *. eapply subsumes_preorder; eauto.
    - destruct H. simpl in *. destruct H, H0; subst; auto. right.
      destruct H, H0. split; auto; eapply subsumes_preorder; eauto.
  Qed.
*)

  Definition when_Perms l P : Perms :=
    meet_Perms (fun R => exists p Hp, p ∈ P /\ R = singleton_Perms (when l p Hp)).

  Definition lfinished_Perms l P : Perms :=
    meet_Perms (fun R => exists p Hp, p ∈ P /\ R = singleton_Perms (lfinished l p Hp)).

  Definition lowned_Perms l P Q : Perms :=
    meet_Perms (fun R => exists r q Hq, R = singleton_Perms (r ** owned l q Hq) /\
                               q ∈ Q /\
                               (forall p, p ∈ P -> forall s, pre r s -> pre p s -> pre q s)).

  Program Definition lowned_Perms' l P Q :=
    {|
      (* exists F: p -> Hp -> .. *)
      in_Perms x := forall p (Hp : nonLifetime p),
        p ∈ P ->
        exists q Hq,
          q ∈ Q /\
            owned l q Hq <= x /\
            (forall c1 c2, pre p ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                      pre x ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                      pre q ((lput c1 (replace_list_index (lget c1) l finished)), c2));
    |}.
  Next Obligation.
    specialize (H p Hp H1). destruct H as (q & Hq' & Hq & Howned & Hpre).
    exists q, Hq'. split; [| split]; auto.
    - etransitivity; eauto.
    - intros. apply Hpre; auto. apply H0. auto.
  Qed.

  Lemma when_perm_Perms l p Hp P :
    p ∈ P ->
    when l p Hp ∈ when_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p, Hp. split; eauto.
    - cbn. reflexivity.
  Qed.

  Lemma lfinished_perm_Perms l p Hp P :
    p ∈ P ->
    lfinished l p Hp ∈ lfinished_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p, Hp. split; eauto.
    - cbn. reflexivity.
  Qed.

  (*
    (* TODO: need to add pre_perm *)
  Lemma lowned_perm_Perms l ls Hsub p Hp P :
    p ∈ P ->
    owned l ls Hsub p Hp ∈ lowned_Perms' l ls Hsub P P.
  Proof.
    cbn. intros. cbn. exists p0. split; [| split]; auto. reflexivity.
    - do 3 eexists. split; [| split]. reflexivity.
      apply H.
      intros. apply H1.
    - exists (fun _ H => H). red. rewrite restrict_same.
      rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity.
  Qed.
   *)

  Definition endLifetime (l : nat) : itree (sceE Si) unit :=
    s <- trigger (Modify id);;
    match nth_error (lget s) l with
    | Some current =>
        trigger (Modify (fun s =>
                           (lput s (replace_list_index
                                      (lget s)
                                      l
                                      finished))));;
        Ret tt
    | _ => throw tt
    end.

  (* Lemma sep_step_lowned p q l Hq : *)
  (*   p ⊥ owned l q Hq -> *)
  (*   p ⊥ q. *)
  (* Proof. *)
  (*   intros. constructor. *)
  (*   - destruct H. intros. apply H. cbn. destruct x, y. right. *)
  (* Qed. *)


  Lemma sep_step_owned_finished l p Hp :
    SepStep.sep_step
      (owned l p Hp)
      (lfinished l p Hp).
  Proof.
    repeat intro. constructor.
    - intros [] [] ?. cbn in *. apply H in H0. cbn in H0. intuition.
    - intros [] [] ?. cbn in *. destruct H0. rewrite H0. reflexivity.
      destruct H0 as (? & ? & ? & ?). apply H. cbn. right. intuition. rewrite H0. reflexivity.
  Qed.

  Lemma typing_end l P Q :
    typing (P * (lowned_Perms' l P Q))
           (fun _ _ => lfinished_Perms l Q)
           (endLifetime l)
           (Ret tt).
  Proof.
    intros p' c1 c2 (p & lowned' & Hp & Hl & Hlte) Hpre.
    assert (Hp' : nonLifetime p) by admit.
    specialize (Hl _ Hp' Hp).
    destruct Hl as (q & Hq' & Hq & Hhlte & Hpre').
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    pose proof Hpre as Hpre''.
    apply Hlte in Hpre. destruct Hpre as (_ & ? & _). apply Hhlte in H. rewrite H.
    rewritebisim @bind_trigger.
    econstructor; unfold id. eauto.
    cbn in *. apply Hlte. constructor 1. right.
    apply Hhlte. cbn. right.
    {
      rewrite lGetPut.
      split; [| split].
      - admit. (* TODO lemma *)
      - unfold statusOf. apply nth_error_replace_list_index_eq.
      - red in Hq'. (* TODO: wait this is an issue *) admit.
    }
    2: {
      econstructor. 2: apply lfinished_perm_Perms; eauto.
      Unshelve. 2: auto.
      cbn. rewrite lGetPut.
      split. apply nth_error_replace_list_index_eq.
      apply Hpre'; auto.
      (* maybe change the precondition clause to use \/, and then use the nonLifetime of p (need to add nonLifetime P first) *)
      (* wait, if P is a when l, then it wouldn't work *)
      (* maybe change it so the hypotheses act on s with lifetime set to current, and conclusion is where lifetime is set to finished *)
      - apply Hlte in Hpre''. cbn in H. admit.
      - apply Hlte in Hpre''. cbn in H. admit.
    }
    eapply SepStep.sep_step_lte; eauto.
    eapply SepStep.sep_step_lte. apply lte_r_sep_conj_perm.
    eapply SepStep.sep_step_lte; eauto.
    apply sep_step_owned_finished.
  Admitted.

  (* Wrong permission:
  Program Definition join_owned_perm'
          p (P : @Perms (Si * Ss)) (Hp' : nonLifetime p) (Hp : p ∈ P)
          Q l powned
          (H :
            forall (p : perm) (Hp : nonLifetime p),
              p ∈ P ->
              {q : perm | {Hq : nonLifetime q |
                            q ∈ Q /\ owned l q Hq <= powned /\ (forall s, pre p s -> pre powned s -> pre q s)}})
          Hinhab : perm :=
    @join_perm' (Si * Ss) (fun p' => _) Hinhab.
  Next Obligation.
    specialize (H p Hp' Hp). destruct H as (q & Hq' & Hq & Hlte & Hpre).
    apply (p' = owned l (p ** q) (nonLifetime_sep_conj _ _ Hp' Hq')).
  Defined.
  Program Definition owned_join_perm'
          p (P : @Perms (Si * Ss)) (Hp' : nonLifetime p) (Hp : p ∈ P)
          Q l powned
          (H :
            forall (p : perm) (Hp : nonLifetime p),
              p ∈ P ->
              {q : perm | {Hq : nonLifetime q |
                            q ∈ Q /\ owned l q Hq <= powned /\ (forall s, pre p s -> pre powned s -> pre q s)}})
          Hinhab : perm :=
    owned l (p ** @join_perm' (Si * Ss) (fun p' => _) Hinhab) _.
  Next Obligation.
    specialize (H p Hp' Hp). destruct H as (q & Hq' & Hq & Hlte & Hpre).
    apply (p' = q).
  Defined.
  Next Obligation.
    admit. (* TODO lemma *)
  Admitted.
   *)

  Program Definition join_owned_perm
          (P : @Perms (Si * Ss)) Q l powned (r : @perm (Si * Ss)) (Hr : nonLifetime r)
          (H :
            forall (p : perm) (Hp : nonLifetime p),
              p ∈ P ->
              {q : perm | {Hq : nonLifetime q |
                            q ∈ Q /\ owned l q Hq <= powned /\ (forall s, pre p s -> pre powned s -> pre q s)}})
          Hinhab : perm :=
    @join_perm' (Si * Ss) (fun p' => exists p (Hp : p ∈ P) (Hp' : nonLifetime p), _) Hinhab.
  Next Obligation.
    specialize (H p Hp' Hp). destruct H as (q & Hq' & Hq & Hlte & Hpre).
    apply (p' = owned l (r ** q) (nonLifetime_sep_conj _ _ Hr Hq')).
  Defined.
  Program Definition owned_join_perm
          (P : @Perms (Si * Ss)) Q l powned r (Hr : nonLifetime r)
          (H :
            forall (p : perm) (Hp : nonLifetime p),
              p ∈ P ->
              {q : perm | {Hq : nonLifetime q |
                            q ∈ Q /\ owned l q Hq <= powned /\ (forall s, pre p s -> pre powned s -> pre q s)}})
          Hinhab : perm :=
    owned l (r ** @join_perm' (Si * Ss) (fun p' => exists p (Hp : p ∈ P) (Hp' : nonLifetime p), _) Hinhab) _.
  Next Obligation.
    specialize (H p Hp' Hp). destruct H as (q & Hq' & Hq & Hlte & Hpre).
    apply (p' = q).
  Defined.
  Next Obligation.
    eapply (clos_trans_nonLifetime _ _ _ _ _ _ H0).
    Unshelve. all: auto.
    repeat intro. cbn in H1.
    induction H1; auto.
    2: etransitivity; eauto.
    destruct H1 as (? & (? & ? & ? & ?) & ?). red in H1.
    destruct (H x2 x4 x3) as (? & ? & ? & ? & ?). subst. apply x6; auto.
  Defined.

  Lemma join'_owned_commut_sig P Q l powned r Hr H Hinhab1 Hinhab2 :
    join_owned_perm P Q l powned r Hr H Hinhab1 <=
      owned_join_perm P Q l powned r Hr H Hinhab2.
  Proof.
    constructor.
    - cbn. intros [] ? x ?.
      destruct H1 as (p & Hp & Hp' & ?). red in H1.
      destruct H as (q & Hq' & Hq & Hlte & Hpre). subst. auto.
    - cbn. intros [] [] ? x ?.
      destruct H0 as (? & ? & ?).
      destruct H1 as (p & Hp & Hp' & ?).
      unfold join_owned_perm_obligation_1 in *.
      unfold owned_join_perm_obligation_1 in *.
      destruct H as (q & Hq' & Hq & Hlte & Hpre) eqn:?. subst.
      cbn. split; [| split]; auto.
      intros. apply H3 in H1. destruct H1. split; auto.
      apply H4. do 3 eexists. rewrite Heqs3. auto.
    - intros ? ? ?. cbn in H0. induction H0. 2: etransitivity; eauto.
      destruct H0 as (? & (p & Hp & Hp' & ?) & ?). red in H0.
      destruct (H p Hp' Hp) as (q & Hq' & Hq & Hlte & Hpre) eqn:?. subst.
      destruct x, y. cbn. destruct H1; auto. right.
      destruct H0 as (? & ? & ?). split; [| split]; auto.
      remember (s, s0). remember (s1, s2).
      revert s s0 s1 s2 Heqp0 Heqp1 H0 H1.
      induction H2; intros; subst.
      + constructor 1. destruct H0; auto. right. constructor 1. exists q.
        split; auto. do 3 eexists. red. rewrite Heqs. auto.
      + destruct y.
        econstructor 2.
        * clear IHclos_trans2.
          apply (IHclos_trans1 s s0 s3 s4); auto.
          -- apply clos_trans_nonLifetime in H2_; auto.
             cbn in H2_. rewrite H2_. reflexivity.
          -- apply clos_trans_nonLifetime in H2_0; auto.
             cbn in H2_0. rewrite H2_0. auto.
        * clear IHclos_trans1. apply (IHclos_trans2 s3 s4 s1 s2); auto.
          apply clos_trans_nonLifetime in H2_0; auto.
          cbn in H2_0. rewrite H2_0. reflexivity.
  Qed.

  Lemma join'_owned_commut l p Hp powned asdf asdf' asdf'' :
    join_perm' (fun pp => exists q Hq, owned l q Hq <= powned /\
                                 pp = owned l (p ** q) (nonLifetime_sep_conj _ _ Hp Hq)) asdf <=
      owned l (p ** join_perm' (fun q => exists Hq, owned l q Hq <= powned) asdf') asdf''.
  Proof.
    constructor.
    - cbn. intros [] ? ? ?. destruct H0 as (? & ? & ? & ?). subst. auto.
    - cbn. intros [] [] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn.
      destruct H as (? & ? & ?). split; auto. split; auto.
      intros. destruct H2; auto. split; auto.
      apply H4. eauto.
    - intros ? ? ?. cbn in H. induction H. 2: etransitivity; eauto.
      destruct H as (? & ? & ?). destruct H as (q & Hq & Hlte & ?). subst.
      destruct x, y. destruct H0; [left; auto | right].
      intuition.
      remember (s, s0). remember (s1, s2).
      revert s s0 s1 s2 H0 H Heqp0 Heqp1.
      induction H2; intros; subst.
      + constructor 1. destruct H; auto. right. constructor 1. exists q. split; eauto.
      + destruct y. etransitivity.
        * apply (IHclos_trans1 s s0 s3 s4); auto.
          -- apply clos_trans_nonLifetime in H2_; auto.
             cbn in H2_. rewrite H2_. reflexivity.
          -- apply clos_trans_nonLifetime in H2_0; auto.
             cbn in H2_0. rewrite H2_0. auto.
        * apply (IHclos_trans2 s3 s4 s1 s2); auto.
          apply clos_trans_nonLifetime in H2_0; auto.
          cbn in H2_0. rewrite H2_0. reflexivity.
  Qed.

  Lemma foo l P Q R (Hinhab : exists q, q ∈ Q /\ nonLifetime q) :
    P * lowned_Perms' l Q R ⊨
    when_Perms l P * lowned_Perms' l (P * Q) (P * R).
  Proof.
    intros p0 (p & powned & Hp & Howned & Hlte). cbn in Howned.
    assert (Hp' : nonLifetime p) by admit.
    eexists (when l p Hp').

    assert (forall (q : perm) (Hq' : nonLifetime q), q ∈ Q -> {r : perm | { Hr : nonLifetime r | r ∈ R /\ owned l r Hr <= powned /\ (forall s, pre q s -> pre powned s -> pre r s)}}) by admit.
    clear Howned.
    eexists (join_owned_perm Q _ l powned p Hp' X _).
    (* Unshelve. *)
    (* 2: { cbn. unfold join_owned_perm_obligation_1. do 4 eexists. *)
    (*      (* use the fact taht Q inhab *) *)
    (*      admit. } *)

    (* eexists (join_perm' (fun p' => exists p Hp, _) _). *)
    (* Unshelve. *)
    (* 5: { *)
    (*   specialize (X p Hp). *)
    (*   destruct X. destruct s. destruct a as (? & ? & ?). *)
    (*   eapply (p' = owned l (x ** p) _). *)
    (* } *)

    (* eexists (join_perm' (fun p' => exists q Hq, owned l q Hq <= powned /\ *)
    (*                                       p' = owned l (p ** q) _) _). *)
    split; [apply when_perm_Perms | split]; auto.
    2: { etransitivity; eauto.
         etransitivity. apply sep_conj_perm_monotone; [reflexivity |].
         apply join'_owned_commut_sig.

         etransitivity. apply convert.
         apply sep_conj_perm_monotone; [reflexivity |].
         unfold owned_join_perm_obligation_1.

         constructor.
         - intros [] ?.
           destruct Hinhab as (? & ? & ?).
           edestruct X as (r & Hr' & Hr & Hlte' & Hpre). apply n. apply i.
           apply Hlte' in H. auto.
         - destruct Hinhab as (? & ? & ?).
           destruct (X x n i) as (r & Hr' & Hr & Hlte' & Hpre).
           intros [] [] ?. split; [| split]; cbn.
           + apply Hlte' in H. apply H.
           + apply Hlte' in H. apply H.
           + intros. destruct H1 as (q & Hq & Hq' & ?).
             destruct (X q Hq' Hq). destruct s3 as (? & ? & ? & ?). subst.
             apply l0 in H. cbn in H. apply H. auto.
         - intros [] [] ?. cbn in H. destruct H; [rewrite H; reflexivity |].
           destruct H as (? & ? & ?).
           remember (s, s0). remember (s1, s2).
           revert s s0 s1 s2 Heqp1 Heqp2 H H0.
           induction H1; intros; subst.
           destruct H as (x & (? & ? & ? & ?) & ?).
           destruct (X x0 x2 x1) as (? & ? & ? & ? & ?). subst.
           + apply l0. cbn. right. split; [| split]; auto.
           + destruct y. etransitivity.
             eapply (IHclos_trans1 s s0 s3 s4); auto.
             admit. admit. (* ok since the r is nonLifetime *)
             eapply (IHclos_trans2 s3 s4 s1 s2); auto.
             admit.
    }
    intros ? ? (? & ? & ? & ? & ?).
    destruct Hinhab as (q & Hq & Hq').
    destruct (X q Hq' Hq) as (r & Hr' & Hr & ? & ?).
    exists (x ** r). eexists. split; [| split].
    - do 2 eexists. split; [| split]; eauto. reflexivity.
    - unfold join_owned_perm, join_owned_perm_obligation_1.
      admit.
    - intros.
      cbn in H3.
      split; [| split].
      + apply

    intros p0' (p' & q & Hp' & Hq & Hlte').
    pose proof (Howned q Hq). destruct H as (r & Hr' & Hr & Hpowned & Hpre).
    exists (p' ** r). eexists. split; [apply sep_conj_Perms_perm | split]; auto.
    admit.
    intros. cbn in *. split; [| split].
    - apply Hlte'. apply H.
    - apply Hpre.
      + apply Hlte'. auto.
      + apply H0. do 2 eexists. split; eauto. admit.
    - apply Hlte' in H.
  Qed.

  (* Require Import Heapster.Typing. *)

  (* Definition startLifetime : itree (sceE C) nat := *)
  (*   ret 0. *)
End LifetimePerms.
