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

From Heapster Require Import
     Utils
     Permissions
     Lifetime.

Import ListNotations.
Open Scope list_scope.
(* end hide *)

Section LifetimePerms.

  Context {C : Type}.
  Context `{Hlens: Lens C Lifetimes}.

  Definition nonLifetime (p : perm) :=
    forall x y, guar p x y -> lget x = lget y.

  Lemma nonLifetime_sep_conj p q (Hp : nonLifetime p) (Hq : nonLifetime q) :
    nonLifetime (p ** q).
  Proof.
    repeat intro. induction H.
    - destruct H; auto.
    - etransitivity; eauto.
  Qed.

  Lemma nonLifetime_bottom : nonLifetime bottom_perm.
  Proof.
    repeat intro; cbn in *; subst; auto.
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
          (l : Lifetime)
          (p : @perm C)
          (Hp : nonLifetime p) : perm :=
    {|
      pre := fun x =>
               statusOf l (lget x) = None \/ statusOf l (lget x) = Some current ->
               (* (lifetime (lget x) n = None \/ lifetime (lget x) n = Some current) -> *)
               pre p x;
      rely := fun x y =>
                Lifetimes_lte (lget x) (lget y) /\
                  ((statusOf l (lget y) = None \/ statusOf l (lget y) = Some current) ->
                   rely p x y);
      guar := fun x y => x = y \/
                        Lifetimes_lte (lget x) (lget y) /\
                          statusOf l (lget x) = Some current /\
                          statusOf l (lget y) = Some current /\
                          guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; intuition.
    - destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros [].
      + etransitivity; eauto. apply H1. left. edestruct H0. rewrite H3 in H5.
        destruct (statusOf l (lget y)); auto; inversion H5.
      + etransitivity; eauto. apply H1. edestruct H0. rewrite H3 in H5.
        destruct (statusOf l (lget y)); [destruct s |]; auto; inversion H5.
  Qed.
  Next Obligation.
    constructor; repeat intro; auto.
    decompose [and or] H; decompose [and or] H0; subst; auto. clear H H0.
    right. split; [| split; [| split]]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct H1.
    - eapply pre_respects; eauto. apply H0. left. edestruct H. rewrite H1 in H4.
      destruct (statusOf l (lget x)); auto; inversion H4.
    - eapply pre_respects; eauto. apply H0. edestruct H. rewrite H1 in H4.
      destruct (statusOf l (lget x)); [destruct s |]; auto; inversion H4.
  Qed.

  Lemma when_monotone n p1 p2 Hp1 Hp2 : p1 <= p2 -> when n p1 Hp1 <= when n p2 Hp2.
  Proof.
    intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 7.
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
          (l : Lifetime)
          (ls : Lifetime -> Prop)
          (Hls: forall l', ls l' -> subsumes l l')
          (p : perm)
          (Hp : nonLifetime p) : @perm C :=
    {|
      (* TODO: probably need soemthing with subsumes *)
      pre := fun x => statusOf l (lget x) = Some current;
      rely := fun x y => Lifetimes_lte (lget x) (lget y) /\
                        statusOf l (lget x) = statusOf l (lget y) /\
                        (statusOf l (lget x) = Some finished -> rely p x y);
      guar := fun x y => x = y \/
                        Lifetimes_lte (lget x) (lget y) /\
                          statusOf l (lget y) = Some finished /\
                          guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
    - split; intuition.
    - destruct H as (? & ? & ?), H0 as (? & ? & ?).
      split; [| split]; intros.
      + etransitivity; eauto.
      + etransitivity; eauto.
      + etransitivity; eauto. apply H4; auto. rewrite <- H1. auto.
  Qed.
  Next Obligation.
    constructor; repeat intro; auto.
    decompose [and or] H; decompose [and or] H0; subst; auto. clear H H0.
    right. split; [| split]; auto; etransitivity; eauto.
  Qed.

  Lemma owned_monotone l ls p1 p2 Hls Hp1 Hp2 :
    p1 <= p2 -> owned l ls Hls p1 Hp1 <= owned l ls Hls p2 Hp2.
  Proof.
    intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto.
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

  (* TODO: write lemma for proving Hpq *)
  Lemma lifetimes_sep_gen p q l ls Hls Hp Hq :
    p ⊥ owned l ls Hls q Hq ->
    when l p Hp ⊥ owned l ls Hls (p ** q) (nonLifetime_sep_conj _ _ Hp Hq).
  Proof.
    split; intros.
    - simpl in H0. decompose [and or] H0; [subst; intuition |]. clear H0.
      simpl. split; auto. intros [].
      + rewrite H0 in H1. inversion H1.
      + rewrite H0 in H1. inversion H1.
    - simpl in H0. decompose [and or] H0; [subst; intuition |]. clear H0.
      simpl. split; [| split]; auto.
      + intros. rewrite H1, H3. auto.
      + intros. rewrite H1 in H0. discriminate H0.
  Qed.

  (* not actually a special case of the above *)
  Lemma lifetimes_sep l ls Hls p Hp : when l p Hp ⊥ owned l ls Hls p Hp.
  Proof.
    constructor; intros; simpl in H; auto.
    - decompose [and or] H; subst; try reflexivity. clear H.
      simpl. split; auto. intros. rewrite H0 in H. destruct H; inversion H.
    - decompose [and or] H; subst; try reflexivity. clear H.
      simpl. split; [| split]; auto.
      + rewrite H0, H2. auto.
      + intros. rewrite H in H0. discriminate H0.
  Qed.

  Lemma convert p q l ls Hls Hp Hq :
    when l p Hp ** owned l ls Hls (p ** q) (nonLifetime_sep_conj _ _ Hp Hq) <=
      p ** owned l ls Hls q Hq.
  Proof.
    split; intros.
    - simpl in *. decompose [and or] H; auto. split; auto. split; auto.
      eapply lifetimes_sep_gen; eauto.
    - simpl in *. destruct H as (? & ? & ? & ?). split; [| split; [| split]]; auto.
    - simpl in H. induction H. 2: econstructor 2; eauto.
      decompose [and or] H; simpl; subst; try solve [constructor; auto].
      clear H. rename H0 into Hlte, H1 into Hy, H3 into Hguar.
      apply Operators_Properties.clos_trans_t1n_iff.
      apply Operators_Properties.clos_trans_t1n_iff in Hguar.

      induction Hguar.
      + constructor 1. destruct H; [left | right]; auto.
      + econstructor 2.
        2: {
          apply IHHguar; auto. clear H Hls Hlte Hy IHHguar. induction Hguar.
          - destruct H; [rewrite (Hp _ _ H) | rewrite (Hq _ _ H)]; reflexivity.
          - destruct H; [rewrite (Hp _ _ H) | rewrite (Hq _ _ H)]; auto.
        }
        destruct H.
        left; auto. right; right; auto. split; [| split]; auto.
        * erewrite Hq. reflexivity. auto.
        * clear Hls Hlte H IHHguar.
          induction Hguar; (destruct H; [rewrite (Hp _ _ H) | rewrite (Hq _ _ H)]; auto).
  Qed.

  (* special case of convert *)
  Lemma convert_bottom p n ls Hsub Hp :
    when n p Hp ** owned n ls Hsub p Hp <= p ** owned n ls Hsub bottom_perm nonLifetime_bottom.
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

  (** n1 subsumes n2, and the rely states that lifetimes don't do weird stuff. **)
  Program Definition lcurrent l1 l2 (H : subsumes l1 l2) : @perm C :=
    {|
      pre x := True;
      rely x y := True;
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
  Qed.
  (* Next Obligation. *)
  (*   destruct H; subst; auto. eapply absurd; eauto. *)
  (* Qed. *)

  (* Program Definition lcurrent n1 n2 : @perm C := *)
  (*   {| *)
  (*     pre x := subsumes n1 n2 (lget x) (lget x); *)
  (*     rely x y := x = y \/ *)
  (*                   lifetime_invariant x y /\ *)
  (*                     (~subsumes n1 n2 (lget x) (lget x) \/ *)
  (*                        subsumes n1 n2 (lget x) (lget x) /\ *)
  (*                        subsumes n1 n2 (lget y) (lget y)); *)
  (*     guar x y := x = y \/ lifetime_invariant x y /\ *)
  (*                         ~subsumes n1 n2 (lget x) (lget x) /\ *)
  (*                         lifetime (lget x) n2 = lifetime (lget y) n2; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro; try solve [intuition]. *)
  (*   destruct H, H0; subst; auto. *)
  (*   right. destruct H, H0. split; [etransitivity; eauto | intuition]. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   constructor; auto. intros ? ? ? [? | [? [? ?]]] [? | [? [? ?]]]; subst; auto. *)
  (*   right. split; [| split]; auto; etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct H; subst; auto. destruct H; intuition. *)
  (* Qed. *)

  Lemma lcurrent_sep n1 n2 H :
    lcurrent n1 n2 H ⊥ lcurrent n1 n2 H.
  Proof.
    constructor; intros ? ? []; reflexivity.
  Qed.

  Lemma lcurrent_transitive n1 n2 n3 H12 H23 H13 :
    lcurrent n1 n3 H13 <= lcurrent n1 n2 H12 ** lcurrent n2 n3 H23.
  Proof.
    constructor; intros; cbn in *; intuition.
  Qed.

  (* Lemma lcurrent_sep_owned n1 n2 (ns : nat -> Prop) p : *)
  (*   ns n2 -> *)
  (*   lcurrent n1 n2 ⊥ owned n1 ns p. *)
  (* Proof. *)
  (*   constructor; intros ? ? []; subst; try reflexivity. *)
  (*   - destruct H0. right. admit. *)
  (*   - simpl in *. *)
  (* Abort. *)

  (* Lemma lcurrent_sep_when n1 n2 p : *)
  (*   lcurrent n1 n2 ⊥ p -> *)
  (*   lcurrent n1 n2 ⊥ when n1 p. *)
  (* Proof. *)
  (*   intros Hsep. split; intros. *)
  (*   - apply Hsep; auto. destruct H; subst; intuition. *)
  (*   - destruct H; subst; [reflexivity |]. *)
  (*     destruct Hsep as [_ ?]. simpl. *)
  (* Admitted. *)

  (* Lemma lcurrent_duplicate n1 n2 : *)
  (*   lcurrent n1 n2 ≡≡ lcurrent n1 n2 ** lcurrent n1 n2. *)
  (* Proof. *)
  (*   split. *)
  (*   - constructor; intros; simpl in *; [apply H | apply H | subst; constructor; left; auto]. *)
  (*   - constructor; intros; simpl in *; subst; auto. *)
  (*     + split; [| split]; auto. apply lcurrent_sep. *)
  (*     + induction H. intuition. *)
  (*       destruct IHclos_trans1 as [? | (? & ? & ?)]; subst; auto. *)
  (*       destruct IHclos_trans2 as [? | (? & ? & ?)]; subst; auto. *)
  (*       right; split; [| split]; auto; etransitivity; eauto. *)
  (* Qed. *)

  (* Weaken the lifetime n1 to n2 *)
  Lemma lcurrent_when n1 n2 p H Hp :
    lcurrent n1 n2 H ** when n2 p Hp <= lcurrent n1 n2 H ** when n1 p Hp.
  Proof.
    constructor; intros.
    - simpl in *. destruct H0 as (_ & ? & ?). split; [| split]; auto.
      + intro. apply H0. destruct H2.
        * (* TODO write lemma for this *)
          pose proof H. eapply subsumes_status in H3.
          rewrite H2 in H3.
          destruct (statusOf n1 (lget x)); [destruct s |]; auto.
          inversion H3.
        * pose proof H. eapply subsumes_status in H3.
          rewrite H2 in H3.
          destruct (statusOf n1 (lget x)); [destruct s |]; auto.
          inversion H3.
      + constructor; intros; cbn in *; subst; auto. split; reflexivity.
    - simpl in *. split; auto. destruct H0 as [_ ?].
      destruct H0 as (? & ?). split; auto.
      intros [].
      + apply H1; auto.
        pose proof H. eapply subsumes_status in H3.
        rewrite H2 in H3.
        destruct (statusOf n1 (lget y)); [destruct s |]; auto.
        inversion H3.
      + apply H1; auto.
        pose proof H. eapply subsumes_status in H3.
        rewrite H2 in H3.
        destruct (statusOf n1 (lget y)); [destruct s |]; auto.
        inversion H3.
    - simpl in *. induction H0. 2: econstructor 2; eauto.
      destruct H0; subst; try solve [constructor; auto].
      destruct H0; subst; try solve [constructor; auto].
      destruct H0 as (? & ? & ? & ?).
      constructor 1. right. right.
      split; [| split; [| split]]; auto.
      + eapply subsumes_status in H.
        rewrite H1 in H.
        destruct (statusOf n1 (lget x)); [destruct s |]; auto.
        inversion H.
        inversion H.
      + eapply subsumes_status in H.
        rewrite H2 in H.
        destruct (statusOf n1 (lget y)); [destruct s |]; auto.
        inversion H.
        inversion H.
  Qed.

  Program Definition lfinished l : @perm C :=
    {|
      pre x := Some finished = statusOf l (lget x);
      rely x y := statusOf l (lget x) = Some finished ->
                  statusOf l (lget y) = Some finished;
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
  Qed.
  Next Obligation.
    symmetry. apply H. symmetry. auto.
  Qed.

  Definition lowned_Perms l ls Hsub P Q : Perms :=
    meet_Perms (fun R => exists r q Hq, R = singleton_Perms (r ** owned l ls Hsub q Hq) /\
                               q ∈ Q /\
                               (forall p, p ∈ P -> forall s, pre r s -> pre p s -> pre q s)).

  (* Require Import Heapster.Typing. *)

  (* Definition startLifetime : itree (sceE C) nat := *)
  (*   ret 0. *)
End LifetimePerms.
