(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

From Heapster2 Require Import
     Utils
     Permissions
     PermissionsSpred2
     Lifetime
     SepStep
     Typing
     PermType.

From ITree Require Import
     ITree
     Eq.Eqit.

From Paco Require Import
     paco.

Import ListNotations.
(* end hide *)

Section LifetimePerms.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  Inductive LifetimeClauses :=
  | Empty : LifetimeClauses
  | Clause : nat -> nat -> LifetimeClauses -> LifetimeClauses
  .
  Fixpoint interp_LifetimeClauses (c : LifetimeClauses) (x : Si * Ss) : Prop :=
    let (si, ss) := x in
    match c with
    | Empty => True
    | Clause n1 n2 c' => subsumes n1 n2 (lget si) (lget si) /\
                          interp_LifetimeClauses c' x
    end.

  (* Some lifetime permissions only work with other permissions that do not affect lifetimes *)
  Definition nonLifetime c (p : @perm {x : Si * Ss | interp_LifetimeClauses c x}) : Prop :=
    (* rely does not tolerate lifetimes going wrong *)
    (* (forall x y, rely p x y -> Lifetimes_lte (lget (fst (proj1_sig x))) (lget (fst (proj1_sig y)))) /\ *)
      (* guar doesn't allow for lifetime changes *)
    (forall x y, guar p x y -> lget (fst (proj1_sig x)) = lget (fst (proj1_sig y))).

  Lemma nonLifetime_restrict c c' Hspred p :
    nonLifetime c' p ->
    nonLifetime c (restrict _ (interp_LifetimeClauses c) (interp_LifetimeClauses c') Hspred p).
  Proof.
    repeat intro.
    cbn in *. red in H, H0. destruct x, y, x, x0.
    specialize (H _ _ H0). cbn in *. auto.
  Qed.

  Lemma nonLifetime_sep_conj c (p q : @perm {x : Si * Ss | interp_LifetimeClauses c x}) (Hp : nonLifetime c p) (Hq : nonLifetime c q) :
    nonLifetime c (p ** q).
  Proof.
    repeat intro.
    induction H.
    - destruct H; auto.
    - etransitivity; eauto.
  Qed.

  Lemma nonLifetime_lte c (p q : @perm {x : Si * Ss | interp_LifetimeClauses c x}) :
    p <= q -> nonLifetime c q -> nonLifetime c p.
  Proof.
    repeat intro.
    apply H0. apply H. auto.
  Qed.

  Lemma nonLifetime_bottom c : nonLifetime c bottom_perm.
  Proof.
    repeat intro; cbn in *; subst; auto.
  Qed.

  Section asdf.
    Context (c : LifetimeClauses).

    (* Note: does not have permission to start or end the lifetime [l] *)
    Program Definition when
            (l : nat)
            (p : @perm {x : Si * Ss | interp_LifetimeClauses c x})
            (Hp : nonLifetime c p) : @perm {x : Si * Ss | interp_LifetimeClauses c x} :=
      {|
        pre x :=
        let '(si, _) := x in
        (lifetime (lget si) l = None \/ lifetime (lget si) l = Some current) ->
        pre p x;

        rely x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        (* TODO check this, can we remove? *)
        Lifetimes_lte (lget si) (lget si') /\
          (* if the lifetime isn't ending or already ended, the rely of p must hold *)
          ((lifetime (lget si') l = None \/ lifetime (lget si') l = Some current) ->
           rely p x y);

        guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          Lifetimes_lte (lget si) (lget si') /\
            lifetime (lget si) l = Some current /\
            lifetime (lget si') l = Some current /\
            guar p x y;
      |}.
    Next Obligation.
      constructor; repeat intro.
      - destruct x, x. split; intuition.
      - destruct x, y, z, x, x0, x1. cbn.
        destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
        intros [].
        + etransitivity; eauto. apply H1. left.
          specialize (H0 l). rewrite H3 in H0.
          destruct (lifetime (lget s1) l); auto. inversion H0.
        + etransitivity; eauto. apply H1.
          specialize (H0 l). specialize (H l). rewrite H3 in H0.
          destruct (lifetime (lget s1) l); auto. destruct s5; auto. inversion H0.
    Qed.
    Next Obligation.
      constructor; repeat intro.
      - destruct x, x. cbn. auto.
      - destruct x, y, z, x, x0, x1. cbn in *.
        destruct H, H0; subst.
        + left. etransitivity; eauto.
        + decompose [and] H0. clear H0.
          inversion H. subst.
          right. split; [| split; [| split]]; auto.
          etransitivity; eauto. rewrite H. reflexivity.
        + decompose [and] H. clear H.
          inversion H0. subst.
          right. split; [| split; [| split]]; auto.
          etransitivity; eauto. rewrite H0. reflexivity.
        + decompose [and] H. clear H.
          decompose [and] H0. clear H0.
          right. split; [| split; [| split]]; auto.
          etransitivity; eauto.
          etransitivity; eauto.
    Qed.
    Next Obligation.
      cbn in *. intros. destruct H.
      destruct H3.
      - eapply pre_respects; eauto.
        apply H0. left. specialize (H l). rewrite H3 in H.
        destruct (lifetime (lget s1) l); auto. inversion H.
      - eapply pre_respects; auto.
        apply H0. specialize (H l). rewrite H3 in H.
        destruct (lifetime (lget s1) l); auto.
        destruct s3; auto. inversion H.
    Qed.

    (* not true since the when cannot tolerate lifetime changes in its rely *)
    (*
    Lemma when_original n p Hp :
      when n p Hp <= p.
    Proof.
      intros. constructor; cbn; intros.
      - destruct x, x. cbn in *. auto.
      - destruct x, y, x, x0. cbn in *. split; auto. destruct Hp.
        specialize (H0 _ _ H). apply H0.
      - destruct x, y, x, x0. cbn in *. destruct H; auto.
        + rewrite H. reflexivity.
        + decompose [and] H; auto 7.
    Qed.
     *)

    Lemma when_monotone n p1 p2 Hp1 Hp2 : p1 <= p2 -> when n p1 Hp1 <= when n p2 Hp2.
    Proof.
      intros. destruct H. constructor; cbn; intros.
      - destruct x, x. cbn in *. auto.
      - destruct x, y, x, x0. cbn in *. destruct H; auto.
      - destruct x, y, x, x0. cbn in *. destruct H; auto.
        decompose [and] H; auto 7.
    Qed.

    Definition subsumes_all l (ls : nat -> Prop) (x : Si * Ss) : Prop :=
      let '(si, _) := x in
      forall l', ls l' -> subsumes l l' (lget si) (lget si).

    (* Permission to end the lifetime [l], which gives us back [p].
       Every lifetime in [ls] is subsumed by [l]. *)
    Program Definition owned
            (l : nat)
            (ls : nat -> Prop)
            (Hspred : forall x, interp_LifetimeClauses c x -> subsumes_all l ls x)
            (p : @perm {x : Si * Ss | interp_LifetimeClauses c x} )
            (Hp : nonLifetime c p) :
      @perm { x : Si * Ss | interp_LifetimeClauses c x } :=
      {|
        (** [l] must be current *)
        pre x :=
        let '(si, _) := x in
        lifetime (lget si) l = Some current;

        (** nobody else can change [l]. If [l] is finished, the rely of [p] holds *)
        rely x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        Lifetimes_lte (lget si) (lget si') /\
          lifetime (lget si) l = lifetime (lget si') l /\
          (lifetime (lget si) l = Some finished -> rely p x y);

        (** If [l] is finished afterwards, the guar of [p] holds *)
        guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          Lifetimes_lte (lget si) (lget si') /\
            lifetime (lget si') l = Some finished /\
            guar p x y;
      |}.
    Next Obligation.
      constructor; repeat intro.
      - destruct x, x. split; intuition.
      - destruct x, y, z, x, x0, x1. cbn in *.
        destruct H as (? & ? & ?), H0 as (? & ? & ?).
        split; [| split]; intros; etransitivity; eauto.
        apply H4; auto. rewrite <- H1. auto.
    Qed.
    Next Obligation.
      constructor; repeat intro.
      - destruct x, x. cbn. auto.
      - destruct x, y, z, x, x0, x1. cbn in *.
        destruct H, H0; subst.
        + left. etransitivity; eauto.
        + decompose [and] H0. clear H0.
          inversion H. subst.
          right. split; [| split]; auto.
          etransitivity; eauto. rewrite H. reflexivity.
        + decompose [and] H. clear H.
          inversion H0. subst.
          right. split; [| split]; auto.
          etransitivity; eauto. rewrite H0. reflexivity.
        + decompose [and] H. clear H.
          decompose [and] H0. clear H0.
          right. split; [| split]; auto.
          etransitivity; eauto.
          etransitivity; eauto.
    Qed.
    Next Obligation.
      cbn in *. destruct H as (? & ? & ?). rewrite <- H3. auto.
    Qed.

    Lemma owned_monotone l ls p1 p2 Hp1 Hp2 Hspred :
      p1 <= p2 -> owned l ls Hspred p1 Hp1 <= owned l ls Hspred p2 Hp2.
    Proof.
      intros. destruct H. constructor; cbn; intros.
      - destruct x, x. cbn in *. intuition.
      - destruct x, y, x, x0. cbn in *. decompose [and] H; auto.
      - destruct x, y, x, x0. cbn in *. destruct H; auto.
        right. decompose [and] H; auto.
    Qed.

    Lemma lifetimes_sep l ls Hls
          p q Hp Hq  :
      when l p Hp ⊥ owned l ls Hls q Hq.
    Proof.
      split; intros.
      - destruct x, y, x, x0. cbn in *. destruct H.
        + inversion H. subst. split; try reflexivity.
          intros. rewrite H. reflexivity.
        + destruct H as (? & ? & ?). split; auto. intros.
          destruct H2; rewrite H2 in H0; inversion H0.
      - destruct x, y, x, x0. cbn in *. destruct H.
        + inversion H. subst. split; [| split]; try reflexivity.
          intros. rewrite H. reflexivity.
        + destruct H as (? & ? & ? & ?). split; [| split]; auto.
          rewrite H0, H1; auto.
          intros. rewrite H0 in H3. inversion H3.
    Qed.

    Lemma lifetimes_sep' l ls Hls
          (p : perm) q Hp Hq  :
      p ⊥ owned l ls Hls q Hq ->
      when l p Hp ⊥ owned l ls Hls (p ** q) (nonLifetime_sep_conj c _ _ Hp Hq).
    Proof.
      intros.
      eapply lifetimes_sep.
    Qed.
    (*   split; intros. *)
    (*   - destruct x, y, x, x0. cbn in *. destruct H0. *)
    (*     + inversion H0. subst. split; try reflexivity. *)
    (*       intros. rewrite H0. reflexivity. *)
    (*     + destruct H0 as (? & ? & ?). split; auto. *)
    (*       intros. destruct H3; rewrite H3 in H1; discriminate H1. *)
    (*   - destruct x, y, x, x0. cbn in *. destruct H0. *)
    (*     + inversion H0. subst. split; [| split]; try reflexivity. *)
    (*       intros. split; rewrite H0; reflexivity. *)
    (*     + destruct H0 as (? & ? & ? & ?). split; [| split]; auto. *)
    (*       rewrite H1, H2; auto. *)
    (*       intros. rewrite H4 in H1. discriminate H1. *)
    (* Qed. *)

    Lemma convert p q l ls Hls Hp Hq :
      when l p Hp ** owned l ls Hls (p ** q) (nonLifetime_sep_conj c _ _ Hp Hq) <=
        p ** owned l ls Hls q Hq.
    Proof.
      split; intros.
      - destruct x, x. cbn in *. decompose [and] H; auto. clear H.
        split; auto.
        split; [| eapply lifetimes_sep; eauto].
        destruct H2; intuition.
        (* right. split; [| split; [| split]]; auto. *)
        (* destruct H3. split. *)
        (* + intros [[]] [[]] ?. apply sep_l. cbn. right. split; auto. *)

        (* eapply lifetimes_sep; eauto. *)
      - destruct x, y, x, x0. cbn in *. destruct H as (? & ? & ? & ?).
        split; [| split; [| split]]; auto.
      - destruct x, y, x, x0. cbn in H. induction H. 2: econstructor 2; eauto.
        clear i s s0. clear i0 s1 s2.
        destruct x, y, x, x0. cbn in *.
        destruct H.
        + destruct H.
          * inversion H. subst. constructor 1. left. rewrite H. reflexivity.
          * destruct H as (? & ? & ? & ?). constructor 1. cbn. left. auto.
        + destruct H.
          * constructor 1. left. rewrite H. reflexivity.
          * destruct H as (? & ? & ?).
            rename H into Hlte, H0 into Hfin, H1 into Hguar.
            {
              apply Operators_Properties.clos_trans_t1n_iff.
              apply Operators_Properties.clos_trans_t1n_iff in Hguar.
              remember (exist _ _ i).
              remember (exist _ _ i0).
              revert s s0 s1 s2 i i0 Heqs3 Heqs4 Hlte Hfin.
              induction Hguar; intros; subst.
              - constructor 1. destruct H; auto.
                right. cbn in *.
                right. split; [| split]; auto.
              - econstructor 2.
                2: { destruct y, x. eapply IHHguar; auto.
                     clear IHHguar H.
                     remember (exist _ _ i1).
                     remember (exist _ _ i0).
                     revert s1 s2 s3 s4 i0 i1 Heqs5 Heqs6 Hlte Hfin.
                     induction Hguar; intros; subst.
                     - destruct H.
                       + specialize (Hp _ _ H). cbn in Hp. rewrite Hp. reflexivity.
                       + specialize (Hq _ _ H). cbn in Hq. rewrite Hq. reflexivity.
                     - destruct H.
                       + destruct y, x.
                         specialize (Hp _ _ H). cbn in Hp. rewrite Hp.
                         eapply IHHguar; auto.
                       + destruct y, x.
                         specialize (Hq _ _ H). cbn in Hq. rewrite Hq.
                         eapply IHHguar; auto.
                }
                clear IHHguar. destruct H; auto.
                right. destruct y, x. cbn in *. right. split; [| split]; auto.
                + specialize (Hq _ _ H). cbn in Hq. rewrite Hq. reflexivity.
                + clear Hls Hlte H.
                  remember (exist _ _ i1).
                  remember (exist _ _ i0).
                  revert s1 s2 s3 s4 i0 i1 Heqs5 Heqs6 Hfin.
                  induction Hguar; intros; subst.
                  * destruct H.
                    -- specialize (Hp _ _ H). cbn in *. rewrite Hp. auto.
                    -- specialize (Hq _ _ H). cbn in *. rewrite Hq. auto.
                  * destruct y, x. subst. destruct H.
                    -- specialize (Hp _ _ H). cbn in *. rewrite Hp.
                       eapply IHHguar; eauto.
                    -- specialize (Hq _ _ H). cbn in *. rewrite Hq.
                       eapply IHHguar; eauto.
            }
    Qed.

    Program Definition lcurrent l1 l2
            (H : forall (x : {x : Si * Ss | interp_LifetimeClauses c x}),
                let '(si, _) := x in subsumes l1 l2 (lget si) (lget si)) :
      @perm {x : Si * Ss | interp_LifetimeClauses c x} :=
      {|
        pre x := True;
        rely x y := True;
        guar x y := x = y;
      |}.
    Next Obligation.
      constructor; repeat intro; auto.
    Qed.

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

    Lemma lcurrent_when n1 n2 p H Hp :
      lcurrent n1 n2 H ** when n2 p Hp <= lcurrent n1 n2 H ** when n1 p Hp.
    Proof.
      constructor; intros.
      - destruct x, x. cbn in *. destruct H0 as (_ & ? & ?). split; [| split]; auto.
        + intro. apply H0. destruct H2.
          * clear H1. specialize (H (exist _ _ i)).
            eapply subsumes_2_none_inv; eauto.
          * clear H1. specialize (H (exist _ _ i)).
            right. eapply subsumes_2_current_inv; eauto.
        + constructor; intros; cbn in *; subst; auto.
          destruct y, x. cbn. split; reflexivity.
      - destruct x, y, x, x0. cbn in *.
        split; auto. destruct H0 as [_ ?].
        destruct H0 as (? & ?). split; auto.
        intros [].
        + apply H1; auto.
          specialize (H (exist _ _ i0)).
          eapply subsumes_2_none_inv; eauto.
        + apply H1; auto. right.
          specialize (H (exist _ _ i0)).
          eapply subsumes_2_current_inv; eauto.
    - cbn in *. induction H0. 2: econstructor 2; eauto.
      destruct H0; subst; try solve [constructor; auto].
      destruct x, y, x, x0. cbn in *.
      destruct H0; subst; try solve [constructor; auto].
      destruct H0 as (? & ? & ? & ?).
      constructor 1. right. right.
      split; [| split; [| split]]; auto.
      + specialize (H (exist _ _ i)).
        eapply subsumes_2_current_inv; eauto.
      + specialize (H (exist _ _ i0)).
        eapply subsumes_2_current_inv; eauto.
    Qed.
  End asdf.


  Definition when_Perms l P : Perms2 :=
    meet_Perms2 (fun R => exists c p Hp, p ∈2 P /\ R = singleton_Perms2 _ (when c l p Hp)).

  Lemma when_perm_Perms c l p Hp P :
    p ∈2 P ->
    when c l p Hp ∈2 when_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists c. exists p. eexists. split. 2: reflexivity. apply H.
    - exists (fun _ H => H). red. rewrite restrict_same. reflexivity.
  Qed.

  (* when l (read_Perms ptr) * lowned l (when l (read_Perms ptr) -o write_Perms ptr) ⊢
     endLifetime l :
     write_Perms p *)

  (* p ∈ read_Perms ptr * lowned l (read_Perms ptr -o write_Perms ptr) *)
  (* -> p >= r * l *)
  (* pre p s is true, so pre of both are true *)

  (* r ∈ read_Perms ptr *)
  (* -> r ≈ read_perm ptr v, for some v *)

  (* l ∈ lowned l .... *)
  (* ∃ w, w ∈ write_Perms ptr /\ l >= owned l w /\
     (forall s, lifetime s = current -> pre r s -> pre l s -> pre w s) *)
  (* -> w ≈ write_perm ptr v, for some v *)

  (* currently "lending" P, and will "return" Q when l ends (and P is provided to lowned). *)
  Definition lowned_Perms l ls Hsub P Q : Perms2 :=
    meet_Perms2 (fun R => (* forall c (p : @perm {x : Si * Ss | interp_LifetimeClauses c x}), p ∈2 P -> *)
                            exists c r q Hq,
                              R = singleton_Perms2 _ (r ** owned c l ls (Hsub c) q Hq) /\
                                q ∈2 Q /\ (* q also has the spred c *)
                                (* r ∈2 (impl_Perms2 P Q) /\ *)
                                (forall p, p ∈2 P -> exists q, q ∈2 Q /\
                                                      (forall s, pre p s -> pre r s -> pre q s))).
  (* remove r? *)

  (* x = owned l (write_perm ptr v) ** pred_perm (ptr |-> v) *)
  (* x ∈ lowned l (read_Perms ptr -o write_Perms ptr) *)
  (* forall r ∈ read_Perms ptr (r ≈ read_perm ptr v', for some v')
     exists w ∈ write_Perms ptr. (pick w = write_perm ptr v)
   x >= owned l w *)


  (* p  \in   lowned l (P1 * P2) Q    /\   p'  \in P1
     then    pred_perm (pre p') ** p   \in  lowned l P2 Q
   *)
  Program Definition lowned_Perms' l ls Hsub (P Q : @Perms2 (Si * Ss)) : Perms2 :=
    {|
      in_Perms2 := fun spred x =>
                     exists c Hspred r1 r2 Hnlr2,
                       r2 ∈2 Q /\
                         hlte_perm2 (Si * Ss) spred (interp_LifetimeClauses c) Hspred
                           (r1 ** owned c l ls (Hsub c) r2 Hnlr2) x /\
                         forall (p : @perm {x : Si * Ss | interp_LifetimeClauses c x}),
                           p ∈2 P ->
                           exists (q : @perm {x : Si * Ss | interp_LifetimeClauses c x}),
                             q ∈2 Q /\
                               sep_step _ (interp_LifetimeClauses c) (interp_LifetimeClauses c) (fun _ H => H) r2 q /\
                               (forall c1 c2 (Hc : interp_LifetimeClauses c (c1, c2)),
                                   pre p ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                   pre r1 ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                   pre q ((lput c1 (replace_list_index (lget c1) l finished)), c2));
    |}.
  Next Obligation.
    cbn.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    rename H into c, H1 into Hspred'.
    exists c. eexists. Unshelve.
    2: { intros. apply Hspred'. apply Hspred. apply H. }
    exists H2, H3, H4. split; auto. split; auto.
    - eapply hlte_perm2_transitive; eauto.
    - intros. (* eapply H7. apply H7. *)
  Admitted.

  Program Definition lowned_Perms'' l ls Hsub (P Q : @Perms2 (Si * Ss)) : Perms2 :=
    {|
      in_Perms2 := fun spred x =>
                     exists c Hspred,
                     forall (p : @perm {x : Si * Ss | interp_LifetimeClauses c x}),
                       p ∈2 P ->
                       exists (q : @perm {x : Si * Ss | interp_LifetimeClauses c x}) Hq,
                         q ∈2 Q /\
                           hlte_perm2
                             (Si * Ss) spred (interp_LifetimeClauses c) Hspred
                             (owned c l ls (Hsub c) q Hq)
                             x /\
                           (forall s, pre p _ -> pre x s -> pre q _);
    |}.
  Next Obligation.
    esplit. apply Hspred. apply H.
  Defined.
  Next Obligation.
    esplit. apply Hspred. apply H.
  Defined.
  Next Obligation.
    rename H into c. rename H1 into Hspred'.
    exists c. eexists. Unshelve. 2: { auto. } intros p Hp.
    specialize (H2 p). destruct H2 as (q & Hq' & Hq & Hhlte & Hpre); auto.
    exists q, Hq'. split; auto. split; auto.
    - eapply hlte_perm2_transitive; eauto.
    - intros [[]]. specialize (Hpre (exist _ _ (Hspred _ s1))). cbn in *.
      intros. apply Hpre; auto.
      red in H0. apply H0 in H1. cbn in H1. apply H1.
  Qed.

  Lemma lowned_perm_Perms c l ls Hsub p Hp P :
    p ∈2 P ->
    owned c l ls (Hsub c) p Hp ∈2 lowned_Perms l ls Hsub P P.
  Proof.
  (*   intros. cbn. do 4 eexists. split; eauto. split. *)
  (*   - red. rewrite restrict_same. reflexivity. *)
  (*   - intros. *)
  (*   Unshelve. intros. auto. *)
  (* Qed. *)
    (* cbn. intros. exists p0. eexists. eexists. *)
    (* split. auto. split. *)
    (* 2: { intros. auto. } *)


    intros. cbn. eexists. split.
    - do 4 eexists. split; [| split]. reflexivity.
      apply H.
      clear p H Hp. intros p Hp. exists p. split; auto.
    - exists (fun _ H => H). red. rewrite restrict_same.
      rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity.
  Qed.

  Definition lte_Perms' (P Q : Perms2) : Prop :=
    forall (c : LifetimeClauses) (p : @perm {x | interp_LifetimeClauses c x}), p ∈2 Q -> p ∈2 P.
  Definition entails P Q := lte_Perms' Q P.

  (* Lemma foo l P : *)
  (*   entails P (when_Perms l P). *)
  (* Proof. *)
  (*   repeat intro. cbn. eexists. split. *)
  (*   - do 2 eexists. split; [| reflexivity]. eapply H. Set Printing All. admit. *)
  (*   - Unset Printing All. cbn. eexists. *)

  Lemma restrict_owned c c' Hspred l ls Hsub p Hp:
    restrict (Si * Ss) (interp_LifetimeClauses c) (interp_LifetimeClauses c') Hspred
             (owned c' l ls Hsub p Hp) <=
      owned c l ls (fun x Hc => Hsub x (Hspred _ Hc)) (restrict _ _ _ Hspred p) (nonLifetime_restrict _ _ Hspred p Hp).
  Proof.
    constructor.
    - intros [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. intuition.
      left. inversion H0. subst. clear H0.
      rewrite (ProofIrrelevance.proof_irrelevance _ i i0). reflexivity.
  Qed.

  Lemma restrict_owned' c c' Hspred l ls Hsub p Hp:
    owned c l ls (fun x Hc => Hsub x (Hspred _ Hc)) (restrict _ _ _ Hspred p) (nonLifetime_restrict _ _ Hspred p Hp) <=
      restrict (Si * Ss) (interp_LifetimeClauses c) (interp_LifetimeClauses c') Hspred
               (owned c' l ls Hsub p Hp).
  Proof.
    constructor.
    - intros [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. intuition.
      left. inversion H0. subst. clear H0.
      rewrite (ProofIrrelevance.proof_irrelevance _ i i0). reflexivity.
  Qed.

  Lemma obvious l ls Hsub P Q :
    entails (lowned_Perms'' l ls Hsub bottom_Perms2 Q)
            (lowned_Perms'' l ls Hsub P Q).
  Proof.
    intros c p' H. cbn in H.
    destruct H as (c' & Hspred & ?).
    exists c', Hspred. intros.
    specialize (H p I). apply H.
  Qed.

  Lemma typing_end l ls Hsub P Q :
    @typing Si Ss LifetimeClauses interp_LifetimeClauses _ _
      (P *2 (lowned_Perms' l ls Hsub P Q))
      (fun _ _ => Q)
      (endLifetime l)
      (Ret tt).
  Proof.
    intros c p' c1 c2 Hc (p & lowned' & Hp & Hl & Hlte) Hpre.
    cbn in Hl.
    destruct Hl as (c' & Hspred & Hl).
    (* specialize (Hl (restrict _ _ _ Hspred p) Hp). destruct Hl as (Hspred & q & Hq' & Hq & Hhlte & Hpre'). *)
    destruct Hl as (r1 & r2 & Hnlr2 & Hr2 & Hhltge & Hf).
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity. cbn. reflexivity.

    pose proof Hpre as Hpre''.
    apply Hlte in Hpre. destruct Hpre as (_ & ? & _). apply Hhlte in H.
    cbn in H. destruct H as (_ & ? & _). unfold lifetime in H. setoid_rewrite H.

    rewritebisim @bind_trigger.
    (* specialize (Hf (restrict _ _ _ Hspred p)). *)


    econstructor; unfold id. eauto.
    cbn in *. apply Hlte. constructor 1. right.
    apply Hhlte. cbn. right.
    {
      rewrite lGetPut.
      split; [| split].
      - admit.
      - unfold lifetime. apply nth_error_replace_list_index_eq.
      - red in Hq'. (* TODO update defn of nonLifetime *) admit.
    }

    2: {
      assert (asdf: interp_LifetimeClauses c (lput c1 (replace_list_index (lget c1) l finished), c2)) by admit.

      econstructor. 2: apply Hq.
      Unshelve. 2: auto.
      3: apply asdf.
      specialize (Hpre' (exist (fun x : Si * Ss => interp_LifetimeClauses c x)
                               (lput c1 (replace_list_index (lget c1) l finished), c2) asdf)).
      cbn in *.
      erewrite (ProofIrrelevance.proof_irrelevance _ asdf).
      apply Hpre'. admit. admit. (* how is this even true here *)
      admit.
    }

    (* ok plausible, since q should be inside the rely and guar of p' *)
    admit.
  Abort.
*)

  Lemma join_commut' c l ls Hsub p Hp powned asdf asdf' asdf'':
    join_perm' (fun pp => exists q Hq, owned c l ls Hsub q Hq <= powned /\
                                  pp = owned c l ls Hsub (p ** q) (nonLifetime_sep_conj _ _ _ Hp Hq)) asdf <=
      owned c l ls Hsub (p ** (join_perm' (fun q => exists Hq, owned c l ls Hsub q Hq <= powned) asdf')) asdf''
  .
  Proof.
    constructor.
    - intros [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn. auto.
    - intros [[]] [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn.
      destruct H as (? & ? & ?). split; auto. split; auto.
      intros. destruct H2; auto. split; auto.
      apply H4. eauto.
    - intros ? ? ?. cbn in H. induction H. 2: etransitivity; eauto.
      destruct H as (? & ? & ?). destruct H as (q & Hq & Hlte & ?). subst.
      destruct x, y, x, x0. cbn in *.
      destruct H0; auto.
      right. destruct H as (? & ? & ?). split; auto. split; auto.
      (* constructor. right. constructor. eexists. split. exists q, Hq. split; auto. *)
      cbn.
      clear H0.
      remember (exist _ _ i). remember (exist _ _ i0).
      revert s s0 s1 s2 i i0 H Heqs3 Heqs4. clear asdf asdf' asdf''.
      induction H1; intros; subst.
      + constructor 1. destruct H; auto.
        right. constructor 1. eexists. split; eauto.
      + destruct y, x.
        specialize (IHclos_trans2 s3 s4). specialize (IHclos_trans1 s s0 s3 s4).
        assert (Lifetimes_lte (lget s3) (lget s1)).
        {
          clear IHclos_trans1 IHclos_trans2 H H1_ s s0 i Hlte powned.
          remember (exist _ _ i1). remember (exist _ _ i0).
          revert s1 s2 s3 s4 i0 i1 Heqs Heqs0.
          rename H1_0 into H.
          induction H; intros; subst.
          - destruct H.
            + apply Hp in H. cbn in *. rewrite H. reflexivity.
            + apply Hq in H. cbn in *. rewrite H. reflexivity.
          - subst. destruct y, x. specialize (IHclos_trans1 s s0 s3 s4).
            etransitivity. eapply IHclos_trans1; eauto.
            eapply IHclos_trans2; eauto.
        }
        assert (Lifetimes_lte (lget s) (lget s3)).
        {
          clear IHclos_trans1 IHclos_trans2 H H0 H1_0 s1 s2 i0 Hlte powned.
          remember (exist _ _ i1). remember (exist _ _ i).
          revert s s0 s3 s4 i i1 Heqs1 Heqs2.
          rename H1_ into H.
          induction H; intros; subst.
          - destruct H.
            + apply Hp in H. cbn in *. rewrite H. reflexivity.
            + apply Hq in H. cbn in *. rewrite H. reflexivity.
          - subst. destruct y, x. specialize (IHclos_trans1 s s0 s1 s2).
            etransitivity. eapply IHclos_trans1; eauto.
            eapply IHclos_trans2; eauto.
        }
        econstructor 2; eauto.
  Qed.


  (*
    Lemma join_commut c l ls Hsub p Hp powned asdf asdf' asdf'':
    join_perm' (fun pp => exists q Hq, owned c l ls Hsub q Hq <= powned /\
                                  pp = owned c l ls Hsub (p ** q) (nonLifetime_sep_conj _ _ _ Hp Hq)) asdf <=
      owned c l ls Hsub (p ** (join_perm' (fun pp => exists q Hq, owned c l ls Hsub q Hq <= powned /\
                        pp = owned c l ls Hsub q Hq) asdf')) asdf''
  .
  Proof.
    constructor.
    - intros [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn. auto.
    - intros [[]] [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn.
      destruct H as (? & ? & ?). split; auto. split; auto.
      intros.
      destruct H2; auto. split; auto.
      specialize (H4 (owned c l ls Hsub x x0)).
      cbn in H4. apply H4; auto. do 2 eexists. split; eauto.
    - intros ? ? ?. cbn in H. induction H. 2: etransitivity; eauto.
      destruct H as (? & ? & ?). destruct H as (q & Hq & Hlte & ?). subst.
      destruct x, y, x, x0. cbn in *.
      destruct H0; auto.
      right. destruct H as (? & ? & ?). split; auto. split; auto.
      (* constructor. right. constructor. eexists. split. exists q, Hq. split; auto. *)
      cbn.
      remember (exist _ _ i). remember (exist _ _ i0).
      revert s s0 s1 s2 i i0 H H0 Heqs3 Heqs4. clear asdf asdf' asdf''.
      induction H1; intros; subst.
      + constructor 1. destruct H; auto.
        right. constructor 1. eexists. split. exists q, Hq. split; auto. cbn.
        right. auto.
      + destruct y, x.
        specialize (IHclos_trans2 s3 s4). specialize (IHclos_trans1 s s0 s3 s4).
        assert (Lifetimes_lte (lget s3) (lget s1)) by admit.
        assert (Lifetimes_lte (lget s) (lget s3)) by admit.
        econstructor 2.
        2: eapply IHclos_trans2; eauto.
        clear IHclos_trans2 H1_0 s1 s2 i0 H H0 H1.

        eapply IHclos_trans1; eauto. admit. (* TODO: I think we need to do more case analysis here *)
  Admitted.
   *)

  Lemma foo l ls Hsub P Q R :
    entails (P *2 (lowned_Perms' l ls Hsub R Q))
            (when_Perms l P *2 (lowned_Perms' l ls Hsub (P *2 R) (P *2 Q))).
  Proof.
    intros c p' H. cbn in H.
    destruct H as (p & powned & Hp & ? & Hlte); subst.
    (* do 2 eexists. *)
    eexists.
    (* assert (Hpr : forall r, nonLifetime c r) by admit. *)
    eexists (join_perm' (fun p' => exists q Hq, owned c l ls (Hsub c) q Hq <= powned /\
                                       p' = owned c l ls (Hsub c) (p ** q) _) _).
    split; [| split].
    3: {
      etransitivity. 2: apply Hlte. etransitivity.
      apply sep_conj_perm_monotone; [reflexivity |].
      apply join_commut'.
      etransitivity. apply convert. apply sep_conj_perm_monotone; [reflexivity |].
      destruct H as (? & ? & ?).
      specialize (H c). unfold hlte_perm2 in H. setoid_rewrite restrict_same in H.
      (* edestruct H as (? & ? & ? & ? & ? & ?). admit. *)
      constructor.
      - intros [[]]. cbn. admit.
      - intros [[]] [[]]. cbn. intros. intuition. admit. admit.
        destruct H2. apply H2 in H0. cbn in H0. apply H0; auto.
      - intros [[]] [[]]. cbn. intros. destruct H0. rewrite H0. reflexivity.
        intuition.
        assert (lifetime (lget s) l = Some finished).
        {
          remember (exist _ _ i). remember (exist _ _ i0).
          revert s s0 i s1 s2 i0 Heqs3 Heqs4 H1 H0.
          induction H3; intros; subst.
          - destruct H0 as (? & (? & ?) & ?). apply x0 in H3. cbn in *. rewrite H3. auto.
          - destruct y, x.
            eapply (IHclos_trans1 _ _ _ _ _ _ eq_refl eq_refl); eauto.
            admit.
            eapply (IHclos_trans2 _ _ _ _ _ _ eq_refl eq_refl); eauto.
            admit.
        }
        remember (exist _ _ i). remember (exist _ _ i0).
        revert s s0 i s1 s2 i0 Heqs3 Heqs4 H1 H0 H2.
        induction H3; intros; subst.
        + destruct H0. destruct H0. destruct H0. apply H0. right. intuition.
        + destruct y, x.
          etransitivity.
          eapply (IHclos_trans1 _ _ _ _ _ _ eq_refl eq_refl); eauto. admit. admit.
          eapply (IHclos_trans2 _ _ _ _ _ _ eq_refl eq_refl); eauto. admit. admit.
    }
    apply when_perm_Perms; auto.
    intros ? ? ?.
    eexists.

    (* Set Printing All. *)
    (* do 2 eexists. split; [| split]. *)
    2: { cbn. do 3 eexists. split.
         - do 2 eexists. split. reflexivity. split.
           + exists p, (restrict _ _ _ Hspred q). split; auto.
             split. 2: reflexivity.
             eapply Perms2_upwards_closed. apply Hq.
             red. reflexivity.
           + intros. cbn.
             destruct H as (? & ? & ? & ? & ?).
             (* destruct (H0 x0). *)
             admit.
         - eexists. red. rewrite restrict_same. reflexivity.
    }
    - apply when_perm_Perms. apply Hp.
    - rewrite <- sep_conj_perm_assoc. rewrite sep_conj_perm_commut.
      etransitivity. red in Hhlte. eapply convert.


             split; [| split].
             2: {
               destruct s, x1. cbn. eapply H0.
               eapply Perms2_upwards_closed. apply H2.
               red. reflexivity.
               cbn. apply H3. admit.
             }
             admit. admit.
             * destruct H as (? & ? & ? & ? & ?).

    3: {
      etransitivity. 2: apply Hlte.
      etransitivity. eapply convert. apply sep_conj_perm_monotone. reflexivity.
      red in Hhlte. etransitivity. 2: apply Hhlte.
      etransitivity. 2: apply restrict_owned'. reflexivity.
    }
    - apply when_perm_Perms; auto.
    - eexists. split.
      + do 3 eexists. split. reflexivity. split.
        (* * (* Set Printing All. do 2 eexists. split; [| split]. apply Hp. apply Hq. reflexivity. *) *)
        2: { intros. destruct H as (? & ? & ? & ? & ?). eapply H0. apply H2. apply H3. auto. }
        admit.
      + cbn. exists Hspred. red. rewrite restrict_owned. rewrite <- (restrict_same _ _ p).

  Qed.

  (* we need to know R includes a nonlifetime perm *)
  Lemma foo l ls Hsub P Q R :
    entails (R *2 lowned_Perms l ls Hsub P Q)
            (when_Perms l R).
  Proof.
    repeat intro. cbn in *.
    destruct H as (r & pl & Hr & (? & (c' & q & Hq' & ? & Hq & ?) & asdf) & Hlte).
    subst. destruct asdf as (Hspred & Hhlte). eexists. split.
    - do 3 eexists. split; [| reflexivity]. eapply Hr.
    - cbn. exists (fun H x => x). red. rewrite restrict_same.
      etransitivity. eapply when_original.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
      Unshelve.
  Qed.


  Lemma foo l ls Hsub P Q R :
    R *2 lowned_Perms l ls Hsub P Q ⊨2
         when_Perms l R.
  Proof.
    repeat intro. destruct H as (r & Hp' & Hr & (? & (q & Hq' & ? & Hq & ?) & asdf) & Hlte).
    subst. destruct asdf as (Hspred & Hhlte). eexists. split.
      - do 2 eexists. split. 2: reflexivity.
        Set Printing All.
    Qed.

      (* lowned_Perms l ls Hsub (P *2 when_Perms l R) (Q *2 R). *)
    Proof.
      repeat intro. cbn in H.
      destruct H as (r & p' & Hr & (? & ((q & Hqnonlifetime & ? & Hq & Hpre) & Hp')) & Hlte).
      subst. destruct Hp' as (Hspred & Hhlte). cbn. Set Printing All.
      eexists. split.
      - do 2 eexists. Set Printing All. split. reflexivity. split.
        + Set Printing All.
          eapply Perms2_upwards_closed. Unshelve. 6: { intros ? asdf. apply asdf. }
                                                Set Printing All.
                                                apply sep_conj_Perms2_perm.
          2: apply Hr.
          eapply Perms2_upwards_closed; eauto. red. Unshelve.
          red. Unshelve. 4: apply Hspred.
        2: { intros pr (p'' & q'' & Hp'' & Hq'' & Hpr).
             intros. eapply Hpre; eauto. apply Hpr. auto. }

        + do 2 eexists. split; [| split]. 3: reflexivity. admit. admit.
        + intros p''' (p'' & ? & (? & (? & (? & ? & ? & ?) & ?) & ?)). subst.
          cbn in H2. destruct H2 as (? & ?). red in H1. rewrite restrict_same in H1.
          clear x0. intros [] ? ?. admit.
      - exists Hspred. red. red in Hp'.
          split.
          * eapply Hpre; auto.
            apply H. apply Hp'. apply Hp. apply H1.
            apply H3. apply H4.
          * split; auto. apply Hp. auto.
            apply Hp in H1. destruct H1 as (? & ? & ?).
            symmetry. eapply separate_antimonotone. apply H6.
            apply Hp'.
            apply Hp' in H5. destruct H5 as (? & ? & ?).
      - eapply Perms2_upwards_closed. 2: { red. rewrite restrict_same. eapply Hlte. }
                                    cbn.




      destruct H as (r & p' & Hr & (P' & (r' & q & Hq' & ? & Hq & Hpre) & Hp') & Hp).
      subst. destruct Hp' as (Hspred & Hp'). cbn in *.
      eexists. split.
      - do 3 eexists. split. reflexivity. split.
        + do 2 eexists. split; [| split]. 3: reflexivity. admit. admit.
        + intros p''' (p'' & ? & (? & (? & (? & ? & ? & ?) & ?) & ?)). subst.
          cbn in H2. destruct H2 as (? & ?). red in H1. rewrite restrict_same in H1.
          clear x0. intros [] ? ?. admit.
      - exists Hspred. red. red in Hp'.
          split.
          * eapply Hpre; auto.
            apply H. apply Hp'. apply Hp. apply H1.
            apply H3. apply H4.
          * split; auto. apply Hp. auto.
            apply Hp in H1. destruct H1 as (? & ? & ?).
            symmetry. eapply separate_antimonotone. apply H6.
            apply Hp'.
            apply Hp' in H5. destruct H5 as (? & ? & ?).
            cbn in H8.
    Qed.
*)

  End asdf.


  Lemma foo l ls Hsub P Q R :
    entails (R *2 lowned_Perms l ls Hsub P Q)
            (when_Perms l R).
  Proof.
    repeat intro. destruct H as (r & Hp' & Hr & (? & (q & Hq' & ? & Hq & ?) & asdf) & Hlte).
    subst. destruct asdf as (Hspred & Hhlte). eexists. split.
    - do 2 eexists. split; [| reflexivity]. eapply Hr.
      Set Printing All.
  Qed.
End LifetimePerms.
