(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

From Heapster2 Require Import
     Utils
     Permissions
     PermissionsSpred2
     Lifetime
     SepStep
     Typing
     PermType.

From Paco Require Import
     paco.

Import MonadNotation.
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
        lifetime (lget si) l = None \/ lifetime (lget si) l = Some current ->
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
      intros. destruct H. constructor; simpl; intros.
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
        (* [l] must be current *)
        pre := fun '(x, _) => lifetime (lget x) l = Some current;
        (* nobody else can change [l]. If [l] is finished, the rely of [p] holds *)
        rely := fun x y =>
                  let '(si, _) := x in
                  let '(si', _) := y in
                  Lifetimes_lte (lget si) (lget si') /\
                    lifetime (lget si) l = lifetime (lget si') l /\
                    (lifetime (lget si) l = Some finished -> rely p x y);
        (* If [l] is finished afterwards, the guar of [p] holds *)
        guar := fun x y =>
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
      - destruct x, x. cbn in *. auto.
      - destruct x, y, x, x0. cbn in *. decompose [and] H; auto.
      - destruct x, y, x, x0. cbn in *. destruct H; auto.
        right. decompose [and] H; auto.
    Qed.

    Lemma lifetimes_sep l ls Hls
          (p : perm) q Hp Hq  :
      p ⊥ owned l ls Hls q Hq ->
      when l p Hp ⊥ owned l ls Hls (p ** q) (nonLifetime_sep_conj c _ _ Hp Hq).
    Proof.
      split; intros.
      - destruct x, y, x, x0. cbn in *. destruct H0.
        + inversion H0. subst. split; try reflexivity.
          intros. rewrite H0. reflexivity.
        + destruct H0 as (? & ? & ?). split; auto.
          intros. destruct H3; rewrite H3 in H1; discriminate H1.
      - destruct x, y, x, x0. cbn in *. destruct H0.
        + inversion H0. subst. split; [| split]; try reflexivity.
          intros. split; rewrite H0; reflexivity.
        + destruct H0 as (? & ? & ? & ?). split; [| split]; auto.
          rewrite H1, H2; auto.
          intros. rewrite H4 in H1. discriminate H1.
    Qed.

    Lemma convert p q l ls Hls Hp Hq :
      when l p Hp ** owned l ls Hls (p ** q) (nonLifetime_sep_conj c _ _ Hp Hq) <=
        p ** owned l ls Hls q Hq.
    Proof.
      split; intros.
      - destruct x, x. cbn in *. decompose [and] H; auto. clear H.
        split; [| split]; auto.
        eapply lifetimes_sep; eauto.
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

  (* currently "lending" P, and will "return" Q when l ends (and P is provided to lowned). *)
  Definition lowned_Perms l ls Hsub P Q : Perms2 :=
    meet_Perms2 (fun R => exists c (* r *) q Hq,
                     R = singleton_Perms2 _ ((* r **  *)owned c l ls (Hsub c) q Hq) /\
                       q ∈2 Q /\ (* q also has the spred c *)
                       (forall p, p ∈2 P -> forall s, (* pre r s -> *) pre p s -> pre q s)).
  (* remove r? *)

  Lemma lowned_perm_Perms c l ls Hsub p Hp P :
    p ∈2 P ->
    owned c l ls (Hsub c) p Hp ∈2 lowned_Perms l ls Hsub P P.
  Proof.
    intros. cbn. eexists. split.
    - do 3 eexists. split; [| split]. reflexivity.
      apply H.
      intros. admit.
    - exists (fun _ H => H). red. rewrite restrict_same. reflexivity.
  Abort.


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

  Lemma foo l ls Hsub P Q R :
    entails (P *2 (lowned_Perms l ls Hsub R Q))
            (when_Perms l P *2 (lowned_Perms l ls Hsub (P *2 R) (P *2 Q))).
  Proof.
    intros c p' H. cbn in H.
    destruct H as (p & powned & Hp & (? & (c' & q & Hq' & ? & Hq & ?) & asdf) & Hlte); subst.
    destruct asdf as (Hspred & Hhlte).
    (* Set Printing All. *)
    do 2 eexists. split; [| split].
    2: { cbn. eexists. split.
         - do 3 eexists. split. reflexivity. split.
           + exists p, (restrict _ _ _ Hspred q). split; auto.
             split. 2: reflexivity.
             eapply Perms2_upwards_closed. apply Hq.
             red. reflexivity.
           + intros. cbn.
             destruct H as (? & ? & ? & ? & ?).
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
