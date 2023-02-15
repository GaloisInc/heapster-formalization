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
  Definition nonLifetime {spred} (p : @perm {x : Si * Ss | spred x}) : Prop :=
    forall x y, guar p x y -> lget (fst (proj1_sig x)) = lget (fst (proj1_sig y)).

  Lemma nonLifetime_sep_conj {spred} (p q : @perm {x : Si * Ss | spred x}) (Hp : nonLifetime p) (Hq : nonLifetime q) :
    nonLifetime (p ** q).
  Proof.
    repeat intro. induction H.
    - destruct H; auto.
    - etransitivity; eauto.
  Qed.

  Lemma nonLifetime_bottom {spred} : @nonLifetime spred bottom_perm.
  Proof.
    repeat intro; cbn in *; subst; auto.
  Qed.

  Section asdf.
    Context (c : LifetimeClauses).

    (* Note: does not have permission to start or end the lifetime [l] *)
    Program Definition when
            (l : nat)
            (p : @perm {x : Si * Ss | interp_LifetimeClauses c x})
            (Hp : nonLifetime p) : @perm {x : Si * Ss | interp_LifetimeClauses c x} :=
      {|
        pre x :=
        let '(si, _) := x in
        lifetime (lget si) l = None \/ lifetime (lget si) l = Some current ->
        pre p x;

        rely x y :=
        let '(si, _) := x in
        let '(si', _) := y in
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
            (Hp : nonLifetime p) :
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
      when l p Hp ⊥ owned l ls Hls (p ** q) (nonLifetime_sep_conj _ _ Hp Hq).
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
      when l p Hp ** owned l ls Hls (p ** q) (nonLifetime_sep_conj _ _ Hp Hq) <=
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
                right. specialize (Hq _ _ H). cbn in Hq. rewrite Hq.
                split; [| split]; auto. reflexivity.
              - econstructor 2.
                2: { destruct y, x. eapply IHHguar; auto.
                     clear IHHguar. clear H.
                     remember (exist _ _ i1).
                     remember (exist _ _ i0).
                     revert s1 s2 s3 s4 i0 i1 Heqs5 Heqs6 Hlte Hfin.
                     induction Hguar; intros; subst.
                     - destruct H.
                       + specialize (Hp _ _ H). cbn in Hp. rewrite Hp. reflexivity.
                       + specialize (Hq _ _ H). cbn in Hq. rewrite Hq. reflexivity.
                     - destruct H.
                       + destruct y, x. specialize (Hp _ _ H). cbn in Hp. rewrite Hp.
                         eapply IHHguar; auto.
                       + destruct y, x. specialize (Hq _ _ H). cbn in Hq. rewrite Hq.
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
                    -- specialize (Hp _ _ H). cbn in *. rewrite Hp. eapply IHHguar; eauto.
                    -- specialize (Hq _ _ H). cbn in *. rewrite Hq. eapply IHHguar; eauto.
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



    Definition when_Perms l P : Perms2 :=
      meet_Perms2 (fun R => exists p Hp, p ∈2 P /\ R = singleton_Perms2 _ (when l p Hp)).

    (* currently "lending" P, and will "return" Q when l ends (and P is returned). *)
    Definition lowned_Perms l ls Hsub P Q : Perms2 :=
      meet_Perms2 (fun R => exists (* r *) q Hq, R = singleton_Perms2 _ ((* r **  *)owned l ls Hsub q Hq) /\
                                     q ∈2 Q /\
                                     (forall p, p ∈2 P -> forall s, (* pre r s ->  *)pre p s -> pre q s)).
    (* remove r? *)

    Lemma foo l ls Hsub P Q R :
      R *2 lowned_Perms l ls Hsub P Q ⊨2
      lowned_Perms l ls Hsub (P *2 when_Perms l R) (Q *2 R).
    Proof.
      repeat intro. cbn in H.
      destruct H as (r & p' & Hr & (? & ((q & Hqnonlifetime & ? & Hq & Hpre) & Hp')) & Hlte).
      subst. destruct Hp' as (Hspred & Hhlte).
      eexists. split.
      - do 2 eexists. split. reflexivity. split.
        + eapply Perms2_upwards_closed. Unshelve. 6: { intros ? asdf. apply asdf. }
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


  End asdf.
End LifetimePerms.
