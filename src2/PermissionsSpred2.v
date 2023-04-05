(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     Relations
     Logic.ProofIrrelevance.

From Heapster2 Require Import
     Permissions.
(* end hide *)

Section SPred.
  Context (config : Type).
  Context (spred1 spred2 : config -> Prop).
  (* spred1 is a subset of spred2 *)
  Context (Hspred: forall x, spred1 x -> spred2 x).

  Definition lift1 (p : {x | spred2 x} -> Prop) : {x | spred1 x} -> Prop.
    intros []. apply p. econstructor. apply Hspred. apply s.
  Defined.
  Definition lift2 (p : relation {x | spred2 x}) :
    relation {x | spred1 x}.
    intros [] []. apply p.
    - econstructor. apply Hspred. apply s.
    - econstructor. apply Hspred. apply s0.
  Defined.

  Program Definition restrict (p : @perm { x | spred2 x }) : @perm { x | spred1 x } :=
    {|
      rely := lift2 (rely p);
      guar := lift2 (guar p);
      pre := lift1 (pre p);
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. cbn. reflexivity.
    - destruct x, y, z. cbn. etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. cbn. reflexivity.
    - destruct x, y, z. cbn. etransitivity; eauto.
  Qed.
  Next Obligation.
    cbn. respects.
  Qed.

  (* smaller perm has smaller config type *)
  (* Definition hlte_perm1 (p : @perm { x | spred1 x }) (q : @perm { x | spred2 x }) : Prop := *)
  (*   lte_perm p (restrict q). *)

  (* smaller perm has bigger config type *)
  Definition hlte_perm2 (p : @perm { x | spred2 x }) (q : @perm { x | spred1 x }) : Prop :=
    lte_perm (restrict p) q.

  (* Program Definition Restrict (P : @Perms { x | spred2 x }) : @Perms { x | spred1 x } := *)
  (*   {| *)
  (*     in_Perms (p : @perm { x | spred1 x }) := *)
  (*     (* p' <= p, but p' has the bigger config type *) *)
  (*     exists (p' : @perm { x | spred2 x }), hlte_perm2 p' p /\ p' ∈ P; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   exists H. split; auto. unfold hlte_perm2 in *. etransitivity; eauto. *)
  (* Qed. *)

  (* Definition hlte_Perms1 (P : @Perms { x | spred1 x }) (Q : @Perms { x | spred2 x }) : Prop := *)
  (*   lte_Perms P (Restrict Q). *)

  (* Definition hlte_Perms2 (P : @Perms { x | spred2 x }) (Q : @Perms { x | spred1 x }) : Prop := *)
  (*   lte_Perms (Restrict P) Q. *)

End SPred.


(*
Section SPred2.
  Context (config specConfig : Type).
  Context (spred1 spred1' : config -> Prop).
  Context (spred2 spred2' : specConfig -> Prop).
  (* spred1 is a subset of spred1' *)
  Context (Hspred1: forall x, spred1 x -> spred1' x).
  Context (Hspred2: forall x, spred2 x -> spred2' x).

  Definition lift21 (p : {x | spred1' x} * {x | spred2' x} -> Prop) :
    {x | spred1 x} * {x | spred2 x} -> Prop.
    intros [[] []]. apply p. split.
    - econstructor. apply Hspred1. apply s.
    - econstructor. apply Hspred2. apply s0.
  Defined.
  Definition lift22 (p : relation ({x | spred1' x} * {x | spred2' x})) :
    relation ({x | spred1 x} * {x | spred2 x}).
    intros [[] []] [[] []]. apply p.
    - split.
      + econstructor. apply Hspred1. apply s.
      + econstructor. apply Hspred2. apply s0.
    - split.
      + econstructor. apply Hspred1. apply s1.
      + econstructor. apply Hspred2. apply s2.
  Defined.

  Program Definition restrict2 (p : @perm ({x | spred1' x} * {x | spred2' x})) :
    @perm ({x | spred1 x} * {x | spred2 x}) :=
    {|
      rely := lift22 (rely p);
      guar := lift22 (guar p);
      pre := lift21 (pre p);
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x as [[] []]. cbn. reflexivity.
    - destruct x as [[] []], y as [[] []], z as [[] []]. cbn. etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - destruct x as [[] []]. cbn. reflexivity.
    - destruct x as [[] []], y as [[] []], z as [[] []]. cbn. etransitivity; eauto.
  Qed.
  Next Obligation.
    cbn. respects.
  Qed.

End SPred2.
*)

Lemma restrict_same config (spred : config -> Prop) p
      (H : forall x, spred x -> spred x) :
  restrict _ _ _ H p ≡≡ p.
Proof.
  split.
  {
    unfold restrict. constructor; cbn; auto.
    - unfold lift1. intros [] ?. rewrite (proof_irrelevance _ (H x s) s); auto.
    - unfold lift2. intros [] [] ?.
      rewrite (proof_irrelevance _ (H x s) s); auto.
      rewrite (proof_irrelevance _ (H x0 s0) s0); auto.
    - unfold lift2. intros [] [] ?.
      rewrite (proof_irrelevance _ s (H x s)); auto.
      rewrite (proof_irrelevance _ s0 (H x0 s0)); auto.
  }
  {
    unfold restrict. constructor; cbn; auto.
    - unfold lift1. intros [] ?. rewrite (proof_irrelevance _ s (H x s)); auto.
    - unfold lift2. intros [] [] ?.
      rewrite (proof_irrelevance _ s (H x s)); auto.
      rewrite (proof_irrelevance _ s0 (H x0 s0)); auto.
    - unfold lift2. intros [] [] ?.
      rewrite (proof_irrelevance _ (H x s) s); auto.
      rewrite (proof_irrelevance _ (H x0 s0) s0); auto.
  }
Qed.

Lemma restrict_restrict config (spred1 spred2 spred3 : config -> Prop) p
      (H12 : forall x, spred1 x -> spred2 x)
      (H23 : forall x, spred2 x -> spred3 x) :
  restrict _ _ _ (fun (x : config) (H : spred1 x) => H23 x (H12 x H)) p ≡≡
  restrict _ _ _ H12 (restrict _ _ _ H23 p).
Proof.
  split.
  {
    intros. constructor.
    - intros [] ?. apply H; auto.
    - intros [] [] ?. apply H; auto.
    - intros [] [] ?. apply H; auto.
  }
  {
    intros. constructor.
    - intros [] ?. apply H; auto.
    - intros [] [] ?. apply H; auto.
    - intros [] [] ?. apply H; auto.
  }
Qed.

(*
Lemma restrict_restrict config (spred1 spred2 spred3 : config -> Prop) p q
      (H12 : forall x, spred1 x -> spred2 x)
      (H23 : forall x, spred2 x -> spred3 x) :
  restrict _ _ _ (fun (x : config) (H : spred1 x) => H23 x (H12 x H)) p <= q ->
  restrict _ _ _ H12 (restrict _ _ _ H23 p) <= q.
Proof.
  intros. constructor.
  - intros [] ?. apply H; auto.
  - intros [] [] ?. apply H; auto.
  - intros [] [] ?. apply H; auto.
Qed.
Lemma restrict_restrict' config (spred1 spred2 spred3 : config -> Prop) p q
      (H12 : forall x, spred1 x -> spred2 x)
      (H23 : forall x, spred2 x -> spred3 x) :
  restrict _ _ _ H12 (restrict _ _ _ H23 p) <= q ->
  restrict _ _ _ (fun (x : config) (H : spred1 x) => H23 x (H12 x H)) p <= q.
Proof.
  intros. constructor.
  - intros [] ?. apply H; auto.
  - intros [] [] ?. apply H; auto.
  - intros [] [] ?. apply H; auto.
Qed.
*)

Lemma lte_perm_restrict config (spred1 spred2 : config -> Prop) (p1 p2 : perm)
  (Hspred : forall x, spred1 x -> spred2 x) :
  p1 <= p2 ->
  restrict _ _ _ Hspred p1 <= restrict _ _ _ Hspred p2.
Proof.
  intros. constructor; intros.
  - destruct x. apply H; auto.
  - destruct x, y. apply H; auto.
  - destruct x, y. apply H; auto.
Qed.

(* Lemma hlte_perm1_reflexive config (spred : config -> Prop) p H : *)
(*   hlte_perm1 config spred spred H p p. *)
(* Proof. *)
(*   unfold hlte_perm1. rewrite restrict_same. reflexivity. *)
(* Qed. *)

(* Lemma hlte_perm1_transitive config (spred1 spred2 spred3 : config -> Prop) (p1 p2 p3 : perm) *)
(*       (H12 : forall x, spred1 x -> spred2 x) *)
(*       (H23 : forall x, spred2 x -> spred3 x) : *)
(*   hlte_perm1 _ _ _ H12 p1 p2 -> *)
(*   hlte_perm1 _ _ _ H23 p2 p3 -> *)
(*   hlte_perm1 _ _ _ ((fun (x : config) (H : spred1 x) => H23 x (H12 x H))) p1 p3. *)
(* Proof. *)
(*   intros. unfold hlte_perm1 in *. etransitivity; eauto. *)
(*   clear H. constructor. *)
(*   - destruct H0 as [? _ _]. *)
(*     intros [] ?. cbn in *. apply pre_inc. cbn. apply H. *)
(*   - destruct H0 as [_ ? _]. *)
(*     intros [] [] ?. cbn in *. apply rely_inc. cbn. apply H. *)
(*   - destruct H0 as [_ _ ?]. *)
(*     intros [] [] ?. cbn in *. *)
(*     specialize (guar_inc _ _ H). (* same as before but slightly cumbersome *) *)
(*     apply guar_inc. *)
(* Qed. *)

Lemma hlte_perm2_reflexive config (spred : config -> Prop) H p :
  hlte_perm2 config spred spred H p p.
Proof.
  unfold hlte_perm2. rewrite restrict_same. reflexivity.
Qed.

Lemma hlte_perm2_transitive config (spred1 spred2 spred3 : config -> Prop) (p1 p2 p3 : perm)
      (H12 : forall x, spred2 x -> spred1 x)
      (H23 : forall x, spred3 x -> spred2 x) :
  hlte_perm2 _ _ _ H12 p1 p2 ->
  hlte_perm2 _ _ _ H23 p2 p3 ->
  hlte_perm2 _ _ _ ((fun (x : config) (H : spred3 x) => H12 x (H23 x H))) p1 p3.
Proof.
  intros. unfold hlte_perm2 in *. etransitivity; eauto.
  clear H0. constructor.
  - destruct H as [? _ _].
    intros [] ?. cbn in *.
    specialize (pre_inc _ H). cbn in pre_inc.
    apply pre_inc.
  - destruct H as [_ ? _].
    intros [] [] ?. cbn in *.
    specialize (rely_inc _ _ H).
    apply rely_inc.
  - destruct H as [_ _ ?].
    intros [] [] ?. cbn in *.
    apply guar_inc. apply H.
Qed.

Lemma separate_restrict config (spred1 spred2 : config -> Prop) (p1 p2 : perm)
      (Hspred : forall x, spred1 x -> spred2 x) :
  p1 ⊥ p2 ->
  (restrict _ _ _ Hspred p1) ⊥ (restrict _ _ _ Hspred p2).
Proof.
  intros. constructor.
  - intros [] [] ?. apply H; auto.
  - intros [] [] ?. apply H; auto.
Qed.

(* only makes sense when the smaller permission also has a smaller spred (actually no) *)
(* Lemma h_sep_antimonotone config (spred1 spred2 : config -> Prop) (p1 p2 p2' : perm) *)
(*       (Hspred : forall x, spred1 x -> spred2 x) : *)
(*   p1 ⊥ p2 -> *)
(*   hlte_perm1 _ _ _ Hspred p2' p2 -> *)
(*   (restrict _ _ _ Hspred p1) ⊥ p2'. *)
(* Proof. *)
(*   intros. *)
(*   eapply separate_antimonotone; eauto. *)
(*   apply separate_restrict; auto. *)
(* Qed. *)

Lemma restrict_sep_conj config (spred1 spred2 : config -> Prop) Hspred p1 p2 :
  restrict config spred1 spred2 Hspred p1 ** restrict config spred1 spred2 Hspred p2 <=
  restrict config spred1 spred2 Hspred (p1 ** p2).
Proof.
  constructor.
  - intros [] (? & ? & ?). split; [| split]; auto. apply separate_restrict; auto.
  - intros [] [] ?. auto.
  - intros [] [] ?. induction H.
    + destruct x1, y. destruct H; constructor; auto.
    + destruct x1, y, z. cbn in *. econstructor 2; eauto.
Qed.

(* the converse is not true *)
Lemma restrict_sep_conj' config (spred1 spred2 : config -> Prop) Hspred p1 p2 :
  restrict config spred1 spred2 Hspred (p1 ** p2) <=
  restrict config spred1 spred2 Hspred p1 ** restrict config spred1 spred2 Hspred p2.
Proof.
  constructor.
  - intros [] (? & ? & ?). split; [| split]; auto.
Abort.

(* Lemma lte_Perms_Restrict config (spred1 spred2 : config -> Prop) (P1 P2 : Perms) *)
(*   (Hspred : forall x, spred1 x -> spred2 x) : *)
(*   P1 ⊑ P2 -> *)
(*   Restrict _ _ _ Hspred P1 ⊑ Restrict _ _ _ Hspred P2. *)
(* Proof. *)
(*   repeat intro. destruct H0 as (p2 & Hhlte & Hp2). *)
(*   exists p2. split; auto. *)
(* Qed. *)

(* Lemma in_Perms_Restrict config (spred1 spred2 : config -> Prop) p P *)
(*   (Hspred : forall x, spred1 x -> spred2 x) : *)
(*   p ∈ P -> *)
(*   restrict _ _ _ Hspred p ∈ Restrict _ _ _ Hspred P. *)
(* Proof. *)
(*   repeat intro. exists p. split; auto. unfold hlte_perm2. reflexivity. *)
(* Qed. *)

(* Lemma hlte_Perms1_transitive config (spred1 spred2 spred3 : config -> Prop) (P1 P2 P3 : Perms) *)
(*       (H12 : forall x, spred1 x -> spred2 x) *)
(*       (H23 : forall x, spred2 x -> spred3 x) : *)
(*   hlte_Perms1 _ _ _ H12 P1 P2 -> *)
(*   hlte_Perms1 _ _ _ H23 P2 P3 -> *)
(*   hlte_Perms1 _ _ _ ((fun (x : config) (H : spred1 x) => H23 x (H12 x H))) P1 P3. *)
(* Proof. *)
(*   intros. unfold hlte_Perms1 in *. etransitivity; eauto. *)
(*   clear H. intros p Hp. destruct Hp as (p3 & Hhlte & Hp3). *)
(*   exists (restrict _ _ _ H23 p3). split. *)
(*   2: { apply H0. apply in_Perms_Restrict; auto. } *)
(*   unfold hlte_perm2 in *. rewrite <- restrict_restrict. apply Hhlte. *)
(* Qed. *)


(* Lemma hlte_Perms2_transitive config (spred1 spred2 spred3 : config -> Prop) (P1 P2 P3 : Perms) *)
(*       (H12 : forall x, spred2 x -> spred1 x) *)
(*       (H23 : forall x, spred3 x -> spred2 x) : *)
(*   hlte_Perms2 _ _ _ H12 P1 P2 -> *)
(*   hlte_Perms2 _ _ _ H23 P2 P3 -> *)
(*   hlte_Perms2 _ _ _ ((fun (x : config) (H : spred3 x) => H12 x (H23 x H))) P1 P3. *)
(* Proof. *)
(*   intros. unfold hlte_Perms2 in *. etransitivity; eauto. *)
(*   intros p Hp. destruct Hp as (p2 & Hhlte & Hp2). *)
(*   apply H in Hp2. destruct Hp2 as (p1 & Hhlte' & Hp1). *)
(*   cbn. exists p1. split; auto. *)
(*   unfold hlte_perm2 in *. etransitivity; eauto. rewrite restrict_restrict. *)
(*   apply lte_perm_restrict. auto. *)
(* Qed. *)

Section PermSet.
  Context {config : Type}.

  Record Perms2 :=
    {
      in_Perms2 : forall {spred}, @perm { x | spred x } -> Prop;
      Perms2_upwards_closed : forall (spred1 spred2 : config -> Prop)
                                (Hspred : forall x, spred1 x -> spred2 x)
                                (p1 : @perm {x | spred2 x}) (p2 : @perm {x | spred1 x}),
        in_Perms2 p1 ->
        hlte_perm2 config spred1 spred2 Hspred p1 p2 ->
        in_Perms2 p2 (* p2 has smaller spred *)
    }.
  Notation "p ∈2 P" := (in_Perms2 P p) (at level 60).

  Definition lte_Perms2 (P Q : Perms2) : Prop :=
    forall spred (p : @perm {x | spred x}), p ∈2 Q -> p ∈2 P.
  Notation "P ⊑2 Q" := (lte_Perms2 P Q) (at level 60).

  Global Instance lte_Perms2_is_preorder : PreOrder lte_Perms2.
  Proof.
    constructor; repeat intro; auto.
  Qed.

  Definition eq_Perms2 (P Q : Perms2) : Prop := P ⊑2 Q /\ Q ⊑2 P.
  Notation "P ≡2 Q" := (eq_Perms2 P Q) (at level 60).

  Global Instance Equivalence_eq_Perms2 : Equivalence eq_Perms2.
  Proof.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H; split; auto.
    - destruct H, H0. split; etransitivity; eauto.
  Qed.

  Global Instance Proper_eq_Perms2_lte_Perms2 :
    Proper (eq_Perms2 ==> eq_Perms2 ==> Basics.flip Basics.impl) lte_Perms2.
  Proof.
    do 5 red. intros. etransitivity. apply H. etransitivity. apply H1. apply H0.
  Qed.

  (* don't know how to write proper instance for this *)
  Lemma eq_Perms2_eq_perm_in_Perms2 spred P P' p p':
    in_Perms2 P p ->
    P ≡2 P' ->
    p ≡≡ p' ->
    @in_Perms2 P' spred p'.
  Proof.
    intros. apply H0. eapply Perms2_upwards_closed; eauto.
    red. rewrite restrict_same. apply H1.
    Unshelve. all: auto.
  Qed.

  Definition entails_Perms2 P Q := Q ⊑2 P.
  Notation "P ⊨2 Q" := (entails_Perms2 P Q) (at level 60).

  Global Instance entails_Perms2_preorder : PreOrder entails_Perms2.
  Proof.
    constructor; repeat intro; auto.
  Qed.

  Global Instance Proper_eq_Perms2_entails_Perms2 :
    Proper (eq_Perms2 ==> eq_Perms2 ==> Basics.flip Basics.impl) entails_Perms2.
  Proof.
    do 6 red. intros. rewrite H. rewrite H0. auto.
  Qed.

  Program Definition top_Perms2 : Perms2 :=
    {|
      in_Perms2 := fun _ _ => False
    |}.
  Program Definition bottom_Perms2 : Perms2 :=
    {|
      in_Perms2 := fun _ _ => True
    |}.

  Program Definition sep_conj_Perms2 (P Q : Perms2) : Perms2 :=
    {|
      in_Perms2 := fun spred (r : @perm {x | spred x}) =>
                     exists (p q : @perm {x | spred x}),
                       p ∈2 P /\
                         q ∈2 Q /\
                         p ** q <= r
    |}.
  Next Obligation.
    rename H into p, H1 into q, H2 into Hp, H3 into Hq.
    exists (restrict _ _ _ Hspred p), (restrict _ _ _ Hspred q). split; [| split].
    - eapply Perms2_upwards_closed. apply Hp. red. reflexivity.
    - eapply Perms2_upwards_closed. apply Hq. red. reflexivity.
    - etransitivity. apply restrict_sep_conj.
      etransitivity. apply lte_perm_restrict; eauto. apply H0.
  Qed.
  Notation "P *2 Q" := (sep_conj_Perms2 P Q) (at level 60).

  Lemma lte_l_sep_conj_Perms2 : forall P Q, P ⊑2 (P *2 Q).
  Proof.
    intros P Q ? p' ?. destruct H as [p [q [? [? ?]]]].
    eapply Perms2_upwards_closed; eauto.
    eapply hlte_perm2_transitive.
    - apply lte_l_sep_conj_perm.
    - red. do 2 rewrite restrict_same. apply H1.
      Unshelve. all: auto.
  Qed.

  Lemma lte_r_sep_conj_Perms2 : forall P Q, Q ⊑2 (P *2 Q).
  Proof.
    intros P Q ? p' ?. destruct H as [p [q [? [? ?]]]].
    eapply Perms2_upwards_closed; eauto.
    eapply hlte_perm2_transitive.
    - red. apply lte_r_sep_conj_perm.
    - red. do 2 rewrite restrict_same. eapply H1.
      Unshelve. all: auto.
  Qed.

  Lemma sep_conj_Perms2_bottom_identity : forall P, bottom_Perms2 *2 P ≡2 P.
  Proof.
    constructor; repeat intro.
    - exists bottom_perm, p. split; simpl; [auto | split; auto].
      rewrite sep_conj_perm_commut. apply sep_conj_perm_bottom.
    - destruct H as [? [? [_ [? ?]]]].
      eapply (Perms2_upwards_closed P); eauto.
      eapply hlte_perm2_transitive.
      + apply lte_r_sep_conj_perm.
      + red. do 2 rewrite restrict_same. apply H0.
        Unshelve. all: auto.
  Qed.

  Lemma sep_conj_Perms2_top_absorb : forall P, top_Perms2 *2 P ≡2 top_Perms2.
  Proof.
    constructor; repeat intro.
    - inversion H.
    - destruct H as [? [_ [[] _]]].
  Qed.

  Lemma sep_conj_Perms2_monotone : forall P P' Q Q', P' ⊑2 P -> Q' ⊑2 Q -> (P' *2 Q') ⊑2 (P *2 Q).
  Proof.
    repeat intro. destruct H1 as [? [? [? [? ?]]]].
    exists x, x0. auto.
  Qed.

  Lemma sep_conj_Perms2_perm: forall {spred} P Q (p q : @perm {x : config | spred x}),
      p ∈2 P ->
      q ∈2 Q ->
      p ** q ∈2 (P *2 Q).
  Proof.
    intros. exists p, q. split; auto. split; auto. reflexivity.
  Qed.

  Lemma sep_conj_Perms2_commut : forall P Q, (P *2 Q) ≡2 (Q *2 P).
  Proof.
    split; repeat intro.
    - destruct H as [q [p' [? [? ?]]]].
      exists p', q. split; [| split]; auto. etransitivity; eauto. apply sep_conj_perm_commut.
    - destruct H as [p' [q [? [? ?]]]].
      exists q, p'. split; [| split]; auto. etransitivity; eauto. apply sep_conj_perm_commut.
  Qed.

  Lemma sep_conj_Perms2_assoc : forall P Q R, (P *2 (Q *2 R)) ≡2 ((P *2 Q) *2 R).
  Proof.
    split; repeat intro.
    - rename p into p'. destruct H as [pq [r [? [? ?]]]].
      destruct H as [p [q [? [? ?]]]].
      exists p, (q ** r).
      split; auto. split; auto. apply sep_conj_Perms2_perm; auto.
      rewrite <- sep_conj_perm_assoc.
      etransitivity; eauto.
      apply sep_conj_perm_monotone; intuition.
    - rename p into p'. destruct H as [p [qr [? [? ?]]]].
      destruct H0 as [q [r [? [? ?]]]].
      exists (p ** q), r.
      split; auto. apply sep_conj_Perms2_perm; auto. split; auto.
      rewrite sep_conj_perm_assoc.
      etransitivity; eauto.
      apply sep_conj_perm_monotone; intuition.
  Qed.


  (** Complete meet of Perms sets = union *)
  Program Definition meet_Perms2 (Ps : Perms2 -> Prop) : Perms2 :=
    {|
      in_Perms2 := fun _ p => exists P, Ps P /\ p ∈2 P
    |}.
  Next Obligation.
    exists H. split; auto.
    eapply (Perms2_upwards_closed _ _ _ _ p1); eauto.
  Qed.

  Lemma lte_meet_Perms2 : forall (Ps : Perms2 -> Prop) P,
      Ps P ->
      meet_Perms2 Ps ⊑2 P.
  Proof.
    repeat intro. exists P. auto.
  Qed.

  Lemma meet_Perms2_max : forall (Ps : Perms2 -> Prop) Q,
      (forall P, Ps P -> Q ⊑2 P) ->
      Q ⊑2 meet_Perms2 Ps.
  Proof.
    repeat intro. destruct H0 as [? [? ?]].
    eapply H; eauto.
  Qed.

  Lemma sep_conj_Perms2_meet_commute : forall (Ps : Perms2 -> Prop) P,
      (meet_Perms2 Ps) *2 P ≡2 meet_Perms2 (fun Q => exists P', Q = P' *2 P /\ Ps P').
  Proof.
    split; repeat intro.
    - destruct H as [? [[Q [? ?]] ?]].
      subst. destruct H1 as [? [? [? [? ?]]]].
      simpl. exists x, x0. split; [ | split]; auto.
      eexists; split; eauto.
    - destruct H as [? [? [[Q [? ?]] [? ?]]]].
      simpl. eexists. split.
      + exists Q. split; auto.
      + eapply Perms2_upwards_closed; eauto.
        simpl. exists x, x0. split; [auto | split; [auto | ]]. reflexivity.
        red. rewrite restrict_same. auto.
        Unshelve. auto.
  Qed.


  (** The least Perms set containing a given p *)
  Program Definition singleton_Perms2 spred1 (p1 : @perm {x : config | spred1 x}) : Perms2 :=
    {|
      in_Perms2 := fun spred2 p2 => exists (Hspred : forall x, spred2 x -> spred1 x),
                       hlte_perm2 config spred2 spred1 Hspred p1 p2
    |}.
  Next Obligation.
    eexists. Unshelve.
    2: { intros. apply H. apply Hspred. auto. }
    eapply hlte_perm2_transitive; eassumption.
  Qed.

  (** Separating implication, though we won't be using it. *)
  Definition impl_Perms2 P Q := meet_Perms2 (fun R => R *2 P ⊨2 Q).

  (** A standard property about separating conjunction and implication. *)
  Lemma adjunction : forall P Q R, P *2 Q ⊨2 R <-> P ⊨2 (impl_Perms2 Q R).
  Proof.
    intros. split; intros.
    - red. red. intros. simpl. exists P. auto.
    - apply (sep_conj_Perms2_monotone _ _ Q Q) in H; intuition.
      red. etransitivity; [ | apply H ].
      unfold impl_Perms2.
      rewrite sep_conj_Perms2_meet_commute.
      apply meet_Perms2_max. intros P' [? [? ?]]. subst. auto.
  Qed.

End PermSet.

Notation "p ∈2 P" := (in_Perms2 P p) (at level 60).
Notation "P ⊑2 Q" := (lte_Perms2 P Q) (at level 60).
Notation "P ⊨2 Q" := (entails_Perms2 P Q) (at level 60).
Notation "P ≡2 Q" := (eq_Perms2 P Q) (at level 60).
Notation "P *2 Q" := (sep_conj_Perms2 P Q) (at level 60).
