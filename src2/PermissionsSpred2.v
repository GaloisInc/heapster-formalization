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
      (* Perms_upwards_closed1 : forall (spred1 spred2 : config -> Prop) *)
      (*                           (Hspred : forall x, spred1 x -> spred2 x) *)
      (*                           (p1 : @perm {x | spred1 x}) (p2 : @perm {x | spred2 x}), *)
      (*   in_Perms2 p1 -> *)
      (*   hlte_perm1 config spred1 spred2 Hspred p1 p2 -> *)
      (*   in_Perms2 p2 (* p2 has bigger spred *); *)
      Perms_upwards_closed2 : forall (spred1 spred2 : config -> Prop)
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
                     (* spred is smaller than spred' *)
                     (* exists (spred' : config -> Prop) *)
                     (*   (Hspred : forall x, spred x -> spred' x) *)
                     exists (p q : @perm {x | spred x}),
                       p ∈2 P /\
                         q ∈2 Q /\
                         p ** q <= r
                         (* hlte_perm2 config spred spred' Hspred (p ** q) r *)
    |}.
  Next Obligation.
    (* rename H into spred', H1 into Hspred', H2 into p, H3 into q. *)
    (* exists spred'. eexists. Unshelve. *)
    (* 2: { intros. auto. } *)
    (* exists p, q. split; [| split]; auto. eapply hlte_perm2_transitive; eauto. *)
    rename H into p, H1 into q, H2 into Hp, H3 into Hq.
    (* Set Printing All. *)
    exists (restrict _ _ _ Hspred p), (restrict _ _ _ Hspred q). split; [| split].
    - eapply Perms_upwards_closed2. apply Hp. red. reflexivity.
    - eapply Perms_upwards_closed2. apply Hq. red. reflexivity.
    - etransitivity. apply restrict_sep_conj.
      etransitivity. apply lte_perm_restrict; eauto. apply H0.
  Qed.

  (** Complete meet of Perms sets = union *)
  Program Definition meet_Perms2 (Ps : Perms2 -> Prop) : Perms2 :=
    {|
      in_Perms2 := fun _ p => exists P, Ps P /\ p ∈2 P
    |}.
  Next Obligation.
    exists H. split; auto.
    eapply (Perms_upwards_closed2 _ _ _ _ p1); eauto.
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

End PermSet.
