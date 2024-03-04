(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties.
(* end hide *)

Section step.
  Context {config : Type}.

  (** * Rely-guarantee permissions *)
  Record perm : Type :=
    {
      inv : config -> Prop;
      (** The rely: the updates this permission allows of others. *)
      rely : config -> config -> Prop;
      rely_PO : PreOrder rely;
      (** The guarantee: the updates that this permission allows. *)
      guar : config -> config -> Prop;
      guar_PO : PreOrder guar;
      (** The precondition on configs. *)
      pre : config -> Prop;
      pre_respects : forall x y, rely x y -> pre x -> pre y;

      inv_rely : forall x y, rely x y -> inv x -> inv y;
      inv_guar : forall x y, guar x y -> inv x -> inv y;
    }.
  Global Instance rely_is_preorder p : PreOrder (rely p) := rely_PO p.
  Global Instance guar_is_preorder p : PreOrder (guar p) := guar_PO p.

  (** ** Separate permissions *)
  Record separate (p q : perm) : Prop :=
    {
      sep_l: forall x y, inv q x -> inv p x ->
                    guar q x y -> rely p x y;
      sep_r: forall x y, inv p x -> inv q x ->
                    guar p x y -> rely q x y;
    }.

  Notation "p ⊥ q" := (separate p q) (at level 50).

  Global Instance separate_symmetric: Symmetric separate.
  Proof.
    intros p q []. constructor; auto.
  Qed.

  (** * Preserves separability *)
  Definition inv_strengthen (p q : perm) : Prop :=
    forall x, inv q x -> inv p x.
  Definition sep_step (p q : perm) : Prop :=
    inv_strengthen p q /\
    forall r, p ⊥ r -> q ⊥ r.

  Global Instance sep_step_refl : Reflexive sep_step.
  Proof.
    split; repeat intro; auto.
  Qed.

  Global Instance sep_step_trans : Transitive sep_step.
  Proof.
    repeat intro. destruct H, H0. split; auto. repeat intro; auto.
  Qed.

  Program Definition bottom_perm : perm :=
    {|
      pre x := True;
      rely x y := True;
      guar := eq;
      inv x := False;
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.

  Lemma bottom_perm_is_bottom : forall p, sep_step p bottom_perm.
  Proof.
    split.
    - repeat intro. inversion H.
    - split; intros; cbn in *; subst; auto; reflexivity.
  Qed.

  Lemma separate_bottom : forall p, p ⊥ bottom_perm.
  Proof.
    constructor; intros; simpl; auto. cbn in *. subst.
    reflexivity.
  Qed.

  Program Definition top_perm : perm :=
    {|
      pre x := False;
      rely x y := x = y;
      guar x y := True;
      inv x := True;
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.

  Lemma top_perm_is_top : forall p, sep_step top_perm p.
  Proof.
    split.
    - repeat intro. cbn. auto.
    - split; intros; cbn in *.
      + apply H in H2; cbn; auto. cbn in H2. subst. reflexivity.
      + apply H; cbn; auto.
  Qed.

  Program Definition sym_guar_perm (p : perm) : perm :=
    {|
      pre x := False;
      rely := guar p;
      guar := rely p;
      inv x := inv p x;
    |}.
  Next Obligation.
    eapply inv_guar; eauto.
  Qed.
  Next Obligation.
    eapply inv_rely; eauto.
  Qed.
  Lemma separate_sym_guar : forall p, p ⊥ sym_guar_perm p.
  Proof.
    intros. split; intros; auto.
  Qed.

  Program Definition sym_guar_perm' (p : perm) : perm :=
    {|
      pre x := False;
      rely := guar p;
      guar := rely p;
      inv x := True;
    |}.
  Lemma separate_sym_guar' : forall p, p ⊥ sym_guar_perm' p.
  Proof.
    intros. split; intros; auto.
  Qed.
  (* Program Definition sym_guar_perm' (p : perm) : perm := *)
  (*   {| *)
  (*     pre x := False; *)
  (*     rely x y := guar p x y /\ inv p x; *)
  (*     guar x y := x = y \/ rely p x y /\ inv p x; *)
  (*     inv x := inv p x; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro. *)
  (*   left. reflexivity. destruct H, H0; subst; auto. destruct H, H0. *)
  (*   right. split; auto. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro. *)
  (*   left. reflexivity. destruct H, H0; subst; auto. destruct H, H0. *)
  (*   right. split; auto. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct H; subst; auto. destruct H. eapply inv_guar; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct H; subst; auto. destruct H. eapply inv_rely; eauto. *)
  (* Qed. *)
  (* Lemma separate_sym_guar' : forall p, p ⊥ sym_guar_perm' p. *)
  (* Proof. *)
  (*   intros. split; cbn; intros; auto. *)
  (*   destruct H1; subst. reflexivity. *)
  (*   destruct H1; auto. *)
  (* Qed. *)

  (* Invariant gets smaller *)
  Lemma sep_step_inv : forall p q x,
      sep_step p q ->
      inv q x ->
      inv p x.
  Proof.
    intros. apply H; auto.
  Qed.


  (* guar gets smaller *)
  Lemma sep_step_guar : forall p q x y,
      sep_step p q ->
      (* inv p x -> *)
      inv q x ->
      guar q x y ->
      guar p x y.
  Proof.
    intros. destruct H as (? & H). specialize (H (sym_guar_perm' p) (separate_sym_guar' p)).
    apply H; cbn; auto.
  Qed.

  (* rely gets bigger *)
  Lemma sep_step_rely : forall p q x y,
      sep_step p q ->
      inv q x ->
      (* inv p x -> *)
      rely p x y ->
      rely q x y.
  Proof.
    intros. destruct H as (? & H). specialize (H (sym_guar_perm' p) (separate_sym_guar' _)).
    apply H; cbn; auto.
  Qed.

(*
  Program Definition sym_guar_inv_perm (p : perm) : perm :=
    {|
      pre x := False;
      rely x y := inv p x <-> inv p y;
      guar x y := inv p x <-> inv p y;
      inv x := True;
    |}.
  Next Obligation.
    constructor; repeat intro; split; auto.
    - intros. apply H0. apply H; auto.
    - intros. apply H. apply H0; auto.
  Qed.
  Next Obligation.
    constructor; repeat intro; split; auto.
    - intros. apply H0. apply H; auto.
    - intros. apply H. apply H0; auto.
  Qed.

  Lemma sep_step_inv_guar : forall p q x, sep_step p q ->
                                       inv q x ->
                                       (* guar q x y -> *)
                                       inv p x.
  Proof.
    intros. specialize (H (sym_guar_inv_perm p)).
    destruct H. admit.
    cbn in *.
    destruct H. cbn in *.
    specialize (sep_r0 x x).
    destruct sep_r0; auto.
  Qed.

  Lemma sep_step_rg : forall p q,
      (forall x y, guar q x y -> guar p x y) ->
      (forall x y, rely p x y -> rely q x y) ->
      sep_step p q.
  Proof.
    repeat intro. split; intros.
    - apply H0. apply H1; auto.
    - apply H1. apply H. auto.
  Qed.

  Lemma sep_step_iff : forall p q,
      sep_step p q <-> (forall x y, rely p x y -> rely q x y) /\ (forall x y, guar q x y -> guar p x y).
  Proof.
    split; [split; intros; [eapply sep_step_rely | eapply sep_step_guar] |
            intros []; apply sep_step_rg]; eauto.
  Qed.

  Lemma sep_step_sep_conj_l : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (p1 ** q) (p2 ** q).
  Proof.
    intros p1 p2 q ? ?.
    repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
    - apply H0. symmetry. eapply separate_sep_conj_perm_l; eauto.
    - symmetry. eapply separate_sep_conj_perm_r; eauto.
  Qed.
  Lemma sep_step_sep_conj_r : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (q ** p1) (q ** p2).
  Proof.
    intros p1 p2 q ? ?.
    repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
    - symmetry. eapply separate_sep_conj_perm_l; eauto.
    - apply H0. symmetry. eapply separate_sep_conj_perm_r; eauto.
    - symmetry. auto.
  Qed.
 *)

  Lemma separate_antimonotone : forall p q r, p ⊥ q -> sep_step q r -> p ⊥ r.
  Proof.
    intros. symmetry. apply H0. symmetry; auto.
  Qed.

  (** ** Separating conjunction for permissions *)
  Program Definition sep_conj_perm (p q: perm) : perm :=
    {|
      pre := fun x => pre p x /\ pre q x;
      rely := fun x y => rely p x y /\ rely q x y;
      guar := clos_trans _ (fun x y => (guar p x y) \/ (guar q x y)) (* separateness implies each move is in the others' rely *) ;
      inv := fun x => inv p x /\ inv q x /\ p ⊥ q;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H, H0.
      split; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor; intuition.
    - repeat intro. destruct H, H0.
      + destruct H, H0; econstructor 2; constructor; eauto.
      + econstructor 2. left. apply H. econstructor 2; eauto.
      + econstructor 2; eauto. econstructor 2; eauto. left. assumption.
      + repeat (econstructor 2; eauto).
  Qed.
  Next Obligation.
    split; eapply pre_respects; eauto.
  Qed.
  Next Obligation.
    split; [| split]; auto; eapply inv_rely; eauto.
  Qed.
  Lemma inv_clos_trans p q x y :
    inv p x ->
    inv q x ->
    p ⊥ q ->
    clos_trans config (fun x y : config => guar p x y \/ guar q x y) x y ->
    inv p y /\ inv q y.
  Proof.
    intros Hp Hq Hsep H. induction H; intros.
    - destruct H.
      + split; [eapply inv_guar; eauto |].
        apply Hsep in H; auto. eapply inv_rely; eauto.
      + split; [| eapply inv_guar; eauto].
        apply Hsep in H; auto. eapply inv_rely; eauto.
    - apply IHclos_trans2; apply IHclos_trans1; auto.
  Qed.
  Next Obligation.
    destruct (inv_clos_trans _ _ _ _ H0 H1 H2 H); auto.
  Qed.
  Notation "p ** q" := (sep_conj_perm p q) (at level 40).

  Lemma sep_conj_perm_commut p q :
    sep_step (p ** q) (q ** p).
  Proof.
    split.
    {
      repeat intro. cbn in *. destruct H as (? & ? & ?). split; [| split]; auto.
      symmetry. auto.
    }
    split; repeat intro.
    - destruct H1 as (? & ? & ?). apply H in H2; auto.
      2: { split; [| split]; auto. symmetry. auto. }
      destruct H2. split; auto.
    - destruct H0 as (? & ? & ?).
      apply H; auto.
      { split; [| split]; auto. symmetry. auto. }
      clear H0 H3 H4 H1.
      induction H2; auto.
      + destruct H0; constructor; [right | left]; auto.
      + etransitivity; eauto.
  Qed.

  Lemma separate_sep_conj_perm_l: forall p q r, p ⊥ q ** r -> p ⊥ q.
  Proof.
    intros. destruct H. constructor; intros.
    - apply sep_l0; auto. admit. constructor. left. auto.
    - apply sep_r0; auto. split; [| split]; auto.
  Abort.

  Lemma sep_step_frame p q r (Hsep : p ⊥ r) :
    sep_step p q -> sep_step (p ** r) (q ** r).
  Proof.
    intros. split.
    - repeat intro. destruct H0 as (? & ? & ?). split; [| split]; auto.
      apply H; auto.
    - intros. split. cbn.
      + intros. split.
        * apply H0 in H3; auto.
          eapply sep_step_rely; eauto. apply H2. apply H3.
          destruct H2 as (? & ? & ?). split; [| split]; auto.
          apply H; auto.
        * apply H0; auto. destruct H2 as (? & ? & ?). split; [| split]; auto.
          apply H; auto.
      + intros. apply H0; auto.
        * destruct H1 as (? & ? & ?). split; [| split]; auto.
          apply H; auto.
        * destruct H1 as (? & ? & ?).
          induction H3.
          -- destruct H3; auto. constructor. left. eapply sep_step_guar; eauto.
             constructor. right. auto.
          -- etransitivity; eauto.
             pose proof (inv_clos_trans _ _ _ _ H1 H4 H5 H3_).
             destruct H3.
             apply IHclos_trans2; auto.
             destruct H0.
             eapply inv_rely; eauto. apply sep_r0; auto. split; auto.
             apply H. auto.
  Qed.

  Lemma clos_trans_guar_eq p x y :
    clos_trans config (fun x y : config => x = y \/ guar p x y) x y ->
    guar p x y.
  Proof.
    intros. induction H.
    - destruct H; auto. subst. reflexivity.
    - etransitivity; eauto.
  Qed.

  Lemma sep_conj_perm_bottom : forall p, sep_step (p ** bottom_perm) p.
  Proof.
  Abort.
  (*   split. *)
  (*   { *)
  (*     repeat intro. cbn in *. admit. *)
  (*   } *)
  (*   split; intros; cbn in *; subst; auto. *)
  (*   - apply H in H2; auto. destruct H2; auto. *)
  (*     split; [| split]; cbn; auto. apply separate_bottom. *)
  (*   - apply H; auto. split; [| split]; cbn; auto. apply separate_bottom. *)
  (*     constructor. left. auto. *)
  (* Qed. *)
  Lemma sep_conj_perm_bottom' : forall p, sep_step p (p ** bottom_perm).
  Proof.
    split.
    {
      repeat intro. cbn in *. destruct H as (_ & ? & _). inversion H.
    }
    split; intros; cbn in *; subst; auto.
    - split; auto. apply H; auto. apply H1.
    - apply H; auto. apply H0.
      clear H H0 H1. induction H2.
      destruct H; auto. subst. reflexivity.
      etransitivity; eauto.
  Qed.
  (* Lemma sep_conj_perm_top : forall p, sep_step (p ** top_perm) top_perm. *)
  (* Proof. *)
  (*   split; intros; cbn in *; subst; auto. *)
  (*   - apply H in H2; auto. destruct H2; auto. *)
  (*     split; [| split]; auto. 2: { *)
  (*   - apply H; auto. split; [| split]; cbn; auto. apply separate_bottom. *)
  (*     constructor. left. auto. *)
  (* Qed. *)

  Program Definition inv_perm (inv : config -> Prop) : perm :=
    {|
      pre x := False;
      rely x y := inv x -> inv y;
      guar x y := x = y;
      inv := inv;
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
  Qed.
  (* Next Obligation. *)
  (*   constructor; repeat intro; auto. *)
  (* Qed. *)

  (* sep_step q (inv q) + "frame rule" would imply this *)
  Lemma sep_step_sep_conj_l p q (Hsep : p ⊥ q) :
    sep_step (p ** q) (inv_perm (inv q) ** p).
  Proof.
    repeat intro.
    (* destruct H. *)
    split; intros.
    - cbn in *. destruct H1 as (? & ? & ?). apply H in H2; auto.
      2: { cbn. auto. }
      destruct H2.
      split; auto. intros. eapply inv_rely; eauto.
    - destruct H0 as (? & ? & ?). cbn in *. apply H; auto.
      split; [| split]; auto.
      constructor 1. left.
      apply clos_trans_guar_eq; auto.
  Qed.

  Lemma sep_step_inv_perm p i :
    sep_step (p ** inv_perm i) p.
  Proof.
    split; repeat intro.
    - apply H; auto. cbn. admit.
    - apply H; auto. admit.
  Abort.

  (** * Permission sets *)
  (** Perms = upwards-closed sets of permissions *)
  Record Perms :=
    {
      in_Perms : perm -> Prop;
      Perms_upwards_closed : forall p1 p2, in_Perms p1 -> sep_step p2 p1 -> in_Perms p2
    }.
  Notation "p ∈ P" := (in_Perms P p) (at level 60).
  (** ** Permission set ordering *)
  (** Defined as superset. *)
  Definition lte_Perms (P Q : Perms) : Prop :=
    forall p, p ∈ Q -> p ∈ P.
  Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).

  Global Instance lte_Perms_is_preorder : PreOrder lte_Perms.
  Proof.
    constructor; repeat intro; auto.
  Qed.

  (** Various lattice definitions. *)
  Program Definition top_Perms : Perms :=
    {|
    in_Perms := fun r => False
    |}.

  Lemma top_Perms_is_top : forall P, P ⊑ top_Perms.
  Proof.
    repeat intro. inversion H.
  Qed.

  Program Definition bottom_Perms : Perms :=
    {|
    in_Perms := fun r => True
    |}.

  Lemma bottom_Perms_is_bottom : forall P, bottom_Perms ⊑ P.
  Proof.
    repeat intro. simpl. auto.
  Qed.

  (** The least Perms set containing a given p *)
  Program Definition singleton_Perms p1 : Perms :=
    {|
    in_Perms := fun p2 => sep_step p2 p1
    |}.
  Next Obligation.
    etransitivity; eassumption.
  Qed.

  Program Definition join_Perms (Ps : Perms -> Prop) : Perms :=
    {|
    in_Perms := fun p => forall P, Ps P -> p ∈ P
    |}.
  Next Obligation.
    eapply Perms_upwards_closed; eauto.
  Qed.
  Lemma lte_join_Perms : forall (Ps : Perms -> Prop) P,
      Ps P ->
      P ⊑ join_Perms Ps.
  Proof.
    repeat intro. apply H0. auto.
  Qed.
  Lemma join_Perms_min : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> P ⊑ Q) ->
      join_Perms Ps ⊑ Q.
  Proof.
    repeat intro.
    eapply H; eauto.
  Qed.

  (** Complete meet of Perms sets = union *)
  Program Definition meet_Perms (Ps : Perms -> Prop) : Perms :=
    {|
    in_Perms := fun p => exists P, Ps P /\ p ∈ P
    |}.
  Next Obligation.
    exists H. split; auto.
    apply (Perms_upwards_closed _ p1); assumption.
  Qed.

  Lemma lte_meet_Perms : forall (Ps : Perms -> Prop) P,
      Ps P ->
      meet_Perms Ps ⊑ P.
  Proof.
    repeat intro. exists P. auto.
  Qed.

  Lemma meet_Perms_max : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> Q ⊑ P) ->
      Q ⊑ meet_Perms Ps.
  Proof.
    repeat intro. destruct H0 as [? [? ?]].
    eapply H; eauto.
  Qed.

  Definition meet_Perms2 P Q : Perms := meet_Perms (fun R => R = P \/ R = Q).

  (** Set equality *)
  Definition eq_Perms (P Q : Perms) : Prop := P ⊑ Q /\ Q ⊑ P.
  Notation "P ≡ Q" := (eq_Perms P Q) (at level 60).

  Global Instance Equivalence_eq_Perms : Equivalence eq_Perms.
  Proof.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H; split; auto.
    - destruct H, H0. split; etransitivity; eauto.
  Qed.

  Global Instance Proper_eq_Perms_lte_Perms :
    Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) lte_Perms.
  Proof.
    do 5 red. intros. etransitivity. apply H. etransitivity. apply H1. apply H0.
  Qed.

  Global Instance Proper_eq_Perms_eq_perm_in_Perms : Proper (eq_Perms ==> eq ==> Basics.flip Basics.impl) in_Perms.
  Proof.
    repeat intro; subst. apply H. auto.
  Qed.

  (** ** Separating conjunction for permission sets *)
  Program Definition sep_conj_Perms (P Q : Perms) : Perms :=
    {|
    in_Perms := fun r => exists p q, p ∈ P /\ q ∈ Q /\ p ⊥ q /\ sep_step r (p ** q)
    |}.
  Next Obligation.
    exists H, H1. split; [| split; [| split]]; auto. etransitivity; eauto.
  Qed.
  Notation "P * Q" := (sep_conj_Perms P Q).

  (* Lemma lte_l_sep_conj_Perms : forall P Q, P ⊑ P * Q. *)
  (* Proof. *)
  (*   intros P Q p' ?. destruct H as (p & q & Hp & Hq & ? & ?). *)
  (*   eapply Perms_upwards_closed; eauto. *)
  (*   etransitivity; eauto. apply lte_l_sep_conj_perm. *)
  (* Qed. *)

  (* Lemma lte_r_sep_conj_Perms : forall P Q, Q ⊑ P * Q. *)
  (* Proof. *)
  (*   intros P Q p' ?. destruct H as (p & q & Hp & Hq & ? & ?). *)
  (*   eapply Perms_upwards_closed; eauto. *)
  (*   etransitivity; eauto. apply lte_r_sep_conj_perm. *)
  (* Qed. *)

  (* Lemma sep_conj_Perms_bottom_identity : forall P, bottom_Perms * P ≡ P. *)
  (* Proof. *)
  (*   constructor; repeat intro. *)
  (*   - exists bottom_perm, p. split; cbn; [| split; [| split]]; auto. *)
  (*     + symmetry. apply separate_bottom. *)
  (*     + etransitivity. 2: apply sep_conj_perm_commut. apply sep_conj_perm_bottom'. *)
  (*   - destruct H as (? & ? & ? & ? & ? & ?).  *)
  (*     eapply (Perms_upwards_closed P); eauto. *)
  (*     etransitivity; eauto. apply lte_r_sep_conj_perm. *)
  (* Qed. *)

  Lemma sep_conj_Perms_top_absorb : forall P, top_Perms * P ≡ top_Perms.
  Proof.
    constructor; repeat intro.
    - inversion H.
    - destruct H as [? [_ [[] _]]].
  Qed.

  Lemma sep_conj_Perms_monotone : forall P P' Q Q', P' ⊑ P -> Q' ⊑ Q -> P' * Q' ⊑ P * Q.
  Proof.
    repeat intro. destruct H1 as [? [? [? [? ?]]]].
    exists x, x0. auto.
  Qed.

  Lemma sep_conj_Perms_perm: forall P Q p q,
      p ∈ P ->
      q ∈ Q ->
      p ⊥ q ->
      p ** q ∈ P * Q.
  Proof.
    intros. exists p, q. split; [| split; [| split]]; auto. reflexivity.
  Qed.


End step.

Notation "p ⊥ q" := (separate p q) (at level 50).
Notation "p ** q" := (sep_conj_perm p q) (at level 40).
Notation "p ∈ P" := (in_Perms P p) (at level 60).
Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).
Notation "P ≡ Q" := (eq_Perms P Q) (at level 60).
Notation "P * Q" := (sep_conj_Perms P Q).

Notation "P ⊨ Q" := (lte_Perms Q P) (at level 60).

From Heapster Require Import
  Utils.

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
  Context {config specConfig : Type}.

  Inductive sbuter_gen {R1 R2 : Type} (sbuter : perm -> (R1 -> R2 -> Perms) -> itree (sceE config) R1 -> config -> itree (sceE specConfig) R2 -> specConfig -> Prop)
            (p : perm) (Q : R1 -> R2 -> Perms) :
    itree (sceE config) R1 -> config -> itree (sceE specConfig) R2 -> specConfig -> Prop :=
  | sbuter_gen_ret r1 c1 r2 c2 :
      pre p (c1, c2) ->
      p ∈ Q r1 r2 ->
      sbuter_gen sbuter p Q (Ret r1) c1 (Ret r2) c2
  | sbuter_gen_err t1 c1 c2 :
      sbuter_gen sbuter p Q t1 c1 (throw tt) c2
  | sbuter_gen_tau_L t1 c1 t2 c2 :
      pre p (c1, c2) ->
      sbuter_gen sbuter p Q t1 c1 t2 c2 ->
      sbuter_gen sbuter p Q (Tau t1) c1 t2 c2
  | sbuter_gen_tau_R t1 c1 t2 c2 :
      pre p (c1, c2) ->
      sbuter_gen sbuter p Q t1 c1 t2 c2 ->
      sbuter_gen sbuter p Q t1 c1 (Tau t2) c2
  | sbuter_gen_tau t1 c1 t2 c2 :
      pre p (c1, c2) ->
      sbuter p Q t1 c1 t2 c2 ->
      sbuter_gen sbuter p Q (Tau t1) c1 (Tau t2) c2
  | sbuter_gen_modify_L f k c1 t2 c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (f c1, c2) ->
      sep_step p p' ->
      sbuter_gen sbuter p' Q (k c1) (f c1) t2 c2 ->
      sbuter_gen sbuter p Q (vis (Modify f) k) c1 t2 c2
  | sbuter_gen_modify_R t1 c1 f k c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (c1, f c2) ->
      sep_step p p' ->
      sbuter_gen sbuter p' Q t1 c1 (k c2) (f c2) ->
      sbuter_gen sbuter p Q t1 c1 (vis (Modify f) k) c2
  | sbuter_gen_modify f1 k1 c1 f2 k2 c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (f1 c1, f2 c2) ->
      sep_step p p' ->
      (* TODO: f1 c1 satisfies the spred *)
      sbuter p' Q (k1 c1) (f1 c1) (k2 c2) (f2 c2) ->
      sbuter_gen sbuter p Q (vis (Modify f1) k1) c1 (vis (Modify f2) k2) c2
  | sbuter_gen_choice_L k c1 t2 c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b, sbuter_gen sbuter p' Q (k b) c1 t2 c2) ->
      sbuter_gen sbuter p Q (vis Or k) c1 t2 c2
  | sbuter_gen_choice_R t1 c1 k c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b, sbuter_gen sbuter p' Q t1 c1 (k b) c2) ->
      sbuter_gen sbuter p Q t1 c1 (vis Or k) c2
  | sbuter_gen_choice k1 c1 k2 c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b1, exists b2, sbuter p' Q (k1 b1) c1 (k2 b2) c2) ->
      (forall b2, exists b1, sbuter p' Q (k1 b1) c1 (k2 b2) c2) ->
      sbuter_gen sbuter p Q (vis Or k1) c1 (vis Or k2) c2
  .

  Lemma sbuter_gen_mon {R1 R2} : monotone6 (@sbuter_gen R1 R2).
  Proof.
    repeat intro. induction IN; subst; try solve [econstructor; eauto]; auto.
    econstructor 11; eauto; intros.
    - destruct (H1 b1). eexists; eauto.
    - destruct (H2 b2). eexists; eauto.
  Qed.
  #[local] Hint Resolve sbuter_gen_mon : paco.

  Definition sbuter {R1 R2} := paco6 (@sbuter_gen R1 R2) bot6.

  Lemma sbuter_gen_pre {R1 R2} r p (Q : R1 -> R2 -> Perms) t s c1 c2 :
    sbuter_gen r p Q t c1 s c2 ->
    s = throw tt \/ pre p (c1, c2).
  Proof.
    inversion 1; auto.
  Qed.

  Lemma sbuter_lte {R1 R2} p Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 :
    sbuter p Q t c1 s c2 -> (forall r1 r2, Q r1 r2 ⊨ Q' r1 r2) -> sbuter p Q' t c1 s c2.
  Proof.
    revert p Q Q' t s c1 c2. pcofix CIH. intros p Q Q' t s c1 c2 Htyping Hlte.
    punfold Htyping. pstep.
    induction Htyping; pclearbot; try solve [econstructor; eauto].
    - constructor; eauto. apply Hlte. auto.
    - econstructor 11; eauto; intros.
      + destruct (H1 b1). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
      + destruct (H2 b2). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
  Qed.

  (** * Typing *)
  Definition typing {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :=
    forall p c1 c2, p ∈ P -> pre p (c1, c2) -> sbuter p Q t c1 s c2.
  (* TODO: add inv here *)

  Lemma typing_lte {R1 R2} P P' Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s ->
    P' ⊨ P ->
    (forall r1 r2, Q r1 r2 ⊨ Q' r1 r2) ->
    typing P' Q' t s.
  Proof.
    repeat intro.
    eapply sbuter_lte; eauto.
  Qed.

  Lemma typing_ret {R1 R2} P Q (r1 : R1) (r2 : R2) :
    P ⊨ Q r1 r2 -> typing P Q (Ret r1) (Ret r2).
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
    typing P Q (ITree.spin : itree (sceE config) R1) (ITree.spin : itree (sceE specConfig) R2).
  Proof.
    repeat intro. pcofix CIH. pstep.
    rewrite (@rewrite_spin _ R1). rewrite (@rewrite_spin _ R2).
    constructor 5; auto.
  Qed.

  Lemma typing_top {R1 R2} Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing top_Perms Q t s.
  Proof.
    repeat intro. inversion H.
  Qed.

  Lemma sbuter_bottom {R1 R2} p Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    sbuter p Q t c1 s c2 -> sbuter p (fun _ _ => bottom_Perms) t c1 s c2.
  Proof.
    revert p Q t s c1 c2. pcofix CIH. intros. pstep. punfold H0.
    induction H0; pclearbot; try solve [econstructor; simpl; eauto].
    econstructor 11; eauto; intros.
    - destruct (H1 b1). eexists. right. eapply CIH; pclearbot; apply H3.
    - destruct (H2 b2). eexists. right. eapply CIH; pclearbot; apply H3.
  Qed.

  Lemma typing_bottom {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s -> typing P (fun _ _ => bottom_Perms) t s.
  Proof.
    repeat intro. eapply sbuter_bottom; eauto.
  Qed.

  Lemma sbuter_bind {R1 R2 S1 S2} (p : perm) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2)
        c1 c2 r :
    pre p (c1, c2) ->
    sbuter p Q t1 c1 s1 c2 ->
    (forall r1 r2 p c1 c2, p ∈ (Q r1 r2) ->
                      pre p (c1, c2) ->
                      paco6 sbuter_gen r p R (t2 r1) c1 (s2 r2) c2) ->
    paco6 sbuter_gen r p R (x <- t1 ;; t2 x) c1 (x <- s1 ;; s2 x) c2.
  Proof.
    revert p Q R t1 t2 s1 s2 c1 c2. pcofix CIH.
    intros p Q R t1 t2 s1 s2 c1 c2 Hpre Htyping1 Htyping2.
    punfold Htyping1. induction Htyping1.
    - do 2 rewritebisim @bind_ret_l. specialize (Htyping2 _ _ _ c1 c2 H0 H).
      eapply paco6_mon; eauto.
    - rewrite throw_bind. pstep. constructor.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - do 2 rewritebisim @bind_tau. pclearbot.
      pstep. constructor 5; auto. right. eapply CIH; eauto.
    - rewritebisim @bind_vis. apply sbuter_gen_pre in Htyping1. destruct Htyping1; subst.
      + rewrite throw_bind. pstep. constructor.
      + specialize (IHHtyping1 H2 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - rewritebisim @bind_vis. apply sbuter_gen_pre in Htyping1. destruct Htyping1; subst.
      + pstep. econstructor; eauto. rewrite H2. rewrite throw_bind. constructor.
      + specialize (IHHtyping1 H2 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - do 2 rewritebisim @bind_vis. pclearbot.
      pose proof H2. punfold H2.
      pstep. econstructor 8; eauto.
      destruct (sbuter_gen_pre _ _ _ _ _ _ _ H2); eauto.
      rewrite H4. rewrite throw_bind. left. pstep. constructor.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (sbuter_gen_pre _ _ _ _ _ _ _ (H1 b)).
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 Htyping2). punfold H2.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (sbuter_gen_pre _ _ _ _ _ _ _ (H1 b)).
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 Htyping2). punfold H2.
    - do 2 rewritebisim @bind_vis. pclearbot. pstep. econstructor 11; eauto; intros.
      + specialize (H1 b1). destruct H1. pclearbot.
        punfold H1. destruct (sbuter_gen_pre _ _ _ _ _ _ _ H1).
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
      + specialize (H2 b2). destruct H2. pclearbot.
        punfold H2. destruct (sbuter_gen_pre _ _ _ _ _ _ _ H2).
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
  Qed.

  Lemma typing_bind {R1 R2 S1 S2} (P : Perms) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2) :
    typing P Q t1 s1 ->
    (forall r1 r2, typing (Q r1 r2) R (t2 r1) (s2 r2)) ->
    typing P R (x <- t1 ;; t2 x) (x <- s1 ;; s2 x).
  Proof.
    repeat intro.
    eapply sbuter_bind; eauto.
  Qed.

  Lemma sbuter_frame {R1 R2} p r p' Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    pre p' (c1, c2) ->
    inv p' (c1, c2) ->
    r ∈ R ->
    sep_step p' (p ** r) ->
    sbuter p Q t c1 s c2 ->
    sbuter p' (fun r1 r2 => Q r1 r2 * R) t c1 s c2.
  Proof.
    revert p r p' Q R t s c1 c2. pcofix CIH. rename r into r0.
    intros p r p' Q R t s c1 c2 Hpre Hinv Hr Hlte Hsbuter. pstep. punfold Hsbuter.
    revert p' Hlte Hpre Hinv. generalize dependent r.
    induction Hsbuter; intros; pclearbot; try solve [econstructor; eauto].
    - constructor; auto. eapply Perms_upwards_closed; eauto.
      apply sep_conj_Perms_perm; auto.

      (* do 2 eexists. split; [| split; [| split]]; eauto. *)
      (* apply Hlte in Hpre. apply Hpre. *)
      (* reflexivity. *)
    - apply sbuter_gen_pre in Hsbuter. destruct Hsbuter; [subst; constructor |].
      econstructor; eauto.
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + eapply IHHsbuter; eauto. reflexivity.
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

  Lemma typing_frame {R1 R2} P Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2):
    typing P Q t s ->
    typing (P * R) (fun r1 r2 => Q r1 r2 * R) t s.
  Proof.
    intros Ht p' c1 c2 (p & r & Hp & Hr & Hsep & Hlte) Hpre.
    pose proof Hpre as H. apply Hlte in H. destruct H as (Hprep & Hprer & Hsep').
    eapply sbuter_frame; eauto.
  Qed.



End bisim.
