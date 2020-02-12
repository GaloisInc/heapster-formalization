From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     Relations.Relation_Operators
     Relations.Operators_Properties.

Import ListNotations.

Definition config : Type := nat.

(* A single permission *)
Record perm :=
  {
    view : config -> config -> Prop;  (* ER over configs *)
    view_ER : Equivalence view;
    dom : config -> Prop; (* domain of valid configs *)
    dom_respects : forall x y, view x y -> (dom x <-> dom y);
    upd : config -> config -> Prop;  (* allowed transitions *)
    upd_PO : PreOrder upd;
  }.

Hint Unfold view.
Hint Unfold dom.
Hint Unfold upd.
Hint Resolve dom_respects.

Instance view_is_ER p : Equivalence (view p) := view_ER p.
Instance upd_is_preorder p : PreOrder (upd p) := upd_PO p.

Record lte_perm (p q: perm) : Prop :=
  {
    dom_inc : forall x, dom q x -> dom p x;
    view_inc : forall x y, view q x y -> view p x y;
    upd_inc : forall x y, upd p x y -> upd q x y;
  }.

Hint Resolve dom_inc.
Hint Resolve view_inc.
Hint Resolve upd_inc.

Notation "p <= q" := (lte_perm p q).

Instance lte_perm_is_PreOrder : PreOrder lte_perm.
Proof.
  constructor; [ constructor; auto | constructor; intros ]; eauto.
Qed.

(* Equality of permissions = the symmetric closure of the ordering *)
Definition eq_perm p q : Prop := p <= q /\ q <= p.

Notation "p ≡ q" := (eq_perm p q) (at level 50).
Lemma eq_perm_lte_1 : forall p q, p ≡ q -> p <= q.
Proof. intros p q []. auto. Qed.
Lemma eq_perm_lte_2 : forall p q, p ≡ q -> q <= p.
Proof. intros p q []. auto. Qed.

Hint Unfold eq_perm.
Hint Resolve eq_perm_lte_1.
Hint Resolve eq_perm_lte_2.

Instance eq_perm_is_Equivalence : Equivalence eq_perm.
Proof.
  constructor.
  - split; reflexivity.
  - intros x y []. split; auto.
  - intros x y z [] []. split; etransitivity; eauto.
Qed.

Instance eq_perm_flip_impl : Proper (eq ==> eq_perm ==> Basics.flip Basics.impl) lte_perm.
Proof.
  repeat intro. subst. etransitivity; eauto.
Qed.
Instance eq_perm_flip_impl' : Proper (eq_perm ==> eq ==> Basics.flip Basics.impl) lte_perm.
Proof.
  repeat intro. subst. etransitivity; eauto.
Qed.

Program Definition bottom_perm : perm :=
  {|
    dom := fun x => True;
    view := fun x y => True;
    upd  := fun x y => x = y;
  |}.
Next Obligation.
  constructor; repeat intro; subst; auto.
Qed.
Next Obligation.
  tauto.
Qed.
Next Obligation.
  constructor; repeat intro; subst; auto.
Qed.

Lemma bottom_perm_is_bottom : forall p, bottom_perm <= p.
Proof.
  constructor; simpl; intros; subst; intuition.
Qed.

Program Definition top_perm : perm :=
  {|
    dom := fun x => False;
    view := fun x y => x = y;
    upd  := fun x y => True;
  |}.
Next Obligation.
  constructor; repeat intro; subst; auto.
Qed.
Next Obligation.
  tauto.
Qed.
Next Obligation.
  constructor; repeat intro; subst; auto.
Qed.

Lemma top_perm_is_top : forall p, p <= top_perm.
Proof.
  constructor; simpl; repeat intro; subst; intuition.
Qed.

Ltac respects := eapply dom_respects; eauto; symmetry; auto.

Program Definition join_perm (p q: perm) : perm :=
  {|
    dom := fun x => dom p x /\ dom q x;
    view := fun x y => view p x y /\ view q x y;
    upd  := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y))
  |}.
Next Obligation.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct H. split; symmetry; auto.
  - destruct H. destruct H0. split; etransitivity; eauto.
Qed.
Next Obligation.
  split; intros []; split; respects.
Qed.
Next Obligation.
  constructor.
  - constructor; left; reflexivity.
  - repeat intro. destruct H, H0.
    + destruct H, H0; econstructor 2; constructor; eauto.
    + econstructor 2. left. apply H. econstructor 2; eauto.
    + econstructor 2; eauto. econstructor 2; eauto. left. assumption.
    + repeat (econstructor 2; eauto).
Qed.

Lemma lte_l_join_perm : forall p q,
    p <= join_perm p q.
Proof.
  intros. constructor; simpl; auto.
  - intros ? [? _]. auto.
  - intros x y []; auto.
  - constructor; auto.
Qed.

Lemma lte_r_join_perm : forall p q,
    q <= join_perm p q.
Proof.
  intros. constructor; simpl; auto.
  - intros ? [_ ?]. auto.
  - intros x y []; auto.
  - constructor; auto.
Qed.

Lemma join_perm_min : forall p q r,
    p <= r ->
    q <= r ->
    join_perm p q <= r.
Proof.
  intros p q r [] []. constructor; intros; simpl; auto.
  - induction H; auto.
    + destruct H; auto.
    + transitivity y; auto.
Qed.

Lemma join_perm_commut' : forall p q,
    join_perm p q <= join_perm q p.
Proof.
  constructor.
  - intros ? []. split; auto.
  - intros x y []. repeat split; auto.
  - intros. induction H.
    + destruct H; constructor; auto.
    + etransitivity; eauto.
Qed.

Lemma join_perm_commut : forall p q,
    join_perm p q ≡ join_perm q p.
Proof.
  split; apply join_perm_commut'.
Qed.

Lemma join_perm_assoc : forall p q r,
    join_perm p (join_perm q r) ≡ join_perm (join_perm p q) r.
Proof.
  split; intros.
  {
    constructor.
    - intros x [[? ?] ?]. split; [| split]; auto.
    - intros x y [[] ?].
      repeat split; auto.
    - intros. induction H; try solve [etransitivity; eauto].
      destruct H.
      + constructor. left. constructor. left. auto.
      + induction H; try solve [etransitivity; eauto].
        destruct H.
        * constructor. left. constructor. right. auto.
        * constructor. right. auto.
  }
  {
    constructor.
    - intros x [? [? ?]]. split; [split |]; auto.
    - intros x y [? []].
      repeat split; auto.
    - intros. induction H; try solve [etransitivity; eauto].
      destruct H.
      + induction H; try solve [etransitivity; eauto].
        destruct H.
        * constructor. left. auto.
        * constructor. right. constructor. left. auto.
      + constructor. right. constructor. right. auto.
  }
Qed.

Lemma join_perm_idem : forall p, join_perm p p ≡ p.
Proof.
  split; intros.
  - constructor; intros.
    + split; auto.
    + repeat split; auto.
    + induction H; try solve [etransitivity; eauto].
      destruct H; auto.
  - constructor.
    + intros ? [? _]; auto.
    + intros x y []. auto.
    + constructor. auto.
Qed.

Definition meet_view p q := clos_trans _ (fun x y => (view p x y) \/ (view q x y)).

Program Definition meet_perm (p q:perm) : perm :=
  {|
    dom := fun x => dom p x \/ dom q x \/ exists y, (dom p y \/ dom q y) /\ meet_view p q x y;
    view := meet_view p q;
    upd  := fun x y => upd p x y /\ upd q x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - constructor. left. reflexivity.
  - induction H.
    + constructor. destruct H; symmetry in H; auto.
    + econstructor 2; eauto.
  - econstructor 2; eauto.
Qed.
Next Obligation.
  induction H; [| rewrite IHclos_trans1; auto].
  split.
  { destruct 1 as [? | [? | [z [? ?]]]].
    - destruct H; symmetry in H; try solve [left; respects].
      right. right. exists x. split; auto. constructor 1. auto.
    - destruct H; symmetry in H; try solve [right; left; respects].
      right. right. exists x. split; auto. constructor 1. auto.
    - destruct H; symmetry in H; right; right; exists z; split; auto;
        econstructor 2; eauto; constructor 1; auto.
  }
  { destruct 1 as [? | [? | [z [? ?]]]].
    - destruct H; try solve [left; respects].
      right. right. exists y. split; auto. constructor 1. auto.
    - destruct H; try solve [right; left; respects].
      right. right. exists y. split; auto. constructor 1. auto.
    - destruct H; right; right; exists z; split; auto;
        econstructor 2; eauto; constructor 1; auto.
  }
Qed.
Next Obligation.
  constructor.
  - constructor; reflexivity.
  - intros x y z [] []. split; etransitivity; eauto.
Qed.

Lemma lte_meet_perm_l : forall p q,
    meet_perm p q <= p.
Proof.
  intros. constructor; simpl; auto.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma lte_meet_perm_r : forall p q,
    meet_perm p q <= q.
Proof.
  intros. constructor; simpl; auto.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma meet_perm_max : forall p q r,
    r <= p ->
    r <= q ->
    r <= meet_perm p q.
Proof.
  intros p q r [] []. constructor; intros; simpl; auto.
  - simpl in H. destruct H as [? | [? | [? [? ?]]]]; auto. (* why is this case so bad *)
    induction H0.
    + destruct H, H0; respects.
    + apply IHclos_trans2 in H.
      clear IHclos_trans1 IHclos_trans2 H0_0.
      induction H0_; auto.
      destruct H0; respects.
  - induction H.
    + destruct H; auto.
    + transitivity y; auto.
Qed.

(*
Lemma meet_perm_commut: forall p q, meet_perm p q ≡ meet_perm q p.
Proof.
  split; intros.
  - constructor; intros.
    + destruct H as [? [? ?]].
    + induction H.
      * destruct H; constructor; auto.
      * etransitivity; eauto.
    + destruct H. constructor; auto.
  - constructor; intros.
    + induction H.
      * destruct H; constructor; auto.
      * etransitivity; eauto.
    + destruct H. constructor; auto.
Qed.

Lemma meet_perm_assoc : forall p q r,
    eq_perm (meet_perm p (meet_perm q r)) (meet_perm (meet_perm p q) r).
Proof.
  split; intros.
  - constructor; intros.
    + induction H; try solve [etransitivity; eauto].
      destruct H.
      * induction H; try solve [etransitivity; eauto].
        destruct H.
        -- constructor. left. auto.
        -- constructor. right. constructor. left. auto.
      * constructor. right. constructor. right. auto.
    + destruct H as [? [? ?]].
      constructor; auto. constructor; auto.
  - constructor; intros.
    + induction H; try solve [etransitivity; eauto].
      destruct H.
      * constructor. left. constructor. left. auto.
      * induction H; try solve [etransitivity; eauto].
        destruct H.
        -- constructor. left. constructor. right. auto.
        -- constructor. right. auto.
    + destruct H as [[? ?] ?].
      constructor; auto. constructor; auto.
Qed.

Lemma meet_perm_idem : forall p, eq_perm (meet_perm p p) p.
Proof.
  split; intros.
  - constructor; intros.
    + constructor. left. auto.
    + destruct H; auto.
  - constructor; intros.
    + induction H; try solve [etransitivity; eauto].
      destruct H; auto.
    + constructor; auto.
Qed.

Lemma join_perm_absorb : forall p q, eq_perm (join_perm p (meet_perm p q)) p.
Proof.
  split; intros.
  - constructor; intros.
    + constructor; auto. constructor; auto.
    + induction H; try solve [etransitivity; eauto].
      destruct H; auto. destruct H; auto.
  - constructor; intros.
    + destruct H. auto.
    + constructor. left. auto.
Qed.

Lemma meet_perm_absorb : forall p q, eq_perm (meet_perm p (join_perm p q)) p.
Proof.
  split; intros.
  - constructor; intros.
    + constructor. left. auto.
    + destruct H. auto.
  - constructor; intros.
    + induction H; try solve [etransitivity; eauto].
      destruct H; auto. destruct H; auto.
    + constructor; auto. constructor; auto.
Qed. *)

Record separate (p q : perm) : Prop :=
  {
    sep_l: forall x y, upd q x y -> view p x y;
    sep_r: forall x y, upd p x y -> view q x y;
  }.

Notation "p ⊥ q" := (separate p q) (at level 50).

Instance separate_symmetric: Symmetric separate.
Proof.
  intros p q []. constructor; auto.
Qed.

Lemma separate_bottom : forall p, p ⊥ bottom_perm.
Proof.
  constructor; intros; simpl; auto.
  inversion H. reflexivity.
Qed.

Program Definition sym_upd_perm (p : perm) : perm :=
  {|
    dom x := False;
    view := clos_refl_sym_trans _ (upd p);
    upd := view p;
  |}.
Next Obligation.
  (* apply clos_rst_is_equiv. *)
  constructor; repeat intro.
  - constructor 1; reflexivity.
  - constructor 3; auto.
  - econstructor 4; eauto.
Qed.
Next Obligation.
  tauto.
Qed.

Lemma separate_self_sym : forall p, p ⊥ sym_upd_perm p.
Proof.
  intros. split; intros; auto.
  constructor; auto.
Qed.

Lemma separate_antimonotone : forall p q r, p ⊥ q -> r <= q -> p ⊥ r.
Proof.
  intros. constructor.
  - intros. apply H. apply H0. auto.
  - intros. apply H0. apply H. auto.
Qed.

Program Definition sep_conj_perm (p q: perm) : perm :=
  {|
    dom := fun x => dom p x /\ dom q x /\ separate p q;
    view := fun x y => view p x y /\ view q x y;
    upd  := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y))
  |}.
Next Obligation.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct H; split; symmetry; auto.
  - destruct H, H0.
    split; etransitivity; eauto.
Qed.
Next Obligation.
  split; intros [? [? ?]]; (split; [respects | split; [respects | auto]]).
Qed.
Next Obligation.
  constructor.
  - constructor; left; reflexivity.
  - repeat intro. destruct H, H0.
    + destruct H, H0; econstructor 2; constructor; eauto.
    + econstructor 2. left. apply H. econstructor 2; eauto.
    + econstructor 2; eauto. econstructor 2; eauto. left. assumption.
    + repeat (econstructor 2; eauto).
Qed.
Notation "p * q" := (sep_conj_perm p q).

Lemma sep_conj_join : forall p q, p ⊥ q -> p * q ≡ join_perm p q.
Proof.
  split; intros.
  - constructor; auto; intros x []; split; auto.
  - constructor; auto; intros x [? [? ?]]; split; auto.
Qed.

Lemma lte_l_sep_conj_perm : forall p q, p <= p * q.
Proof.
  intros. constructor; simpl; auto.
  - intros x []; auto.
  - intros x y []; auto.
  - constructor; auto.
Qed.

Lemma lte_r_sep_conj_perm : forall p q, q <= p * q.
Proof.
  intros. constructor; simpl; auto.
  - intros x [? [? ?]]; auto.
  - intros x y []; auto.
  - constructor; auto.
Qed.

Lemma sep_conj_perm_monotone_l : forall p p' q,
    p' <= p -> p' * q <= p * q.
Proof.
  constructor; intros; simpl.
  - destruct H0 as [? [? ?]]; split; [| split]; auto.
    + apply H; auto.
    + symmetry. symmetry in H2. eapply separate_antimonotone; eauto.
  - split.
    + apply H. apply H0.
    + apply H0.
  - induction H0.
    + constructor. destruct H0; auto. left. apply H. auto.
    + econstructor 2; eauto.
Qed.

Lemma sep_conj_perm_monotone_r : forall p q q',
    q' <= q -> p * q' <= p * q.
Proof.
  constructor; intros; simpl.
  - destruct H0 as [? [? ?]]; split; [| split]; auto.
    + apply H; auto.
    + eapply separate_antimonotone; eauto.
  - split.
    + apply H0.
    + apply H. apply H0.
  - induction H0.
    + constructor. destruct H0; auto. right. apply H. auto.
    + econstructor 2; eauto.
Qed.

Lemma sep_conj_perm_bottom' : forall p, p * bottom_perm <= p.
Proof.
  constructor; intros.
  - split; [| split]; simpl; intuition. apply separate_bottom.
  - repeat split; auto.
  - induction H.
    + destruct H; auto. inversion H. reflexivity.
    + etransitivity; eauto.
Qed.

Lemma sep_conj_perm_bottom : forall p, p * bottom_perm ≡ p.
Proof.
  split; [apply sep_conj_perm_bottom' | apply lte_l_sep_conj_perm].
Qed.

Lemma sep_conj_perm_top' : forall p, p * top_perm <= top_perm.
Proof.
  constructor; intros; simpl in *; intuition.
  subst. reflexivity.
Qed.

Lemma sep_conj_perm_top : forall p, top_perm ≡ p * top_perm.
Proof.
  split; [apply lte_r_sep_conj_perm | apply sep_conj_perm_top'].
Qed.

Lemma sep_conj_perm_commut' : forall p q, p * q <= q * p.
Proof.
  constructor.
  - intros x [? [? ?]]; simpl; split; [| split]; intuition.
  - intros x y []; repeat split; auto.
  - intros. induction H.
    + destruct H; constructor; auto.
    + etransitivity; eauto.
Qed.

Lemma sep_conj_perm_commut : forall p q, p * q ≡ q * p.
Proof.
  split; apply sep_conj_perm_commut'.
Qed.

Lemma separate_sep_conj_perm_l: forall p q r, p ⊥ q * r -> p ⊥ q.
Proof.
  intros. destruct H. constructor; intros.
  - apply sep_l0. constructor. left. auto.
  - apply sep_r0. auto.
Qed.
Lemma separate_sep_conj_perm_r: forall p q r, p ⊥ q * r -> p ⊥ r.
Proof.
  intros. destruct H. constructor; intros.
  - apply sep_l0. constructor. right. auto.
  - apply sep_r0. auto.
Qed.
Lemma separate_sep_conj_perm: forall p q r, p ⊥ q ->
                                       p ⊥ r ->
                                       r ⊥ q ->
                                       p ⊥ q * r.
Proof.
  intros. constructor; intros.
  - induction H2.
    + destruct H2; [apply H | apply H0]; auto.
    + etransitivity; eauto.
  - split; [apply H | apply H0]; auto.
Qed.

Lemma sep_conj_perm_assoc : forall p q r,
    p * q * r ≡ p * (q * r).
Proof.
  split; intros.
  {
    constructor.
    - intros x [? [[? [? ?]] ?]].
      pose proof (separate_sep_conj_perm_l _ _ _ H3).
      pose proof (separate_sep_conj_perm_r _ _ _ H3).
      split; [split; [| split] | split]; auto.
      symmetry. apply separate_sep_conj_perm; symmetry; auto.
    - intros x y [? [? ?]]. split; [split |]; auto.
    - intros. induction H; try solve [etransitivity; eauto].
      destruct H.
      + induction H; try solve [etransitivity; eauto].
        destruct H.
        * constructor. left. auto.
        * constructor. right. constructor. left. auto.
      + constructor. right. constructor. right. auto.
  }
  {
    constructor.
    - intros x [[? [? ?]] [? ?]]. symmetry in H3.
      pose proof (separate_sep_conj_perm_l _ _ _ H3). symmetry in H4.
      pose proof (separate_sep_conj_perm_r _ _ _ H3). symmetry in H5.
      split; [| split; [split; [| split] |]]; auto.
      apply separate_sep_conj_perm; auto. symmetry; auto.
    - intros x y [[? ?] ?]; simpl; auto.
    - intros. induction H; try solve [etransitivity; eauto].
      destruct H.
      + constructor. left. constructor. left. auto.
      + induction H; try solve [etransitivity; eauto].
        destruct H.
        * constructor. left. constructor. right. auto.
        * constructor. right. auto.
  }
Qed.

(* Perms = upwards-closed sets of permissions *)
Record Perms :=
  {
    in_Perms : perm -> Prop;
    Perms_upwards_closed : forall p1 p2, in_Perms p1 -> p1 <= p2 -> in_Perms p2
  }.
Notation "p ∈ P" := (in_Perms P p) (at level 60).

(* superset *)
Definition lte_Perms (P Q : Perms) : Prop :=
  forall p, p ∈ Q -> p ∈ P.
Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).

Instance lte_Perms_is_preorder : PreOrder lte_Perms.
Proof.
  constructor; repeat intro; auto.
Qed.

(* The least Perms set containing a given p *)
Program Definition singleton_Perms p1 : Perms :=
  {|
    in_Perms := fun p2 => p1 <= p2
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

(* Complete meet of Perms sets = union *)
Program Definition meet_Perms (Ps : Perms -> Prop) : Perms :=
  {|
    in_Perms := fun p => exists P, Ps P /\ p ∈ P
  |}.
Next Obligation.
  exists H. split; auto.
  apply (Perms_upwards_closed _ p1); try assumption.
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

(* Set equality *)
Definition eq_Perms (P Q : Perms) : Prop := P ⊑ Q /\ Q ⊑ P.
Notation "P ≡≡ Q" := (eq_Perms P Q) (at level 60).

Instance eq_Perms_flip_impl : Proper (eq ==> eq_Perms ==> Basics.flip Basics.impl) lte_Perms.
Proof.
  intros P Q [] ? ? ? ?. etransitivity; subst; eauto. apply H.
Qed.
Instance eq_Perms_flip_impl' : Proper (eq_Perms ==> eq ==> Basics.flip Basics.impl) lte_Perms.
Proof.
  intros P Q [] ? ? ? ?. etransitivity; subst; eauto.
Qed.

Program Definition sep_conj_Perms (P Q : Perms) : Perms :=
  {|
    in_Perms := fun r => exists p q, p ∈ P /\ q ∈ Q /\ p * q <= r
  |}.
Next Obligation.
  exists H, H1. split; [| split]; auto. etransitivity; eauto.
Qed.
Notation "P ** Q" := (sep_conj_Perms P Q) (at level 50).

Lemma lte_l_sep_conj_Perms : forall P Q, P ⊑ P ** Q.
Proof.
  intros P Q p' ?. destruct H as [p [q [? [? ?]]]].
  eapply Perms_upwards_closed; eauto.
  etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma lte_r_sep_conj_Perms : forall P Q, Q ⊑ P ** Q.
Proof.
  intros P Q q' ?. destruct H as [p [q [? [? ?]]]].
  eapply Perms_upwards_closed; eauto.
  etransitivity; eauto. apply lte_r_sep_conj_perm.
Qed.

Lemma sep_conj_Perms_bottom_identity : forall P, bottom_Perms ** P ≡≡ P.
Proof.
  constructor; repeat intro.
  - exists bottom_perm, p. split; simpl; [auto | split; auto].
    rewrite sep_conj_perm_commut. apply sep_conj_perm_bottom.
  - destruct H as [? [? [_ [? ?]]]].
    eapply (Perms_upwards_closed P); eauto.
    etransitivity; eauto. apply lte_r_sep_conj_perm.
Qed.

Lemma sep_conj_Perms_top_absorb : forall P, top_Perms ** P ≡≡ top_Perms.
Proof.
  constructor; repeat intro.
  - inversion H.
  - destruct H as [? [_ [[] _]]].
Qed.

Lemma sep_conj_Perms_monotone_l : forall P P' Q, P ⊑ P' -> P ** Q ⊑ P' ** Q.
Proof.
  repeat intro. destruct H0 as [? [? [? [? ?]]]].
  exists x, x0. auto.
Qed.
Lemma sep_conj_Perms_monotone_r : forall P Q Q', Q ⊑ Q' -> P ** Q ⊑ P ** Q'.
Proof.
  repeat intro. destruct H0 as [? [? [? [? ?]]]].
  exists x, x0. auto.
Qed.

Lemma sep_conj_Perms_perm: forall P Q p q,
    p ∈ P ->
    q ∈ Q ->
    p * q ∈ P ** Q.
Proof.
  intros. exists p, q. split; auto. split; auto. reflexivity.
Qed.

Lemma sep_conj_Perms_commut : forall P Q, P ** Q ≡≡ Q ** P.
Proof.
  split; repeat intro.
  - destruct H as [q [p' [? [? ?]]]].
    exists p', q. split; [| split]; auto. etransitivity; eauto. apply sep_conj_perm_commut.
  - destruct H as [p' [q [? [? ?]]]].
    exists q, p'. split; [| split]; auto. etransitivity; eauto. apply sep_conj_perm_commut.
Qed.

Lemma sep_conj_Perms_assoc : forall P Q R, P ** (Q ** R) ≡≡ (P ** Q) ** R.
Proof.
  split; repeat intro.
  - rename p into p'. destruct H as [pq [r [? [? ?]]]].
    destruct H as [p [q [? [? ?]]]].
    exists p, (q * r).
    split; auto. split; auto. apply sep_conj_Perms_perm; auto.
    rewrite <- sep_conj_perm_assoc.
    etransitivity; eauto.
    apply sep_conj_perm_monotone_l; auto.
  - rename p into p'. destruct H as [p [qr [? [? ?]]]].
    destruct H0 as [q [r [? [? ?]]]].
    exists (p * q), r.
    split; auto. apply sep_conj_Perms_perm; auto. split; auto.
    rewrite sep_conj_perm_assoc.
    etransitivity; eauto.
    apply sep_conj_perm_monotone_r; auto.
Qed.

Lemma sep_conj_Perms_meet_commute : forall (Ps : Perms -> Prop) P,
    (meet_Perms Ps) ** P ≡≡ meet_Perms (fun Q => exists P', Q = P' ** P /\ Ps P').
Proof.
  split; repeat intro.
  - destruct H as [? [[Q [? ?]] ?]].
    subst. destruct H1 as [? [? [? [? ?]]]].
    simpl. exists x, x0. split; [ | split]; auto.
    eexists; split; eauto.
  - destruct H as [? [? [[Q [? ?]] [? ?]]]].
    simpl. eexists. split.
    + exists Q. split; auto.
    + eapply Perms_upwards_closed; eauto.
      simpl. exists x, x0. split; [auto | split; [auto | ]]. reflexivity.
Qed.

Definition entails_Perms P Q := Q ⊑ P.
Notation "P ⊦ Q" := (entails_Perms P Q) (at level 50).

Definition impl_Perms P Q := meet_Perms (fun R => R ** P ⊦ Q).

Lemma adjunction : forall P Q R, P ** Q ⊦ R <-> P ⊦ (impl_Perms Q R).
Proof.
  intros. split; intros.
  - red. red. intros. simpl. exists P. auto.
  - apply (sep_conj_Perms_monotone_l _ _ Q) in H.
    red. etransitivity; [ | apply H ].
    unfold impl_Perms.
    rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max. intros P' [? [? ?]]. subst. auto.
Qed.

From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus.

From Paco Require Import
     paco.

Import ITreeNotations.
Import ITree.Basics.Basics.Monads.

Require Import ITree.Eq.EqAxiom.

Section ts.

  Definition E := (stateE config +' nondetE).
  (* Context {E : Type -> Type}. *)
  (* Context {HasStateConfig : stateE config -< E}. *)
  (* Context {HasNondet : nondetE -< E}. *)

  Context {R : Type}.

  Definition par_match
             (par : itree E R -> itree E R -> itree E R)
             (t1 t2 : itree E R)
    : itree E R :=
    vis Or (fun b : bool =>
              if b then
                match (observe t1) with
                | RetF _ => t2
                | TauF t => Tau (par t t2)
                | VisF o k => vis o (fun x => par (k x) t2)
                end
              else
                match (observe t2) with
                | RetF _ => t1
                | TauF t => Tau (par t1 t)
                | VisF o k => vis o (fun x => par t1 (k x))
                end).

  CoFixpoint par (t1 t2 : itree E R) := par_match par t1 t2.

  Lemma rewrite_par : forall t1 t2, par t1 t2 = par_match par t1 t2.
  Proof.
    intros. apply bisimulation_is_eq. revert t1 t2.
    ginit. gcofix CIH. intros. gstep. unfold par. constructor. red. intros.
    apply Reflexive_eqit_gen_eq. (* not sure why reflexivity doesn't work here *)
  Qed.

  Variant step : itree E R -> config -> itree E R -> config -> Prop :=
  | step_tau : forall t c, step (Tau t) c t c
  | step_nondet_true : forall k c, step (vis Or k) c (k true) c
  | step_nondet_false : forall k c, step (vis Or k) c (k false) c
  | step_get : forall k c, step (vis (Get _) k) c (k c) c
  | step_put : forall k c c', step (vis (Put _ c') k) c (k tt) c'
  .

  Lemma step_bind : forall (t1 t2 : itree E R) (c1 c2 : config) (k : R -> itree E R),
      step t1 c1 t2 c2 ->
      step (t1 >>= k) c1 (t2 >>= k) c2.
  Proof.
    intros. inversion H; subst.
    - pose proof (bind_tau _ t2 k) as bind_tau.
      apply bisimulation_is_eq in bind_tau. rewrite bind_tau. constructor.
    - pose proof (bind_vis _ _ (subevent _ Or) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
    - pose proof (bind_vis _ _ (subevent _ Or) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
    - pose proof (bind_vis _ _ (subevent _ (Get _)) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
    - pose proof (bind_vis _ _ (subevent _ (Put _ c2)) k0 k) as bind_vis.
      apply bisimulation_is_eq in bind_vis. rewrite bind_vis. constructor.
  Qed.

  Lemma step_ret_bind : forall (t1 t2 : itree E R) (c1 c2 : config) (r : R),
      step t1 c1 t2 c2 ->
      step (Ret r;; t1) c1 t2 c2.
  Proof.
    intros. pose proof (bind_ret_l r (fun _ => t1)) as bind_ret.
    apply bisimulation_is_eq in bind_ret. rewrite bind_ret. assumption.
  Qed.

  (* to handle the nondeterminism, par needs double the amount of steps *)
  Lemma par_step_left : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'', step (par t1 t') c t'' c /\ step t'' c (par t2 t') c'.
  Proof.
    inversion 1; subst;
      (rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor).
  Qed.
  Lemma par_step_right : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'', step (par t' t1) c t'' c /\ step t'' c (par t' t2) c'.
  Proof.
    inversion 1; subst;
      (rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor).
  Qed.

  Definition sep_step p q : Prop :=
    (forall x, dom p x -> dom q x) /\
    (forall r, p ⊥ r -> q ⊥ r).

  Instance sep_step_refl : Reflexive sep_step.
  Proof.
    split; repeat intro; tauto.
  Qed.

  Instance sep_step_trans : Transitive sep_step.
  Proof.
    repeat intro. destruct H. destruct H0. split; auto.
  Qed.

  Lemma sep_step_lte : forall p p' q, p <= p' -> sep_step p q -> sep_step p' q.
  Proof.
    intros. destruct H0. split; intros.
    - destruct H; auto.
    - apply H1. symmetry. symmetry in H2. eapply separate_antimonotone; eauto.
  Qed.

  Lemma sep_step_view : forall p q x y, sep_step p q -> view p x y -> view q x y.
  Proof.
    intros. destruct H. specialize (H1 (sym_upd_perm p) (separate_self_sym _)).
    apply H1; auto.
  Qed.

  Lemma sep_step_sep_conj_l : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (p1 * q) (p2 * q).
  Proof.
    intros p1 p2 q ? []. split.
    - intros x [? [? ?]]; auto. split; [| split]; auto.
    - intros; auto. symmetry in H2. symmetry. apply separate_sep_conj_perm; symmetry; auto.
      + apply H1. symmetry. eapply separate_sep_conj_perm_l; eauto.
      + symmetry. eapply separate_sep_conj_perm_r; eauto.
  Qed.
  Lemma sep_step_sep_conj_r : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (q * p1) (q * p2).
  Proof.
    intros p1 p2 q ? []. split.
    - intros x [? [? ?]]; auto. symmetry in H4. split; [| split]; auto; symmetry; auto.
    - intros; auto. symmetry in H2. symmetry. apply separate_sep_conj_perm; symmetry; auto.
      + symmetry. eapply separate_sep_conj_perm_l; eauto.
      + apply H1. symmetry. eapply separate_sep_conj_perm_r; eauto.
      + symmetry. auto.
  Qed.

  (* Lemma eq_sep_sep_conj : forall p1 p2 q, eq_sep p1 p2 -> *)
  (*                                    eq_sep (p1 * q) (p2 * q). *)
  (* Proof. *)
  (*   repeat intro. red in H. split; intros. *)
  (*   - symmetry in H0. *)
  (*     pose proof (separate_sep_conj_perm_l _ _ _ H0); symmetry in H1. rewrite H in H1. *)
  (*     pose proof (separate_sep_conj_perm_r _ _ _ H0); symmetry in H2. *)
  (*     split; intros. *)
  (*     + simpl. split; [| split]. *)
  (*       * apply H1; auto. *)
  (*       * apply H2; auto. *)
  (*       * left. admit. *)
  (*     + induction H3. *)
  (*       * destruct H3; [apply H1 | apply H2]; auto. *)
  (*       * etransitivity; eauto. *)
  (*   - admit. *)
  (* Admitted. *)

  Variant typing_perm_gen typing (p : perm) (t : itree E R) : Prop :=
  | cond : (forall c, dom p c ->
                 forall t' c',
                   step t c t' c' ->
                   (
                     (* we step to configs that satisfy the perm *)
                     (upd p c c') /\
                     (* we step to machines that are well-typed by some other perm that maintains separation *)
                     (exists p', typing p' t' /\ sep_step p p'))) -> (* todo add dom p' c' *)
           typing_perm_gen typing p t.

  Definition typing_perm p t := paco2 typing_perm_gen bot2 p t.

  Lemma typing_perm_gen_mon : monotone2 typing_perm_gen.
  Proof.
    repeat intro.
    inversion IN. econstructor. intros. specialize (H _ H0 _ _ H1).
    destruct H as [? [? [? ?]]]. split; eauto.
  Qed.
  Hint Resolve typing_perm_gen_mon : paco.

  Lemma rewrite_spin : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.

  Lemma typing_perm_lte : forall p q t, typing_perm p t -> p <= q -> typing_perm q t.
  Proof.
    intros. pcofix CIH. pstep. constructor; intros.
    pinversion H. edestruct H3; eauto. split; eauto.
    destruct H5 as [p' [? ?]]. exists p'. split.
    - pclearbot. left. eapply paco2_mon_bot; eauto.
    - eapply sep_step_lte; eauto.
  Qed.

  Definition typing P t := forall p, p ∈ P -> typing_perm p t.

  Lemma type_lte : forall P Q t, typing P t -> P ⊑ Q -> typing Q t.
  Proof.
    repeat intro. specialize (H p (H0 _ H1)). auto.
  Qed.

  Lemma type_spin : forall P, typing P ITree.spin.
  Proof.
    pcofix CIH. intros. pstep. constructor. intros. rewrite rewrite_spin in H1.
    inversion H1; subst. split; try reflexivity.
    exists p. split; eauto. eapply sep_step_refl; eauto.
  Qed.

  Lemma type_ret : forall P r, typing P (Ret r).
  Proof.
    repeat intro.
    pstep. constructor. intros. inversion H1.
  Qed.

  Lemma type_top : forall t, typing top_Perms t.
  Proof.
    repeat intro. pstep. constructor. intros. inversion H.
  Qed.

  Lemma type_tau : forall P t, typing P t -> typing P (Tau t).
  Proof.
    repeat intro. specialize (H _ H0). pinversion H.
    pfold. econstructor. intros.
    inversion H3; subst.
    split; intuition.
    exists p. split; auto. apply sep_step_refl.
  Qed.

  Lemma type_tau' : forall p t c, typing_perm p (Tau t) ->
                             dom p c ->
                             exists p', typing_perm p' t /\ sep_step p p'.
  Proof.
    intros. pinversion H.
    specialize (H1 _ H0 _ _ (step_tau _ _)). destruct H1 as [_ [p' [? ?]]].
    exists p'. pclearbot. split; [eapply paco2_mon_bot |]; eauto.
  Qed.

  (* Lemma type_tau'' : forall P t, typing P (Tau t) -> *)
  (*                           exists P', typing P' t. *)
  (* Proof. *)
  (*   intros. red in H. *)
  (* Qed. *)

  Lemma frame : forall P1 P2 t, typing P1 t -> typing (P1 ** P2) t.
  Proof.
    intros. eapply type_lte; eauto. apply lte_l_sep_conj_Perms.
  Qed.
  (* todo get proper instance working *)
  Lemma frame' : forall P1 P2 t, typing P2 t -> typing (P1 ** P2) t.
  Proof.
    intros. eapply type_lte; eauto. apply lte_r_sep_conj_Perms.
  Qed.

  Axiom par_tau : forall t1 t2, par t1 t2 = Tau (par t1 t2).
  Axiom par_ret_l : forall r t, par (Ret r) t = t.
  Axiom par_ret_r : forall r t, par t (Ret r) = t.
  Axiom par_tau_l : forall t1 t2, par (Tau t1) t2 = par t1 t2.
  Axiom par_tau_r : forall t1 t2, par t1 (Tau t2) = par t1 t2.

  Require Import Coq.Program.Equality.

  Lemma parallel_perm : forall p1 p2 t1 t2,
      typing_perm p1 t1 -> typing_perm p2 t2 -> typing_perm (p1 * p2) (par t1 t2).
  Proof.
    pcofix CIH. intros p1 p2 t1 t2 Ht1 Ht2.
    pstep. econstructor. intros c [Hdom1 [Hdom2 Hsep]] t' c' Hstep.
    rewrite rewrite_par in Hstep. unfold par_match in Hstep.
    dependent destruction Hstep; split; try reflexivity.
    { destruct (observe t1) eqn:?.
      - exists p2. split; [left; eapply paco2_mon_bot; eauto |].
        split; auto.
        + intros x [? [? ?]]; auto.
        + intros. symmetry. symmetry in H. eapply separate_sep_conj_perm_r; eauto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht1.
        pinversion Ht1. destruct (H _ Hdom1 _ _ (step_tau _ _)) as [? [p [? ?]]].
        exists (p * p2). pclearbot. split.
        + rewrite <- par_tau. eauto.
        + apply sep_step_sep_conj_l; auto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht1.
        destruct e; [destruct s | destruct n]; pinversion Ht1; exists (p1 * p2); split; intuition;
          left; pstep; constructor; intros ? [Hdom1' [Hdom2' Hsep']] ? ? Hstep;
            inversion Hstep; auto_inj_pair2; subst.
        + destruct (H _ Hdom1' _ _ (step_get _ _)) as [? [p [? ?]]]. pclearbot.
          split; intuition.
          exists (p * p2). split; auto. apply sep_step_sep_conj_l; auto.
        + destruct (H _ Hdom1' _ _ (step_put _ _ _)) as [? [p [? ?]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p * p2). split; auto. apply sep_step_sep_conj_l; auto.
        + destruct (H _ Hdom1' _ _ (step_nondet_true _ _)) as [? [p [? ?]]]. pclearbot.
          split; intuition.
          exists (p * p2). split; auto. apply sep_step_sep_conj_l; auto.
        + destruct (H _ Hdom1' _ _ (step_nondet_false _ _)) as [? [p [? ?]]]. pclearbot.
          split; intuition.
          exists (p * p2). split; auto. apply sep_step_sep_conj_l; auto.
    }
    { symmetry in Hsep. destruct (observe t2) eqn:?.
      - exists p1. split; [left; eapply paco2_mon_bot; eauto |].
        split; auto.
        + intros x [? [? ?]]; auto.
        + intros. symmetry. symmetry in H. eapply separate_sep_conj_perm_l; eauto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht2.
        pinversion Ht2. destruct (H _ Hdom2 _ _ (step_tau _ _)) as [? [p [? ?]]].
        exists (p1 * p). pclearbot. split.
        + rewrite <- par_tau. eauto.
        + apply sep_step_sep_conj_r; auto.
      - symmetry in Heqi. pose proof (bisimulation_is_eq _ _ (simpobs Heqi)) as Heqi'.
        rewrite Heqi' in Ht2.
        destruct e; [destruct s | destruct n]; pinversion Ht2; exists (p1 * p2); split; intuition;
          left; pstep; constructor; intros ? [Hdom1' [Hdom2' Hsep']] ? ? Hstep;
            inversion Hstep; auto_inj_pair2; subst.
        + destruct (H _ Hdom2' _ _ (step_get _ _)) as [? [p [? ?]]]. pclearbot.
          split; intuition.
          exists (p1 * p). split; auto. apply sep_step_sep_conj_r; auto.
        + destruct (H _ Hdom2' _ _ (step_put _ _ _)) as [? [p [? ?]]]. pclearbot.
          split; [constructor |]; auto.
          exists (p1 * p). split; auto. apply sep_step_sep_conj_r; auto.
        + destruct (H _ Hdom2' _ _ (step_nondet_true _ _)) as [? [p [? ?]]]. pclearbot.
          split; intuition.
          exists (p1 * p). split; auto. apply sep_step_sep_conj_r; auto.
        + destruct (H _ Hdom2' _ _ (step_nondet_false _ _)) as [? [p [? ?]]]. pclearbot.
          split; intuition.
          exists (p1 * p). split; auto. apply sep_step_sep_conj_r; auto.
      }
  Qed.

  Lemma parallel : forall P1 P2 t1 t2,
      typing P1 t1 -> typing P2 t2 -> typing (P1 ** P2) (par t1 t2).
  Proof.
    intros P1 P2 t1 t2 Ht1 Ht2 p [p1 [p2 [? [? ?]]]].
    assert (Hp1: p ∈ P1).
    { eapply Perms_upwards_closed; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm. }
    assert (Hp2: p ∈ P2).
    { eapply Perms_upwards_closed; eauto. etransitivity; eauto. apply lte_r_sep_conj_perm. }
    specialize (Ht1 _ H).
    specialize (Ht2 _ H0). eapply typing_perm_lte; eauto. eapply parallel_perm; eauto.
  Qed.
End ts.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Import ITreeNotations.
Import ITree.Basics.Basics.Monads.

Definition test : itree (stateE config +' _) unit :=
  par
    (x <- (trigger (Get _)) ;; (trigger (Put _ x)))
    (par (vis (Get _) (fun x => Ret tt))
         (Ret tt)).

Compute (burn 10 test).

(* Eval cbv in (burn 10 (step (trigger (Put _ 0)) 1)). *)
(* Eval cbn in (burn 10 (step test 1)). *)
Eval cbn in (burn 10 (run_state test 1)).
