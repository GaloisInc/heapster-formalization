From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     Relations.Relation_Operators
     Relations.Operators_Properties.

Import ListNotations.

(* TODO: move to another file, this file is for abstract config stuff *)
Variant Lifetime := invalid | current | finished.
Record config : Type :=
  {
    l : nat -> Lifetime;
  }.

(* A single permission *)
Record perm : Type :=
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

Instance Proper_eq_perm_lte_perm : Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) lte_perm.
Proof.
  repeat intro. subst. etransitivity; eauto. etransitivity; eauto.
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

Definition read_perm p := forall x y, upd p x y -> x = y.

Lemma separate_self_read : forall p, read_perm p -> p ⊥ p.
Proof.
  intros. split; intros x y Hupd; specialize (H _ _ Hupd); subst; reflexivity.
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

Lemma sep_conj_perm_monotone : forall p p' q q',
    p' <= p -> q' <= q -> p' * q' <= p * q.
Proof.
  constructor; intros; simpl.
  - destruct H1 as [? [? ?]]; split; [| split]; eauto.
    eapply separate_antimonotone; eauto.
    symmetry. symmetry in H3. eapply separate_antimonotone; eauto.
  - split.
    + apply H. apply H1.
    + apply H0. apply H1.
  - induction H1.
    + constructor. destruct H1; eauto.
    + econstructor 2; eauto.
Qed.

(* Lemma sep_conj_perm_monotone_l : forall p p' q, *)
(*     p' <= p -> p' * q <= p * q. *)
(* Proof. *)
(*   constructor; intros; simpl. *)
(*   - destruct H0 as [? [? ?]]; split; [| split]; auto. *)
(*     + apply H; auto. *)
(*     + symmetry. symmetry in H2. eapply separate_antimonotone; eauto. *)
(*   - split. *)
(*     + apply H. apply H0. *)
(*     + apply H0. *)
(*   - induction H0. *)
(*     + constructor. destruct H0; auto. left. apply H. auto. *)
(*     + econstructor 2; eauto. *)
(* Qed. *)

(* Lemma sep_conj_perm_monotone_r : forall p q q', *)
(*     q' <= q -> p * q' <= p * q. *)
(* Proof. *)
(*   constructor; intros; simpl. *)
(*   - destruct H0 as [? [? ?]]; split; [| split]; auto. *)
(*     + apply H; auto. *)
(*     + eapply separate_antimonotone; eauto. *)
(*   - split. *)
(*     + apply H0. *)
(*     + apply H. apply H0. *)
(*   - induction H0. *)
(*     + constructor. destruct H0; auto. right. apply H. auto. *)
(*     + econstructor 2; eauto. *)
(* Qed. *)

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

(* Set equality *)
Definition eq_Perms (P Q : Perms) : Prop := P ⊑ Q /\ Q ⊑ P.
Notation "P ≡≡ Q" := (eq_Perms P Q) (at level 60).

Instance Equivalence_eq_Perms : Equivalence eq_Perms.
Proof.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct H; split; auto.
  - destruct H, H0. split; etransitivity; eauto.
Qed.

Instance Proper_eq_Perms_lte_Perms :
  Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) lte_Perms.
Proof.
  do 5 red. intros. etransitivity. apply H. etransitivity. apply H1. apply H0.
Qed.

Program Definition sep_conj_Perms (P Q : Perms) : Perms :=
  {|
    in_Perms := fun r => exists p q, p ∈ P /\ q ∈ Q /\ p * q <= r
  |}.
Next Obligation.
  exists H, H1. split; [| split]; auto. etransitivity; eauto.
Qed.
Notation "P ** Q" := (sep_conj_Perms P Q) (at level 51, right associativity).

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

Lemma sep_conj_Perms_monotone : forall P P' Q Q', P' ⊑ P -> Q' ⊑ Q -> P' ** Q' ⊑ P ** Q.
Proof.
  repeat intro. destruct H1 as [? [? [? [? ?]]]].
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
    apply sep_conj_perm_monotone; intuition.
  - rename p into p'. destruct H as [p [qr [? [? ?]]]].
    destruct H0 as [q [r [? [? ?]]]].
    exists (p * q), r.
    split; auto. apply sep_conj_Perms_perm; auto. split; auto.
    rewrite sep_conj_perm_assoc.
    etransitivity; eauto.
    apply sep_conj_perm_monotone; intuition.
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
Notation "P ⊦ Q" := (entails_Perms P Q) (at level 60).

Instance entails_Perms_preorder : PreOrder entails_Perms.
Proof.
  constructor; repeat intro; auto.
Qed.

Instance Proper_eq_Perms_entails_Perms :
  Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) entails_Perms.
Proof.
  do 6 red. intros. rewrite H. rewrite H0. auto.
Qed.

Instance Proper_eq_Perms_sep_conj_Perms :
  Proper (eq_Perms ==> eq_Perms ==> eq_Perms) sep_conj_Perms.
Proof.
  repeat intro. etransitivity.
  - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H.
  - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H; reflexivity.
Qed.

Definition impl_Perms P Q := meet_Perms (fun R => R ** P ⊦ Q).

Lemma adjunction : forall P Q R, P ** Q ⊦ R <-> P ⊦ (impl_Perms Q R).
Proof.
  intros. split; intros.
  - red. red. intros. simpl. exists P. auto.
  - apply (sep_conj_Perms_monotone _ _ Q Q) in H; intuition.
    red. etransitivity; [ | apply H ].
    unfold impl_Perms.
    rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max. intros P' [? [? ?]]. subst. auto.
Qed.

Program Definition when (n : nat) (p : perm) : perm :=
  {|
    dom := fun x => l x n = current /\ dom p x;
    view := fun x y => x = y \/
                    l x n <> current /\ l y n <> current \/
                    l x n = current /\ l y n = current /\ view p x y;
    upd := fun x y => x = y \/
                    l x n <> current /\ l y n <> current \/
                    l x n = current /\ l y n = current /\ upd p x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - left; auto.
  - destruct H as [| [[? ?] | [? [? ?]]]]; auto.
    right; right. split; [| split]; auto. symmetry. auto.
  - destruct H as [| [[? ?] | [? [? ?]]]], H0 as [| [[? ?] | [? [? ?]]]]; subst; intuition.
    right; right. split; [| split]; auto. etransitivity; eauto.
Qed.
Next Obligation.
  split; intros [].
  - destruct H as [| [[? ?] | [? [? ?]]]]; subst; intuition.
    eapply dom_respects; eauto. symmetry; auto.
  - destruct H as [| [[? ?] | [? [? ?]]]]; subst; intuition.
    eapply dom_respects; eauto.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  destruct H as [| [[? ?] | [? [? ?]]]], H0 as [| [[? ?] | [? [? ?]]]]; subst; intuition.
  right; right. split; [| split]; auto. etransitivity; eauto.
Qed.

Program Definition owned (n : nat) (p : perm) : perm :=
  {|
    dom := fun x => l x n = current;
    view := fun x y => x = y \/
                    (* l x n <> finished /\ l y n <> finished \/ *)
                    l x n = finished /\ l y n = finished /\ view p x y;
    upd := clos_trans _ (fun x y =>
                           x = y \/
                           (l x n = current /\ l y n = finished /\ forall n', n <> n' -> l x n' = l y n') \/
                           (l x n = finished /\ l y n = finished /\ upd p x y));
  |}.
Next Obligation.
  constructor; repeat intro; auto.
  - destruct H as [| [? [? ?]]]; auto.
    right. split; [| split]; auto. symmetry. auto.
  - destruct H as [| [? [? ?]]], H0 as [| [? [? ?]]]; subst; intuition.
    right. split; [| split]; auto. etransitivity; eauto.
  (* - destruct H as [| [[? ?] | [? [? ?]]]]; auto. *)
  (*   right; right. split; [| split]; auto. symmetry. auto. *)
  (* - destruct H as [| [[? ?] | [? [? ?]]]], H0 as [| [[? ?] | [? [? ?]]]]; subst; intuition. *)
  (*   right; right. split; [| split]; auto. etransitivity; eauto. *)
Qed.
Next Obligation.
  split; intros.
  - destruct H as [| [? [? ?]]]; subst; intuition.
    rewrite H in H0. discriminate H0.
  - destruct H as [| [? [? ?]]]; subst; auto.
    rewrite H1 in H0. discriminate H0.
Qed.
Next Obligation.
  constructor; repeat intro.
  - constructor. auto.
  - econstructor 2; eauto.
Qed.

Lemma lifetimes_sep n p : when n p ⊥ owned n p.
Proof.
  constructor; intros; simpl in *.
  - induction H.
    + destruct H as [? | [[? [? ?]] | [? [? ?]]]]; subst; auto.
      * admit.
      * right; left. split; admit.
    + admit.
  -
Qed.
