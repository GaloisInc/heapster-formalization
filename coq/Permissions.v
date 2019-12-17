From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     Relations.Relation_Operators.

Import ListNotations.

Definition config : Type := nat.

Lemma PER_refl {A} (p : A -> A -> Prop) `{PER _ p} : forall x y, p x y -> p x x.
Proof.
  intros. etransitivity; eauto; try symmetry; eauto.
Qed.

(* A single permission *)
Record perm :=
  mkPerm {
      view : config -> config -> Prop;  (* PER over configs *)
      view_PER : PER view;
      upd : config -> config -> Prop;  (* allowed transitions *)
      upd_PO : PreOrder upd;
    }.

Instance view_is_PER p : PER (view p) := view_PER p.
Instance upd_is_preorder p : PreOrder (upd p) := upd_PO p.

Record lte_perm (p q:perm) : Prop :=
  {
    view_inc : forall x y, (view q) x y -> (view p) x y;
    upd_inc : forall x y, (upd p) x y -> (upd q) x y;
  }.

Notation "p <= q" := (lte_perm p q).

Instance lte_perm_is_PreOrder : PreOrder lte_perm.
Proof.
  constructor; constructor; auto; intros.
  - apply H. apply H0. assumption.
  - apply H0. apply H. assumption.
Qed.

(* Equality of permissions = the symmetric closure of the ordering *)
Definition eq_perm p q : Prop := p <= q /\ q <= p.

Program Definition bottom_perm : perm :=
  {|
    view := fun x y => True;
    upd  := fun x y => x = y;
  |}.
Next Obligation.
  constructor; intro; intros; trivial.
Defined.
Next Obligation.
  constructor; intro; intros; [ trivial | transitivity y; assumption ].
Defined.

Lemma bottom_perm_is_bottom : forall p, bottom_perm <= p.
Proof. constructor; simpl; intuition. rewrite H. reflexivity. Qed.

Program Definition top_perm : perm :=
  {|
    view := fun x y => False;
    upd  := fun x y => True;
  |}.
Next Obligation.
  constructor; intro; intros; trivial.
Defined.
Next Obligation.
  constructor; intro; intros; trivial.
Defined.

Lemma top_perm_is_top : forall p, p <= top_perm.
Proof. constructor; simpl; intuition. Qed.

(* Program Definition join_perm_gen (ps : perm -> Prop) (p: exists p, ps p) : perm := *)
(*   {| *)
(*     view := fun x y => forall p, ps p -> view p x y; *)
(*     upd  := clos_trans _ (fun x y => exists p, ps p /\ upd p x y) *)
(*   |}. *)
(* Next Obligation. *)
(*   constructor; repeat intro. *)
(*   - symmetry. auto. *)
(*   - transitivity y; auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; repeat intro. *)
(*   - constructor. exists p. split; intuition. *)
(*   - destruct H0, H1. *)
(*     + econstructor 2; constructor; eauto. *)
(*     + econstructor 2. left. eassumption. econstructor 2; eauto. *)
(*     + econstructor 2; eauto. econstructor 2; eauto. left. assumption. *)
(*     + repeat (econstructor 2; eauto). *)
(* Qed. *)

(* Definition join_perm (p q : perm) : perm. *)
(*   apply join_perm_gen with (ps := (fun r => r = p \/ r = q)). exists p. left. auto. *)
(* Defined. *)

Program Definition join_perm (p q:perm) : perm :=
  {|
    view := fun x y => view p x y /\ view q x y;
    upd  := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y))
  |}.
Next Obligation.
  constructor.
  - constructor; destruct H; symmetry; auto.
  - constructor; destruct H, H0; transitivity y; auto.
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
    p <= (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.

Lemma lte_r_join_perm : forall p q,
    q <= (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.

Lemma join_perm_min : forall p q r,
    p <= r ->
    q <= r ->
    join_perm p q <= r.
Proof.
  intros p q r [] []. constructor; intros; simpl in *; auto.
  induction H.
  - destruct H; auto.
  - transitivity y; auto.
Qed.

Lemma join_perm_commut : forall p q,
    eq_perm (join_perm p q) (join_perm q p).
Proof.
  split; intros.
  - constructor; intros.
    + destruct H. constructor; auto.
    + induction H.
      * destruct H; constructor; auto.
      * etransitivity; eauto.
  - constructor; intros.
    + destruct H. constructor; auto.
    + induction H.
      * destruct H; constructor; auto.
      * etransitivity; eauto.
Qed.

Lemma join_perm_assoc : forall p q r,
    eq_perm (join_perm p (join_perm q r)) (join_perm (join_perm p q) r).
Proof.
  split; intros.
  - constructor; intros.
    + destruct H as [[? ?] ?].
      constructor; auto. constructor; auto.
    + induction H; try solve [etransitivity; eauto].
      destruct H.
      * constructor. left. constructor. left. auto.
      * induction H; try solve [etransitivity; eauto].
        destruct H.
        -- constructor. left. constructor. right. auto.
        -- constructor. right. auto.
  - constructor; intros.
    + destruct H as [? [? ?]].
      constructor; auto. constructor; auto.
    + induction H; try solve [etransitivity; eauto].
      destruct H.
      * induction H; try solve [etransitivity; eauto].
        destruct H.
        -- constructor. left. auto.
        -- constructor. right. constructor. left. auto.
      * constructor. right. constructor. right. auto.
Qed.

Lemma join_perm_idem : forall p, eq_perm (join_perm p p) p.
Proof.
  split; intros.
  - constructor; intros.
    + constructor; auto.
    + induction H; try solve [etransitivity; eauto].
      destruct H; auto.
  - constructor; intros.
    + destruct H; auto.
    + constructor. left. auto.
Qed.

Program Definition meet_perm (p q:perm) : perm :=
  {|
    view := clos_trans _ (fun x y => (view p x y) \/ (view q x y)) ;
    upd  := fun x y => (upd p x y) /\ (upd q x y) ;
  |}.
Next Obligation.
  constructor.
  - repeat intro. induction H.
    + constructor. destruct H; symmetry in H; auto.
    + econstructor 2; eauto.
  - repeat intro. econstructor 2; eauto.
Qed.
Next Obligation.
  constructor.
  - constructor; reflexivity.
  - intros x y z [] []. split; etransitivity; eauto.
Qed.

Lemma lte_meet_perm_l : forall p q,
    meet_perm p q <= p.
Proof.
  intros. constructor.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma lte_meet_perm_r : forall p q,
    meet_perm p q <= q.
Proof.
  intros. constructor.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma meet_perm_max : forall p q r,
    r <= p ->
    r <= q ->
    r <= meet_perm p q.
Proof.
  intros p q r [] []. constructor; intros; simpl in *; auto.
  induction H.
  - destruct H; auto.
  - transitivity y; auto.
Qed.

Lemma meet_perm_commut: forall p q, eq_perm (meet_perm p q) (meet_perm q p).
Proof.
  split; intros.
  - constructor; intros.
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
Qed.

Definition separate (p q : perm) : Prop :=
  (forall x y, view p x x -> upd q x y -> view p x y) /\
  (forall x y, view q x x -> upd p x y -> view q x y).

Lemma sep_self : forall p,
    (forall x y, upd p x y -> x = y) -> separate p p.
Proof.
  split; repeat intro; apply H in H1; subst; auto.
Qed.

Definition separate' (p q : perm) : Prop :=
  (forall x y z, view p x y -> upd q y z -> view p x z) /\
  (forall x y z, view q x y -> upd p y z -> view q x z).

Lemma separate_separate' : forall p q,
    separate p q -> separate' p q.
Proof.
  intros p q [H H']. split; repeat intro.
  - etransitivity; eauto. apply H; auto. eapply PER_refl; eauto; intuition; symmetry; eauto.
  - etransitivity; eauto. apply H'; auto. eapply PER_refl; eauto; intuition; symmetry; eauto.
Qed.

Lemma separate'_separate : forall p q,
    separate' p q -> separate p q.
Proof.
  intros p q [H H']. split; repeat intro; eauto.
Qed.

Record permConj :=
  {
    in_permConj : perm -> Prop;
  }.

Program Definition singleton_permConj (p : perm) : permConj :=
  {|
    in_permConj := fun q => q = p;
  |}.

Program Definition permConj_perm (pc : permConj) : perm :=
  {|
    view := fun x y => forall p, in_permConj pc p ->
                         view p x y /\
                         forall q, in_permConj pc q -> q <> p -> separate p q;
    upd := fun x y => x = y \/ clos_trans _ (fun x y => exists p, in_permConj pc p /\ upd p x y) x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - destruct (H p H0). split; try symmetry; auto.
    (* intros. destruct (H2 q); eauto. *)
  - destruct (H p H1) as [? ?]. destruct (H0 p H1) as [? ?].
    split. etransitivity; eauto.
    intros.
    apply H3; auto.
    (* destruct (H3 q H6 H7), (H5 q H6 H7). repeat (split; try etransitivity; eauto). *)
Qed.
Next Obligation.
  constructor.
  - constructor 1. reflexivity. (* exists p; split; intuition. *)
  - repeat intro. destruct H, H0; subst.
    + left. auto.
    + right. auto.
    + right. auto.
    + right. econstructor 2; eauto.
Qed.

Lemma lte_permConj_perm : forall pc p, in_permConj pc p -> p <= permConj_perm pc.
Proof.
  intros. constructor; intros.
  - destruct (H0 p H). auto.
  - simpl. right. constructor. exists p. split; auto.
Qed.

(* Subset *)
Definition lte_permConj pc1 pc2 : Prop := forall p, in_permConj pc1 p -> in_permConj pc2 p.

Instance lte_permConj_is_PreOrder : PreOrder lte_permConj.
Proof.
  constructor; repeat intro; auto.
Qed.

Notation "p ⊆ q" := (lte_permConj p q) (at level 20).

(* todo name *)
Lemma permConj_perm_lte_perm : forall (pc1 pc2 : permConj),
    pc1 ⊆ pc2 ->
    permConj_perm pc1 <= permConj_perm pc2.
Proof.
  repeat intro. constructor; repeat intro; auto.
  split. apply H0; auto. intros. apply H0; auto.
  destruct H0; subst; intuition. right. induction H0.
  - destruct H0 as [? [? ?]]. constructor. exists x0. split; auto.
  - econstructor 2; eauto.
Qed.

Definition eq_permConj pc1 pc2 := pc1 ⊆ pc2 /\ pc2 ⊆ pc1.

Program Definition bottom_permConj :=
  {|
    in_permConj := fun p => False;
  |}.

Lemma bottom_permConj_is_bottom : forall pc, bottom_permConj ⊆ pc.
Proof.
  repeat intro. inversion H.
Qed.

Lemma bottom_permConj_perm : eq_perm (permConj_perm bottom_permConj) bottom_perm.
Proof.
  constructor; constructor; repeat intro; simpl in *; auto.
  - inversion H0.
  - destruct H; auto. induction H; subst; auto.
    destruct H as [_ [[] _]].
Qed.

Program Definition top_permConj :=
  {|
    in_permConj := fun p => True;
  |}.

Lemma top_permConj_is_top : forall pc, pc ⊆ top_permConj.
Proof.
  repeat intro. constructor.
Qed.

Lemma top_permConj_perm : eq_perm (permConj_perm top_permConj) top_perm.
Proof.
  constructor; constructor; repeat intro; simpl in *; auto.
  - inversion H.
  - destruct (H top_perm I). destruct H0.
  - right. constructor. exists top_perm. split; auto.
Qed.

(* Union *)
Program Definition join_permConj pc1 pc2 : permConj :=
  {|
    in_permConj := fun p => in_permConj pc1 p \/ in_permConj pc2 p;
  |}.

Lemma lte_l_join_permConj : forall pc1 pc2,
    pc1 ⊆ join_permConj pc1 pc2.
Proof.
  repeat intro. left. auto.
Qed.

Lemma lte_r_join_permConj : forall pc1 pc2,
    pc2 ⊆ join_permConj pc1 pc2.
Proof.
  repeat intro. right. auto.
Qed.

Lemma join_permConj_min : forall pc1 pc2 pc3,
    pc1 ⊆ pc3 ->
    pc2 ⊆ pc3 ->
    join_permConj pc1 pc2 ⊆ pc3.
Proof.
  repeat intro. destruct H1; auto.
Qed.

Lemma join_permConj_commut : forall pc1 pc2,
    eq_permConj (join_permConj pc1 pc2) (join_permConj pc2 pc1).
Proof.
  split; repeat intro; (destruct H; [ right | left ]; auto).
Qed.

Lemma join_permConj_assoc : forall pc1 pc2 pc3,
    eq_permConj (join_permConj pc1 (join_permConj pc2 pc3))
                (join_permConj (join_permConj pc1 pc2) pc3).
Proof.
  split; repeat intro.
  - destruct H as [? | [? | ?]].
    + left. left. auto.
    + left. right. auto.
    + right. auto.
  - destruct H as [[? | ?] | ?].
    + left. auto.
    + right. left. auto.
    + right. right. auto.
Qed.

Lemma join_permConj_idem : forall pc, eq_permConj (join_permConj pc pc) pc.
Proof.
  split; repeat intro.
  - destruct H; auto.
  - left. auto.
Qed.

(* Intersection *)
Program Definition meet_permConj pc1 pc2 : permConj :=
  {|
    in_permConj := fun p => in_permConj pc1 p /\ in_permConj pc2 p;
  |}.

Lemma lte_meet_permConj_l : forall pc1 pc2,
    meet_permConj pc1 pc2 ⊆ pc1.
Proof.
  repeat intro. destruct H. auto.
Qed.

Lemma lte_meet_permConj_r : forall pc1 pc2,
    meet_permConj pc1 pc2 ⊆ pc2.
Proof.
  repeat intro. destruct H. auto.
Qed.

Lemma meet_permConj_max : forall pc1 pc2 pc3,
    pc3 ⊆ pc1 ->
    pc3 ⊆ pc2 ->
    pc3 ⊆ meet_permConj pc1 pc2.
Proof.
  repeat intro. constructor; auto.
Qed.

Lemma meet_permConj_commut : forall pc1 pc2,
    eq_permConj (meet_permConj pc1 pc2) (meet_permConj pc2 pc1).
Proof.
  split; repeat intro; destruct H; constructor; auto.
Qed.

Lemma meet_permConj_assoc : forall pc1 pc2 pc3,
    eq_permConj (meet_permConj pc1 (meet_permConj pc2 pc3))
                (meet_permConj (meet_permConj pc1 pc2) pc3).
Proof.
  split; repeat intro.
  - destruct H as [? [? ?]]. constructor; [ constructor | ]; auto.
  - destruct H as [[? ?] ?]. constructor; [ | constructor ]; auto.
Qed.

Lemma meet_permConj_idem : forall pc, eq_permConj (meet_permConj pc pc) pc.
Proof.
  split; repeat intro.
  - destruct H; auto.
  - constructor; auto.
Qed.

Definition sep_conj_permConj := join_permConj.

Definition separate_permConj pc1 pc2 : Prop := separate (permConj_perm pc1)
                                                     (permConj_perm pc2).


Lemma sep_conj_permConj_top_absorb : forall pc,
    eq_permConj (sep_conj_permConj top_permConj pc) top_permConj.
Proof.
  split; repeat intro; simpl; auto.
Qed.

Lemma sep_conj_permConj_bottom_identity : forall pc,
    eq_permConj (sep_conj_permConj bottom_permConj pc) pc.
Proof.
  split; repeat intro; simpl in *; auto.
  destruct H; auto. inversion H.
Qed.

(* Perms = upwards-closed sets of conjunctive permission sets *)
Record Perms :=
  {
    in_Perms : permConj -> Prop;
    Perms_upwards_closed : forall pc1 pc2, in_Perms pc1 -> pc1 ⊆ pc2 -> in_Perms pc2
  }.

(* superset *)
Definition lte_Perms (P Q : Perms) : Prop :=
  forall p, in_Perms Q p -> in_Perms P p.

Instance lte_Perms_is_preorder : PreOrder lte_Perms.
Proof.
  constructor; repeat intro; auto.
Qed.

Notation "P ⊑ Q" := (lte_Perms P Q) (at level 20, right associativity).

(* The least Perms set containing a given p *)
Program Definition singleton_Perms pc1 : Perms :=
  {|
    in_Perms := fun pc2 => pc1 ⊆ pc2
  |}.
Next Obligation.
  transitivity pc0; assumption.
Defined.

(* Complete meet of Perms sets = union *)
Program Definition meet_Perms (Ps : Perms -> Prop) : Perms :=
  {|
    in_Perms := fun pc => exists P, Ps P /\ in_Perms P pc
  |}.
Next Obligation.
  exists H. split; auto.
  apply (Perms_upwards_closed _ pc1); try assumption.
Defined.

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

Program Definition sep_conj_Perms (P Q : Perms) : Perms :=
  {|
    in_Perms := fun r => exists p q, in_Perms P p /\ in_Perms Q q /\ sep_conj_permConj p q ⊆ r
  |}.
Next Obligation.
  exists H, H1. split; auto. split; auto. etransitivity; eauto.
Defined.

Lemma lte_l_sep_conj_Perms : forall P Q, P ⊑ sep_conj_Perms P Q.
Proof.
  intros P Q p' ?. destruct H as [p [q [? [? ?]]]].
  eapply Perms_upwards_closed; eauto.
  etransitivity; eauto. apply lte_l_join_permConj.
Qed.

Lemma lte_r_sep_conj_Perms : forall P Q, Q ⊑ sep_conj_Perms P Q.
Proof.
  intros P Q q' ?. destruct H as [p [q [? [? ?]]]].
  eapply Perms_upwards_closed; eauto.
  etransitivity; eauto. apply lte_r_join_permConj.
Qed.

Lemma sep_conj_Perms_bottom_identity : forall P, eq_Perms (sep_conj_Perms bottom_Perms P) P.
Proof.
  constructor; repeat intro.
  - exists bottom_permConj, p. split; simpl; [auto | split; auto].
    apply sep_conj_permConj_bottom_identity.
  - destruct H as [? [? [_ [? ?]]]].
    eapply (Perms_upwards_closed P); eauto.
    etransitivity; eauto. apply lte_r_join_permConj.
Qed.

Lemma sep_conj_Perms_top_absorb : forall P, eq_Perms (sep_conj_Perms top_Perms P) top_Perms.
Proof.
  constructor; repeat intro.
  - inversion H.
  - destruct H as [? [_ [[] _]]].
Qed.

(* P ⊆ Q *)
Definition entails_Perms P Q := Q ⊑ P.

Definition impl_Perms P Q := meet_Perms (fun R => entails_Perms (sep_conj_Perms R P) Q).

Lemma sep_conj_Perms_monotonic : forall P Q R, P ⊑ Q -> sep_conj_Perms P R ⊑ sep_conj_Perms Q R.
Proof.
  repeat intro. destruct H0 as [? [? [? [? ?]]]].
  exists x, x0. auto.
Qed.

Lemma sep_conj_Perms_permConj: forall P Q p q, in_Perms P p ->
                       in_Perms Q q ->
                       in_Perms (sep_conj_Perms P Q) (sep_conj_permConj p q).
Proof.
  intros. exists p, q. split; auto. split; auto. reflexivity.
Qed.

Lemma sep_conj_Perms_comm : forall P Q, eq_Perms (sep_conj_Perms P Q)
                                            (sep_conj_Perms Q P).
Proof.
  split; repeat intro.
  - destruct H as [q [p' [? [? ?]]]].
    exists p', q. repeat split; auto. repeat intro. apply H1. destruct H2; [right | left]; auto.
  - destruct H as [p' [q [? [? ?]]]].
    exists q, p'. repeat split; auto. repeat intro. apply H1. destruct H2; [right | left]; auto.
Qed.

Lemma sep_conj_Perms_assoc : forall P Q R, eq_Perms (sep_conj_Perms P (sep_conj_Perms Q R))
                                               (sep_conj_Perms (sep_conj_Perms P Q) R).
Proof.
  split; repeat intro.
  - rename p into p'. destruct H as [pq [r [? [? ?]]]].
    destruct H as [p [q [? [? ?]]]].
    exists p, (sep_conj_permConj q r).
    split; auto. split; auto. apply sep_conj_Perms_permConj; auto. repeat intro.
    apply H1. destruct H4.
    + left. apply H3. left. auto.
    + destruct H4.
      * left. apply H3. right. auto.
      * right. auto.
  - rename p into p'. destruct H as [p [qr [? [? ?]]]].
    destruct H0 as [q [r [? [? ?]]]].
    exists (sep_conj_permConj p q), r.
    split; auto. apply sep_conj_Perms_permConj; auto. split; auto.
    repeat intro. apply H1. destruct H4.
    + destruct H4.
      * left. auto.
      * right. apply H3. left. auto.
    + right. apply H3. right. auto.
Qed.

Lemma sep_conj_Perms_meet_commute : forall (Ps : Perms -> Prop) P,
    eq_Perms (sep_conj_Perms (meet_Perms Ps) P)
             (meet_Perms (fun Q => exists P', Q = sep_conj_Perms P' P /\ Ps P')).
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

Instance eq_Perms_flip_impl : forall P, Proper (eq_Perms ==> Basics.flip Basics.impl) (lte_Perms P).
Proof.
  intros P Q R [] ?. etransitivity; eauto.
Qed.

Lemma adjunction : forall P Q R, entails_Perms (sep_conj_Perms P Q) R <->
                            entails_Perms P (impl_Perms Q R).
Proof.
  intros. split; intros.
  - red. red. intros. simpl. exists P. auto.
  - apply (sep_conj_Perms_monotonic _ _ Q) in H.
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

  Context {E : Type -> Type}.
  Context {HasStateConfig : stateE config -< E}.
  Context {HasNondet : nondetE -< E}.

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
    intros. pose proof (bind_ret r (fun _ => t1)) as bind_ret.
    apply bisimulation_is_eq in bind_ret. rewrite bind_ret. assumption.
  Qed.

  (* to handle the nondeterminism, par needs double the amount of steps *)
  Lemma par_step_left : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'', step (par t1 t') c t'' c /\ step t'' c (par t2 t') c'.
  Proof.
    intros. inversion H; subst;
              (rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor).
  Qed.
  Lemma par_step_right : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'', step (par t' t1) c t'' c /\ step t'' c (par t' t2) c'.
  Proof.
    intros. inversion H; subst;
              (rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor).
  Qed.

  Lemma test_view : forall pc1 pc2 x y, pc1 ⊆ pc2 -> view (permConj_perm pc2) x y ->
                               view (permConj_perm pc1) x y.
  Proof.
    repeat intro. split; intros; apply H0; auto.
  Qed.
  Lemma test_upd : forall pc1 pc2 x y, pc1 ⊆ pc2 -> upd (permConj_perm pc1) x y ->
                               upd (permConj_perm pc2) x y.
  Proof.
    repeat intro. destruct H0; subst; intuition.
    simpl. right. induction H0.
    - destruct H0 as [p [? ?]]. left. exists p. split; auto.
    - eright; eauto.
  Qed.

  Definition sep P' pc c c' :=
    forall pc_s,
      view (permConj_perm (sep_conj_permConj pc pc_s)) c c ->
      exists pc', in_Perms P' pc' /\
             view (permConj_perm (sep_conj_permConj pc' pc_s)) c' c'.

  Definition sep' P' pc (c c' : config) : Prop :=
    forall pc_s, separate_permConj pc pc_s ->
            exists pc', in_Perms P' pc' /\ separate_permConj pc' pc_s /\ view (permConj_perm pc') c' c'.

  Definition eq_sep P1 P2 pc1 : Prop :=
    in_Perms P1 pc1 ->
    exists pc2, in_Perms P2 pc2 /\
               (forall pc, separate_permConj pc2 pc -> separate_permConj pc1 pc)(*  /\ *)
               (* (forall pc, separate_permConj pc2 pc -> separate_permConj pc1 pc) *).

  Lemma eq_sep_refl : forall P pc, in_Perms P pc -> eq_sep P P pc.
  Proof.
    eexists; eauto.
  Qed.

  Lemma eq_sep_trans : forall P Q R pc, eq_sep P Q pc -> (forall q, eq_sep Q R q) -> eq_sep P R pc.
  Proof.
    repeat intro. specialize (H H1). destruct H as [q [? ?]].
    specialize (H0 q H). destruct H0 as [r [? ?]].
    exists r. split; auto.
  Qed.

  Lemma eq_sep_lte : forall P Q R pc, P ⊑ Q -> eq_sep P R pc -> eq_sep Q R pc.
  Proof.
    repeat intro.
    red in H0. specialize (H0 (H _ H1)). destruct H0 as [pc' [? ?]].
    exists pc'. split; auto.
  Qed.

  Lemma test : forall pc1 pc2 pc3 pc, sep_conj_permConj pc1 pc2 ⊆ pc ->
                                 separate_permConj pc pc3 ->
                                 separate_permConj pc2 pc3.
  Proof.
    intros. red. red in H0.
    destruct H0. split; intros; simpl; intros; (split; [ | apply H2; auto]).
    - red in H. simpl in H. apply H0; auto; intros. (* cannot conclude... *)
      eapply view_inc; eauto.
      admit.
    - apply H1; auto. eapply upd_inc; eauto. apply permConj_perm_lte_perm.
      etransitivity; eauto. apply lte_r_join_permConj.
  Abort.

  Lemma test : forall P1 P2 Q1 Q2 pc1 pc2, eq_sep P1 Q1 pc1 ->
                                      eq_sep P2 Q2 pc2 ->
                                      eq_sep (sep_conj_Perms P1 P2)
                                             (sep_conj_Perms Q1 Q2)
                                             (sep_conj_permConj pc1 pc2).
  Proof.
    repeat intro. destruct H1 as [p1 [p2 [? [? ?]]]]. red in H.
  Qed.

  Variant typing_gen typing (P : Perms) (t : itree E R) : Prop :=
  | cond : (forall pc c, in_Perms P pc ->
                    let p := permConj_perm pc in
                    view p c c ->
                    forall t' c',
                      step t c t' c' ->
                      (
                        (* we step to configs that satisfy the perm *)
                        (upd p c c') /\
                        (* we step to machines that are well-typed by some other perm that maintains separation *)
                        (exists P', typing P' t' /\ eq_sep P P' pc))) (* sep' P' pc c c'))) *)
                               (* forall pc_s, *)
                               (*   view (permConj_perm (sep_conj_permConj pc pc_s)) c c -> *)
                               (*   exists pc', in_Perms P' pc' /\ *)
                               (*         view (permConj_perm (sep_conj_permConj pc' pc_s)) c' c')))  *)->
           typing_gen typing P t.

  Definition typing P t := paco2 typing_gen bot2 P t.

  Lemma typing_gen_mon : monotone2 typing_gen.
  Proof.
    repeat intro.
    inversion IN. econstructor. intros. specialize (H _ _ H0 H1 _ _ H2).
    destruct H as [? [? [? ?]]]. split; eauto.
  Qed.
  Hint Resolve typing_gen_mon : paco.

  Lemma rewrite_spin : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.

  Lemma type_spin : forall P, typing P ITree.spin.
  Proof.
    pcofix CIH. intros. pstep. constructor. intros. rewrite rewrite_spin in H1.
    inversion H1; subst. split; try reflexivity.
    exists P. split; auto. eapply eq_sep_refl; eauto.

    (* intros. exists pc. split; auto. *)
  Qed.

  Lemma type_ret : forall P r, typing P (Ret r).
  Proof.
    pstep. constructor. intros. inversion H1.
  Qed.

  Lemma type_top : forall t, typing top_Perms t.
  Proof.
    intros. pstep. constructor. intros. inversion H.
  Qed.

  Lemma type_lte : forall P Q t, typing P t -> P ⊑ Q -> typing Q t.
  Proof.
    pcofix CIH. intros. pinversion H0. pstep. constructor. intros.
    destruct (H _ _ (H1 _ H2) H3 _ _ H4). split; auto.
    destruct H6 as [P' [? ?]]. exists P'. split; auto. pclearbot. left. eapply paco2_mon_bot; eauto.

    red in H7. specialize (H7 (H1 _ H2)). destruct H7 as [pc' [? ?]].
    exists pc'. split; auto.
  Qed.

  Lemma type_tau : forall P t, typing P t -> typing P (Tau t).
  Proof.
    intros. pfold. econstructor. intros.
    inversion H2; subst.
    split; intuition.
    exists P. split; auto.
    exists pc. split; auto.
  Qed.

  Lemma frame : forall P1 P2 t, typing P1 t -> typing (sep_conj_Perms P1 P2) t.
  Proof.
    intros. eapply type_lte; eauto. apply lte_l_sep_conj_Perms.
  Qed.

  Lemma view_permConj : forall pc p c, in_permConj pc p ->
                                  view (permConj_perm pc) c c ->
                                  view p c c.
  Proof.
    intros. simpl in H0. apply H0; auto.
  Qed.

  Lemma view_sep_conj_l : forall pc1 pc2 pc c,
      sep_conj_permConj pc1 pc2 ⊆ pc ->
      view (permConj_perm pc) c c ->
      view (permConj_perm pc1) c c.
  Proof.
    repeat intro. red in H. split.
    - eapply view_permConj. apply H. apply lte_l_join_permConj. auto. auto.
    - intros. simpl in H0. apply H0.
      apply H. left. auto. apply H. left. auto. auto.
  Qed.

  Lemma view_sep_conj_r : forall pc1 pc2 pc c,
      sep_conj_permConj pc1 pc2 ⊆ pc ->
      view (permConj_perm pc) c c ->
      view (permConj_perm pc2) c c.
  Proof.
    repeat intro. red in H. split.
    - eapply view_permConj. apply H. apply lte_r_join_permConj. auto. auto.
    - intros. simpl in H0. apply H0.
      apply H. right. auto. apply H. right. auto. auto.
  Qed.

  Lemma sep_sep_conj_Perms : forall P1 P2 pc c, in_Perms (sep_conj_Perms P1 P2) pc ->
                                           view (permConj_perm pc) c c ->
                                           sep P2 pc c c.
  Proof.
    red. intros. destruct H as [p1 [p2 [Hp1 [Hp2 ?]]]].
    exists p2. split; auto. simpl in H1. simpl. intros. destruct H2.
    - split.
      + apply H1. left. apply H. right. auto.
      + intros. destruct H3; apply H1; auto; left; apply H; right; auto.
    - split.
      + apply H1. right. auto.
      + intros. destruct H3; apply H1; auto; left; apply H; right; auto.
  Qed.

  Lemma sep_sep_conj_Perms'' : forall P1 P2 pc c, in_Perms (sep_conj_Perms P1 P2) pc ->
                                             view (permConj_perm pc) c c ->
                                             sep' P2 pc c c.
  Proof.
    red. intros. destruct H as [p1 [p2 [Hp1 [Hp2 ?]]]].
    exists p2. split; auto. split; auto. 2: { eapply view_sep_conj_r; eauto. }
    red in H. red.
  Abort.

  Lemma anti_mon : forall pc1 pc2 pc3, separate_permConj pc2 pc3 -> pc1 ⊆ pc2 ->
                                  separate_permConj pc1 pc3.
  Proof.
    repeat red. split; intros.
    - eapply test_view; eauto. destruct H. apply H; auto.
      (* not true *) admit.
    - apply H; auto. eapply test_upd; eauto.
  Abort.

  Lemma sep_sep_conj_Perms' : forall P1 P2 pc c, in_Perms (sep_conj_Perms P1 P2) pc ->
                                           view (permConj_perm pc) c c ->
                                           sep (sep_conj_Perms P1 P2) pc c c.
  Proof.
    red. intros. destruct H as [p1 [p2 [Hp1 [Hp2 ?]]]].
    exists (sep_conj_permConj p1 p2). split; auto.
    - apply sep_conj_Perms_permConj; auto.
    - repeat intro. split.
      + apply H1. destruct H2.
        * left. apply H. auto.
        * right. auto.
      + intros. apply H1; auto.
        * destruct H2.
          left. auto.
          right. auto.
        * destruct H3.
          left. auto.
          right. auto.
  Qed.

  (* Lemma sep_test : forall pc1 pc2 c, *)
  (*     view (permConj_perm (sep_conj_permConj pc1 pc2)) c c -> *)
  (*     separate_permConj pc1 pc2. *)
  (* Proof. *)
  (*   intros. red. simpl in H. *)
  (*   apply H. *)
  (* Qed. *)

  Lemma par_eutt_tau : forall t1 t2, par t1 t2 ≈ Tau (par t1 t2).
  Proof.
    intros. apply eqit_tauR. reflexivity.
  Qed.

  Axiom par_tau : forall t1 t2, par t1 t2 = Tau (par t1 t2).
  Axiom par_ret_l : forall r t, par (Ret r) t = t.
  Axiom par_ret_r : forall r t, par t (Ret r) = t.
  Axiom par_tau_l : forall t1 t2, par (Tau t1) t2 = par t1 t2.
  Axiom par_tau_r : forall t1 t2, par t1 (Tau t2) = par t1 t2.

  Lemma type_tau' : forall P pc c t, typing P (Tau t) ->
                                view (permConj_perm pc) c c ->
                                in_Perms P pc ->
                                exists P', typing P' t /\ sep P' pc c c /\ exists pc', in_Perms P' pc'.
  Proof.
    intros P pc c t Htyping Hpccc HPpc.
    pinversion Htyping.
    destruct (H _ _ HPpc Hpccc _ _ (step_tau _ _)) as [_ [P' [? ?]]].
    pose proof H1.
    (* destruct H1 with (pc_s := bottom_permConj) as [? [? _]]. *)
    - admit. (* rewrite join_permConj_commut. rewrite sep_conj_permConj_bottom_identity. *)
    (* - exists P'. pclearbot. split; auto. split; auto. exists x. auto. *)
  Admitted.

  Require Import Coq.Program.Equality.

  Lemma separation : forall P1 P2 t1 t2,
      typing P1 t1 -> typing P2 t2 -> typing (sep_conj_Perms P1 P2) (par t1 t2).
  Proof.
    pcofix CIH. intros P1 P2 t1 t2 Ht1 Ht2.
    pstep. econstructor.
    intros pc c Hpc ? Hcc t' c' Hstep. destruct Hpc as [p1 [p2 [Hp1 [Hp2 Hpc]]]].
    (* assert (view (permConj_perm p1) c c). { *)
    (*   apply (view_inc _ p); auto. *)
    (*   apply permConj_perm_lte_perm. etransitivity; eauto. apply lte_l_join_permConj. *)
    (* } *)
    (* specialize (H _ _ H2 H7). *)

    rewrite rewrite_par in Hstep. unfold par_match in Hstep.
    dependent destruction Hstep. (* inversion Hstep; auto_inj_pair2; subst. *)
    - split; intuition. destruct (observe t1) eqn:?.
      + exists P2. split. left. eapply paco2_mon_bot; eauto.
        intro. exists p2. (* probably sep_conj_permConj bottom_permConj p2 *)
        split; auto. intros.

        (* red. red. split; intros. *)
        (* * simpl. *)

        (* eapply test; eauto. *)
      (* eapply sep_sep_conj_Perms; eauto. simpl. exists p1, p2. repeat split; eauto. *)
        admit.
      + pose proof type_tau'. symmetry in Heqi. pose proof (simpobs Heqi).
        apply bisimulation_is_eq in H0. rewrite H0 in Ht1.
        specialize (H _ p1 c _ Ht1). destruct H as [P' [HP' [? [pc' ?]]]]; auto.
        { eapply view_sep_conj_l; eauto. }

        exists (sep_conj_Perms P' P2). split; auto.
        * rewrite <- par_tau. right. apply CIH; auto.
        * red. intros.
          exists (sep_conj_permConj pc' p2). split. apply sep_conj_Perms_permConj; auto. red in H.
          simpl. intros. (* don't have enough info about P'? *)

          (* old way without intros *)
      (* apply sep_sep_conj_Perms'; auto. exists p1, p2. repeat split; auto. red in H. *)
          admit.
      + eexists. split.
        * left. pinversion Ht1.

          pstep. constructor. intros.

        (* exists (sep_conj_Perms P1 P2). split; auto. *)
        (* * admit. *)
        (* * apply sep_sep_conj_Perms'; auto. exists p1, p2. repeat split; auto. *)

    (* What should this P be? *)
        admit.
    - (* same as last case, basically *) admit.
    - admit.
    - admit.
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
