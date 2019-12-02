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

(*
NOTE: turns out, the general notion of "separate"  does not really make sense!

We need to define it this way, because, if we don't have the view x x,
precondition it implies that each view is reflexive, since each upd is. But then
this notion of separateness is not anti-monotone!

Record separate (p q:perm) : Prop :=
  {
    upd1: forall x y:config,
      (view q) x x -> (upd p) x y -> (view q) x y;
    upd2: forall x y:config,
      (view p) x x -> (upd q) x y -> (view p) x y;
  }.

Lemma separate_anti_monotone : forall (p1 p2 q : perm) (HSep: separate p2 q) (Hlte: p1 <= p2),
    separate p1 q.
Proof.
  intros p1 p2 q [sep1 sep2] [lte1 lte2].
 constructor; intros.
  - apply sep1; try assumption. apply lte2. assumption.
  - apply lte1. apply sep2; auto. NOTE: here is where we get stuck!
 *)

Record sep_at (x:config) (p q:perm) : Prop :=
  {
    sep_at_view_l : view p x x;
    sep_at_view_r : view q x x;
    sep_at_upd_l : forall y:config, (upd p) x y -> (view q) x y;
    sep_at_upd_r : forall y:config, (upd q) x y -> (view p) x y;
  }.

Arguments sep_at_view_l [x p q].
Arguments sep_at_view_r [x p q].
Arguments sep_at_upd_l [x p q].
Arguments sep_at_upd_r [x p q].

Instance sep_at_commutative : forall x, Symmetric (sep_at x).
Proof.
  repeat intro. destruct H. constructor; auto.
Qed.

Lemma sep_at_anti_monotone : forall x p1 p2 q,
    sep_at x p2 q -> p1 <= p2 -> sep_at x p1 q.
Proof.
  intros x p1 p2 q sepat [lte_view lte_upd]; constructor; intros.
  - apply lte_view. apply sepat.
  - apply sepat.
  - apply sepat. apply lte_upd. assumption.
  - apply lte_view. apply sepat. assumption.
Qed.

(* Bottom is separate from everything *)
Lemma sep_at_bottom: forall p x, view p x x -> sep_at x bottom_perm p.
Proof.
  intros. unfold bottom_perm. constructor; simpl; intros; try trivial.
  rewrite <- H0. assumption.
Qed.

Definition separate (p q : perm) : Prop :=
  forall x, view p x x -> view q x x -> sep_at x p q.

Lemma separate_bottom : forall p, separate bottom_perm p.
Proof.
  intros p x ? ?. apply sep_at_bottom. assumption.
Qed.

Lemma separate_anti_monotone : forall p1 p2 q,
    separate p2 q -> p1 <= p2 -> separate p1 q.
Proof.
  repeat intro. eapply sep_at_anti_monotone; eauto. apply H; auto.
  (* Not true since x may not be in the view of p1 *)
  (* note that this definition is the same as in the long comment above *)
Abort.

Definition separate' (p q : perm) : Prop :=
  (forall x y, view p x x -> upd q x y -> view p x y) /\
  (forall x y, view q x x -> upd p x y -> view q x y).

Lemma sep_self : forall p,
    (forall x y, upd p x y -> x = y) -> separate' p p.
Proof.
  split; repeat intro; apply H in H1; subst; auto.
Qed.

Definition separate'' (p q : perm) : Prop :=
  (forall x y z, view p x y -> upd q y z -> view p x z) /\
  (forall x y z, view q x y -> upd p y z -> view q x z).

Lemma sep_test : forall p q,
    separate' p q -> separate'' p q.
Proof.
  intros p q [H H']. split; repeat intro.
  - etransitivity; eauto. apply H; auto. eapply PER_refl; eauto; intuition; symmetry; eauto.
  - etransitivity; eauto. apply H'; auto. eapply PER_refl; eauto; intuition; symmetry; eauto.
Qed.

Lemma sep_test' : forall p q,
    separate'' p q -> separate' p q.
Proof.
  intros p q [H H']. split; repeat intro; eauto.
Qed.

Record permConj :=
  {
    in_permConj : perm -> Prop;
    (* nonEmpty : exists p, in_permConj p; *)
  }.

Program Definition singleton_permConj (p : perm) : permConj :=
  {|
    in_permConj := fun q => q = p;
  |}.

Program Definition permConj_perm (pc : permConj) : perm :=
  {|
    view := fun x y => forall p, in_permConj pc p ->
                         view p x y /\
                         forall q, in_permConj pc q -> q <> p -> separate' p q;
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

Definition separate_permConj pc1 pc2 : Prop := separate' (permConj_perm pc1)
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

(* Subset *)
Definition lte_Perms (P Q : Perms) : Prop :=
  forall p, in_Perms P p -> in_Perms Q p.

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

(* Complete join of Perms sets = union *)
Program Definition join_Perms (Ps : Perms -> Prop) : Perms :=
  {|
    in_Perms := fun pc => exists P, Ps P /\ in_Perms P pc
  |}.
Next Obligation.
  exists H. split; auto.
  apply (Perms_upwards_closed _ pc1); try assumption.
Defined.

Lemma lte_join_Perms : forall (Ps : Perms -> Prop) P,
    Ps P ->
    P ⊑ join_Perms Ps.
Proof.
  repeat intro. exists P. auto.
Qed.

Lemma join_Perms_min : forall (Ps : Perms -> Prop) Q,
    (forall P, Ps P -> P ⊑ Q) ->
    join_Perms Ps ⊑ Q.
Proof.
  repeat intro. destruct H0 as [? [? ?]].
  eapply H; eauto.
Qed.

Definition join_Perms2 P Q : Perms := join_Perms (fun R => R = P \/ R = Q).

Program Definition top_Perms : Perms :=
  {|
    in_Perms := fun r => True
  |}.

Lemma top_Perms_is_top : forall P, P ⊑ top_Perms.
Proof.
  repeat intro. simpl. auto.
Qed.

Program Definition bottom_Perms : Perms :=
  {|
    in_Perms := fun r => False
  |}.

Lemma bottom_Perms_is_bottom : forall P, bottom_Perms ⊑ P.
Proof.
  repeat intro. inversion H.
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

Lemma lte_l_sep_conj_Perms : forall P Q, sep_conj_Perms P Q ⊑ P.
Proof.
  intros P Q p' ?. destruct H as [p [q [? [? ?]]]].
  eapply Perms_upwards_closed; eauto.
  etransitivity; eauto. apply lte_l_join_permConj.
Qed.

Lemma sep_conj_Perms_top_identity : forall P, eq_Perms (sep_conj_Perms top_Perms P) P.
Proof.
  constructor; repeat intro.
  - destruct H as [? [? [_ [? ?]]]].
    eapply (Perms_upwards_closed P); eauto.
    etransitivity; eauto. apply lte_r_join_permConj.
  - exists bottom_permConj, p. split; simpl; [auto | split; auto].
    apply sep_conj_permConj_bottom_identity.
Qed.

Lemma sep_conj_Perms_bottom_absorb : forall P, eq_Perms (sep_conj_Perms bottom_Perms P) bottom_Perms.
Proof.
  constructor; repeat intro.
  - destruct H as [? [_ [[] _]]].
  - inversion H.
Qed.

Definition entails_Perms P Q := P ⊑ Q.

Definition impl_Perms P Q := join_Perms (fun R => entails_Perms (sep_conj_Perms R P) Q).

Lemma sep_conj_Perms_monotonic : forall P Q R, P ⊑ Q -> sep_conj_Perms P R ⊑ sep_conj_Perms Q R.
Proof.
  repeat intro. destruct H0 as [? [? [? [? ?]]]].
  exists x, x0. auto.
Qed.

Lemma sep_conj_Perms_join_commute : forall (Ps : Perms -> Prop) P,
    eq_Perms (sep_conj_Perms (join_Perms Ps) P)
             (join_Perms (fun Q => exists P', Q = sep_conj_Perms P' P /\ Ps P')).
Proof.
  split; repeat intro.
  - destruct H as [? [? [[Q [? ?]] [? ?]]]].
    simpl. eexists. split.
    + exists Q. split; auto.
    + eapply Perms_upwards_closed; eauto.
      simpl. exists x, x0. split; [auto | split; [auto | ]]. reflexivity.
  - destruct H as [? [[Q [? ?]] ?]].
    subst. destruct H1 as [? [? [? [? ?]]]].
    simpl. exists x, x0. split; [ | split]; auto.
    eexists; split; eauto.
Qed.

Lemma sep_conj_Perms_join_commute' : forall (Ps : Perms -> Prop) P,
    eq (sep_conj_Perms (join_Perms Ps) P)
             (join_Perms (fun Q => exists P', Q = sep_conj_Perms P' P /\ Ps P')).
Admitted.

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
    red. etransitivity; [ apply H | ].
    unfold impl_Perms.
    rewrite sep_conj_Perms_join_commute.
    apply join_Perms_min. intros P' [? [? ?]]. subst. auto.
Qed.


From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.Nondeterminism
     Eq.Eq.

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
                        (* (typing P t'))) -> *)
                        (exists P', typing P' t' /\
                               forall pc_s,
                                 view (permConj_perm (sep_conj_permConj pc pc_s)) c c ->
                                 exists pc', in_Perms P' pc' /\
                                       view (permConj_perm (sep_conj_permConj pc' pc_s)) c' c'))) ->
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
    pcofix CIH. intros. pfold. econstructor. intros. rewrite rewrite_spin in H1.
    inversion H1; subst. split; try reflexivity.
    exists P. split; auto. intros. exists pc. split; auto.
  Qed.

  Lemma type_tau : forall P t, typing P t -> typing P (Tau t).
  Proof.
    pcofix CIH. intros. pfold. econstructor. intros.
    inversion H2; subst.
    split; intuition.
    exists P. split.
    - left. eapply paco2_mon_bot; eauto.
    - exists pc. split; auto.
  Qed.

  Lemma type_tau' : forall P t, typing P (Tau t) -> typing P t.
  Proof.
    pcofix CIH. intros P t Htyping. pfold.
    econstructor. intros p c Hp Hviewpcc t' c' Hstep. pinversion Htyping.
    (* specialize (H _ _ Hp Hviewpcc _ _ (step_tau _ _)). *)
    (* destruct H as [Hupdpcc [P' [Htyping' Hp_s]]]. *)
    (* destruct Htyping' as [Htyping' | ?]; try contradiction. *)
    (* pinversion Htyping'. *)
    (* specialize (H6 _ _ *)
Abort.
  (* Qed. *)

  (*   inversion H2; subst. *)
  (*   - split; intuition. *)
  (*     specialize (H3 _ _ H H1 (Tau t') c'). *)
  (*     destruct H3 as [? [P' [? [p' [? ?]]]]]. constructor. *)
  (*     destruct H4; try contradiction. *)
  (*     exists P'; split; eauto. *)
  (*   - split; intuition. *)
  (*     specialize (H3 _ _ H H1 (Vis (subevent bool Or) k) c'). *)
  (*     destruct H3 as [? [P' [? [p' [? ?]]]]]. constructor. *)
  (*     destruct H4; try contradiction. *)

  (*     pinversion H4. *)
  (*     assert (view p' c' c') by admit. *)
  (*     specialize (H7 _ c' H5 H8 (k true) c'). *)
  (*     destruct H7 as [? [P'' [? [p'' [? ?]]]]]. constructor. *)
  (*     destruct H9; try contradiction. *)
  (*     exists P''. split; eauto. left. eapply paco2_mon_bot; eauto. *)
  (*   - split; intuition. *)
  (*     specialize (H3 _ _ H H1 (Vis (subevent bool Or) k) c'). *)
  (*     destruct H3 as [? [P' [? [p' [? ?]]]]]. constructor. *)
  (*     destruct H4; try contradiction. *)

  (*     pinversion H4. *)
  (*     assert (view p' c' c') by admit. *)
  (*     specialize (H7 _ c' H5 H8 (k false) c'). *)
  (*     destruct H7 as [? [P'' [? [p'' [? ?]]]]]. constructor. *)
  (*     destruct H9; try contradiction. *)
  (*     exists P''. split; eauto. left. eapply paco2_mon_bot; eauto. *)
  (*   - split; intuition. *)
  (*     specialize (H3 _ _ H H1 (Vis (subevent config (Get config)) k) c'). *)
  (*     destruct H3 as [? [P' [? [p' [? ?]]]]]. constructor. *)
  (*     destruct H4; try contradiction. *)

  (*     pinversion H4. *)
  (*     assert (view p' c' c') by admit. *)
  (*     specialize (H7 _ c' H5 H8 (k c') c'). *)
  (*     destruct H7 as [? [P'' [? [p'' [? ?]]]]]. constructor. *)
  (*     destruct H9; try contradiction. *)
  (*     exists P''. split; eauto. left. eapply paco2_mon_bot; eauto. *)
  (*   - specialize (H3 _ _ H H1 (Vis (subevent unit (Put config c')) k) c). *)
  (*     destruct H3 as [? [P' [? [p' [? ?]]]]]. constructor. *)
  (*     destruct H4; try contradiction. *)

  (*     pinversion H4. *)
  (*     assert (view p' c c) by admit. *)
  (*     specialize (H7 p c H5 H8 (k tt) c'). *)
  (*     destruct H7 as [? [P'' [? [p'' [? ?]]]]]. constructor. *)
  (*     destruct H9; try contradiction. split. admit. *)
  (*     exists P''. split; eauto. left. eapply paco2_mon_bot; eauto. *)
  (*     exists p''. split; auto. intros. apply H11. *)
  (* Qed. *)

(*   Lemma sep_at_sep_conj : forall s p1 p2 p3, *)
(*       sep_at s p1 p2 -> sep_at s p1 p3 -> sep_at s p2 p3 -> sep_at s p1 (sep_conj p2 p3). *)
(*   Proof. *)
(*     intros s p1 p2 p3 [] [] ?. constructor; auto. *)
(*     - split; auto. *)
(*     - intros. split; auto. split; auto. split; auto. *)
(*       constructor; auto. *)
(*       + eapply PER_refl; intuition. symmetry. apply sep_at_upd_l0. auto. *)
(*       + eapply PER_refl; intuition. symmetry. apply sep_at_upd_l1. auto. *)
(*       + intros. destruct H. etransitivity. *)
(*         * symmetry. apply sep_at_upd_l2. auto. *)
(* Admitted. *)
(*   (* Qed. *) *)

  Lemma frame : forall P1 P2 t, typing P1 t -> typing (sep_conj_Perms P1 P2) t.
  Proof.
    pcofix CIH. intros P1 P2 t Htype. pfold. pinversion Htype.
    econstructor. intros p c [p1 [p2 [Hp1 [Hp2 [? ?]]]]] Hpc t' c' Hstep.
    destruct (view_inc0 _ _ Hpc) as [Hp1c [Hp2c [Hcp1p2 _]]].
    specialize (H _ _ Hp1 Hp1c _ _ Hstep).
    destruct H as [Hp1cc' [P1' [Htype' Hp_s]]].
    split.
    - apply upd_inc0. constructor; auto.
    - exists (sep_conj_Perms P1' P2). split.
      + right. apply CIH. destruct Htype'; try contradiction; auto.
      + intros p_s [_ [Hp_sc [Hcpp_s _]]].
        destruct Hcpp_s.
        destruct (Hp_s (sep_conj p_s p2)) as [p1' [Hp1' Hp1'p_sc']].
        { split; auto. split.
          - split; auto. split; auto.
            assert (sep_at c p_s p2).
            { constructor; auto.
              - intros. apply view_inc0. auto.
              - intros. apply sep_at_upd_l0. apply upd_inc0. left. right. auto.
            }
            auto.
          - assert (sep_at c p1 p_s).
            { constructor; auto.
              - intros. apply sep_at_upd_l0. apply upd_inc0. left. left. auto.
              - intros. apply view_inc0. auto.
            }
            assert (sep_at c p_s p2).
            {
              constructor; auto.
              - intros. apply view_inc0. auto.
              - intros. apply sep_at_upd_l0. apply upd_inc0. left. right. auto.
            }
            assert (sep_at c p1 (sep_conj p_s p2)).
            {
              constructor; auto.
              - split; auto.
              - intros. split.
                apply sep_at_upd_l0. apply upd_inc0. left. left. auto. split.
                destruct Hcp1p2. apply sep_at_upd_l1. auto. split; auto.
                constructor; auto.
                + eapply PER_refl; intuition. symmetry. apply sep_at_upd_l0.
                  apply upd_inc0. left. left. auto.
                + eapply PER_refl; intuition. symmetry. destruct Hcp1p2.
                  apply sep_at_upd_l1. auto.
                + intros. destruct Hcp1p2. etransitivity. symmetry. apply sep_at_upd_l1; auto.
                  apply view_inc0. apply sep_at_upd_r0.
                  admit.
                  (* apply view_inc0. etransitivity. symmetry. apply sep_at_upd_r0. *)
                  (* eauto. *)
                + admit.
              - admit.
            }
            auto.
        }
        {
          exists (sep_conj p1' p2). split.
          * exists p1', p2. split; intuition.
          * destruct Hp1'p_sc' as [Hp1'c' [Hp_sc' [Hc'p1'p_s _]]].
            destruct Hc'p1'p_s as [_ _ ? ?].
            {
              (* maybe use assoc/commut here? *)
              split. split; auto. split. apply view_inc0. apply sep_at_upd_r0.

        specialize (H9 p2).
        destruct H9 as [p1' [? ?]]. constructor; auto.
        exists (sep_conj p1' p2). split.
        * exists p'. exists p2. split; auto. split; intuition. admit.
        * split. admit.
          assert (view p_s c' c').
          {
            destruct H12. eapply PER_refl; intuition. symmetry. eapply sep_at_upd_l0.
            apply upd_inc0. constructor. left. auto.
          }
          split; auto.
          split.
          destruct H13 as [? [? [? _]]].


          inversion H3; subst; auto.
          admit. admit. admit. admit.



          -- constructor; auto. constructor; auto.
             intros.
             destruct H16. destruct H12. apply sep_at_upd_l1.
             apply upd_inc0. constructor. destruct H17. destruct H12.
          destruct H17. apply sep_at_upd_l0.
          constructor; eauto.
          { intros.
            (* hmm *)


            inversion H3; subst; eauto.
    - split; try reflexivity.
      right. apply CIH. apply type_tau'. pfold. apply H0.
    - split; try reflexivity.
      destruct H1 as [? [? [? [? ?]]]].
      destruct H5 as [? _]. specialize (view_inc0 _ _ H2). destruct view_inc0.
      destruct (H _ _ H1 H5 _ _ (step_nondet_true _ _)).
      destruct H8; try contradiction.
      right. apply CIH. auto.
    - split; try reflexivity.
      destruct H1 as [? [? [? [? ?]]]].
      destruct H5 as [? _]. specialize (view_inc0 _ _ H2). destruct view_inc0.
      destruct (H _ _ H1 H5 _ _ (step_nondet_false _ _)).
      destruct H8; try contradiction.
      right. apply CIH. auto.
    - split; try reflexivity.
      destruct H1 as [? [? [? [? ?]]]].
      destruct H5 as [? _]. specialize (view_inc0 _ _ H2). destruct view_inc0.
      destruct (H _ _ H1 H5 _ _ (step_get _ _)).
      destruct H8; try contradiction.
      right. apply CIH. auto.
    - destruct H1 as [? [? [? [? ?]]]].
      destruct H5 as [? ?]. specialize (view_inc0 _ _ H2). destruct view_inc0.
      destruct (H _ _ H1 H5 _ _ (step_put _ _ _)).
      destruct H8; try contradiction.
      split.
      + apply upd_inc0. constructor. left. auto.
      + right. apply CIH. auto.
  Qed.

  Lemma separation : forall P1 P2 t1 t2,
      typing P1 t1 -> typing P2 t2 -> typing (sep_conj_Perms P1 P2) (par t1 t2).
  Proof.
    pcofix CIH. intros. pfold. pinversion H0.
    econstructor. intros. rewrite rewrite_par in H4. unfold par_match in H4.
    inversion H4; auto_inj_pair2; subst; clear H4.
    - split; intuition. destruct (observe t1) eqn:?.
      + left. (* true by (generalized with different r) frame rule? *) admit.
      + left. (* true by type_tau'? *) admit.
      + left. pfold. constructor. intros. admit.
    -
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
