From Coq Require Import
     Classes.Morphisms
     Lists.List
     Relations.Relation_Operators.

Import ListNotations.

Parameter config : Type.

(* A single permission *)
Record perm :=
  mkPerm {
      view : config -> config -> Prop;  (* PER over configs *)
      view_PER : PER view;
      upd  : config -> config -> Prop;  (* allowed transitions *)
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
  admit.
Admitted.

Lemma lte_refl : forall (p:perm), p <= p.
Proof.
  intros; split; intros; tauto.
Qed.

Program Definition join_perm (p q:perm) : perm :=
  {|
    view := fun x y => (view p x y) /\ (view q x y) ;
    upd  := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y)) ;
  |}.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.

(*
Lemma join_good : forall p q,
    good_perm p -> good_perm q -> good_perm (join_perm p q).
Proof.
  intros p q Hgoodp Hgoodq. constructor; simpl.
  - constructor.
    + destruct Hgoodp as [[? _] _]. destruct Hgoodq as [[? _] _].
      intros x y []. split; auto.
    + destruct Hgoodp as [[_ ?] _]. destruct Hgoodq as [[_ ?] _].
      intros x y z [] []. split; eauto.
  - constructor.
    + destruct Hgoodp as [_ [? _]]. destruct Hgoodq as [_ [? _]].
      constructor; auto.
    + destruct Hgoodp as [_ [_ ?]]. destruct Hgoodq as [_ [_ ?]].
      red. intros.
      induction H; induction H0.
      * destruct H, H0; econstructor 2; constructor; eauto.
      * econstructor 2; eauto.
      * econstructor 2; eauto. apply IHclos_trans2. constructor; auto.
      * repeat (econstructor 2; eauto).
Qed.
*)

Lemma lte_l_join : forall p q,
    p <= (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.

Lemma lte_r_join : forall p q,
    q <= (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.

Lemma join_min : forall p q r,
    p <= r ->
    q <= r ->
    join_perm p q <= r.
Proof.
  admit.
Admitted.
(*
  intros p q r [] []. constructor; intros; simpl in *; auto.
  induction H; eauto.
  destruct H; auto.
Qed.
 *)

Program Definition meet_perm (p q:perm) : perm :=
  {|
    view := clos_trans _ (fun x y => (view p x y) \/ (view q x y)) ;
    upd  := fun x y => (upd p x y) /\ (upd q x y) ;
  |}.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.

Lemma lte_meet_l : forall p q,
    meet_perm p q <= p.
Proof.
  intros. constructor.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma lte_meet_r : forall p q,
    meet_perm p q <= q.
Proof.
  intros. constructor.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma meet_max : forall p q r,
    r <= p ->
    r <= q ->
    r <= meet_perm p q.
Proof.
  admit.
Admitted.
(*
  intros p q r [[_ ?] _] [] []. constructor; intros; simpl in *; auto.
  induction H; eauto.
  destruct H; auto.
Qed.
 *)

(*
Lemma meet_good : forall p q,
    good_perm p -> good_perm q -> good_perm (meet_perm p q).
Proof.
  intros p q Hgoodp Hgoodq. constructor; simpl.
  - constructor.
    + destruct Hgoodp as [[? _] _]. destruct Hgoodq as [[? _] _].
      intros x y H. induction H.
      * constructor. destruct H; auto.
      * econstructor 2; eauto.
    + destruct Hgoodp as [[_ ?] _]. destruct Hgoodq as [[_ ?] _].
      red. intros.
      induction H; induction H0.
      * destruct H, H0; econstructor 2; constructor; eauto.
      * econstructor 2; eauto.
      * econstructor 2; eauto. apply IHclos_trans2. constructor; auto.
      * repeat (econstructor 2; eauto).
  - constructor.
    + destruct Hgoodp as [_ [? _]]. destruct Hgoodq as [_ [? _]].
      constructor; auto.
    + destruct Hgoodp as [_ [_ ?]]. destruct Hgoodq as [_ [_ ?]].
      intros x y z [] []. split; eauto.
Qed.
 *)

Program Definition bottom_perm : perm :=
  {|
    view := fun x y => True ;
    upd  := fun x y => x = y ;
  |}.
Next Obligation.
  constructor; intro; intros; trivial.
Defined.
Next Obligation.
  constructor; intro; intros; [ trivial | transitivity y; assumption ].
Defined.

Lemma bottom_perm_is_bot : forall p, bottom_perm <= p.
Proof. constructor; simpl; intuition. rewrite H. reflexivity. Qed.

Program Definition top_perm : perm :=
  {|
    view := fun x y => False ;
    upd  := fun x y => True ;
  |}.
Next Obligation.
  constructor; intro; intros; trivial.
Defined.
Next Obligation.
  constructor; intro; intros; trivial.
Defined.

Lemma top_perm_is_top : forall p, p <= top_perm.
Proof. constructor; simpl; intuition. Qed.

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
  - NOTE: here is where we get stuck!
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

Lemma sep_at_anti_monotone : forall x p1 p2 q,
    sep_at x p2 q -> p1 <= p2 -> sep_at x p1 q.
Proof.
  intros x p1 p2 q sepat [lte_view lte_upd]; constructor; intros.
  - apply lte_view. apply (sep_at_view_l sepat); assumption.
  - apply (sep_at_view_r sepat).
  - apply (sep_at_upd_l sepat). apply lte_upd. assumption.
  - apply lte_view. apply (sep_at_upd_r sepat). assumption.
Qed.

(* NOTE: this implies that the fields of p and q are complete; maybe this
definition would be better if we quantified over all x in the fields (i.e., the
fields on the PERs) of p and q?  *)
Definition separate' (p q : perm) : Prop := forall x, sep_at x p q.

(* Equality of permissions = the symmetric closure of the ordering *)
Definition eq_perm p q : Prop := p <= q /\ q <= p.

(* Bottom is separate from everything *)
Lemma sep_at_bottom: forall p x, view p x x -> sep_at x bottom_perm p.
Proof.
  intros. unfold bottom_perm. constructor; simpl; intros; try trivial.
  rewrite <- H0. assumption.
Qed.

(*
Lemma separate_bottom : forall p, separate' bottom_perm p.
Proof. intros p x. apply sep_at_bottom. Qed.
*)

Program Definition sep_conj (p q : perm) : perm :=
  {|
    view := fun x y =>
              (view p x y) /\ (view q x y) /\ sep_at x p q /\ sep_at y p q;
    upd := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y));
  |}.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.


Lemma separate_join_is_sep_conj: forall p q, separate' p q -> eq_perm (join_perm p q) (sep_conj p q).
Proof.
  admit.
Admitted.
(*
  intros. red in H. constructor; intros.
  {
    split; intros; simpl in *.
    - destruct H0 as [? [? ?]]. auto.
    - destruct H0. auto.
  }
  {
    split; intros; simpl in *.
    - induction H0.
      + destruct H0; constructor; auto.
      + econstructor 2; eauto.
    - induction H0.
      + destruct H0; constructor; auto.
      + econstructor 2; eauto.
  }
Qed.
 *)

Lemma sep_conj_top_absorb : forall p, eq_perm (sep_conj top_perm p) top_perm.
Proof.
  admit.
Admitted.
(*
  intros. unfold sep_conj. destruct p. unfold top_perm. constructor; intros; simpl.
  - split; intros; try contradiction.
    destruct H. contradiction.
  - split; intros.
    + induction H; auto.
    + constructor. left. auto.
Qed.
*)

Lemma sep_conj_bottom_identity : forall p, eq_perm (sep_conj bottom_perm p) p.
Proof.
  admit.
Admitted.
(*
  intros p Hgood. unfold sep_conj. destruct p. unfold bottom_perm. constructor; intros; simpl.
  - split; intros; auto.
    + repeat split; auto; intros; simpl in *; contradiction.
    + destruct H as [? [? ?]]; auto.
  - split; intros; auto.
    + induction H.
      * destruct H; auto; contradiction.
      * destruct Hgood. destruct upd_PO0. simpl in *. eapply preord_trans; eauto.
    + constructor. right. auto.
Qed.
 *)

(* Definition sep_disj (p q : perm) : perm := *)
(*   {| *)
(*     view := fun x y => (clos_trans _ (fun x y => (view p x y) \/ (view q x y))) x y /\ sep_at p q x /\ sep_at p q y ; *)
(*     upd := fun x y => (upd p x y) /\ (upd q x y) ; *)
(*   |}. *)
(* Lemma separate_meet_is_sep_disj: forall p q, separate' p q -> eq_perm (meet_perm p q) (sep_disj p q). *)
(* Proof. *)
(*   intros. red in H. constructor; intros. *)
(*   { *)
(*     split; intros; simpl in *; auto. *)
(*     destruct H0 as [? [? ?]]. auto. *)
(*   } *)
(*   { *)
(*     split; intros; simpl in *; auto. *)
(*   } *)
(* Qed. *)
(* Lemma sep_disj_bottom_absorb : forall p, eq_perm (sep_disj bottom_perm p) bottom_perm. *)
(* Proof. *)
(*   intros. unfold sep_disj. destruct p. unfold bottom_perm. constructor; intros; simpl. *)
(*   - split; intros; try contradiction; auto. *)
(*     repeat split; simpl; auto; intros; try contradiction. *)
(*     constructor. left. auto. *)
(*   - split; intros; try contradiction. *)
(*     destruct H. contradiction. *)
(* Qed. *)

(* Lemma sep_disj_top_identity : forall p, good_perm p -> eq_perm (sep_disj top_perm p) p. *)
(* Proof. *)
(*   intros p Hgood. unfold sep_disj. destruct p. unfold top_perm. constructor; intros; simpl. *)
(*   - split; intros; auto. *)
(*     + split. *)
(*       constructor. right. auto. *)
(*       split; constructor; intros; simpl in *; auto. *)
(*       * simpl. *)
(*     + destruct H as [? [? ?]]; auto. *)
(*   - split; intros; auto. *)
(*     + induction H. *)
(*       * destruct H; auto; contradiction. *)
(*       * destruct Hgood. destruct upd_PO0. simpl in *. eapply preord_trans; eauto. *)
(*     + constructor. right. auto. *)
(* Qed. *)

(* Perms = upwards-closed sets of single permissions *)
Record Perms :=
  {
    in_Perms : perm -> Prop;
    Perms_upwards_closed : forall p1 p2, in_Perms p1 -> p1 <= p2 -> in_Perms p2
  }.

(* The ordering on Perms sets is the superset ordering *)
Definition lte_Perms (P Q : Perms) : Prop :=
  forall p, in_Perms Q p -> in_Perms P p.

Notation "P ⊑ Q" := (lte_Perms P Q) (at level 80, right associativity).

(* The least Perms set containing a given p *)
Program Definition singleton_Perms p : Perms :=
  {|
    in_Perms := fun q => p <= q
  |}.
Next Obligation.
  transitivity p1; assumption.
Defined.

(* Complete meet of Perms sets = union *)
Program Definition meet_Perms (Ps : Perms -> Prop) : Perms :=
  {|
    in_Perms := fun p => exists P, Ps P -> in_Perms P p
  |}.
Next Obligation.
  exists H. intro.
  apply (Perms_upwards_closed _ p1); try assumption.
  apply H1. assumption.
Qed.


(*
FIXME:
- Prove that meet_Perms is a greatest lower bound
- Define binary meet as a special case
- Define conjunction of Perms pointwise
- Define the top and bottom Perms sets
- Define entailment as the inverse of lte_Perms
- Define impl_Perms as the adjoint (w.r.t. entailment) of conjunction


Definition join_Perm (P Q : Perm) : Perm :=
  fun p => P p /\ Q p.

Lemma lte_join_Perm_l : forall P Q (HgoodP: goodPerm P) (HgoodQ: goodPerm Q),
    P ⊑ join_Perm P Q.
Proof.
  intros P Q [] []. red. intros. destruct H. exists q. split; auto. constructor; auto.
Qed.
Lemma lte_join_Perm_r : forall P Q (HgoodP: goodPerm P) (HgoodQ: goodPerm Q),
    Q ⊑ join_Perm P Q.
Proof.
  intros P Q [] []. red. intros. destruct H. exists q. split; auto. constructor; auto.
Qed.
Lemma join_Perm_min : forall P Q R (HgoodP: goodPerm P) (HgoodQ: goodPerm Q) (HgoodR: goodPerm R),
    P ⊑ R ->
    Q ⊑ R ->
    join_Perm P Q ⊑ R.
Proof.
  intros P Q R [] [] [] ? ? ? ?.
  destruct (H _ H1) as [? [? ?]]. destruct (H0 _ H1) as [? [? ?]].
  specialize (Perm_upward_closed0 _ _ H2 H3).
  specialize (Perm_upward_closed1 _ _ H4 H5).
  exists q. split; try red; try constructor; auto.
Qed.

Definition bottom_Perm : Perm :=
  fun p => True.
Lemma bottom_Perm_is_bot : forall P (Hgood: goodPerm P), bottom_Perm ⊑ P.
Proof.
  intros P Hgood p Hp. exists bottom_perm.
  split; try red; auto.
  apply bottom_perm_is_bot.
Qed.

Definition top_Perm : Perm :=
  fun p => False.
Lemma top_Perm_is_top : forall P (Hgood: goodPerm P), P ⊑ top_Perm.
Proof.
  intros P Hgood p Hp. inversion Hp.
Qed.

Definition separate_Perm (P Q : Perm) : Prop :=
  forall p q, P p -> Q q -> separate p q.

(* Doesn't hold, P1 must contain stuff such that P1 ⊑ P2, but aside from that
   it can contain anything. *)
Lemma separate_Perm_anti_monotone : forall (P1 P2 Q : Perm)
                                      (HSep : separate_Perm P2 Q)
                                      (Hlte : P1 ⊑ P2),
    separate_Perm P1 Q.
Proof.
  intros P1 P2 Q ? ? p q ? ?.
  (* red in HSep. *)
  (* red in Hlte. specialize (Hlte _ H). destruct Hlte as [p2 [? ?]]. *)
  (* eapply separate_anti_monotone; eauto. *)
Abort.

(* sep conj is pointwise ? *)

 *)
