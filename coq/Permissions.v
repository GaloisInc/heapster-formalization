From Coq Require Import
     Classes.RelationClasses
     Relations.Relations
     Relations.Relation_Operators
     Lists.List
     Logic.FunctionalExtensionality
     Setoids.Setoid.

Import ListNotations.

Parameter config : Type.

(* Denotation of permissions *)
Record perm :=
  mkPerm {
      view : config -> config -> Prop;  (* PER over configs *)
      upd  : config -> config -> Prop;  (* allowed transitions *)
    }.

Record good_perm (p:perm) : Prop :=
  {
    view_PER   : PER _ (view p) ;
    upd_PO     : preorder _ (upd p) ;
  }.

Record lte_perm (p q:perm) : Prop :=
  {
    view_inc : forall x y, (view q) x y -> (view p) x y;
    upd_inc : forall x y, (upd p) x y -> (upd q) x y;
  }.

Lemma lte_refl : forall (p:perm), lte_perm p p.
Proof.
  intros; split; intros; tauto.
Qed.

Definition join_perm (p q:perm) : perm :=
  {|
    view := fun x y => (view p x y) /\ (view q x y) ;
    upd  := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y)) ;
  |}.

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

Lemma lte_l_join : forall p q,
    lte_perm p (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.

Lemma lte_r_join : forall p q,
    lte_perm q (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.
Lemma join_min : forall p q r (Hgood: good_perm r),
    lte_perm p r ->
    lte_perm q r ->
    lte_perm (join_perm p q) r.
Proof.
  intros p q r [_ [_ ?]] [] []. constructor; intros; simpl in *; auto.
  induction H; eauto.
  destruct H; auto.
Qed.

Definition meet_perm (p q:perm) : perm :=
  {|
    view := clos_trans _ (fun x y => (view p x y) \/ (view q x y)) ;
    upd  := fun x y => (upd p x y) /\ (upd q x y) ;
  |}.

Lemma lte_meet_l : forall p q,
    lte_perm (meet_perm p q) p.
Proof.
  intros. constructor.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma lte_meet_r : forall p q,
    lte_perm (meet_perm p q) q.
Proof.
  intros. constructor.
  - left; auto.
  - intros x y []; auto.
Qed.
Lemma meet_max : forall p q r (Hgood : good_perm r),
    lte_perm r p ->
    lte_perm r q ->
    lte_perm r (meet_perm p q).
Proof.
  intros p q r [[_ ?] _] [] []. constructor; intros; simpl in *; auto.
  induction H; eauto.
  destruct H; auto.
Qed.

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

Definition bottom_perm : perm :=
  {|
    view := fun x y => True ;
    upd  := fun x y => False ;
  |}.

Lemma bottom_perm_is_bot : forall p, lte_perm bottom_perm p.
Proof. constructor; simpl; intuition. Qed.

Definition top_perm : perm :=
  {|
    view := fun x y => False ;
    upd  := fun x y => True ;
  |}.

Lemma top_perm_is_top : forall p, lte_perm p top_perm.
Proof. constructor; simpl; intuition. Qed.

Record separate (p q:perm) : Prop :=
  {
    upd1: forall x y:config, (upd p) x y -> (view q) x y;
    upd2: forall x y:config, (upd q) x y -> (view p) x y;
  }.

Lemma separate_anti_monotone : forall (p1 p2 q : perm) (HSep: separate p2 q) (Hlte: lte_perm p1 p2),
    separate p1 q.
Proof.
  intros p1 p2 q [] [].
  constructor; auto.
Qed.

Record sep_at (p q:perm) (x:config) : Prop :=
  {
    upd1': forall y:config, (upd p) x y -> (view q) x y;
    upd2': forall y:config, (upd q) x y -> (view p) x y;
  }.

Definition separate' (p q : perm) : Prop := forall x, sep_at p q x.

Lemma separate_defns : forall p q, separate p q <-> separate' q p.
Proof.
  split; intros.
  {
    intro. destruct p, q. inversion H. constructor; auto.
  }
  {
    red in H. destruct p, q. constructor; intros; apply H; auto.
  }
Qed.

Record eq_perm (p q : perm) : Prop :=
  {
    view_eq : forall x y, view q x y <-> view p x y;
    upd_eq: forall x y, upd p x y <-> upd q x y;
  }.
Lemma eq_lte : forall p q, eq_perm p q <-> lte_perm p q /\ lte_perm q p.
Proof.
  intros [] [].
  split; intros.
  {
    inversion H.
    split; inversion H; constructor; intros; simpl in *.
    rewrite <- view_eq0; auto.
    rewrite <- upd_eq0; auto.
    rewrite view_eq0; auto.
    rewrite upd_eq0; auto.
  }
  {
    destruct H. inversion H. inversion H0. constructor; simpl in *; split; intros; auto.
  }
Qed.

Lemma sep_at_bottom: forall p x, sep_at bottom_perm p x.
Proof.
  intros. unfold bottom_perm. destruct p. constructor; simpl in *; intuition.
Qed.
Lemma separate_bottom : forall p, separate' bottom_perm p.
Proof. intros p x. apply sep_at_bottom. Qed.

Definition sep_conj (p q : perm) : perm :=
  {|
    view := fun x y => (view p x y) /\ (view q x y) /\ sep_at p q x /\ sep_at p q y ;
    upd := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y)) ;
  |}.

Lemma separate_join_is_sep_conj: forall p q, separate' p q -> eq_perm (join_perm p q) (sep_conj p q).
Proof.
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

Lemma sep_conj_top_absorb : forall p, eq_perm (sep_conj top_perm p) top_perm.
Proof.
  intros. unfold sep_conj. destruct p. unfold top_perm. constructor; intros; simpl.
  - split; intros; try contradiction.
    destruct H. contradiction.
  - split; intros.
    + induction H; auto.
    + constructor. left. auto.
Qed.

Lemma sep_conj_bottom_identity : forall p, good_perm p -> eq_perm (sep_conj bottom_perm p) p.
Proof.
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

Definition Perm := perm -> Prop.

Definition lte_Perm (P Q : Perm) : Prop :=
  forall p, P p -> (exists q, Q q /\ lte_perm p q).

(* Ideal *)
Record goodPerm (P : Perm) : Prop :=
  {
    Perm_nonempty: exists p, P p;
    Perm_good: forall p, P p -> good_perm p;
    Perm_downward_closed: forall p q, P p -> lte_perm q p -> P q;
    Perm_directed: forall p q, P p -> P q -> exists r, P r /\ lte_perm p r /\ lte_perm q r
  }.

Lemma lte_Perm_subset : forall P Q (GP:goodPerm P) (GQ:goodPerm Q),
    lte_Perm P Q <-> (forall p, P p -> Q p).
Proof.
  intros P Q GP GQ.
  split; intros H.
  - intros p Hp.
    apply H in Hp.
    destruct Hp as [q [HQ HLT]].
    eapply (GQ.(Perm_downward_closed _)).
    apply HQ.
    assumption.
  - unfold lte_Perm.
    intros p Hp.
    exists p. split. apply H. assumption. apply lte_refl.
Qed.

Definition join_Perm (P Q : Perm) : Perm :=
  fun p => P p \/ Q p.

Lemma lte_join_Perm_l : forall P Q (HgoodP: goodPerm P) (HgoodQ: goodPerm Q),
    lte_Perm P (join_Perm P Q).
Proof.
  intros P Q [] []. red. destruct Perm_nonempty0 as [p Hp].
  intros r ?. exists r. split; auto. left. auto. constructor; auto.
Qed.
Lemma lte_join_Perm_r : forall P Q (HgoodP: goodPerm P) (HgoodQ: goodPerm Q),
    lte_Perm Q (join_Perm P Q).
Proof.
  intros P Q [] []. red. destruct Perm_nonempty1 as [q Hq].
  intros r ?. exists r. split; auto. right. auto. constructor; auto.
Qed.
Lemma join_Perm_min : forall P Q R (HgoodP: goodPerm P) (HgoodQ: goodPerm Q) (HgoodR: goodPerm R),
    lte_Perm P R ->
    lte_Perm Q R ->
    lte_Perm (join_Perm P Q) R.
Proof.
  intros P Q R [] [] [] ? ? ? ?.
  destruct H1; auto.
Qed.

Definition bottom_Perm : Perm :=
  fun p => p = bottom_perm.
Lemma bottom_Perm_is_bot : forall P (Hgood: goodPerm P), lte_Perm bottom_Perm P.
Proof.
  intros P Hgood p Hp. exists bottom_perm.
  split.
  - destruct Hgood. destruct Perm_nonempty0.
    eapply Perm_downward_closed0; eauto. apply bottom_perm_is_bot.
  - inversion Hp. constructor; auto.
Qed.
Definition separate_Perm (P Q : Perm) : Prop :=
  forall p q, P p -> Q q -> separate p q.

Lemma separate_Perm_anti_monotone : forall (P1 P2 Q : Perm)
                                      (HSep : separate_Perm P2 Q)
                                      (Hlte : lte_Perm P1 P2),
    separate_Perm P1 Q.
Proof.
  intros P1 P2 Q ? ? p q ? ?. specialize (Hlte _ H). destruct Hlte as [p2 [? ?]].
  eapply separate_anti_monotone; eauto.
Qed.
