From Coq Require Import
     (* Classes.RelationClasses *)
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

Record goodPerm (p:perm) : Prop :=
  {
    view_PER   : PER _ (view p) ;
    upd_PO     : preorder _ (upd p) ;
  }.

Record lte_perm (p q:perm) : Prop :=
  {
    view_inc : forall x y, (view q) x y -> (view p) x y;
    upd_inc : forall x y, (upd p) x y -> (upd q) x y;
  }.

Definition join_perm (p q:perm) : perm :=
  {|
    view := fun x y => (view p x y) /\ (view q x y) ;
    upd  := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y)) ;
  |}.

Lemma join_good : forall p q,
    goodPerm p -> goodPerm q -> goodPerm (join_perm p q).
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
Lemma join_min : forall p q r (Hgood: goodPerm r),
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
Lemma meet_max : forall p q r (Hgood : goodPerm r),
    lte_perm r p ->
    lte_perm r q ->
    lte_perm r (meet_perm p q).
Proof.
  intros p q r [[_ ?] _] [] []. constructor; intros; simpl in *; auto.
  induction H; eauto.
  destruct H; auto.
Qed.

Lemma meet_good : forall p q,
    goodPerm p -> goodPerm q -> goodPerm (meet_perm p q).
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

Lemma separate_anti_monotone : forall (p1 p2 q : perm) (HSep: separate p2 q) (Hlt: lte_perm p1 p2),
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

Lemma sep_conj_top : forall p, eq_perm (sep_conj top_perm p) top_perm.
Proof.
  intros. unfold sep_conj. destruct p. unfold top_perm. constructor; intros; simpl.
  - split; intros; try contradiction.
    destruct H. contradiction.
  - split; intros.
    + induction H; auto.
    + constructor. left. auto.
Qed.

Lemma sep_conj_bottom : forall p, goodPerm p -> eq_perm (sep_conj bottom_perm p) p.
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

Definition sep_disj (p q : perm) : perm :=
  {|
    view := fun x y => (clos_trans _ (fun x y => (view p x y) \/ (view q x y))) x y /\ sep_at p q x /\ sep_at p q y ;
    upd := fun x y => (upd p x y) /\ (upd q x y) ;
  |}.
Lemma separate_meet_is_sep_disj: forall p q, separate' p q -> eq_perm (meet_perm p q) (sep_disj p q).
Proof.
  intros. red in H. constructor; intros.
  {
    split; intros; simpl in *; auto.
    destruct H0 as [? [? ?]]. auto.
  }
  {
    split; intros; simpl in *; auto.
  }
Qed.
