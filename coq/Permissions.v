From Coq Require Import
     (* Classes.RelationClasses *)
     Relations.Relations
     Relations.Relation_Operators
     Lists.List.

Import ListNotations.

Parameter T : Type.
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
    upd  := fun x y => clos_trans _ (fun x y => (upd p x y) \/ (upd q x y)) x y ;
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
      induction H.
      * inversion H0; subst.
Abort.

Lemma join_lte_l : forall p q,
    lte_perm p (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.

Lemma join_lte_r : forall p q,
    lte_perm q (join_perm p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
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
  intros p1 p2 q HSep Hlt.
  destruct HSep. destruct Hlt.
  constructor; auto.
Qed.
