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
  constructor; constructor; auto; intros.
  - apply H. apply H0. assumption.
  - apply H0. apply H. assumption.
Qed.

Program Definition join_perm (p q:perm) : perm :=
  {|
    view := fun x y => (view p x y) /\ (view q x y) ;
    upd  := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y)) ;
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
  intros p q r [] []. constructor; intros; simpl in *; auto.
  induction H.
  - destruct H; auto.
  - transitivity y; auto.
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
  intros p q r [] []. constructor; intros; simpl in *; auto.
  induction H.
  - destruct H; auto.
  - transitivity y; auto.
Qed.

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

Lemma sep_at_commutative : forall x p q,
    sep_at x p q -> sep_at x q p.
Proof.
  intros. destruct H. constructor; auto.
Qed.

Lemma sep_at_anti_monotone : forall x p1 p2 q,
    sep_at x p2 q -> p1 <= p2 -> sep_at x p1 q.
Proof.
  intros x p1 p2 q sepat [lte_view lte_upd]; constructor; intros.
  - apply lte_view. apply (sep_at_view_l sepat); assumption.
  - apply (sep_at_view_r sepat).
  - apply (sep_at_upd_l sepat). apply lte_upd. assumption.
  - apply lte_view. apply (sep_at_upd_r sepat). assumption.
Qed.

Definition separate (p q : perm) : Prop :=
  forall x, view p x x -> view q x x -> sep_at x p q.

(* Equality of permissions = the symmetric closure of the ordering *)
Definition eq_perm p q : Prop := p <= q /\ q <= p.

(* Bottom is separate from everything *)
Lemma sep_at_bottom: forall p x, view p x x -> sep_at x bottom_perm p.
Proof.
  intros. unfold bottom_perm. constructor; simpl; intros; try trivial.
  rewrite <- H0. assumption.
Qed.

Lemma separate_bottom : forall p, separate bottom_perm p.
Proof.
  intros p x ? ?. apply sep_at_bottom. assumption.
Qed.

Program Definition sep_conj (p q : perm) : perm :=
  {|
    view := fun x y =>
              (view p x y) /\ (view q x y) /\ sep_at x p q /\ sep_at y p q;
    upd := clos_trans _ (fun x y => (upd p x y) \/ (upd q x y));
  |}.
Next Obligation.
  constructor.
  - repeat intro. destruct H as [? [? [? ?]]]. repeat (split; try symmetry; auto).
  - repeat intro. destruct H as [? [? [? ?]]]. destruct H0 as [? [? [? ?]]].
    repeat (split; try etransitivity; eauto).
Qed.
Next Obligation.
  constructor.
  - intro. constructor 1. left. reflexivity.
  - repeat intro. econstructor 2; eauto.
Qed.

Lemma PER_refl {A} (p : A -> A -> Prop) `{PER _ p} : forall x y, p x y -> p x x.
Proof.
  intros. etransitivity; eauto; try symmetry; eauto.
Qed.

(* Lemma sep_at_sep_conj_assoc : forall x p q r, *)
(*     sep_at x (sep_conj p q) r <-> sep_at x p (sep_conj q r). *)
(* Proof. *)
(*   split; intros. *)
(*   { *)
(*     destruct H as [[? [? [? ?]]] ?]. *)
(*     constructor; auto. *)
(*     - split; [ | split ]; auto. *)
(*       split; (constructor; auto; intros; *)
(*               [apply sep_at_upd_l0; constructor; auto | *)
(*                destruct (sep_at_upd_r0 _ H3) as [_ [? _]]; auto]). *)
(*     - intros. clear H2. destruct H1. split; [ | split; [ | split ]]; auto. *)
(*       + apply sep_at_upd_l0. constructor. left. auto. *)
(*       + constructor; auto; intros. *)
(*         * apply sep_at_upd_l0. constructor. right. auto. *)
(*         * destruct (sep_at_upd_r0 _ H1) as [_ [? _]]; auto. *)
(*       + constructor; auto; intros. *)
(*         * eapply PER_refl; intuition. symmetry. apply sep_at_upd_l1. auto. *)
(*         * eapply PER_refl; intuition. symmetry. apply sep_at_upd_l0. constructor. left. auto. *)
(*         * etransitivity. *)
(*           -- symmetry. apply sep_at_upd_l0. constructor. left. auto. *)
(*           -- apply sep_at_upd_l0. econstructor 2; constructor; eauto. *)
(*         * etransitivity. *)
(*           -- symmetry. apply sep_at_upd_l1. auto. *)
(*           -- (* specialize (sep_at_upd_r0 _ H1). *) admit. *)
(*     - admit. *)
(* Abort. *)

Lemma separate_join_is_sep_conj: forall p q, separate p q -> eq_perm (join_perm p q) (sep_conj p q).
Proof.
  intros. red in H. split; intros.
  {
    constructor; intros; simpl in *; auto.
    destruct H0 as [? [? ?]]. split; auto.
  }
  {
    constructor; intros; simpl in *; auto. destruct H0.
    split; auto. split; auto. split; apply H. (* TODO make nicer *)
    eapply PER_refl; intuition; eauto.
    eapply PER_refl; intuition; eauto.
    eapply PER_refl; intuition; symmetry; eauto.
    eapply PER_refl; intuition; symmetry; eauto.
  }
Qed.

Lemma sep_conj_top_absorb : forall p, eq_perm (sep_conj top_perm p) top_perm.
Proof.
  intros. split; split; intros; simpl in *; intuition.
Qed.

Lemma sep_conj_bottom_identity : forall p, eq_perm (sep_conj bottom_perm p) p.
Proof.
  intros. split; intros.
  {
    split; intros; simpl in *.
    - split; auto. split; auto. split.
      + apply sep_at_bottom. eapply PER_refl; intuition; eauto.
      + apply sep_at_bottom. eapply PER_refl; intuition; symmetry; eauto.
    - induction H; auto.
      + destruct H; auto. rewrite H. reflexivity.
      + etransitivity; eauto.
  }
  {
    split; intros; simpl in *.
    - destruct H as [_ [? _]]. auto.
    - constructor 1. right. auto.
  }
Qed.

Lemma lte_l_sep_conj : forall p q,
    p <= (sep_conj p q).
Proof.
  intros. constructor.
  - intros x y []; auto.
  - left; auto.
Qed.

Lemma lte_r_sep_conj : forall p q,
    q <= (sep_conj p q).
Proof.
  intros. constructor.
  - intros x y [? [? _]]; auto.
  - left; auto.
Qed.

Lemma sep_conj_commutative : forall p q, sep_conj p q <= sep_conj q p.
Proof.
  constructor.
  - intros x y [? [? [? ?]]].
    split; [ | split ; [ | split ]]; auto; try apply sep_at_commutative; auto.
  - intros. induction H.
    + destruct H; auto; constructor; auto.
    + etransitivity; eauto.
Qed.

(* Lemma sep_conj_assoc : forall p q r, eq_perm (sep_conj (sep_conj p q) r) *)
(*                                         (sep_conj p (sep_conj q r)). *)
(* Proof. *)
(*   split. *)
(*   { *)
(*     constructor; repeat intro. *)
(*     - destruct H as [? [[? [? [? ?]]] [? ?]]]. *)
(*       split; [ split ; [ | split; [ | split ] ] | split ; [ | split; [ | ] ] ]; auto. *)
(*       + split; auto. split; auto. split. *)
(*         * constructor. auto. eapply PER_refl; eauto; intuition. *)
(*           intros. *)


(* Perms = upwards-closed sets of single permissions *)
Record Perms :=
  {
    in_Perms : perm -> Prop;
    Perms_upwards_closed : forall p1 p2, in_Perms p1 -> p1 <= p2 -> in_Perms p2
  }.

(* The ordering on Perms sets is the superset ordering *)
Definition lte_Perms (P Q : Perms) : Prop :=
  forall p, in_Perms Q p -> in_Perms P p.

Instance lte_Perms_is_preorder : PreOrder lte_Perms.
Proof.
  constructor; repeat intro; auto.
Qed.

Notation "P ⊑ Q" := (lte_Perms P Q) (at level 20, right associativity).

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
    in_Perms := fun p => exists P, Ps P /\ in_Perms P p
  |}.
Next Obligation.
  exists H. split; auto.
  apply (Perms_upwards_closed _ p1); try assumption.
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
    in_Perms := fun r => exists p q, in_Perms P p /\ in_Perms Q q /\ sep_conj p q <= r
  |}.
Next Obligation.
  exists H, H1. split; auto. split; auto. etransitivity; eauto.
Defined.

Lemma sep_conj_Perms_top_identity : forall P, eq_Perms (sep_conj_Perms top_Perms P) top_Perms.
Proof.
  constructor; repeat intro.
  - inversion H.
  - destruct H as [? [? [? ?]]]. inversion H.
Qed.

Lemma sep_conj_Perms_bottom_absorb : forall P, eq_Perms (sep_conj_Perms bottom_Perms P) P.
Proof.
  constructor; repeat intro; simpl in *.
  - exists bottom_perm, p. split; [auto | split; auto].
    apply sep_conj_bottom_identity.
  - destruct H as [? [? [_ [? ?]]]].
    eapply (Perms_upwards_closed P); eauto.
    etransitivity; eauto. apply lte_r_sep_conj.
Qed.

Definition entails_Perms P Q := Q ⊑ P.

Definition impl_Perms P Q := meet_Perms (fun R => entails_Perms (sep_conj_Perms R P) Q).

Lemma sep_conj_Perms_monotonic : forall P Q R, P ⊑ Q -> sep_conj_Perms P R ⊑ sep_conj_Perms Q R.
Proof.
  repeat intro. destruct H0 as [? [? [? [? ?]]]].
  exists x, x0. auto.
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
    red. etransitivity; [ | apply H].
    unfold impl_Perms.
    rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max. intros P' [? [? ?]]. subst. auto.
Qed.

Section ts.
  From ITree Require Import
       Basics.Basics
       Core.ITreeDefinition
       Events.State
       Events.Nondeterminism
       Indexed.Sum
       Core.Subevent
       Interp.Interp.

  Context {E : Type -> Type}.
  Context {HasStateNat : stateE nat -< E}.
  Context {HasStateUnit : stateE unit -< E}.
  Context {HasNondet : nondetE -< E}.

  Definition par_match
             (par : itree E unit -> itree E unit -> itree E unit )
             (t1 t2 : itree E unit)
    : itree E unit :=
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

  CoFixpoint par (t1 t2 : itree E unit) := par_match par t1 t2.

  CoFixpoint step
             (t : itree (nondetE +' stateE nat) unit)
             (n : nat)
    : itree (nondetE +' stateE nat) unit :=
    match (observe t) with
    | RetF _ => t
    | TauF t => Tau (step t n)
    | VisF o k =>
      match o with
      | inl1 _ => (vis o (fun x => (step (k x) n)))
      | inr1 s => match s in stateE _ X return (X -> _) -> _ with
                 | Get _ => fun id => k (id n)
                 | Put _ n' => fun id => k (id tt)
                 end id
      end
    end.

  CoInductive step' : itree (nondetE +' stateE nat) unit -> nat -> itree (nondetE +' stateE nat) unit -> nat -> Prop :=
  | step_ret : forall n, step' (Ret tt) n (Ret tt) n
  | step_tau : forall t n t' n', step' t n t' n' -> step' (Tau t) n t' n'
  (* | step_nondet : forall n k, step' (vis Or k) n *)
  .

End ts.


From ExtLib Require Import
     Structures.Functor
     Structures.Monad.


Import ITreeNotations.
Import ITree.Basics.Basics.Monads.

Definition test : itree (stateE nat +' _) unit :=
  par
    (x <- (trigger (Get _)) ;; (trigger (Put _ x)))
    (par (vis (Get nat) (fun x => Ret tt))
         (Ret tt)).

Compute (burn 10 test).

Eval cbv in (burn 10 (step (trigger (Put _ 0)) 1)).
(* Eval cbn in (burn 10 (step test 1)). *)
Eval cbn in (burn 10 (run_state test 1)).
