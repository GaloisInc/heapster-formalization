From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     Relations.Relation_Operators.

Import ListNotations.

Definition config : Type := nat.

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

(* todo get rewriting to work *)
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

  (* Variant step_ : itree' E R -> config -> itree' E R -> config -> Prop := *)
  (* | step_tau' : forall t c, step_ (TauF t) c (observe t) c *)
  (* | step_nondet_true' : forall k c, step_ (VisF (subevent _ Or) k) c (observe (k true)) c *)
  (* | step_nondet_false' : forall k c, step_ (VisF (subevent _ Or) k) c (observe (k false)) c *)
  (* | step_get' : forall k c, step_ (VisF (subevent _ (Get _)) k) c (observe (k c)) c *)
  (* | step_put' : forall k c c', step_ (VisF (subevent _ (Put _ c')) k) c (observe (k tt)) c' *)
  (* . *)

  (* Definition step t c t' c' := step_ (observe t) c (observe t') c'. *)

  (* Instance test : Proper *)
  (*                   (eq_itree eq ==> *)
  (*                             eq ==> *)
  (*                             eq ==> *)
  (*                             eq ==> *)
  (*                             Basics.flip Basics.impl) step. *)
  (* Proof. *)
  (*   intros t1 t2 Heq ? ? ? ? ? ? ? ? ? ?. subst. inversion H2; subst. *)
  (*   - rewrite (itree_eta t2) in Heq. rewrite <- H0 in Heq. *)


      (*   red. rewrite <- H. *)
      (* red. rewrite <- H0 in Heq. red in Heq. red in Heq. destruct (observe y0). *)
      (* destruct (eq_itree_inv_tau _ _ Heq) as [? [? ?]]. red. rewrite H1. rewrite <- H. destruct (observe t1); inversion H. rewrite Heq in H. rewrite H1. *)
  (* Admitted. *)

  (* Instance test' t c : Proper *)
  (*                      (observing eq ==> *)
  (*                                eq ==> *)
  (*                             Basics.flip Basics.impl) (step t c). *)
  (* Proof. *)
  (*   (* intros t1 t2 Hobs ? ? ? ?. *) *)
  (*   (* subst. *) *)
  (*   (* red. red in H0. rewrite Hobs. auto. *) *)
  (* Admitted. *)

  Lemma step_bind : forall (t1 t2 : itree E R) (c1 c2 : config) (k : R -> itree E R),
      step t1 c1 t2 c2 ->
      step (t1 >>= k) c1 (t2 >>= k) c2.
  Proof.
    intros. inversion H; subst.
    -
      (* rewrite (unfold_bind_ t2 _). *)
      (* rewrite unfold_bind_. *)
      (* rewrite <- H1. rewrite <- H3. *)
      (* rewrite <- unfold_bind_. *)
      (* simpl. constructor. *)
      pose proof (bind_tau _ t2 k) as bind_tau.
      apply bisimulation_is_eq in bind_tau. rewrite bind_tau. constructor.
    (* - *)
    (*   rewrite (unfold_bind_ t2 _). *)
    (*   rewrite unfold_bind_. *)
    (*   rewrite <- H1. rewrite <- H3. *)
    (*   rewrite <- unfold_bind_. *)
    (*   simpl. constructor. *)
    (* - *)
    (*   rewrite (unfold_bind_ t2 _). *)
    (*   rewrite unfold_bind_. *)
    (*   rewrite <- H1. rewrite <- H3. *)
    (*   rewrite <- unfold_bind_. *)
    (*   simpl. constructor. *)
    (* - *)
    (*   rewrite (unfold_bind_ t2 _). *)
    (*   rewrite unfold_bind_. *)
    (*   rewrite <- H1. rewrite <- H3. *)
    (*   rewrite <- unfold_bind_. *)
    (*   simpl. constructor. *)
    (* - *)
    (*   rewrite (unfold_bind_ t2 _). *)
    (*   rewrite unfold_bind_. *)
    (*   rewrite <- H1. rewrite <- H3. *)
    (*   rewrite <- unfold_bind_. *)
    (*   simpl. constructor. *)

    -
      pose proof (bind_vis _ _ (subevent _ Or) k0 k) as bind_vis.
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
  Lemma par_step : forall (t1 t2 t' : itree E R) (c c' : config),
      step t1 c t2 c' ->
      exists t'' c'', step (par t1 t') c t'' c'' /\ step t'' c'' (par t2 t') c'.
  Proof.
    intros. inversion H; subst;
              (rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor).
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
