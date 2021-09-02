(** * Interaction trees: core definitions *)

(* begin hide *)
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

From Coq Require Import
     JMeq.

From Paco Require Import paco.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.
(* end hide *)

(** ** The type of interaction trees *)

(** An [itree E R] is the denotation of a program as coinductive
    (possibly infinite) tree where the leaves [Ret] are labeled with
    [R] and every node is either a [Tau] node with one child, or a
    branching node [Vis] with a _visible event_ [E X] that branches
    on the values of [X]. *)

Section itree.

  Context {E : Type -> Type} {R : Type}.

  (** The type [itree] is defined as the final coalgebra ("greatest
      fixed point") of the functor [itreeF]. *)
  Variant itreeF (itree : Type) :=
  | RetF (r : R)
  | TauF {X : Type} (t : X -> itree)
  | VisF {X : Type} (e : E X) (k : X -> itree)
  .

  (** We define non-recursive types such as [itreeF] using the [Variant]
      command. The main practical difference from [Inductive] is that
      [Variant] does not generate any induction schemes (which are
      unnecessary). *)

  CoInductive itree : Type := go
  { _observe : itreeF itree }.

  (** A primitive projection, such as [_observe], must always be
      applied. To be used as a function, wrap it explicitly:
      [fun x => _observe x] or [observe] (defined below). *)

  (* Notes about using [itree]:

     - You should simplify using [cbn] rather than [simpl] when working
       with terms of the form [observe e] where [e] is defined by
       [CoFixpoint] (as in [bind] and [map] below).  [simpl] does not
       unfold the definition properly to expose the [observe t] term.

     - Once you have [observe t] as the subject of [match], you can
       [destruct (observe t)] to do the case split.
   *)

End itree.

(* begin hide *)
(*
  The following line removes the warning on >=8.10, but is incompatible for <8.10
 *)
(* Declare Scope itree_scope. *)
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Arguments itree _ _ : clear implicits.
Arguments itreeF _ _ : clear implicits.
(* end hide *)

(** An [itree'] is a "forced" [itree]. It is the type of inputs
    of [go], and outputs of [observe]. *)
Notation itree' E R := (itreeF E R (itree E R)).

(** We wrap the primitive projection [_observe] in a function
    [observe]. *)
Definition observe {E R} (t : itree E R) : itree' E R := @_observe E R t.

(** Note that when [_observe] appears unapplied in an expression,
    it is implicitly wrapped in a function. However, there is no
    way to distinguish whether such wrapping took place, so relying
    on this behavior can lead to confusion.

    We recommend to always use a primitive projection applied,
    and wrap it in a function explicitly like the above to pass
    around as a first-order function. *)

(** We introduce notation for the [Tau], [Ret], and [Vis] constructors. Using
    notation rather than definitions works better for extraction.  (The [spin]
    definition, given below does not extract correctly if [Tau] is a definition.)

    Using this notation means that we occasionally have to eta expand, e.g.
    writing [Vis e (fun x => Ret x)] instead of [Vis e Ret]. (In this
    particular case, this is [ITree.trigger].)
*)
Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).

(** ** Main operations on [itree] *)

(** The core definitions are wrapped in a module for namespacing.
    They are meant to be used qualified (e.g., ITree.bind) or
    via notations (e.g., [>>=]). *)

(** *** How to write cofixpoints *)

(** We define cofixpoints in two steps: first a plain definition
    (prefixed with an [_], e.g., [_bind], [_iter]) defines the body
    of the function:

    - it takes the recursive call ([bind]) as a parameter;
    - if we are deconstructing an itree, this body takes
      the unwrapped [itreeF];

    second the actual [CoFixpoint] (or, equivalently, [cofix]) ties
    the knot, applying [observe] to any [itree] parameters. *)

(** This style allows us to keep [cofix] from ever appearing in
    proofs, which could otherwise get quite unwieldly.
    For every [CoFixpoint] (such as [bind]), we prove an unfolding
    lemma to rewrite it as a term whose head is [_bind], without
    any [cofix] above it.
[[
    unfold_bind : observe (bind t k)
                = observe (_bind (fun t' => bind t' k) t)
]]
    Note that this is an equality "up to" [observe]. It would not be
    provable if it were a plain equality:
[[
    bind t k = _bind (...) t  (* unfold the definition of [bind]... *)
    (cofix bind' t1 := _bind (...) t1) t = _bind (...) t1
]]
    The [cofix] is stuck, and can only be unstuck under the primitive
    projection [_observe] (which is wrapped by [observe]).
 *)

(** *** Definitions *)

(** These are meant to be imported qualified, e.g., [ITree.bind],
    [ITree.trigger], to avoid ambiguity with identifiers of the same
    name (some of which are overloaded generalizations of these).
 *)
Module ITree.

(** [bind]: monadic composition, tree substitution, sequencing of
    computations. [bind t k] is also denoted by [t >>= k] and using
    "do-notation" [x <- t ;; k x]. *)

Section bind.
  Context {E : Type -> Type} {T U : Type}.
  (* We can keep the continuation outside the cofixpoint.
     In particular, this allows us to nest [bind] in other cofixpoints,
     as long as the recursive occurences are in the continuation
     (i.e., this makes it easy to define tail-recursive functions).
   *)
  Variable k : T -> itree E U.

  Definition _bind
             (bind : itree E T -> itree E U)
             (oc : itreeF E T (itree E T)) : itree E U :=
    match oc with
    | RetF r => k r
    | TauF t => Tau (fun x => bind (t x))
    | VisF e h => Vis e (fun x => bind (h x))
    end.

  CoFixpoint bind' (t : itree E T) : itree E U :=
    _bind bind' (observe t).

End bind.

Arguments _bind _ _ /.


Notation bind c k := (bind' k c).


(** Monadic composition of continuations (i.e., Kleisli composition).
 *)
Definition cat {E T U V}
           (k : T -> itree E U) (h : U -> itree E V) :
  T -> itree E V :=
  fun t => bind' h (k t).

(** [iter]: See [Basics.Basics.MonadIter]. *)

(* [on_left lr l t]: run a computation [t] if the first argument is an [inl l].
   [l] must be a variable (used as a pattern), free in the expression [t]:
   - [on_left (inl x) l t = t{l := x}]
   - [on_left (inr y) l t = Ret y]
 *)
Notation on_left lr l t :=
  (match lr with
  | inl l => t
  | inr r => Ret r
  end) (only parsing).

(* Note: here we must be careful to call [iter_ l] under [Tau] to avoid an eager
   infinite loop if [step i] is always of the form [Ret (inl _)] (cf. issue #182). *)
Definition iter {E : Type -> Type} {R I: Type}
           (step : I -> itree E (I + R)) : I -> itree E R :=
  cofix iter_ i := bind (step i) (fun lr => on_left lr l (Tau (fun _ : unit => iter_ l))).

(* note(gmm): There needs to be generic automation for monads to simplify
 * using the monad laws up to a setoid.
 * this would be *really* useful to a lot of projects.
 *
 * this will be especially important for this project because coinductives
 * don't simplify very nicely.
 *)

(** Functorial map ([fmap] in Haskell) *)
Definition map {E R S} (f : R -> S)  (t : itree E R) : itree E S :=
  bind t (fun x => Ret (f x)).

(** Atomic itrees triggering a single event. *)
Definition trigger {E : Type -> Type} : forall X, E X -> itree E X :=
  fun R e => Vis e (fun x => Ret x).

(** Ignore the result of a tree. *)
Definition ignore {E R} : itree E R -> itree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {E R} : itree E R := Tau (fun _ : unit => spin).

(** Repeat a computation infinitely. *)
Definition forever {E R S} (t : itree E R) : itree E S :=
  cofix forever_t := bind t (fun _ => Tau (fun _ : unit => forever_t)).

End ITree.

(** ** Notations *)

(** Sometimes it's more convenient to work without the type classes
    [Monad], etc. When functions using type classes are specialized,
    they simplify easily, so lemmas without classes are easier
    to apply than lemmas with.

    We can also make ExtLib's [bind] opaque, in which case it still
    doesn't hurt to have these notations around.
 *)

Module ITreeNotations.
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 58, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 61, t1 at next level, right associativity) : itree_scope.
Notation "` x : t <- t1 ;; t2" := (ITree.bind t1 (fun x : t => t2))
  (at level 61, t at next level, t1 at next level, x ident, right associativity, only parsing) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 61, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 61, t1 at next level, p pattern, right associativity) : itree_scope.
Infix ">=>" := ITree.cat (at level 61, right associativity) : itree_scope.
End ITreeNotations.

(** ** Instances *)

Instance Functor_itree {E} : Functor (itree E) :=
{ fmap := @ITree.map E }.

(* Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
   [pure] and [ret] to make the extracted code respect OCaml's
   value restriction. *)
Instance Applicative_itree {E} : Applicative (itree E) :=
{ pure := fun _ x => Ret x
; ap := fun _ _ f x =>
          ITree.bind f (fun f => ITree.bind x (fun x => Ret (f x)))
}.

Instance Monad_itree {E} : Monad (itree E) :=
{| ret := fun _ x => Ret x
;  bind := fun T U t k => @ITree.bind' E T U k t
|}.

(** ** Tactics *)

(* [inv], [rewrite_everywhere], [..._except] are general purpose *)

Lemma hexploit_mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.
Ltac hexploit x := eapply hexploit_mp; [eapply x|].

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Ltac inv H := inversion H; clear H; subst.

Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).

Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                 match H with X => fail 1 | _ => rewrite lem in H end
             end); repeat rewrite lem).

Ltac genobs x ox := remember (observe x) as ox.
Ltac genobs_clear x ox := genobs x ox; match goal with [H: ox = observe x |- _] => clear H x end.
Ltac simpobs := repeat match goal with [H: _ = observe _ |- _] =>
                    rewrite_everywhere_except (@eq_sym _ _ _ H) H
                end.

Section eqit.
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  Inductive refF (ref : itree E R1 -> itree E R2 -> Prop) :
    itree' E R1 -> itree' E R2 -> Prop :=
  | EqRet r1 r2
          (REL: RR r1 r2):
      refF ref (RetF r1) (RetF r2)
  | EqTau {X1 X2} m1 m2
          (REL: forall (x1 : X1), exists (x2 : X2), ref (m1 x1) (m2 x2)):
      refF ref (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2
          (REL: forall v, ref (k1 v) (k2 v) : Prop):
      refF ref (VisF e k1) (VisF e k2)
  | EqTauL {X} t1 ot2
           (REL: forall (x : X), refF ref (observe (t1 x)) ot2):
      refF ref (TauF t1) ot2
  | EqTauR {X} ot1 t2 (x : X)
           (REL: refF ref ot1 (observe (t2 x))):
      refF ref ot1 (TauF t2)
  .
  Hint Constructors refF: core.


  Definition ref_ ref :
    itree E R1 -> itree E R2 -> Prop :=
    fun t1 t2 => refF ref (observe t1) (observe t2).
  Hint Unfold ref_: core.

  Lemma refF_mono x0 x1 ref ref'
        (IN: refF ref x0 x1)
        (LE: ref <2= ref'):
    refF ref' x0 x1.
  Proof.
    intros. induction IN; eauto.
    econstructor; eauto. intros. destruct (REL x1). exists x. eauto.
  Qed.

  Lemma ref__mono : monotone2 ref_.
  Proof.
    do 2 red. intros. eapply refF_mono; eauto.
  Qed.

  Hint Resolve ref__mono : paco.

  Definition ref : itree E R1 -> itree E R2 -> Prop :=
    paco2 ref_ bot2.

End eqit.



(* This exists in the stdlib as [ProofIrrelevance.inj_pair2], but we reprove
   it to not depend on proof irrelevance (we use axiom [JMeq.JMeq_eq] instead) *)
Lemma inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
    existT P p x = existT P p y -> x = y.
Proof.
  intros. apply JMeq_eq.
  refine (
      match H in _ = w return JMeq x (projT2 w) with
      | eq_refl => JMeq_refl
      end).
Qed.

Lemma ref_refl {E R} (t : itree E R) : ref eq t t.
Proof.
  revert t. pcofix CIH.
  pstep. red. intros t. destruct (observe t); try constructor; auto.
  intros x. exists x. right. auto.
Qed.

Goal forall {E}, ref eq (Ret 1 : itree E nat) (Tau (fun b : bool => if b then Ret 1 else Ret 2)).
Proof.
  intros. pstep. red. apply EqTauR with (x := true).
  constructor; auto.
Qed.

Goal forall {E}, ~ ref eq (Tau (fun b : bool => if b then Ret 1 else Ret 2)) (Ret 1 : itree E nat).
Proof.
  intros ? ?. pinversion H. 2: { (* todo *) apply ref__mono. }.
  clear H; subst. apply inj_pair2 in H2. subst. specialize (REL false).
  inversion REL. inversion REL0.
Qed.

Variant test : Type -> Type :=
| Event : nat -> test unit
.

Goal ref eq
     (Tau (fun b : bool => if b then Vis (Event 1) (fun _ => Ret 1) else Vis (Event 1) (fun _ => Ret 2)))
     (Vis (Event 1) (fun _ => Tau (fun b : bool => if b then Ret 1 else Ret 2))).
Proof.
  pstep. constructor. intros [].
  - constructor. intros. left. pstep. apply EqTauR with (x := true). constructor; auto.
  - constructor. intros. left. pstep. apply EqTauR with (x := false). constructor; auto.
Qed.

Goal ~ ref eq
     (Vis (Event 1) (fun _ => Tau (fun b : bool => if b then Ret 1 else Ret 2)))
     (Tau (fun b : bool => if b then Vis (Event 1) (fun _ => Ret 1) else Vis (Event 1) (fun _ => Ret 2))).
Proof.
  intro. pinversion H. 2: apply ref__mono.
  apply inj_pair2 in H3. clear H; subst. destruct x.
  - inversion REL; clear REL.
    apply inj_pair2 in H1.
    apply inj_pair2 in H2.
    apply inj_pair2 in H.
    apply inj_pair2 in H4.
    subst. simpl in *. specialize (REL0 tt). pclearbot.
    pinversion REL0; clear REL0. 2: apply ref__mono.
    apply inj_pair2 in H2. subst. specialize (REL false). inversion REL. inversion REL0.
  - inversion REL; clear REL.
    apply inj_pair2 in H1.
    apply inj_pair2 in H2.
    apply inj_pair2 in H.
    apply inj_pair2 in H4.
    subst. simpl in *. specialize (REL0 tt). pclearbot.
    pinversion REL0; clear REL0. 2: apply ref__mono.
    apply inj_pair2 in H2. subst. specialize (REL true). inversion REL. inversion REL0.
Qed.
