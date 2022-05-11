(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     FSets.FMaps.

From Heapster Require Import
     Utils
     RoseTree.

Import ListNotations.
Open Scope list_scope.
(* end hide *)

(* Lifetime keys *)
Variant status := current | finished.

Definition status_lte (s1 s2 : status) : Prop :=
  match s1, s2 with
  | finished, current => False
  | _, _ => True
  end.

(* (** [s1] subsumes [s2]: [s1] cannot finish before [s2] *) *)
(* Definition status_subsumes (s1 s2 : status) : Prop := *)
(*   match s1, s2 with *)
(*   | finished, current => False *)
(*   | _, _ => True *)
(*   end. *)

Global Instance status_lte_preorder : PreOrder status_lte.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; constructor.
  - destruct x, y, z; auto.
Qed.

Definition statusOf_lte (s1 s2 : option status) : Prop :=
  match s1, s2 with
  | Some s1, Some s2 => status_lte s1 s2
  | Some _, None => False
  | _, _ => True
  end.
Global Instance statusOf_lte_preorder : PreOrder statusOf_lte.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; cbn; auto. reflexivity.
  - destruct x, y, z; cbn in *; intuition.
    etransitivity; eauto.
Qed.

(** [s1] subsumes [s2], now with unstarted lifetimes (None) *)
Definition statusOf_subsumes (s1 s2 : option status) : Prop :=
  match s1, s2 with
  (* [s1] can't end before [s2] *)
  | Some finished, Some finished => True
  | Some finished, _ => False
    (* [s2] can't start before [s1] *)
  | None, Some _ => False
  | _, _ => True
  end.

Global Instance statusOf_subsumes_preorder : PreOrder statusOf_subsumes.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; [destruct s |]; cbn; auto.
  - destruct x, y, z; cbn in *; intuition; destruct s, s0; intuition.
Qed.

(** a [Lifetime] contains a number for disambiguation and its direct parent [Lifetime]s *)
Definition Lifetime := rose.

Definition parent_of (l1 l2 : Lifetime) : Prop :=
  l1 = l2 \/
    parent l1 l2 = true.

Global Instance parent_of_trans : Transitive parent_of.
Proof.
  repeat intro. destruct H, H0; subst; unfold parent_of; auto.
  right. eapply parent_trans; eauto.
Qed.

Definition index (l : Lifetime) : nat :=
  match l with
  | node index _ => index
  end.

(* Definition parents (l : Lifetime) : Parents := *)
(*   match l with *)
(*   | node _ parents => parents *)
(*   end. *)

Module K <: DecidableType.
  Definition t := Lifetime.
  Definition eq := @eq Lifetime.
  Definition eq_refl := @eq_refl Lifetime.
  Definition eq_sym := @eq_sym Lifetime.
  Definition eq_trans := @eq_trans Lifetime.
  Definition eq_dec := rose_eq_dec.
End K.

Module Import M := FMapWeakList.Make(K).
Module P := WProperties_fun K M.
Module F := P.F.

Definition mapT := M.t status.

Record Lifetimes : Type :=
  {
    m : mapT;

    (** Properties *)
    (* (* maybe not needed *) *)
    (* acyclic_keys : forall l, In l m -> acyclic l; *)

    parents_exist : forall l p, In l m ->
                           parent_of p l ->
                           In p m;

    parents_subsume : forall l p, In l m ->
                             parent_of p l ->
                             statusOf_subsumes (find p m) (find l m);
  }.

Definition Lifetimes_In (l : Lifetime) (ls : Lifetimes) : Prop :=
    In l (m ls).

(* Maybe do a lookup on l for its parents' statuses. This will implicitly end all children lifetimes hwen you end a parent lifetime *)

(* Alternatively make ls a total map, so we can keep track of *all* children *)
Definition statusOf (l : Lifetime) (ls : Lifetimes) : option status :=
  (* map through the parnets of l, and look for any that are in ls. If any of those are finished, then we should return finished too *)
  find l (m ls).

Definition Lifetimes_lte (ls ls' : Lifetimes) : Prop :=
  forall l, (In l (m ls) -> In l (m ls')) /\ statusOf_lte (statusOf l ls) (statusOf l ls').

Global Instance Lifetimes_lte_preorder : PreOrder Lifetimes_lte.
Proof.
  constructor; repeat intro.
  - split; auto. reflexivity.
  - split.
    + intros. apply H0. apply H; auto.
    + edestruct H, H0. etransitivity; eauto.
Qed.

(*
  Program Definition newLifetime (ls : Lifetimes) (ps : list Lifetime) (H : forall p, In p parents -> inL p ls) :
    (Lifetime * Lifetimes) :=
    let i := length (lst ls) in
    let parentIndices := map index parents in
    (
      node i parents,
      {|
        lst := lst ls ++ [(current, parentIndices)];
      |}
    ).
  Next Obligation.
  Admitted.
  Next Obligation.
    pose proof parents_subsumption.
  Admitted.
  Next Obligation.
  Admitted.
 *)

Program Definition endLifetime (l : Lifetime) (ls : Lifetimes) (* and some proof that all the parents are finished? *) : Lifetimes.
Admitted.

(** [l1] subsumes [l2] *)
Definition subsumes (l1 l2 : Lifetime) : Prop :=
  l1 = l2 \/ parent_of l1 l2.

#[global] Instance subsumes_preorder : PreOrder subsumes.
Proof.
  constructor; repeat intro; cbn; auto.
  - left; auto.
  - unfold subsumes in *. destruct H, H0; subst; auto. right.
    etransitivity; eauto.
Qed.

Lemma parent_find l1 l2 l s :
  parent_of l1 l2 ->
  @find status l1 (m l) = Some s ->
  @find status l2 (m l) = Some s.
Proof.
  intros.
  destruct l. cbn in *.
Admitted.

Lemma subsumes_status l :
  forall l1 l2, subsumes l1 l2 ->
           statusOf_subsumes (statusOf l1 l) (statusOf l2 l).
Proof.
    intros. unfold subsumes in H. destruct H; subst; auto.
    reflexivity.
    destruct (F.In_dec (m l) l2).
    - apply parents_subsume; auto.
    - unfold statusOf. apply F.not_find_in_iff in n. rewrite n.
      destruct (find l1 (m l)) eqn:?; cbn; auto.
      destruct s; auto. erewrite parent_find in n; eauto. inversion n.
Qed.

(*
Variant Lifetime := current | finished.

Definition Lifetimes := list Lifetime.

(** lifetime helpers **)

Definition lifetime : Lifetimes -> nat -> option Lifetime :=
  @nth_error Lifetime.

(* Definition replace_lifetime (l : Lifetimes) (n : nat) (new : Lifetime) : Lifetimes := *)
(*   replace_list_index l n new. *)

(* Lemma replace_lifetime_same c n l : *)
(*   lifetime c n = Some l -> replace_lifetime c n l = c. *)
(* Proof. *)
(*   apply replace_list_index_eq. *)
(* Qed. *)

(* Lemma lifetime_replace_lifetime c n l : *)
(*   lifetime (replace_lifetime c n l) n = Some l. *)
(* Proof. *)
(*   apply nth_error_replace_list_index_eq. *)
(* Qed. *)

(** [n1] in the lifetime list [x1] subsumes [n2] in the lifetime list [x2] *)
Definition subsumes n1 n2 x1 x2 :=
  (Some current = lifetime x2 n2 -> Some current = lifetime x1 n1) /\
  (Some finished = lifetime x1 n1 -> Some finished = lifetime x2 n2) /\
  (None = lifetime x1 n1 -> None = lifetime x2 n2).

(* TODO: generalize to a single lemma *)
Instance subsumes_preorder x : PreOrder (fun a b => subsumes a b x x).
Proof.
  unfold subsumes.
  constructor; [repeat intro; auto |].
  intros n1 n2 n3. intros (? & ? & ?) (? & ? & ?). split; [| split]; intros.
  - apply H. apply H2; auto.
  - apply H3. apply H0; auto.
  - apply H4. apply H1; auto.
Qed.
Instance subsumes_preorder' x : PreOrder (subsumes x x).
Proof.
  unfold subsumes.
  constructor; [repeat intro; auto |].
  intros n1 n2 n3. intros (? & ? & ?) (? & ? & ?). split; [| split]; intros.
  - apply H. apply H2; auto.
  - apply H3. apply H0; auto.
  - apply H4. apply H1; auto.
Qed.

Lemma subsumes_decidable n1 n2 l1 l2 : decidable (subsumes n1 n2 l1 l2).
Proof.
  unfold subsumes.
Admitted.

Lemma not_subsumes n1 n2 n3 l :
  ~subsumes n1 n3 l l -> ~subsumes n1 n2 l l \/ ~subsumes n2 n3 l l.
Proof.
  intro H. red in H.
  destruct (lifetime l n1) eqn:Hl1; [destruct l0 |];
    (destruct (lifetime l n2) eqn:Hl2; [destruct l0 |]);
    (destruct (lifetime l n3) eqn:Hl3; [destruct l0 |]).
  all: try solve [exfalso; apply H; split; [| split];
                  rewrite Hl1, Hl3; auto; intro Hc; discriminate Hc].
  all: try solve [left; intro H'; red in H'; rewrite Hl1, Hl2 in H';
                  destruct H' as (H1 & H2 & H3);
                  try solve [discriminate H1; auto];
                  try solve [discriminate H2; auto];
                  try solve [discriminate H3; auto]].
  all: try solve [right; intro H'; red in H'; rewrite Hl2, Hl3 in H';
                  destruct H' as (H1 & H2 & H3);
                  try solve [discriminate H1; auto];
                  try solve [discriminate H2; auto];
                  try solve [discriminate H3; auto]].
Qed.

(** Lifetime ordering **)
Definition lifetime_lte (l1 l2 : option Lifetime) : Prop :=
  match l1, l2 with
  | None, _ => True
  | Some current, None => False
  | Some current, _ => True
  | Some finished, Some finished => True
  | _, _ => False
  end.

Instance lifetime_lte_preorder : PreOrder lifetime_lte.
Proof.
  constructor; repeat intro.
  - destruct x as [[] |]; simpl; auto.
  - destruct x as [[] |], y as [[] |], z as [[] |]; simpl; intuition.
Qed.

*)
