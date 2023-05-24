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

Definition Lifetimes := list status.

(* Definition parent_of (l1 l2 : Lifetime) : Prop := *)
(*   l1 = l2 \/ *)
(*     parent l1 l2 = true. *)

(* Global Instance parent_of_trans : Transitive parent_of. *)
(* Proof. *)
(*   repeat intro. destruct H, H0; subst; unfold parent_of; auto. *)
(*   right. eapply parent_trans; eauto. *)
(* Qed. *)

(* Definition index (l : Lifetime) : nat := *)
(*   match l with *)
(*   | node index _ => index *)
(*   end. *)

(* Definition parents (l : Lifetime) : Parents := *)
(*   match l with *)
(*   | node _ parents => parents *)
(*   end. *)

(* Maybe do a lookup on l for its parents' statuses. This will implicitly end all children lifetimes hwen you end a parent lifetime *)

(* Alternatively make ls a total map, so we can keep track of *all* children *)
Definition statusOf (l : nat) (ls : Lifetimes) : option status :=
  nth_error ls l.

Definition Lifetimes_lte (ls ls' : Lifetimes) : Prop :=
  forall l, statusOf_lte (statusOf l ls) (statusOf l ls').

Global Instance Lifetimes_lte_preorder : PreOrder Lifetimes_lte.
Proof.
  constructor; repeat intro.
  - destruct (statusOf l x); [destruct s |]; cbn; auto.
  - specialize (H l). specialize (H0 l). etransitivity; eauto.
Qed.

Lemma Lifetimes_lte_app ls ls' r :
  Lifetimes_lte ls ls' ->
  Lifetimes_lte ls (ls' ++ r).
Proof.
  repeat intro. unfold statusOf. destruct (Compare_dec.dec_lt l (length ls)).
  - rewrite nth_error_app1; auto.
Admitted.

Lemma Lifetimes_lte_finished ls l :
  Lifetimes_lte ls (replace_list_index ls l finished).
Proof.
  intro l'. destruct (Compare_dec.lt_eq_lt_dec l l') as [[? | ?] | ?]; subst; unfold statusOf.
  - destruct (Compare_dec.dec_lt l (length ls)).
    + erewrite nth_error_replace_list_index_neq; eauto. reflexivity. lia.
    + erewrite nth_error_replace_list_index_neq_after; try lia.
      erewrite (proj2 (nth_error_None ls l')). reflexivity. lia.
  - rewrite nth_error_replace_list_index_eq.
    destruct (nth_error ls l'); [destruct s |]; constructor.
  - destruct (Compare_dec.dec_lt l (length ls)).
    + erewrite nth_error_replace_list_index_neq; eauto. reflexivity. lia.
    + destruct (Compare_dec.dec_lt l' (length ls)).
      * erewrite nth_error_replace_list_index_neq_before; eauto. reflexivity. lia.
      * erewrite nth_error_replace_list_index_neq_new; try lia.
        destruct (nth_error ls l'); [destruct s |]; cbn; auto.
Qed.

Lemma Lifetimes_lte_replace_list_index ls ls' l s :
  Lifetimes_lte ls ls' ->
  Lifetimes_lte (replace_list_index ls l s) (replace_list_index ls' l s).
Proof.
  repeat intro.
  destruct (Peano_dec.dec_eq_nat l l0).
  - subst. red in H. unfold statusOf in *. do 2 rewrite nth_error_replace_list_index_eq.
    reflexivity.
  - admit.
Admitted.


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
