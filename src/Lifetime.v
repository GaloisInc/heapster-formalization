(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms.

From Heapster Require Import
     Utils
     Permissions.

Import ListNotations.
(* end hide *)

Variant Lifetime := current | finished.
Definition Lifetimes := list Lifetime.

(** lifetime helpers **)

Definition lifetime : Lifetimes -> nat -> option Lifetime :=
  @nth_error Lifetime.

Definition replace_lifetime (l : Lifetimes) (n : nat) (new : Lifetime) : Lifetimes :=
  replace_list_index l n new.

Lemma replace_lifetime_same c n l :
  lifetime c n = Some l -> replace_lifetime c n l = c.
Proof.
  apply replace_list_index_eq.
Qed.

Lemma lifetime_replace_lifetime c n l :
  lifetime (replace_lifetime c n l) n = Some l.
Proof.
  apply nth_error_replace_list_index_eq.
Qed.

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

Section LifetimePerms.

  Context {C : Type}.
  Context `{Hlens: Lens C Lifetimes}.

  Definition lifetime_invariant x y :=
    (forall n n', subsumes n' n (lget x) (lget x) ->
             subsumes n' n (lget y) (lget y)) /\
      (forall n, lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n)).

  Instance lifetime_invariant_preorder : PreOrder lifetime_invariant.
  Proof.
    split; [split; intuition |].
    - intros ? ? ? [] []. split; auto; etransitivity; eauto.
  Qed.

  Definition monotonic_at (p : @perm C) (n : nat) x y : Prop :=
    guar p x y -> lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n).

  Instance monotonic_at_reflexive p n : Reflexive (monotonic_at p n).
  Proof.
    repeat intro. reflexivity.
  Qed.

  Lemma bottom_monotonic_at n : forall x y, monotonic_at bottom_perm n x y.
  Proof.
    repeat intro. simpl in H. subst. reflexivity.
  Qed.

  Definition monotonic (P : Perms) (n : nat) : Prop :=
    forall p, p ∈ P -> exists p', p' <= p /\ p' ∈ P /\ forall x y, monotonic_at p' n x y.

  Lemma monotonic_bottom n : monotonic bottom_Perms n.
  Proof.
    repeat intro. exists bottom_perm. split; [| split].
    apply bottom_perm_is_bottom. auto. apply bottom_monotonic_at.
  Qed.

  Program Definition restrict_monotonic_at (p : perm) (n : nat) : @perm C :=
    {|
      pre := pre p;
      rely := rely p;
      guar := fun x y => guar p x y /\ monotonic_at p n x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; intuition.
    - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto.
  Qed.
  Next Obligation.
    respects.
  Qed.

  Lemma restrict_monotonic_at_monotone p p' n :
    p <= p' -> restrict_monotonic_at p n <= restrict_monotonic_at p' n.
  Proof.
    intros []. constructor; intros; simpl; auto. destruct H.
    split; auto. intro. auto.
  Qed.

  Lemma restrict_monotonic_at_lte p n : restrict_monotonic_at p n <= p.
  Proof.
    constructor; intros; simpl in *; intuition.
  Qed.

  Definition invariant_at (p : perm) (n : nat) : Prop :=
    forall l1 l2 x y, guar p x y <-> guar p (replace_lifetime x n l1) (replace_lifetime y n l2).

  Lemma invariant_l p n (Hinv : invariant_at p n) :
    forall l1 l2 x y, lifetime y n = Some l2 ->
                 guar p x y <-> guar p (replace_lifetime x n l1) y.
  Proof.
    intros.
    erewrite <- (replace_list_index_eq _ y n l2) at 2; auto.
  Qed.

  Lemma invariant_r p n (Hinv : invariant_at p n) :
    forall l1 l2 x y, lifetime x n = Some l1 ->
                 guar p x y <-> guar p x (replace_lifetime y n l2).
  Proof.
    intros.
    rewrite <- (replace_list_index_eq _ x n l1) at 2; auto.
  Qed.

  (* Note: does not have permission to start or end the lifetime [n] *)
  Program Definition when (n : nat) (p : @perm C) : perm :=
    {|
      pre := fun x =>
               (lifetime (lget x) n = None \/ lifetime (lget x) n = Some current) ->
               pre p x;
      rely := fun x y =>
                lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n) /\
                  ((lifetime (lget y) n = None \/
                      lifetime (lget y) n = Some current) ->
                   rely p x y);
                   (* \/ *)
                   (*   y = lput x (replace_lifetime (lget x) n current)); *)
                  (* (lifetime (lget x) n = None -> *)
                  (*  lifetime (lget y) n = Some current -> *)
                  (*  pre p y); *)
      guar := fun x y => x = y \/
                        lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n) /\
                          lifetime (lget x) n = Some current /\
                          lifetime (lget y) n = Some current /\
                          guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct (lifetime (lget x) n) as [[] |]; intuition;
        try discriminate H; try discriminate H0.
    - destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros [].
      + admit.
      + admit.

      (* split; auto. *)
      (* + intros. *)
      (*   assert (lifetime (lget y) n = Some current). *)
      (*   { *)
      (*     rewrite H5 in H. rewrite H6 in H0. *)
      (*     destruct (lifetime (lget y) n); [destruct l |]; auto. *)
      (*     - inversion H0. *)
      (*     - inversion H. *)
      (*   } *)
      (*   etransitivity; eauto. *)
      (* + intros. *)
      (*   destruct (lifetime (lget y) n); [destruct l |]; auto. *)
      (*   * eapply pre_respects; eauto. *)
        (*   * rewrite H6 in H0. inversion H0. *)
  Admitted.
  Next Obligation.
    constructor; repeat intro; auto.
    decompose [and or] H; decompose [and or] H0; subst; auto.
    right. split; [| split; [| split]]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct H1.
    - rewrite H1 in H.
      destruct (lifetime (lget x) n); [destruct l |]; auto; inversion H.
      eapply pre_respects; eauto.
    - rewrite H1 in H.
      destruct (lifetime (lget x) n); [destruct l |]; auto; inversion H.
      + eapply pre_respects; eauto.
      + eapply pre_respects; eauto.
  Qed.

  Lemma when_monotone n p1 p2 : p1 <= p2 -> when n p1 <= when n p2.
  Proof.
    intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 7.
  Qed.

  Instance Proper_lte_perm_when :
    Proper (eq ==> lte_perm ==> lte_perm) when.
  Proof.
    repeat intro; subst. apply when_monotone; auto.
  Qed.

  Instance Proper_eq_perm_when :
    Proper (eq ==> eq_perm ==> eq_perm) when.
  Proof.
    repeat intro; subst. split; apply when_monotone; auto.
  Qed.

  Lemma restrict_monotonic_at_when p n : when n p ≡≡ restrict_monotonic_at (when n p) n.
  Proof.
    split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
    decompose [and or] H; subst; try solve [intuition]. split; auto.
    intro. rewrite H0, H2. reflexivity.
  Qed.
  Lemma when_restrict_monotonic_at p n : when n p ≡≡ when n (restrict_monotonic_at p n).
  Proof.
    split; constructor; intros; simpl in *; intuition.
    right; intuition. intro. rewrite H0, H1. reflexivity.
  Qed.

  (* Gives us permission to end the lifetime [n], which gives us back [p] *)
  Program Definition owned (n : nat) (ls : nat -> Prop) (p : perm) : @perm C :=
    {|
      (* TODO: probably need soemthing with subsumes *)
      pre := fun x => lifetime (lget x) n = Some current;
      rely := fun x y => lifetime (lget x) n = lifetime (lget y) n /\
                        (forall l, ls l -> subsumes l l (lget x) (lget y)) /\ (* TODO: double check this *)
                        (lifetime (lget x) n = Some finished -> rely p x y);
      guar := fun x y => x = y \/
                        lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n) /\
                          lifetime (lget y) n = Some finished /\
                          guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
    - split; intuition.
    - decompose [and] H. decompose [and] H0. clear H H0.
      split; [| split]; intros.
      + etransitivity; eauto.
      + etransitivity. apply H3; auto. auto.
      + etransitivity. eauto. apply H7; auto. rewrite <- H1. auto.
  Qed.
  Next Obligation.
    constructor; repeat intro; auto.
    decompose [and or] H; decompose [and or] H0; subst; auto.
    right. split; [| split]; auto; etransitivity; eauto.
  Qed.

  Lemma owned_monotone n ls p1 p2 : p1 <= p2 -> owned n ls p1 <= owned n ls p2.
  Proof.
    intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 6.
  Qed.

  Instance Proper_lte_perm_owned :
    Proper (eq ==> eq ==> lte_perm ==> lte_perm) owned.
  Proof.
    repeat intro; subst. apply owned_monotone; auto.
  Qed.

  Instance Proper_eq_perm_owned :
    Proper (eq ==> eq ==> eq_perm ==> eq_perm) owned.
  Proof.
    repeat intro; subst. split; apply owned_monotone; auto.
  Qed.

  Lemma restrict_monotonic_at_owned n ls p : owned n ls p ≡≡ restrict_monotonic_at (owned n ls p) n.
  Proof.
    split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
    decompose [and or] H; subst; try solve [intuition]. split; auto. clear H.
    intro. rewrite H0. destruct (lifetime (lget x) n) as [[] |]; simpl; auto.
  Qed.
  Lemma owned_restrict_monotonic_at n ls p : owned n ls p ≡≡ owned n ls (restrict_monotonic_at p n).
  Proof.
    split; constructor; intros; simpl in *; intuition.
    right; intuition. intro. auto.
  Qed.

  (* trivial direction *)
  Lemma foo' n ls p q :
    owned n ls (restrict_monotonic_at p n ** restrict_monotonic_at q n) <=
      owned n ls (restrict_monotonic_at (p ** q) n).
  Proof.
    rewrite <- owned_restrict_monotonic_at. apply owned_monotone.
    apply sep_conj_perm_monotone; apply restrict_monotonic_at_lte.
  Qed.

  Lemma lifetimes_sep_gen p q n ls :
    p ⊥ owned n ls q -> when n p ⊥ owned n ls (p ** q).
  Proof.
    split; intros.
    - simpl in H0. decompose [and or] H0; [subst; intuition |]. clear H0.
      simpl. split; auto. intros [].
      + rewrite H0 in H1. inversion H1.
      + rewrite H0 in H1. inversion H1.
    - simpl in H0. decompose [and or] H0; [subst; intuition |].
      simpl. split; [| split].
      + rewrite H1, H3; auto.
      + intros. destruct H. apply sep_r; auto.
      + intros. rewrite H1 in H4. discriminate H4.
  Qed.

  (* no longer true after adding [ls]. Fortunately it's not used. *)
  (* not actually a special case of the above *)
  (* Lemma lifetimes_sep n p ls : when n p ⊥ owned n ls p. *)
  (* Proof. *)
  (*   constructor; intros; simpl in H; auto. *)
  (*   - decompose [and or] H; subst; try reflexivity. *)
  (*     simpl. right; left; auto. *)
  (*   - decompose [and or] H; subst; try reflexivity. *)
  (*     simpl. split; [| split]. *)
  (*     + rewrite H2, H0. auto. *)
  (*     + intros. *)
  (*     + intros. rewrite H1 in H2. discriminate H2. *)
  (* Qed. *)

  Lemma convert p q n ls (Hmon : forall x y, monotonic_at p n x y) (Hmon' : forall x y, monotonic_at q n x y) :
    when n p ** owned n ls (p ** q) <= p ** owned n ls q.
  Proof.
    split; intros.
    - simpl in *. decompose [and or] H; auto. split; auto. split; auto.
      eapply lifetimes_sep_gen; eauto.
    - simpl in *. destruct H as (? & ? & ? & ?). split; auto.
      destruct (lifetime (lget x) n) as [[] | ]; split; auto; rewrite <- H0; constructor.
    - simpl in H. induction H. 2: { econstructor 2; eauto. }
      decompose [and or] H; simpl; subst; try solve [constructor; auto].
      clear H. rename H0 into Hlte, H1 into Hy, H3 into Hguar.
      apply Operators_Properties.clos_trans_t1n_iff.
      apply Operators_Properties.clos_trans_t1n_iff in Hguar.

      induction Hguar.
      + constructor 1. destruct H; [left | right]; auto.
      + econstructor 2.
        2: { apply IHHguar; auto. rewrite Hy.
             destruct (lifetime (lget y) n); [destruct l |]; constructor.
        }
        destruct H.
        left; auto. right; right; auto. split; [| split]; auto.
        (* TODO: q should not be able to change lifetimes *) admit.
        (* TODO: similarly, p and q should not be able to change lifetimes *) admit.
  Admitted.

  (* special case of convert *)
  Lemma convert_bottom p n ls (Hmon : forall x y, monotonic_at p n x y) :
    when n p ** owned n ls p <= p ** owned n ls bottom_perm.
  Proof.
    rewrite <- (sep_conj_perm_bottom p) at 2. apply convert; auto.
    repeat intro. simpl in H. subst. reflexivity.
  Qed.

(* Lemma lcurrent_pre_trans' x n1 n2 n3 : *)
(*     lcurrent_pre x n1 n3 -> *)
(*     lcurrent_pre x n1 n2 /\ lcurrent_pre x n2 n3. *)
(* Proof. *)
(*   unfold lcurrent_pre. split. *)
(*   - split. *)
(*     + intro. apply H. *)
  (* Admitted. *)

  (** The naive defn is transitive, at least *)
(*    Program Definition lcurrent n1 n2 : @perm C :=
    {|
      pre x := subsumes n1 n2 (lget x) (lget x);
      rely x y := x = y \/
                    subsumes n1 n2 (lget x) (lget x) /\
                    subsumes n1 n2 (lget y) (lget y);
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; try solve [intuition].
    destruct H, H0; subst; auto.
    right. destruct H, H0. split; eapply subsumes_preorder; eauto; reflexivity.
  Qed.
  Next Obligation.
    constructor; repeat intro; subst; intuition.
  Qed.
  Next Obligation.
    destruct H; subst; auto. destruct H; intuition.
  Qed.

  Lemma lcurrent_transitive n1 n2 n3 :
    lcurrent n1 n3 <= lcurrent n1 n2 ** lcurrent n2 n3.
  Proof.
    constructor; intros; cbn; intuition.
    - destruct H as (? & ? & ?). simpl in *. eapply subsumes_preorder; eauto.
    - destruct H. simpl in *. destruct H, H0; subst; auto. right.
      destruct H, H0. split; auto; eapply subsumes_preorder; eauto.
  Qed.
*)

  (** n1 subsumes n2, and the rely states that lifetimes don't do weird stuff. **)
  Program Definition lcurrent n1 n2 (H : forall x, subsumes n1 n2 x x) : @perm C :=
    {|
      pre x := True;
      rely x y := True;
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
  Qed.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.
  (* Next Obligation. *)
  (*   destruct H; subst; auto. eapply absurd; eauto. *)
  (* Qed. *)

  (* Program Definition lcurrent n1 n2 : @perm C := *)
  (*   {| *)
  (*     pre x := subsumes n1 n2 (lget x) (lget x); *)
  (*     rely x y := x = y \/ *)
  (*                   lifetime_invariant x y /\ *)
  (*                     (~subsumes n1 n2 (lget x) (lget x) \/ *)
  (*                        subsumes n1 n2 (lget x) (lget x) /\ *)
  (*                        subsumes n1 n2 (lget y) (lget y)); *)
  (*     guar x y := x = y \/ lifetime_invariant x y /\ *)
  (*                         ~subsumes n1 n2 (lget x) (lget x) /\ *)
  (*                         lifetime (lget x) n2 = lifetime (lget y) n2; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro; try solve [intuition]. *)
  (*   destruct H, H0; subst; auto. *)
  (*   right. destruct H, H0. split; [etransitivity; eauto | intuition]. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   constructor; auto. intros ? ? ? [? | [? [? ?]]] [? | [? [? ?]]]; subst; auto. *)
  (*   right. split; [| split]; auto; etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct H; subst; auto. destruct H; intuition. *)
  (* Qed. *)

  Lemma lcurrent_sep n1 n2 H :
    lcurrent n1 n2 H ⊥ lcurrent n1 n2 H.
  Proof.
    constructor; intros ? ? []; reflexivity.
  Qed.

  Lemma lcurrent_transitive n1 n2 n3 H12 H23 H13 :
    lcurrent n1 n3 H13 <= lcurrent n1 n2 H12 ** lcurrent n2 n3 H23.
  Proof.
    constructor; intros; cbn in *; intuition.
  Qed.

  (* Lemma lcurrent_sep_owned n1 n2 (ns : nat -> Prop) p : *)
  (*   ns n2 -> *)
  (*   lcurrent n1 n2 ⊥ owned n1 ns p. *)
  (* Proof. *)
  (*   constructor; intros ? ? []; subst; try reflexivity. *)
  (*   - destruct H0. right. admit. *)
  (*   - simpl in *. *)
  (* Abort. *)

  (* Lemma lcurrent_sep_when n1 n2 p : *)
  (*   lcurrent n1 n2 ⊥ p -> *)
  (*   lcurrent n1 n2 ⊥ when n1 p. *)
  (* Proof. *)
  (*   intros Hsep. split; intros. *)
  (*   - apply Hsep; auto. destruct H; subst; intuition. *)
  (*   - destruct H; subst; [reflexivity |]. *)
  (*     destruct Hsep as [_ ?]. simpl. *)
  (* Admitted. *)

  (* Lemma lcurrent_duplicate n1 n2 : *)
  (*   lcurrent n1 n2 ≡≡ lcurrent n1 n2 ** lcurrent n1 n2. *)
  (* Proof. *)
  (*   split. *)
  (*   - constructor; intros; simpl in *; [apply H | apply H | subst; constructor; left; auto]. *)
  (*   - constructor; intros; simpl in *; subst; auto. *)
  (*     + split; [| split]; auto. apply lcurrent_sep. *)
  (*     + induction H. intuition. *)
  (*       destruct IHclos_trans1 as [? | (? & ? & ?)]; subst; auto. *)
  (*       destruct IHclos_trans2 as [? | (? & ? & ?)]; subst; auto. *)
  (*       right; split; [| split]; auto; etransitivity; eauto. *)
  (* Qed. *)

  (* Weaken the lifetime n1 to n2 *)
  Lemma lcurrent_when n1 n2 p H :
    lcurrent n1 n2 H ** when n2 p <= lcurrent n1 n2 H ** when n1 p.
  Proof.
    constructor; intros.
    - simpl in *. destruct H0 as (_ & ? & ?). split; [| split]; auto.
      + intro. apply H0. destruct H2.
        * admit. (* TODO write lemma about this *)
        * right. symmetry. apply H. auto.
      + admit.
    - simpl in *. split; auto. destruct H0 as [_ ?].
      destruct H0 as (? & ?). split.
      + (* TODO: add invariant here *) admit.
      + intros [].
        * apply H1; auto. admit. (* as above *)
        * apply H1. right. symmetry. apply H. auto.
    - simpl in *. induction H0. 2: econstructor 2; eauto.
      destruct H0; subst; try solve [constructor; auto].
      destruct H0; subst; try solve [constructor; auto].
      destruct H0 as (? & ? & ? & ?).
      constructor 1. right. right.
      split; [| split; [| split]]; auto.
      2, 3: symmetry; apply H; auto.
      (* TODO invariant *) admit.
  Admitted.

  (*  - simpl. destruct H as (? & ? & ?). simpl in *. *)
  (*    intro. symmetry in H2. apply H in H2. auto. *)
  (*  - destruct H. destruct H; subst; try reflexivity. destruct H as ((? & ?) & ? & ?). *)
  (*    destruct H0 as [[? ?] | [? | ?]]. *)
  (*    + left. split; symmetry; [apply H | apply H1]; auto. *)
  (*    + right. left. symmetry. apply H1; auto. *)
  (*    + (* subsumes x n1 n2 gives us the wrong direction here. *) *)
  (*      right. destruct (lifetime y n2) eqn:?; auto. destruct l. *)
  (*      * right. destruct H0 as (? & ? & ?). split; [| split]; auto. *)
  (*        destruct (lifetime x n2) eqn:?. destruct l. all: auto; try contradiction H3. *)
  (*        red in H. rewrite H0, Heqo0 in H. *)
  (*        admit. *)
  (*      * admit. *)
  (*      * admit. *)
  (*  (* right. destruct H2 as (? & ? & ?). split; [| split]; admit. *) *)
  (*  admit. admit. *)
  (*  - induction H. 2: econstructor 2; eauto. *)
  (*    destruct H. constructor. left. auto. *)

  (*    destruct H; subst; try reflexivity. destruct H as (? & ? & ?). *)
  (*    constructor. right. right. split; [| split]; auto. *)
  (* Abort. *)
