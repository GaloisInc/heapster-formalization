From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

From Heapster Require Export
     Permissions
     Memory
     SepStep
     Functional.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import MonadNotation.
Import ListNotations.
Import ITreeNotations.

Section Config.
  Context {specConfig : Type}.

  Variant Lifetime := current | finished.

  Record config : Type :=
    {
    l : list Lifetime;
    m : memory;
    }.

  Definition start_config :=
    {|
    l := nil;
    m := fun _ => None;
    |}.

  (** lifetime helpers **)

  Definition lifetime : config -> nat -> option Lifetime :=
    fun c => nth_error (l c).

  Fixpoint replace_list_index {A : Type} (l : list A) (n : nat) (new : A) :=
    match l with
    | [] => repeat new (n + 1)
    | h :: t => match n with
              | O => new :: t
              | S n => h :: replace_list_index t n new
              end
    end.
  Definition replace_lifetime (c : config) (n : nat) (new : Lifetime) : config :=
    {|
    l := replace_list_index (l c) n new;
    m := m c;
    |}.

  Lemma replace_lifetime_same c n l :
    lifetime c n = Some l -> replace_lifetime c n l = c.
  Proof.
    intros. destruct c. unfold lifetime in H. unfold replace_lifetime. f_equal. simpl in *.
    generalize dependent n. induction l0; intros; simpl in *; auto.
    - assert (@nth_error Lifetime [] n <> None). intro. rewrite H in H0. discriminate H0.
      apply nth_error_Some in H0. inversion H0.
    - destruct n; auto.
      + inversion H. auto.
      + rewrite IHl0; auto.
  Qed.

  Lemma lifetime_replace_lifetime c n l :
    lifetime (replace_lifetime c n l) n = Some l.
  Proof.
    destruct c. unfold replace_lifetime. simpl. revert n l.
    induction l0; intros; simpl; induction n; auto.
    unfold lifetime in *. simpl in *. auto.
  Qed.

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

  (* Definition monotonic_at (p : perm) (n : nat) (x y : config) : Prop := *)
  (*   @guar _ specConfig p x y -> lifetime_lte (lifetime x n) (lifetime y n). *)

  (* Instance monotonic_at_reflexive p n : Reflexive (monotonic_at p n). *)
  (* Proof. *)
  (*   repeat intro. reflexivity. *)
  (* Qed. *)

  (* Lemma bottom_monotonic_at n : forall x y, monotonic_at bottom_perm n x y. *)
  (* Proof. *)
  (*   repeat intro. simpl in H. subst. reflexivity. *)
  (* Qed. *)

  (* Definition monotonic (P : Perms) (n : nat) : Prop := *)
  (*   forall p, p ∈ P -> exists p', p' <= p /\ p' ∈ P /\ forall x y, monotonic_at p' n x y. *)

  (* Lemma monotonic_bottom n : monotonic bottom_Perms n. *)
  (* Proof. *)
  (*   repeat intro. exists bottom_perm. split; [| split]. *)
  (*   apply bottom_perm_is_bottom. auto. apply bottom_monotonic_at. *)
  (* Qed. *)

  (* Program Definition restrict_monotonic_at (p : perm) (n : nat) : perm := *)
  (*   {| *)
  (*   pre := pre p; *)
  (*   rely := rely p; *)
  (*   guar := fun x y => guar p x y /\ monotonic_at p n x y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro. *)
  (*   - split; intuition. *)
  (*   - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   respects. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_monotone p p' n : *)
  (*   p <= p' -> restrict_monotonic_at p n <= restrict_monotonic_at p' n. *)
  (* Proof. *)
  (*   intros []. constructor; intros; simpl; auto. destruct H. *)
  (*   split; auto. intro. auto. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_lte p n : restrict_monotonic_at p n <= p. *)
  (* Proof. *)
  (*   constructor; intros; simpl in *; intuition. *)
  (* Qed. *)

  (* Definition invariant_at (p : @perm _ specConfig) (n : nat) : Prop := *)
  (*   forall l1 l2 x y, guar p x y <-> guar p (replace_lifetime x n l1) (replace_lifetime y n l2). *)

  (* Lemma invariant_l p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime y n = Some l2 -> *)
  (*                guar p x y <-> guar p (replace_lifetime x n l1) y. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite <- (replace_lifetime_same y n l2) at 2; auto. *)
  (* Qed. *)

  (* Lemma invariant_r p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime x n = Some l1 -> *)
  (*                guar p x y <-> guar p x (replace_lifetime y n l2). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite <- (replace_lifetime_same x n l1) at 2; auto. *)
  (* Qed. *)

  (** memory helpers **)

  (* read c at memory location ptr. ptr must be a valid location and allocated. *)
  Definition read (c : config) (ptr : addr)
    : option Value :=
    match m c (fst ptr) with
    | Some (LBlock size bytes) => if snd ptr <? size then bytes (snd ptr) else None
    | _ => None
    end.

  (* TODO clean up *)
  Definition config_mem (ptr : addr) (v : Value) :=
    {|
    l := nil;
    m := fun b => if b =? (fst ptr)
               then Some (LBlock (snd ptr + 1) (fun o => if o =? (snd ptr)
                                                      then Some v
                                                      else None))
               else None;
    |}.
  Lemma read_config_mem l v : read (config_mem l v) l = Some v.
  Proof.
    destruct l as [b o]. unfold read, config_mem. simpl. repeat rewrite Nat.eqb_refl.
    assert (o < o + 1). rewrite Nat.add_1_r. apply Nat.lt_succ_diag_r.
    pose proof Nat.ltb_spec0.
    eapply Bool.reflect_iff in H0. rewrite H0 in H. rewrite H. reflexivity.
  Qed.

  Definition is_some {A} (o : option A) : bool :=
    match o with
    | Some _ => true
    | None => false
    end.

  Definition allocated (c : config) (ptr : addr) : Prop :=
    match m c (fst ptr) with
    | Some (LBlock size bytes) =>
      match bytes (snd ptr) with
      | Some _ => snd ptr < size
      | _ => False
      end
    | _ => False
    end.

  Definition alloc_invariant (c1 c2 : config) (ptr : addr) : Prop :=
    allocated c1 ptr = allocated c2 ptr.

  Lemma alloc_invariant_read c1 c2 ptr :
    alloc_invariant c1 c2 ptr ->
    read c2 ptr = None ->
    read c1 ptr = None.
  Proof.
    destruct ptr as [b o].
    unfold alloc_invariant. unfold allocated. unfold read. simpl in *. intros.
    destruct (m c1 b), (m c2 b); try solve [inversion H0]; auto.
    - destruct l0, l1.
      destruct (bytes o), (bytes0 o).
      + destruct (o <? size) eqn:?; auto.
        rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0.
        rewrite H in Heqb0.
        rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0.
        rewrite Heqb0 in H0. inversion H0.
      + destruct (o <? size) eqn:?; auto.
        rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0.
        rewrite H in Heqb0. inversion Heqb0.
      + destruct (o <? size); auto.
      + destruct (o <? size); auto.
    - destruct l0. destruct (bytes o).
      + destruct (o <? size) eqn:?; auto.
        rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0.
        rewrite H in Heqb0. inversion Heqb0.
      + destruct (o <? size); auto.
  Qed.

  (* write val to c at memory location ptr. ptr must be a valid location and allocated. *)
  Definition write (c : config) (ptr : addr) (val : Value)
    : option config :=
    match m c (fst ptr) with
    | Some (LBlock size bytes) =>
      if andb (snd ptr <? size) (is_some (bytes (snd ptr)))
      then Some {|
               l := l c;
               m := fun b => if b =? fst ptr
                          then Some (LBlock size (fun o => if o =? snd ptr
                                                        then Some val
                                                        else bytes o))
                          else m c b;
             |}
      else None
    | _ => None
    end.

  Lemma write_config_mem l v v' : write (config_mem l v) l v' = Some (config_mem l v').
  Proof.
    destruct l as [b o]. unfold write, config_mem. simpl. repeat rewrite Nat.eqb_refl.
    assert (o < o + 1). rewrite Nat.add_1_r. apply Nat.lt_succ_diag_r.
    pose proof Nat.ltb_spec0.
    eapply Bool.reflect_iff in H0. rewrite H0 in H. rewrite H. simpl.
    do 2 f_equal. apply functional_extensionality. intros.
    destruct (x =? b); auto. do 2 f_equal. apply functional_extensionality. intros.
    destruct (x0 =? o); auto.
  Qed.

  Lemma write_success_allocation c c' ptr val :
    write c ptr val = Some c' ->
    alloc_invariant c c' ptr.
  Proof.
    destruct ptr as [b o].
    intros. unfold alloc_invariant. unfold allocated. unfold write in H. simpl in *.
    destruct (m c b) eqn:?; try solve [inversion H]. destruct l0.
    destruct (o <? size) eqn:?; try solve [inversion H].
    destruct (is_some (bytes o)) eqn:?; try solve [inversion H].
    inversion H; subst; clear H. simpl. repeat rewrite Nat.eqb_refl.
    destruct (bytes o); auto. inversion Heqb1.
  Qed.

  Lemma read_success_write c ptr val val' :
    read c ptr = Some val ->
    exists c', write c ptr val' = Some c'.
  Proof.
    unfold read, write. intros. destruct ptr as [b o]. simpl in *.
    destruct (m c b); inversion H. destruct l0. destruct (o <? size); inversion H.
    destruct (bytes o); inversion H; subst. simpl. eexists; reflexivity.
  Qed.

  Lemma write_success_ptr c c' ptr val :
    write c ptr val = Some c' ->
    read c' ptr = Some val.
  Proof.
    intros. destruct ptr as [b o]. unfold read, write in *. simpl in *.
    destruct (m c b); try solve [inversion H]. destruct l0.
    destruct (o <? size) eqn:?, (is_some (bytes o)) eqn:?; simpl in *; inversion H; simpl in *.
    repeat rewrite Nat.eqb_refl. rewrite Heqb0. auto.
  Qed.

  Lemma write_success_other_ptr c c' ptr val :
    write c ptr val = Some c' ->
    forall ptr', ptr <> ptr' -> read c ptr' = read c' ptr'.
  Proof.
    destruct ptr as [b o].
    unfold write. unfold read. simpl. intros.
    destruct (m c b) eqn:?; try solve [inversion H]. destruct l0.
    destruct (o <? size) eqn:?; try solve [inversion H].
    destruct (is_some (bytes o)) eqn:?; try solve [inversion H].
    inversion H; subst; clear H. destruct ptr' as [b' o']. simpl.
    destruct (addr_neq_cases b b' o o' H0).
    - rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H.
      apply Bool.not_true_is_false in H. rewrite Nat.eqb_sym.
      rewrite H. reflexivity.
    - destruct (b' =? b) eqn:?; auto.
      rewrite <- (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in Heqb2. subst.
      rewrite Heqo0.
      rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H.
      apply Bool.not_true_is_false in H. rewrite Nat.eqb_sym.
      rewrite H. reflexivity.
  Qed.

  Lemma write_success_others c c' ptr val :
    write c ptr val = Some c' ->
    l c = l c'.
  Proof.
    destruct ptr as [b o].
    unfold write. simpl. intros.
    destruct (m c b); try solve [inversion H].
    destruct l0. destruct ((o <? size) && is_some (bytes o))%bool; try solve [inversion H].
    inversion H; subst; simpl. split; auto.
  Qed.

  Lemma write_read : forall c c' ptr val,
      write c ptr val = Some c' ->
      read c' ptr = Some val.
  Proof.
    intros. destruct ptr as [b o].
    unfold write, read in *. simpl in *.
    destruct (m c b); try solve [inversion H]. destruct l0.
    destruct (o <? size) eqn:?; try solve [inversion H].
    destruct (bytes o); try solve [inversion H]. simpl in *. inversion H; simpl.
    repeat rewrite Nat.eqb_refl. rewrite Heqb0. reflexivity.
  Qed.

  (* Lemma read_write : forall c ptr, *)
  (*     (exists val, read c ptr = Some val) -> *)
  (*     bind (read c ptr) (fun val => write c ptr val) = Some c. *)
  (* Proof. *)
  (*   intros. destruct H. simpl. rewrite H. unfold read in H. unfold write. *)
  (*   destruct ptr as (b & o). destruct c. simpl in *. *)
  (*   destruct (m0 b) eqn:?; try solve [inversion H]. destruct l1. *)
  (*   destruct (o <? size); try solve [inversion H]. *)
  (*   apply f_equal. (* not sure why I need apply *) *)
  (*   f_equal. apply functional_extensionality. intros. destruct (x0 =? b) eqn:?; auto. *)
  (*   rewrite <- (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in Heqb0; subst. *)
  (*   rewrite Heqo0. f_equal. f_equal. apply functional_extensionality. intros. *)
  (*   destruct (x0 =? o) eqn:?; auto. *)
  (*   rewrite <- (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in Heqb0. subst. auto. *)
  (* Qed. *)

  (* Lemma write_write : forall c ptr val, *)
  (*     bind (write c ptr val) (fun c' => write c' ptr val) = write c ptr val. *)
  (* Proof. *)
  (*   simpl. intros. destruct (write c ptr val) eqn:?; auto. unfold write in *. *)
  (*   destruct (m c (fst ptr)) eqn:?; try solve [inversion Heqo]. *)
  (*   destruct l0 eqn:?. destruct (snd ptr <? size) eqn:?; inversion Heqo. *)
  (*   simpl. rewrite Nat.eqb_refl. rewrite Heqb. apply f_equal. f_equal. *)
  (*   apply functional_extensionality. intros. destruct (x =? fst ptr); auto. *)
  (*   repeat f_equal. apply functional_extensionality. intros. *)
  (*   destruct (x0 =? snd ptr); auto. *)
  (* Qed. *)

  (** error helpers **)
  Definition error_config (c : config) : config :=
    {|
    l := l c;
    m := m c;
    |}.

  (** Lifetime permissions **)

  (* Program Definition when (n : nat) (p : @perm _ specConfig) : perm := *)
  (*   {| *)
  (*   pre := fun x s => (lifetime x n = Some current /\ pre p x s) \/ *)
  (*                  lifetime x n = Some finished; *)
  (*   rely := fun x y => lifetime x n = None /\ lifetime y n = None \/ *)
  (*                   lifetime y n = Some finished \/ *)
  (*                   lifetime x n = Some current /\ lifetime y n = Some current /\ rely p x y; *)
  (*   guar := fun x y => x = y \/ *)
  (*                   lifetime x n = Some current /\ lifetime y n = Some current /\ guar p x y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro. *)
  (*   - destruct (lifetime x n) as [[] |]; intuition. *)
  (*   - decompose [and or] H; decompose [and or] H0; subst; auto. *)
  (*     + rewrite H1 in H3. discriminate H3. *)
  (*     + rewrite H2 in H3. discriminate H3. *)
  (*     + rewrite H1 in H2. discriminate H2. *)
  (*     + rewrite H2 in H5. discriminate H5. *)
  (*     + right; right. split; [| split]; auto. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro; auto. *)
  (*   decompose [and or] H; decompose [and or] H0; subst; auto. *)
  (*   right. split; [| split]; auto. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   decompose [and or] H; decompose [or and] H0; subst; auto. *)
  (*   - rewrite H2 in H4. discriminate H4. *)
  (*   - rewrite H1 in H2. discriminate H2. *)
  (*   - left. split; auto. eapply pre_respects; eauto. *)
  (*   - rewrite H1 in H3. discriminate H3. *)
  (* Qed. *)

  (* Lemma when_monotone n p1 p2 : p1 <= p2 -> when n p1 <= when n p2. *)
  (* Proof. *)
  (*   intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 7. *)
  (* Qed. *)

  (* Instance Proper_lte_perm_when : *)
  (*   Proper (eq ==> lte_perm ==> lte_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. apply when_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_when : *)
  (*   Proper (eq ==> eq_perm ==> eq_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply when_monotone; auto. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_when p n : when n p ≡ restrict_monotonic_at (when n p) n. *)
  (* Proof. *)
  (*   split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte]. *)
  (*   decompose [and or] H; subst; try solve [intuition]. split; auto. *)
  (*   intro. rewrite H1, H0. reflexivity. *)
  (* Qed. *)
  (* Lemma when_restrict_monotonic_at p n : when n p ≡ when n (restrict_monotonic_at p n). *)
  (* Proof. *)
  (*   split; constructor; intros; simpl in *; intuition. *)
  (*   right; intuition. intro. rewrite H, H0. reflexivity. *)
  (* Qed. *)

  (* Program Definition owned (n : nat) (p : @perm _ specConfig) : (@perm _ specConfig) := *)
  (*   {| *)
  (*   pre := fun x s => lifetime x n = Some current; *)
  (*   rely := fun x y => lifetime x n = lifetime y n /\ (lifetime x n = Some finished -> rely p x y); *)
  (*   guar := fun x y => x = y \/ *)
  (*                   lifetime y n = Some finished /\ guar p (replace_lifetime x n finished) y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro; auto. *)
  (*   - split; intuition. *)
  (*   - destruct H, H0. *)
  (*     split; etransitivity; eauto. apply H2. rewrite <- H. auto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro; auto. *)
  (*   decompose [and or] H; decompose [and or] H0; subst; auto. *)
  (*   right. split; auto. etransitivity; eauto. *)
  (*   rewrite <- (replace_lifetime_same y n finished); auto. *)
  (* Qed. *)

  (* Lemma owned_monotone n p1 p2 : p1 <= p2 -> owned n p1 <= owned n p2. *)
  (* Proof. *)
  (*   intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 6. *)
  (* Qed. *)

  (* Instance Proper_lte_perm_owned : *)
  (*   Proper (eq ==> lte_perm ==> lte_perm) owned. *)
  (* Proof. *)
  (*   repeat intro; subst. apply owned_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_owned : *)
  (*   Proper (eq ==> eq_perm ==> eq_perm) owned. *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply owned_monotone; auto. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_owned p n : owned n p ≡ restrict_monotonic_at (owned n p) n. *)
  (* Proof. *)
  (*   split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte]. *)
  (*   decompose [and or] H; subst; try solve [intuition]. split; auto. clear H. *)
  (*   intro. rewrite H1. destruct (lifetime x n) as [[] |]; simpl; auto. *)
  (* Qed. *)
  (* Lemma owned_restrict_monotonic_at p n : owned n p ≡ owned n (restrict_monotonic_at p n). *)
  (* Proof. *)
  (*   split; constructor; intros; simpl in *; intuition. *)
  (*   right; intuition. intro. rewrite H. rewrite lifetime_replace_lifetime. reflexivity. *)
  (* Qed. *)

  (* (* trivial direction *) *)
  (* Lemma foo' p q n : *)
  (*   owned n (restrict_monotonic_at p n * restrict_monotonic_at q n) <= *)
  (*   owned n (restrict_monotonic_at (p * q) n). *)
  (* Proof. *)
  (*   rewrite <- owned_restrict_monotonic_at. apply owned_monotone. *)
  (*   apply sep_conj_perm_monotone; apply restrict_monotonic_at_lte. *)
  (* Qed. *)

  (* Lemma lifetimes_sep_gen p q n : *)
  (*   p ⊥ owned n q -> when n p ⊥ owned n (p * q). *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - simpl in H0. decompose [and or] H0. subst; intuition. *)
  (*     simpl. right; left; auto. *)
  (*   - simpl in H0. decompose [and or] H0. subst; intuition. *)
  (*     simpl. split. rewrite H1, H2; auto. *)
  (*     intros. rewrite H2 in H3. discriminate H3. *)
  (* Qed. *)

  (* (* not actually a special case of the above *) *)
  (* Lemma lifetimes_sep n p : when n p ⊥ owned n p. *)
  (* Proof. *)
  (*   constructor; intros; simpl in H; auto. *)
  (*   - decompose [and or] H; subst; try reflexivity. *)
  (*     simpl. right; left; auto. *)
  (*   - decompose [and or] H; subst; try reflexivity. *)
  (*     simpl. split. rewrite H1, H0. auto. intros. rewrite H1 in H2. discriminate H2. *)
  (* Qed. *)

  (* Lemma convert p q n (Hmon : forall x y, monotonic_at p n x y) (Hmon' : forall x y, monotonic_at q n x y) : *)
  (*   when n p * owned n (p * q) <= p * owned n q. *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - simpl in *. decompose [and or] H; auto. split; auto. split; auto. *)
  (*     eapply lifetimes_sep_gen; eauto. *)
  (*   - simpl in *. decompose [and or] H; auto. destruct (lifetime x n) as [[] | ]; auto 7. *)
  (*   - simpl in H. induction H. 2: { econstructor 2; eauto. } *)
  (*     decompose [and or] H; simpl; subst; try solve [constructor; auto]. *)
  (*     clear H. *)
  (*     apply Operators_Properties.clos_trans_t1n_iff. *)
  (*     apply Operators_Properties.clos_trans_t1n_iff in H2. *)
  (*     constructor 2 with (y:=replace_lifetime x n finished). *)
  (*     { right; right. split; [apply lifetime_replace_lifetime | reflexivity]. } *)
  (*     pose proof (lifetime_replace_lifetime x n finished). *)
  (*     induction H2; intros; subst; auto. *)
  (*     + constructor. destruct H1; auto. right; right. split; auto. *)
  (*       rewrite replace_lifetime_same; auto. *)
  (*     + assert (lifetime y n = Some finished). *)
  (*       { destruct H1; [apply Hmon in H1 | apply Hmon' in H1]; rewrite H in H1; simpl in H1; *)
  (*           destruct (lifetime y n) as [[] |]; inversion H1; auto. } *)
  (*       econstructor 2. 2: apply IHclos_trans_1n; auto. *)
  (*       destruct H1; auto. right; right. split; auto. rewrite replace_lifetime_same; auto. *)
  (* Qed. *)

  (* (* special case of convert *) *)
  (* Lemma convert_bottom p n (Hmon : forall x y, monotonic_at p n x y) : *)
  (*   when n p * owned n p <= p * owned n bottom_perm. *)
  (* Proof. *)
  (*   rewrite <- (sep_conj_perm_bottom p) at 2. apply convert; auto. *)
  (*   repeat intro. simpl in H. subst. reflexivity. *)
  (* Qed. *)

  (** memory permissions **)

  Program Definition read_perm (ptr : addr) (v : Value) : (@perm (config * specConfig)) :=
    {|
    (* ptr points to valid memory *)
    pre '(x, _) := read x ptr = Some v;
    (* only checks if the memory ptr points to in the 2 configs are equal *)
    rely '(x, _) '(y, _) := read x ptr = read y ptr;
    (* no guarates allowed *)
    guar '(x, _) '(y, _) := x = y;
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; subst; auto.
  Qed.

  Program Definition write_perm (ptr : addr) (v : Value) : (@perm (config * specConfig)) :=
    {|
    (* ptr points to valid memory *)
    pre '(x, _) := read x ptr = Some v;
    (* only checks if the memory ptr points to in the 2 configs are equal *)
    rely '(x, _) '(y, _) := read x ptr = read y ptr;
    (* only the pointer we have write permission to may change *)
    guar '(x, _) '(y, _) := (forall ptr', ptr <> ptr' -> read x ptr' = read y ptr') /\
                            alloc_invariant x y ptr /\
                            l x = l y
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - intros []; split; [| split]; intros; reflexivity.
    - intros [] [] [] (? & ? & ?) (? & ? & ?); split; [| split]; intros; try congruence.
      etransitivity. apply H; auto. apply H2; auto.
  Qed.

  Definition read_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : Value, Q = singleton_Perms (read_perm ptr y) * P y).

  Definition write_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : Value, Q = singleton_Perms (write_perm ptr y) * P y).

  Lemma read_lte_write : forall ptr v, read_perm ptr v <= write_perm ptr v.
  Proof.
    constructor; simpl; intros [] []; subst; auto. intros; subst.
    split; [| split; [| split]]; intros; reflexivity.
  Qed.

  (* Lemma read_write_separate_neq_ptr : forall ptr ptr' v v', *)
  (*     read_perm ptr v ⊥ write_perm ptr' v' <-> ptr <> ptr'. *)
  (* Proof. *)
  (*   split; repeat intro. *)
  (*   - destruct H as [? _]. simpl in *. subst. *)
  (*     specialize (sep_l (config_mem ptr' (Byte 0)) (config_mem ptr' (Byte 1))). *)
  (*     do 2 rewrite read_config_mem in sep_l. *)
  (*     assert (Some (Byte 0) = Some (Byte 1) -> False) by inversion 1. *)
  (*     apply H. clear H. apply sep_l. split; [| split; [| split]]; auto. *)
  (*     + intros. unfold read, config_mem. simpl. *)
  (*       destruct ptr', ptr'0. destruct (addr_neq_cases _ _ _ _ H); simpl in *. *)
  (*       * rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H0. *)
  (*         apply Bool.not_true_is_false in H0. rewrite Nat.eqb_sym in H0. *)
  (*         rewrite H0. auto. *)
  (*       * destruct (n1 =? n); auto. destruct (n2 <? n0 + 1); auto. *)
  (*         rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H0. *)
  (*         apply Bool.not_true_is_false in H0. rewrite Nat.eqb_sym in H0. *)
  (*         rewrite H0. auto. *)
  (*     + unfold alloc_invariant, allocated, config_mem. simpl. *)
  (*       repeat rewrite Nat.eqb_refl. auto. *)
  (*   - constructor; intros; simpl in *; subst; auto. *)
  (*     destruct H0. auto. *)
  (* Qed. *)

  (* Lemma write_write_separate_neq_ptr : forall ptr ptr' v v', *)
  (*     write_perm ptr v ⊥ write_perm ptr' v' <-> ptr <> ptr'. *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - symmetry in H. eapply separate_antimonotone in H. symmetry in H. *)
  (*     eapply read_write_separate_neq_ptr. apply H. apply read_lte_write. *)
  (*   - constructor; intros; simpl in *; destruct H0; auto. *)
  (* Qed. *)

  (* Lemma read_separate : forall ptr ptr' v v', read_perm ptr v ⊥ read_perm ptr' v'. *)
  (* Proof. *)
  (*   constructor; intros; simpl in *; subst; reflexivity. *)
  (* Qed. *)


  Definition load (v : Value) : itree (E config) Value :=
    c <- trigger (Modify id);;
    match v with
    | VNum _ => throw tt
    | VPtr p => match read c p with
               | None => throw tt
               | Some b => Ret b
               end
    end.

  Definition store (l : Value) (v : Value) : itree (E config) config :=
    match l with
    | VNum _ => throw tt
    | VPtr l => c <- trigger (Modify (fun c => match write c l v with
                                          | None => c
                                          | Some c' => c'
                                          end)) ;;
               match write c l v with
               | None => throw tt
               | Some c' => Ret c'
               end
    end.

  Example no_error_load : no_error (config_mem (0, 0) (VNum 1))
                                   (load (VPtr (0, 0))).
  Proof.
    pstep. unfold load. rewritebisim @bind_trigger. constructor.
    left. pstep. constructor.
  Qed.
  Example no_error_store : no_error (config_mem (0, 0) (VNum 1))
                                    (store (VPtr (0, 0)) (VNum 2)).
  Proof.
    pstep. unfold store. rewritebisim @bind_trigger. constructor.
    left. pstep. constructor.
  Qed.

  Lemma typing_load {R} ptr (Q : Value -> (@Perms (config * specConfig))) (r : R) :
    typing
      (read_Perms ptr Q)
      (fun x _ => (read_Perms ptr (eq_p x)) * Q x)
      (load (VPtr ptr))
      (Ret r).
  Proof.
    repeat intro. pstep. unfold load. rewritebisim @bind_trigger.
    econstructor; eauto; try reflexivity.
    destruct H as (? & (? & ?) & ?); subst.
    destruct H1 as (? & ? & ? & ? & ?). simpl in *.
    assert (read c1 ptr = Some x0).
    { apply H2 in H0. destruct H0 as (? & _). apply H in H0. auto. }
    rewrite H3. constructor; eauto.
    simpl. exists x, x1. split; [| split]; eauto. eexists. split; eauto.
    simpl. exists x, bottom_perm. split; [| split]; eauto.
    rewrite sep_conj_perm_bottom. reflexivity.
  Qed.

  Lemma typing_store {R} ptr val' (P Q : Value -> (@Perms (config * specConfig))) (r : R) :
    typing
      (write_Perms ptr P * Q val')
      (fun _ _ => write_Perms ptr Q)
      (store (VPtr ptr) val')
      (Ret r).
  Proof.
    repeat intro. pstep. unfold store. rewritebisim @bind_trigger.
    rename p into p''. rename H0 into Hpre.
    destruct H as (p' & q & Hwrite & Hq & Hlte). destruct Hwrite as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pw & p & Hwritelte & Hp & Hlte'). simpl in *.
    assert (exists val, read c1 ptr = Some val).
    {
      apply Hlte in Hpre. destruct Hpre as (Hpre & _).
      apply Hlte' in Hpre. destruct Hpre as (Hpre & _).
      apply Hwritelte in Hpre. eexists. apply Hpre.
    }
    destruct H as (val & Hread). eapply (read_success_write _ _ _ val') in Hread.
    destruct Hread as (c' & Hwrite).
    assert (Hguar : guar p' (c1, c2) (c', c2)).
    {
      apply Hlte'. constructor 1. left. apply Hwritelte. simpl.
      split; [| split].
      + eapply write_success_other_ptr; eauto.
      + eapply write_success_allocation; eauto.
      + eapply write_success_others; eauto.
    }
    econstructor; eauto.
    3: {
      rewrite Hwrite. constructor; eauto.
      2: { simpl. eexists. split. exists val'. reflexivity.
           simpl. eexists. exists q. split; [reflexivity | split]; eauto. reflexivity. }
      split; [| split].
      - eapply write_read; eauto.
      - apply Hlte in Hpre. respects. 2: apply Hpre; eauto.
        apply Hpre. auto.
      - apply Hlte in Hpre. destruct Hpre as (_ & _ & Hsep). symmetry in Hsep.
        eapply separate_antimonotone in Hsep; eauto. apply separate_sep_conj_perm_l in Hsep.
        eapply separate_antimonotone in Hsep; eauto. symmetry. constructor; apply Hsep.
    }
    - rewrite Hwrite. apply Hlte. constructor 1. left. auto.
    - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l.
      { apply Hlte in Hpre. apply Hpre. }
      eapply sep_step_lte; eauto. eapply sep_step_lte. apply lte_l_sep_conj_perm.
      eapply sep_step_lte; eauto.
      intros ? []. constructor; auto.
  Qed.

  Lemma typing_store' {R} ptr val' (P : Value -> (@Perms (config * specConfig))) (r : R):
    typing
      (write_Perms ptr P)
      (fun _ _ => write_Perms ptr (eq_p val'))
      (store (VPtr ptr) val')
      (Ret r).
  Proof.
    assert (bottom_Perms ≡ @eq_p config specConfig _ val' val').
    { split; repeat intro; simpl; auto. }
    rewrite <- sep_conj_Perms_bottom_identity. rewrite sep_conj_Perms_commut.
    rewrite H. apply typing_store.
  Qed.

End Config.
