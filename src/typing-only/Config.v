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
     Memory.

Import MonadNotation.
Import ListNotations.

Variant Lifetime := current | finished.

Record config : Type :=
  {
  l : list Lifetime;
  m : memory;
  e : bool;
  }.
Module Config <: Permissions.Config.
  Definition t := config.
End Config.

Definition start_config :=
  {|
  l := nil;
  m := fun _ => None;
  e := false;
  |}.

Module Permissions' := Permissions Config.
Export Config.
Export Permissions'.

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
  e := e c;
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

Definition monotonic_at (p : perm) (n : nat) (x y : config) : Prop :=
  guar p x y -> lifetime_lte (lifetime x n) (lifetime y n).

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

Program Definition restrict_monotonic_at (p : perm) (n : nat) : perm :=
  {|
  pre := pre p;
  rely := rely p;
  guar := fun x y => guar p x y /\ monotonic_at p n x y;
  |}.
Next Obligation.
  respects.
Qed.
Next Obligation.
  constructor; repeat intro.
  - split; intuition.
  - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto.
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
  rewrite <- (replace_lifetime_same y n l2) at 2; auto.
Qed.

Lemma invariant_r p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime x n = Some l1 ->
               guar p x y <-> guar p x (replace_lifetime y n l2).
Proof.
  intros.
  rewrite <- (replace_lifetime_same x n l1) at 2; auto.
Qed.

(** memory helpers **)

(* read c at memory location ptr. ptr must be a valid location and allocated. *)
Definition read (c : config) (ptr : addr)
  : option SByte :=
  match m c (fst ptr) with
  | Some (LBlock size bytes) => if snd ptr <? size then bytes (snd ptr) else None
  | _ => None
  end.

(* TODO clean up *)
Definition config_mem (ptr : addr) (v : SByte) :=
  {|
  l := nil;
  m := fun b => if b =? (fst ptr)
             then Some (LBlock (snd ptr + 1) (fun o => if o =? (snd ptr)
                                                    then Some v
                                                    else None))
             else None;
  e := false;
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
Definition write (c : config) (ptr : addr) (val : SByte)
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
             e := e c;
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
  l c = l c' /\ e c = e c'.
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
  e := true;
  |}.

(** Lifetime permissions **)

Program Definition when (n : nat) (p : perm) : perm :=
  {|
  pre := fun x => (lifetime x n = Some current /\ pre p x) \/
               lifetime x n = Some finished;
  rely := fun x y => lifetime x n = None /\ lifetime y n = None \/
                  lifetime y n = Some finished \/
                  lifetime x n = Some current /\ lifetime y n = Some current /\ rely p x y;
  guar := fun x y => x = y \/
                 lifetime x n = Some current /\ lifetime y n = Some current /\ guar p x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - destruct (lifetime x n) as [[] |]; intuition.
  - decompose [and or] H; decompose [and or] H0; subst; auto.
    + rewrite H1 in H3. discriminate H3.
    + rewrite H2 in H3. discriminate H3.
    + rewrite H1 in H2. discriminate H2.
    + rewrite H2 in H5. discriminate H5.
    + right; right. split; [| split]; auto. etransitivity; eauto.
Qed.
Next Obligation.
  decompose [and or] H; decompose [or and] H0; subst; auto.
  - rewrite H2 in H4. discriminate H4.
  - rewrite H1 in H2. discriminate H2.
  - left. split; auto. eapply pre_respects; eauto.
  - rewrite H1 in H3. discriminate H3.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; [| split]; auto. etransitivity; eauto.
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

Lemma restrict_monotonic_at_when p n : when n p ≡ restrict_monotonic_at (when n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto.
  intro. rewrite H1, H0. reflexivity.
Qed.
Lemma when_restrict_monotonic_at p n : when n p ≡ when n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H, H0. reflexivity.
Qed.

Program Definition owned (n : nat) (p : perm) : perm :=
  {|
  pre := fun x => lifetime x n = Some current;
  rely := fun x y => lifetime x n = lifetime y n /\ (lifetime x n = Some finished -> rely p x y);
  guar := fun x y => x = y \/
                 lifetime y n = Some finished /\ guar p (replace_lifetime x n finished) y;
  |}.
Next Obligation.
  constructor; repeat intro; auto.
  - split; intuition.
  - destruct H, H0.
    split; etransitivity; eauto. apply H2. rewrite <- H. auto.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; auto. etransitivity; eauto.
  rewrite <- (replace_lifetime_same y n finished); auto.
Qed.

Lemma owned_monotone n p1 p2 : p1 <= p2 -> owned n p1 <= owned n p2.
Proof.
  intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 6.
Qed.

Instance Proper_lte_perm_owned :
  Proper (eq ==> lte_perm ==> lte_perm) owned.
Proof.
  repeat intro; subst. apply owned_monotone; auto.
Qed.

Instance Proper_eq_perm_owned :
  Proper (eq ==> eq_perm ==> eq_perm) owned.
Proof.
  repeat intro; subst. split; apply owned_monotone; auto.
Qed.

Lemma restrict_monotonic_at_owned p n : owned n p ≡ restrict_monotonic_at (owned n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto. clear H.
  intro. rewrite H1. destruct (lifetime x n) as [[] |]; simpl; auto.
Qed.
Lemma owned_restrict_monotonic_at p n : owned n p ≡ owned n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H. rewrite lifetime_replace_lifetime. reflexivity.
Qed.

(* trivial direction *)
Lemma foo' p q n :
  owned n (restrict_monotonic_at p n * restrict_monotonic_at q n) <=
  owned n (restrict_monotonic_at (p * q) n).
Proof.
  rewrite <- owned_restrict_monotonic_at. apply owned_monotone.
  apply sep_conj_perm_monotone; apply restrict_monotonic_at_lte.
Qed.

Lemma lifetimes_sep_gen p q n :
  p ⊥ owned n q -> when n p ⊥ owned n (p * q).
Proof.
  split; intros.
  - simpl in H0. decompose [and or] H0. subst; intuition.
    simpl. right; left; auto.
  - simpl in H0. decompose [and or] H0. subst; intuition.
    simpl. split. rewrite H1, H2; auto.
    intros. rewrite H2 in H3. discriminate H3.
Qed.

(* not actually a special case of the above *)
Lemma lifetimes_sep n p : when n p ⊥ owned n p.
Proof.
  constructor; intros; simpl in H; auto.
  - decompose [and or] H; subst; try reflexivity.
    simpl. right; left; auto.
  - decompose [and or] H; subst; try reflexivity.
    simpl. split. rewrite H1, H0. auto. intros. rewrite H1 in H2. discriminate H2.
Qed.

Lemma convert p q n (Hmon : forall x y, monotonic_at p n x y) (Hmon' : forall x y, monotonic_at q n x y) :
  when n p * owned n (p * q) <= p * owned n q.
Proof.
  split; intros.
  - simpl in *. decompose [and or] H; auto. split; auto. split; auto.
    eapply lifetimes_sep_gen; eauto.
  - simpl in *. decompose [and or] H; auto. destruct (lifetime x n) as [[] | ]; auto 7.
  - simpl in H. induction H. 2: { econstructor 2; eauto. }
    decompose [and or] H; simpl; subst; try solve [constructor; auto].
    clear H.
    apply Operators_Properties.clos_trans_t1n_iff.
    apply Operators_Properties.clos_trans_t1n_iff in H2.
    constructor 2 with (y:=replace_lifetime x n finished).
    { right; right. split; [apply lifetime_replace_lifetime | reflexivity]. }
    pose proof (lifetime_replace_lifetime x n finished).
    induction H2; intros; subst; auto.
    + constructor. destruct H1; auto. right; right. split; auto.
      rewrite replace_lifetime_same; auto.
    + assert (lifetime y n = Some finished).
      { destruct H1; [apply Hmon in H1 | apply Hmon' in H1]; rewrite H in H1; simpl in H1;
          destruct (lifetime y n) as [[] |]; inversion H1; auto. }
      econstructor 2. 2: apply IHclos_trans_1n; auto.
      destruct H1; auto. right; right. split; auto. rewrite replace_lifetime_same; auto.
Qed.

(* special case of convert *)
Lemma convert_bottom p n (Hmon : forall x y, monotonic_at p n x y) :
  when n p * owned n p <= p * owned n bottom_perm.
Proof.
  rewrite <- (sep_conj_perm_bottom p) at 2. apply convert; auto.
  repeat intro. simpl in H. subst. reflexivity.
Qed.

(** memory permissions **)

(* Program Definition read_p (ptr : addr) : perm := *)
(*   {| *)
(*   (* ptr points to valid memory *) *)
(*   pre x := exists v, read x ptr = Some v; *)
(*   (* only checks if the memory ptr points to in the 2 configs are equal *) *)
(*   rely x y := alloc_invariant x y ptr; *)
(*   (* read x ptr = None <-> read y ptr = None; *) *)
(*   (* only the pointer we have write permission to may change *) *)
(*   guar x y := x = y; *)
(*   |}. *)
(* Next Obligation. *)
(*   constructor; unfold alloc_invariant; unfold allocated; repeat intro; auto. *)
(*   destruct (m x (fst ptr)), (m y (fst ptr)), (m z (fst ptr)); intuition. *)
(*   - destruct l0, l1, l2. *)
(*     destruct (bytes (snd ptr)), (bytes0 (snd ptr)), (bytes1 (snd ptr)); subst; *)
(*       etransitivity; eauto. *)
(*   - destruct l0, l1. *)
(*     destruct (bytes (snd ptr)), (bytes0 (snd ptr)); subst; *)
(*       etransitivity; eauto. *)
(*   - destruct l0, l1. *)
(*     destruct (bytes (snd ptr)), (bytes0 (snd ptr)); subst; *)
(*       etransitivity; eauto. *)
(*   - destruct l0, l1. *)
(*     destruct (bytes (snd ptr)), (bytes0 (snd ptr)); subst; *)
(*       etransitivity; eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   destruct (read y ptr) eqn:?. *)
(*   eexists; eauto. *)
(*   assert ((None : option SByte) = None) by reflexivity. *)
(*   eapply alloc_invariant_read in Heqo; eauto. rewrite H1 in Heqo. inversion Heqo. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; repeat intro; auto. etransitivity; eauto. *)
(* Qed. *)

(* (* TODO factor out common pre and rely *) *)
(* Program Definition write_p (ptr : addr) : perm := *)
(*   {| *)
(*   (* ptr points to valid memory *) *)
(*   pre x := exists v, read x ptr = Some v; *)
(*   (* only checks if the memory ptr points to in the 2 configs are equal *) *)
(*   rely x y := read x ptr = read y ptr; *)
(*   (* only the pointer we have write permission to may change *) *)
(*   (* TODO: cannot dealloc or alloc here... *) *)
(*   guar x y := (forall ptr', ptr <> ptr' -> read x ptr' = read y ptr') /\ *)
(*              alloc_invariant x y ptr; *)
(*   |}. *)
(* Next Obligation. *)
(*   constructor; repeat intro; auto. etransitivity; eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   eexists; eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; split; repeat intro; try solve [intuition]. *)
(*   - reflexivity. *)
(*   - destruct H, H0. etransitivity. apply H; auto. auto. *)
(*   - destruct H, H0. etransitivity. apply H1. auto. *)
(* Qed. *)

Program Definition read_perm (ptr : addr) (v : SByte) : perm :=
  {|
  (* ptr points to valid memory *)
  pre x := read x ptr = Some v;
  (* only checks if the memory ptr points to in the 2 configs are equal *)
  rely x y := read x ptr = read y ptr;
  (* no updates allowed *)
  guar x y := x = y;
  |}.
Next Obligation.
  constructor; repeat intro; auto. etransitivity; eauto.
Qed.

Program Definition write_perm (ptr : addr) (v : SByte) : perm :=
  {|
  (* ptr points to valid memory *)
  pre x := read x ptr = Some v;
  (* only checks if the memory ptr points to in the 2 configs are equal *)
  rely x y := read x ptr = read y ptr;
  (* only the pointer we have write permission to may change *)
  guar x y := (forall ptr', ptr <> ptr' -> read x ptr' = read y ptr') /\
             alloc_invariant x y ptr /\
             l x = l y /\
             e x = e y;
  |}.
Next Obligation.
  constructor; repeat intro; auto. etransitivity; eauto.
Qed.
Next Obligation.
  constructor; split; repeat intro; try solve [intuition].
  - split; [| split]; reflexivity.
  - destruct H, H0. etransitivity. apply H; auto. auto.
  - destruct H as (? & ? & ? & ?), H0 as (? & ? & ? & ?).
    split; [| split]; etransitivity; eauto.
Qed.

Definition read_Perms (ptr : addr) (P : SByte -> Perms) : Perms :=
  meet_Perms (fun Q => exists y : SByte, Q = singleton_Perms (read_perm ptr y) ** P y).

Definition write_Perms (ptr : addr) (P : SByte -> Perms) : Perms :=
  meet_Perms (fun Q => exists y : SByte, Q = singleton_Perms (write_perm ptr y) ** P y).

Lemma read_lte_write : forall ptr v, read_perm ptr v <= write_perm ptr v.
Proof.
  constructor; simpl; repeat intro; subst; auto.
  split; [| split; [| split]]; intros; reflexivity.
Qed.

Lemma read_write_separate_neq_ptr : forall ptr ptr' v v',
    read_perm ptr v ⊥ write_perm ptr' v' <-> ptr <> ptr'.
Proof.
  split; repeat intro.
  - destruct H as [? _]. simpl in *. subst.
    specialize (sep_l0 (config_mem ptr' (Byte 0)) (config_mem ptr' (Byte 1))).
    do 2 rewrite read_config_mem in sep_l0.
    assert (Some (Byte 0) = Some (Byte 1) -> False) by inversion 1.
    apply H. clear H. apply sep_l0. split; [| split; [| split]]; auto.
    + intros. unfold read, config_mem. simpl.
      destruct ptr', ptr'0. destruct (addr_neq_cases _ _ _ _ H); simpl in *.
      * rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H0.
        apply Bool.not_true_is_false in H0. rewrite Nat.eqb_sym in H0.
        rewrite H0. auto.
      * destruct (n1 =? n); auto. destruct (n2 <? n0 + 1); auto.
        rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H0.
        apply Bool.not_true_is_false in H0. rewrite Nat.eqb_sym in H0.
        rewrite H0. auto.
    + unfold alloc_invariant, allocated, config_mem. simpl.
      repeat rewrite Nat.eqb_refl. auto.
  - constructor; intros; simpl in *; subst; auto.
    destruct H0. auto.
Qed.

Lemma write_write_separate_neq_ptr : forall ptr ptr' v v',
    write_perm ptr v ⊥ write_perm ptr' v' <-> ptr <> ptr'.
Proof.
  split; intros.
  - symmetry in H. eapply separate_antimonotone in H. symmetry in H.
    eapply read_write_separate_neq_ptr. apply H. apply read_lte_write.
  - constructor; intros; simpl in *; destruct H0; auto.
Qed.

Lemma read_separate : forall ptr ptr' v v', read_perm ptr v ⊥ read_perm ptr' v'.
Proof.
  constructor; intros; simpl in *; subst; reflexivity.
Qed.
