From Heapster Require Import
     Permissions
     Config.

Definition value_Perms {T} := T -> Perms.

Definition apply {T} (P : value_Perms) (x : T) := P x.
Notation "x : P" := (apply P x) (at level 40).

Definition value_Perms_monotonic {T} (P : value_Perms) := forall (x : T) n, monotonic (x:P) n.

Definition empty := bottom_Perms.
Definition true_p {T} : @value_Perms T := fun _ => bottom_Perms.

Program Definition when' {T} (n : nat) (P : value_Perms) (x : T) :=
  {|
    in_Perms := fun p => exists p', in_Perms (P x) p' /\ when n p' <= p;
  |}.
Next Obligation.
  exists H. split; auto. etransitivity; eauto.
Qed.

Program Definition owned' (n : nat) (P : Perms) :=
  {|
    in_Perms := fun p => exists p', in_Perms P p' /\ owned n p' <= p;
  |}.
Next Obligation.
  exists H. split; auto. etransitivity; eauto.
Qed.

(* TODO: strengthen to value_Perms_monotonic? *)
Lemma convert {T} (x : T) (P : value_Perms) (Q : Perms) n
      (Hmon : monotonic (x:P) n) (Hmon' : monotonic Q n) :
  x:P ** (owned' n Q) ⊦ x:(when' n P) ** (owned' n (x:P ** Q)).
Proof.
  repeat intro. simpl in H. decompose [ex and] H. clear H. simpl.
  specialize (Hmon _ H0).
  specialize (Hmon' _ H1).
  decompose [ex and] Hmon. clear Hmon.
  decompose [ex and] Hmon'. clear Hmon'.
  exists (when n x3).
  exists (owned n (x3 * x4)).
  split; [| split].
  3: {
    etransitivity.
    { apply convert; auto. }
    etransitivity; eauto.
    apply sep_conj_perm_monotone; eauto.
    etransitivity; eauto. apply owned_monotone; auto.
  }
  - exists x3. split; intuition.
  - exists (x3 * x4). split; intuition.
    exists x3, x4. intuition.
Qed.

Lemma drop {T} (x : T) (P : value_Perms) : x:P ⊦ empty.
Proof.
  repeat intro. simpl. auto.
Qed.
Lemma true_intro {T} (x : T) : empty ⊦ x:true_p.
Proof.
  repeat intro; auto.
Qed.

Program Definition eq_p {T} (y x : T) :=
  {|
    in_Perms := fun _ => x = y;
  |}.

Lemma eq_p_monotonic {T} (y : T) :
  value_Perms_monotonic (eq_p(y)).
Proof.
  repeat intro. simpl in H; subst. exists bottom_perm.
  split; [apply bottom_perm_is_bottom |]; simpl; intuition.
  repeat intro. inversion H. reflexivity.
Qed.

Lemma eq_refl {T} (x : T) : empty ⊦ x:eq_p(x).
Proof.
  repeat intro. simpl. auto.
Qed.

Lemma eq_trans {T} (x y z : T) : x:eq_p(y) ** y:eq_p(z) ⊦ x:eq_p(z).
Proof.
  repeat intro. destruct H as [p1 [p2 [Hp1 [Hp2 ?]]]]. simpl in *. subst. auto.
Qed.

Lemma eq_elim {T} (x y : T) P : x:eq_p(y) ** y:P ⊦ x:P.
Proof.
  repeat intro. destruct H as [p1 [p2 [Hp1 [Hp2 ?]]]].
  destruct Hp1.
  eapply Perms_upwards_closed; eauto. etransitivity. apply lte_r_sep_conj_perm. eauto.
Qed.

Lemma copy {T} (x : T) P : (forall p, p ∈ x:P -> copyable p) ->
                           x:P ⊦ x:P ** x:P.
Proof.
  repeat intro. exists p, p. split; [| split]; auto.
  specialize (H _ H0). apply copyable_separate in H. split; intros; simpl; eauto.
  induction H1.
  - destruct H1; auto.
  - etransitivity; eauto.
Qed.

Definition or_Perms {T} (P Q : @value_Perms T) := fun x => meet_Perms2 (x:P) (x:Q).

Lemma or_Perms_monotonic {T} (P Q : @value_Perms T)
      (Hmon : value_Perms_monotonic P)
      (Hmon' : value_Perms_monotonic Q) :
  value_Perms_monotonic (or_Perms P Q).
Proof.
  repeat intro. simpl in *. decompose [ex and or] H; clear H; subst.
  - specialize (Hmon _ n _ H2). decompose [ex and] Hmon; clear Hmon.
    eexists; split; eauto.
  - specialize (Hmon' _ n _ H2). decompose [ex and] Hmon'; clear Hmon'.
    eexists; split; eauto.
Qed.

Lemma or_intro_l {T} (x : T) P Q : x:P ⊦ x:(or_Perms P Q).
Proof.
  repeat intro. exists (x:P). split; auto.
Qed.
Lemma or_intro_r {T} (x : T) P Q : x:Q ⊦ x:(or_Perms P Q).
Proof.
  repeat intro. exists (x:Q). split; auto.
Qed.

Lemma or_elim {T} (x : T) P Q R : x:P ⊦ R ->
                                  x:Q ⊦ R ->
                                  x:(or_Perms P Q) ⊦ R.
Proof.
  repeat intro. destruct H1 as [X [? ?]]. destruct H1; subst; auto.
Qed.

Definition exists_Perms {T} (P : T -> value_Perms) : value_Perms :=
  fun (x : T) => meet_Perms (fun Q => exists (y : T), Q = x:P(y)).

Lemma exists_intro {T} (x e : T) P : x:P(e) ⊦ x:(exists_Perms P).
Proof.
  repeat intro. exists (x:P(e)). split; auto. exists e; auto.
Qed.

Lemma exists_elim {T} (x : T) P R : (forall (y': T), x:P(y') ⊦ R) ->
                                x:(exists_Perms P) ⊦ R.
Proof.
  repeat intro. destruct H0 as [X [[? ?] ?]]. subst. eapply H; eauto.
Qed.

Class Ilookup {T} (x : T) (lhs : Perms) (x_P : value_Perms) rem : Prop :=
  ilookup : lhs ⊦ x:x_P ** rem.

Instance Ilookup_empty {T} (x : T) :
  Ilookup x empty true_p empty.
Proof.
  red. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

Instance Ilookup_base {T} (x : T) (P : value_Perms) (lhs : Perms) :
  Ilookup x (x:P ** lhs) P lhs.
Proof.
  red. reflexivity.
Qed.

Instance Ilookup_step {T T' : Type} (x: T) (x' : T') (lhs rem : Perms) (P : value_Perms) (P' : value_Perms) :
  Ilookup x lhs P rem ->
  Ilookup x (x':P' ** lhs) P (x':P' ** rem).
Proof.
  intros. red. red in H.
  rewrite (sep_conj_Perms_commut (x:P) _). rewrite <- sep_conj_Perms_assoc.
  apply sep_conj_Perms_monotone; intuition. rewrite sep_conj_Perms_commut. apply H.
Qed.

Class Ivar {T} (x : T) (P_lhs : value_Perms) (lhs : Perms) P_rhs rem : Prop :=
  ivar : x:P_lhs ** lhs ⊦ x:P_rhs ** rem.

Instance Ivar_base {T} (x : T) lhs P_lhs :
  Ivar x P_lhs lhs P_lhs lhs.
Proof.
  red. reflexivity.
Qed.

Instance Ivar_true {T} (x : T) lhs P_lhs :
  Ivar x P_lhs lhs true_p (x:P_lhs ** lhs).
Proof.
  red. rewrite (sep_conj_Perms_commut (x:true_p) _).
  rewrite <- sep_conj_Perms_bottom_identity at 1. rewrite sep_conj_Perms_commut.
  apply sep_conj_Perms_monotone; reflexivity.
Qed.

Instance Ivar_eq_refl {T} (x : T) lhs P_lhs :
  Ivar x P_lhs lhs (eq_p(x)) (x:P_lhs ** lhs).
Proof.
  red. rewrite (sep_conj_Perms_commut (x:eq_p(x))).
  rewrite <- sep_conj_Perms_bottom_identity at 1. rewrite sep_conj_Perms_commut.
  apply sep_conj_Perms_monotone; intuition.
  apply eq_refl.
Qed.

Instance Ivar_eq_elim {T} (x y : T) lhs P_y P_x rem1 rhs :
  Ilookup y lhs P_y rem1 ->
  Ivar x P_y rem1 P_x rhs ->
  Ivar x (eq_p(y)) lhs P_x rhs.
Proof.
  intros. red in H, H0. red.
  etransitivity. 2: apply H0.
  repeat intro. destruct H1 as [? [? [? [? ?]]]]. destruct H1. apply H.
  eapply Perms_upwards_closed. eauto. etransitivity. apply lte_r_sep_conj_perm. eauto.
Qed.

Instance Ivar_or_intro_l {T} (x : T) lhs P Q :
  Ivar x P lhs (or_Perms P Q) lhs.
Proof.
  red. eapply sep_conj_Perms_monotone; intuition. apply or_intro_l.
Qed.
Instance Ivar_or_intro_r {T} (x : T) lhs P Q :
  Ivar x Q lhs (or_Perms P Q) lhs.
Proof.
  red. eapply sep_conj_Perms_monotone; intuition. apply or_intro_r.
Qed.

Instance Ivar_or_elim {T} (x : T) lhs rhs P Q R :
  Ivar x P lhs R rhs ->
  Ivar x Q lhs R rhs ->
  Ivar x (or_Perms P Q) lhs R rhs.
Proof.
  intros. red in H, H0. repeat red. intros.
  destruct H1 as [? [? [? [? ?]]]]. destruct H1 as [? [[] ?]]; subst.
  - apply H. exists x0, x1; auto.
  - apply H0. exists x0, x1; auto.
Qed.

Instance Ivar_exists_intro {T} (x e : T) lhs (P : T -> value_Perms) :
  Ivar x (P e) lhs (exists_Perms P) lhs.
Proof.
  eapply sep_conj_Perms_monotone; intuition. apply exists_intro.
Qed.

Instance Ivar_exists_elim {T} (x : T) (P : T -> value_Perms) lhs R rhs:
  (forall (y : T), Ivar x (P y) lhs R rhs) ->
  Ivar x (exists_Perms P) lhs R rhs.
Proof.
  intros. red in H. repeat red. intros.
  destruct H0 as [? [? [? [? ?]]]]. destruct H0 as [? [[? ?] ?]]. subst.
  specialize (H x3). apply H. exists x0, x1. auto.
Qed.

(* Instance Ivar_ptr_elim {T} (x y : T) (l : lifetime) (e : nat) (P Q : T -> Perms) lhs rem rhs : *)
(*   l e = true -> *)
(*   Ilookup y lhs P rem -> *)
(*   Ivar x P rem Q rhs -> *)
(*   Ivar x (ptr l e (eq_p(y))) lhs Q rhs. *)
(* Proof. *)
(*   intros. red in H0, H1 |- *. rewrite ptr_current; auto. eapply Ivar_eq_elim; eauto. *)
(* Qed. *)

Class Implies (lhs rhs rem : Perms) : Prop :=
  impl: lhs ⊦ rhs ** rem.

(* results in an infinite typeclass resolution loop *)
(* Instance Implies_test (lhs P : Perms) : *)
(*   Implies lhs (P ** empty) lhs -> *)
(*   Implies lhs P lhs. *)
(* Proof. *)
(*   red. intros. red in H. *)
(*   rewrite <- sep_conj_Perms_bottom_identity at 2. *)
(*   rewrite sep_conj_Perms_assoc. apply H. *)
(* Qed. *)

Instance Implies_empty (lhs : Perms) :
  Implies lhs empty lhs.
Proof.
  red. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

Instance Implies_nonempty {T} (x : T) (lhs rhs rem1 rem2 rem3 : Perms) (P_lhs P_rhs : T -> Perms) :
  Ilookup x lhs P_lhs rem1 ->
  Ivar x P_lhs rem1 P_rhs rem2 ->
  Implies rem2 rhs rem3 ->
  Implies lhs (x:P_rhs ** rhs) rem3.
Proof.
  intros. red. red in H, H0, H1. etransitivity. apply H.
  etransitivity. apply H0. rewrite <- sep_conj_Perms_assoc.
  apply sep_conj_Perms_monotone; intuition.
Qed.

(* Typeclasses eauto := debug. *)

Goal forall T (x y : T), Ilookup x (x:true_p ** y:true_p ** empty) true_p (y:true_p ** empty).
Proof.
  typeclasses eauto.
Qed.

Goal forall T (x y : T), Ilookup y (x:true_p ** y:true_p ** empty) true_p (x:true_p ** empty).
Proof.
  typeclasses eauto.
Qed.

Goal forall T (x : T), exists rem, Implies empty (x:true_p ** empty) rem.
Proof.
  eexists.
  typeclasses eauto.
Qed.

Goal forall T (x y : T), exists rem, Implies empty (x:true_p ** y:true_p ** empty) rem.
Proof.
  eexists.
  typeclasses eauto.
Qed.

Goal forall T (x y : T) P, exists rem, Implies (x:(eq_p y) ** y:P ** empty) (x:P ** empty) rem.
Proof.
  eexists.
  typeclasses eauto.
Qed.

Goal forall T (x : T) P, exists rem y,
      Implies (x:(exists_Perms P) ** empty) (x:P(y) ** empty) rem.
Proof.
(*   do 2 eexists. *)
(*   eapply Implies_nonempty. *)
(*   - apply Ilookup_base. *)
(*   - apply Ivar_exists_elim. intros. apply Ivar_base. *)
(*   typeclasses eauto. *)
(* Qed. *)
Abort.
