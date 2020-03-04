Require Import Heapster.Permissions.


Section implication.
  Inductive type :=
  | TUnit : type
  | TNat : type
  .

  Inductive term (T : Type) :=
  | Var : T -> term T
  .

  Context (T : Type).

  Definition apply {T} (P : T -> Perms) (x : T) := P x.
  Notation "x : P" := (apply P x) (at level 40).

  Definition empty := bottom_Perms.
  Definition true_p := fun (_ : T) => bottom_Perms.

  Lemma drop (x : T) P : x:P ⊦ empty.
  Proof.
    repeat intro. simpl. auto.
  Qed.
  Lemma true_intro (x : T) : empty ⊦ x:true_p.
  Proof.
    repeat intro; auto.
  Qed.

  (* Perms where domain is x = y *)
  Program Definition eq_p (y : T) :=
    fun (x : T) =>
      {|
        in_Perms := fun _ => x = y;
      |}.

  Lemma eq_refl (x : T) : empty ⊦ x:eq_p(x).
  Proof.
    repeat intro. simpl. auto.
  Qed.

  Lemma eq_trans (x y z : T) : x:eq_p(y) ** y:eq_p(z) ⊦ x:eq_p(z).
  Proof.
    repeat intro. destruct H as [p1 [p2 [Hp1 [Hp2 ?]]]]. simpl in *. subst. auto.
  Qed.

  Lemma eq_elim (x y : T) P : x:eq_p(y) ** y:P ⊦ x:P.
  Proof.
    repeat intro. destruct H as [p1 [p2 [Hp1 [Hp2 ?]]]].
    destruct Hp1.
    eapply Perms_upwards_closed; eauto. etransitivity. apply lte_r_sep_conj_perm. eauto.
  Qed.

  Lemma copy (x : T) P : (forall p, p ∈ x:P -> read_perm p) ->
                    x:P ⊦ x:P ** x:P.
  Proof.
    repeat intro. exists p, p. split; [| split]; auto.
    specialize (H _ H0). apply separate_self_read in H. split; intros; simpl; eauto.
    induction H1.
    - destruct H1; auto.
    - etransitivity; eauto.
  Qed.

  Lemma or_left_intro (x : T) P Q : x:P ⊦ meet_Perms2 (x:P) (x:Q).
  Proof.
    repeat intro. exists (x:P). split; auto.
  Qed.
  Lemma or_right_intro (x : T) P Q : x:Q ⊦ meet_Perms2 (x:P) (x:Q).
  Proof.
    repeat intro. exists (x:Q). split; auto.
  Qed.

  Lemma or_elim (x : T) P Q R : x:P ⊦ R ->
                                x:Q ⊦ R ->
                                meet_Perms2 (x:P) (x:Q) ⊦ R.
  Proof.
    repeat intro. destruct H1 as [X [? ?]]. destruct H1; subst; auto.
  Qed.

  Definition exists_Perms T (P : T -> T -> Perms) : T -> Perms :=
    fun x => meet_Perms (fun Q => exists y, Q = x:P(y)).

  Lemma exists_intro (x y : T) P : x:P(y) ⊦ x:(exists_Perms T P).
  Proof.
    repeat intro. exists (x:P(y)). split; auto. exists y; auto.
  Qed.

  Lemma exists_elim (x : T) P R : (forall (y': T), x:P(y') ⊦ R) ->
                                  x:(exists_Perms T P) ⊦ R.
  Proof.
    repeat intro. destruct H0 as [X [[? ?] ?]]. subst. eapply H; eauto.
  Qed.

  Class Ilookup (x : T) (lhs : Perms) (x_P : T -> Perms) rem : Prop :=
    ilookup : lhs ⊦ x:x_P ** rem.

  Instance Ilookup_empty x :
    Ilookup x empty true_p empty.
  Proof.
    red. rewrite sep_conj_Perms_bottom_identity. reflexivity.
  Qed.

  Instance Ilookup_base x P lhs :
    Ilookup x (x:P ** lhs) P lhs.
  Proof.
    red. reflexivity.
  Qed.

  Instance Ilookup_step (T' : Type) (x: T) (x' : T') lhs P P' rem :
    Ilookup x lhs P rem ->
    Ilookup x (x':P' ** lhs) P (x':P' ** rem).
  Proof.
    intros. red. red in H.
    Check Proper_entails_Perms_entails_Perms.
    rewrite (sep_conj_Perms_commut (x:P) _). rewrite <- sep_conj_Perms_assoc.
    apply sep_conj_Perms_monotone; intuition. rewrite sep_conj_Perms_commut. apply H.
  Qed.

  Class Ivar (x : T) P_lhs lhs P_rhs rem : Prop :=
    ivar : x:P_lhs ** lhs ⊦ x:P_rhs ** rem.

  Class Implies (lhs rhs rem : Perms) : Prop :=
    impl: lhs ⊦ rhs ** rem.

  Instance Implies_empty lhs :
    Implies lhs empty lhs.
  Proof.
    red. rewrite sep_conj_Perms_bottom_identity. reflexivity.
  Qed.

  Instance Implies_nonempty x lhs rhs P_lhs P_rhs rem1 rem2 rem3 :
    Ilookup x lhs P_lhs rem1 ->
    Ivar x P_lhs rem1 P_rhs rem2 ->
    Implies rem2 rhs rem3 ->
    Implies lhs (x:P_rhs ** rhs) rem3.
  Proof.
    intros. red. red in H, H0, H1. etransitivity. apply H.
    etransitivity. apply H0. rewrite <- sep_conj_Perms_assoc.
    apply sep_conj_Perms_monotone; intuition.
  Qed.

  Instance Ivar_true x lhs P_lhs :
    Ivar x P_lhs lhs true_p (x:P_lhs ** lhs).
  Proof.
    red. rewrite (sep_conj_Perms_commut (x:true_p) _).
    rewrite <- sep_conj_Perms_bottom_identity at 1. rewrite sep_conj_Perms_commut.
    apply sep_conj_Perms_monotone; reflexivity.
  Qed.

  Instance Ivar_eq_refl x lhs P_lhs :
    Ivar x P_lhs lhs (eq_p(x)) (x:P_lhs ** lhs).
  Proof.
    red. rewrite (sep_conj_Perms_commut (x:eq_p(x))).
    rewrite <- sep_conj_Perms_bottom_identity at 1. rewrite sep_conj_Perms_commut.
    apply sep_conj_Perms_monotone; intuition.
    (* typeclasses eauto. should work ? *)
    etransitivity. apply eq_refl.
    reflexivity.
  Qed.

  Instance Ivar_eq_elim x y lhs P_y P_x rem1 rem2:
    Ilookup y lhs P_y rem1 ->
    Ivar x P_y rem1 P_x rem2 ->
    Ivar x (eq_p(y)) lhs P_x rem2.
  Proof.
    intros. red in H, H0. red. etransitivity. 2: { apply H0. }
    repeat intro. destruct H1 as [? [? [? [? ?]]]]. destruct H1. apply H.
    eapply Perms_upwards_closed. eauto. etransitivity. apply lte_r_sep_conj_perm. eauto.
    (* todo use eq_elim lemma *)
  Qed.

  (* Typeclasses eauto := debug. *)

  Goal forall x y, Ilookup x (x:true_p ** (y:true_p ** empty)) true_p (y:true_p ** empty).
  Proof.
    typeclasses eauto.
  Qed.

  Goal forall x, Implies empty (x:true_p ** empty) (x:true_p ** empty).
  Proof.
    typeclasses eauto.
  Qed.

  Goal forall x y, Implies empty (x:true_p ** (y:true_p ** empty)) (x:true_p ** (y:true_p ** empty)).
  Proof.
    typeclasses eauto.
  Qed.

End implication.
