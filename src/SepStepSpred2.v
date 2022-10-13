(* begin hide *)
From Heapster Require Import
     Permissions
     PermissionsSpred2.

From Coq Require Import
     Classes.RelationClasses.
(* end hide *)

Section step.
  Context (config : Type).
  Context (spred spred' : config -> Prop).
  (* Context {spred2 spred2' : specConfig -> Prop}. *)
  Context (Hspred : forall x, spred x -> spred' x).
  (* Context (Hspred2 : forall x, spred2 x -> spred2' x). *)
  (* TODO: change to 1 spred *)

  (** * Preserves separability *)
  Definition sep_step
             (p : @perm ({x | spred' x}))
             (q : @perm ({x | spred x})) : Prop :=
    forall r, p ⊥ r -> q ⊥ (restrict _ _ _ Hspred r).
End step.

Global Instance sep_step_refl config spred : Reflexive (sep_step config spred spred (fun x H => H)).
Proof.
  repeat intro; auto. rewrite restrict_same. auto.
Qed.

(* Global Instance sep_step_trans : Transitive sep_step. *)
(* Proof. *)
(*   repeat intro. auto. *)
(* Qed. *)

Lemma sep_step_lte config (spred1 spred2 : config -> Prop) Hspred :
  forall p p' q, p <= p' ->
            sep_step config spred1 spred2 Hspred p q ->
            sep_step config spred1 spred2 Hspred p' q.
Proof.
  repeat intro. apply H0. symmetry. symmetry in H1. eapply separate_antimonotone; eauto.
Qed.

(* Lemma sep_step_lte' : forall p q, q <= p -> sep_step p q. *)
(* Proof. *)
(*   repeat intro. symmetry. eapply separate_antimonotone; eauto. symmetry; auto. *)
(* Qed. *)

(* Program Definition sym_guar_perm (p : @perm config) : perm := *)
(*   {| *)
(*     pre x := False; *)
(*     rely := guar p; *)
(*     guar := rely p; *)
(*   |}. *)
(* Lemma separate_self_sym : forall p, p ⊥ sym_guar_perm p. *)
(* Proof. *)
(*   intros. split; intros; auto. *)
(* Qed. *)

(* Lemma sep_step_rely : forall p q x y, sep_step p q -> *)
(*                                  rely p x y -> *)
(*                                  rely q x y. *)
(* Proof. *)
(*   intros. specialize (H (sym_guar_perm p) (separate_self_sym _)). *)
(*   apply H; auto. *)
(* Qed. *)

(* Lemma sep_step_guar : forall p q x y, sep_step p q -> *)
(*                                  guar q x y -> *)
(*                                  guar p x y. *)
(* Proof. *)
(*   intros. specialize (H (sym_guar_perm p) (separate_self_sym _)). *)
(*   apply H; auto. *)
(* Qed. *)

(* Lemma sep_step_rg : forall p q, *)
(*     (forall x y, guar q x y -> guar p x y) -> *)
(*     (forall x y, rely p x y -> rely q x y) -> *)
(*     sep_step p q. *)
(* Proof. *)
(*   repeat intro. split; intros. *)
(*   - apply H0. apply H1. auto. *)
(*   - apply H1. apply H. auto. *)
(* Qed. *)

(* Lemma sep_step_iff : forall p q, *)
(*     sep_step p q <-> (forall x y, rely p x y -> rely q x y) /\ (forall x y, guar q x y -> guar p x y). *)
(* Proof. *)
(*   split; [split; intros; [eapply sep_step_rely | eapply sep_step_guar] | *)
(*            intros []; apply sep_step_rg]; eauto. *)
(* Qed. *)

Lemma sep_step_sep_conj_l config spred1 spred2 Hspred :
  forall p1 p2 q, p1 ⊥ q ->
             sep_step config spred1 spred2 Hspred p1 p2 ->
             sep_step config spred1 spred2 Hspred (p1 ** q) (p2 ** q).
Proof.
  intros p1 p2 q ? ?.
  repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
  - apply H0. symmetry. eapply separate_sep_conj_perm_l; eauto.
  - symmetry. eapply separate_sep_conj_perm_r; eauto.
Qed.
Lemma sep_step_sep_conj_r : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (q ** p1) (q ** p2).
Proof.
  intros p1 p2 q ? ?.
  repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
  - symmetry. eapply separate_sep_conj_perm_l; eauto.
  - apply H0. symmetry. eapply separate_sep_conj_perm_r; eauto.
  - symmetry. auto.
Qed.
