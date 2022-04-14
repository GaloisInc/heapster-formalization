From Heapster Require Import
     Config.

From Coq Require Import
     Structures.Equalities
     Ensembles
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     Program.Equality.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.
Open Scope itree_scope.
Open Scope monad_scope.

Variant MemoryE : Type -> Type :=
| Load : forall (p : SByte), MemoryE SByte
| Store : forall (p v : SByte) , MemoryE unit
.

(* Definition E := (stateE config +' nondetE). *)
Definition E := (MemoryE +' nondetE).

Variant step {R} : itree E R -> config -> itree E R -> config -> Prop :=
| step_tau : forall t c, step (Tau t) c t c
| step_nondet_true : forall k c, step (vis Or k) c (k true) c
| step_nondet_false : forall k c, step (vis Or k) c (k false) c
| step_load : forall k c p v, read c p = Some v ->
                         step (vis (Load (Ptr p)) k) c (k v) c
| step_store : forall k c c' p v, write c p v = Some c' ->
                             step (vis (Store (Ptr p) v) k) c (k tt) c'
| step_load_fail : forall k c p, read c p = None ->
                            step (vis (Load (Ptr p)) k) c (k (Byte 0)) (error_config c)
| step_store_fail : forall k c p v, write c p v = None ->
                               step (vis (Store (Ptr p) v) k) c (k tt) (error_config c)
| step_load_invalid : forall k c b, step (vis (Load (Byte b)) k) c (k (Byte 0)) (error_config c)
| step_store_invalid : forall k c b v, step (vis (Store (Byte b) v) k) c (k tt) (error_config c)
.

Inductive multistep {R} : itree E R -> config -> itree E R -> config -> Prop :=
| multistep_refl : forall t c, multistep t c t c
| multistep_step : forall t c t' c' t'' c'',
    multistep t c t' c' -> step t' c' t'' c'' -> multistep t c t'' c''
.

Ltac rewritebisim lem := pose proof lem as bisim;
                         eapply bisimulation_is_eq in bisim;
                         rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply bisimulation_is_eq in bisim;
                              rewrite bisim in H;
                              clear bisim.

Lemma step_bind {R1 R2} : forall (t1 t2 : itree E R1) (c1 c2 : config) (k : R1 -> itree E R2),
    step t1 c1 t2 c2 ->
    step (t1 >>= k) c1 (t2 >>= k) c2.
Proof.
  intros. inversion H; subst; try solve [rewritebisim @bind_vis; constructor; auto].
  - rewritebisim @bind_tau. constructor.
  - rewritebisim @bind_vis.
    (* constructor doesn't work here for some reason *)
    apply (step_load (fun v => x <- k0 v;; k x) _ _ _ H0).
Qed.

Lemma step_ret_bind {R1 R2} : forall (t1 t2 : itree E R1) (c1 c2 : config) (r : R2),
    step t1 c1 t2 c2 ->
    step (Ret r;; t1) c1 t2 c2.
Proof.
  intros. rewritebisim @bind_ret_l. assumption.
Qed.

Lemma step_fmap {R1 R2} : forall (t t' : itree E R1) c c' (f : R1 -> R2),
    step t c t' c' ->
    step (fmap f t) c (fmap f t') c'.
Proof.
  intros. inversion H; subst; simpl; unfold ITree.map;
            try solve [rewritebisim @bind_vis; constructor; auto].
  - rewritebisim @bind_tau. constructor; auto.
  - rewritebisim @bind_vis.
    (* again have to specify k manually? *)
    apply (step_load (fun x => x' <- k x;; Ret (f x'))); auto.
Qed.

Lemma bind_fst {R1 R2} (t : itree E R1) (r2 : R2) :
  x1 <- t;; x <- Ret (x1, r2);; Ret (fst x) ≅ t.
Proof.
  revert t r2. pcofix CIH. intros.
  rewritebisim @unfold_bind. pstep.
  rewrite (itree_eta_ t0). destruct (observe t0); simpl.
  - rewritebisim @unfold_bind. constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma bind_snd {R1 R2} (t : itree E R2) (r1 : R1) :
  x2 <- t;; x <- Ret (r1, x2);; Ret (snd x) ≅ t.
Proof.
  revert t r1. pcofix CIH. intros.
  rewritebisim @unfold_bind. pstep.
  rewrite (itree_eta_ t0). destruct (observe t0); simpl.
  - rewritebisim @unfold_bind. constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma step_fmap_fst {R1 R2} : forall (t : itree E R2) (t' : itree E (R1 * R2)) c c' (r1 : R1),
    step (fmap (fun r2 : R2 => (r1, r2)) t) c t' c' ->
    step t c (fmap snd t') c'.
Proof.
  simpl. intros. unfold ITree.map in *. inversion H; subst.
  - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_snd. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 true). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_snd. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 false). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_snd. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 v). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 (Byte 0)). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor 7; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 (Byte 0)). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 tt). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
Qed.

Lemma step_fmap_snd {R1 R2} : forall (t : itree E R1) (t' : itree E (R1 * R2)) c c' (r2 : R2),
    step (fmap (fun r1 : R1 => (r1, r2)) t) c t' c' ->
    step t c (fmap fst t') c'.
Proof.
  simpl. intros. unfold ITree.map in *. inversion H; subst.
  - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_fst. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 true). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_fst. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 false). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_fst. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 v). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 (Byte 0)). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor 7; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 (Byte 0)). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 tt). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
Qed.

Lemma step_fmap_inv {R1 R2 : Type} (f : R1 -> R2) (t : itree E R1) (t' : itree E R2) c c' :
  step (fmap f t) c t' c' ->
  exists t'', t' = fmap f t''.
Proof.
  intros. simpl in *. unfold ITree.map in *. inversion H; subst.
  - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 true). apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 false). apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 v). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 (Byte 0)). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 (Byte 0)). apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 tt). apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
Qed.
