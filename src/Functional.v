From Heapster Require Import
     Permissions
     Config.
     (* StepError. *)
     (* Typing. *)

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

Section bisim.
  Variant ModifyE {C : Type} : Type -> Type :=
  | Modify : forall (f : C -> C), ModifyE C
  .

  Definition E (C : Type) := (exceptE unit +' @ModifyE C +' nondetE).

  Context {config specConfig : Type}.

  (* todo move somewhere else *)
  Definition sep_step (p q : @perm config specConfig) : Prop :=
    forall r, p ⊥ r -> q ⊥ r.

  Inductive typing_gen {R1 R2 : Type} typing (p : perm) (Q : R1 -> R2 -> Perms) :
    itree (E config) R1 -> config -> itree (E specConfig) R2 -> specConfig -> Prop :=
  | typing_ret r1 c1 r2 c2 :
      pre p c1 c2 ->
      p ∈ Q r1 r2 ->
      typing_gen typing p Q (Ret r1) c1 (Ret r2) c2
  | typing_err t1 c1 c2 :
      typing_gen typing p Q t1 c1 (throw tt) c2
  | typing_tau_L t1 c1 t2 c2 :
      pre p c1 c2 ->
      typing_gen typing p Q t1 c1 t2 c2 ->
      typing_gen typing p Q (Tau t1) c1 t2 c2
  | typing_tau_R t1 c1 t2 c2 :
      pre p c1 c2 ->
      typing_gen typing p Q t1 c1 t2 c2 ->
      typing_gen typing p Q t1 c1 (Tau t2) c2
  | typing_tau t1 c1 t2 c2 :
      pre p c1 c2 ->
      typing p Q t1 c1 t2 c2 ->
      typing_gen typing p Q (Tau t1) c1 (Tau t2) c2
  | typing_modify_L f k c1 t2 c2 p' :
      pre p c1 c2 ->
      guar p c1 (f c1) ->
      sep_step p p' ->
      typing_gen typing p' Q (k c1) (f c1) t2 c2 ->
      typing_gen typing p Q (vis (Modify f) k) c1 t2 c2
  | typing_modify_R t1 c1 f k c2 p' :
      pre p c1 c2 ->
      sep_step p p' ->
      typing_gen typing p Q t1 c1 (k c2) (f c2) ->
      typing_gen typing p Q t1 c1 (vis (Modify f) k) c2
  | typing_modify f1 k1 c1 f2 k2 c2 p' :
      pre p c1 c2 ->
      guar p c1 (f1 c1) ->
      sep_step p p' ->
      typing p Q (k1 c1) (f1 c1) (k2 c2) (f2 c2) ->
      typing_gen typing p Q (vis (Modify f1) k1) c1 (vis (Modify f2) k2) c2
  | typing_choice_L k c1 t2 c2 p' :
      pre p c1 c2 ->
      sep_step p p' ->
      (forall b, typing_gen typing p Q (k b) c1 t2 c2) ->
      typing_gen typing p Q (vis Or k) c1 t2 c2
  | typing_choice_R t1 c1 k c2 p' :
      pre p c1 c2 ->
      sep_step p p' ->
      (forall b, typing_gen typing p Q t1 c1 (k b) c2) ->
      typing_gen typing p Q t1 c1 (vis Or k) c2
  | typing_choice k1 c1 k2 c2 p' :
      pre p c1 c2 ->
      sep_step p p' ->
      (forall b1 b2, typing p Q (k1 b1) c1 (k2 b2) c2) ->
      typing_gen typing p Q (vis Or k1) c1 (vis Or k2) c2
  .

  Definition typing {R1 R2} := paco6 (@typing_gen R1 R2) bot6.

End bisim.



Variant typing_gen {R1 R2 : Type} typing (P : Perms) (Q : R1 -> R2 -> Perms) :
  itree E R1 -> itree specE R2 -> Prop :=
| cond : forall t spec, (exists c t' c', step t c t' c') /\ (* we can step *)
                   (forall p c, p ∈ P ->
                           pre p c ->
                           forall t' c',
                             step t c t' c' -> (* and everything we can step to... *)
                             (
                               (* we step to configs that satisfy the perm *)
                               guar p c c' /\
                               (* we step to machines that are well-typed by some
                                  other perm that maintains separation *)
                               exists spec', spec ≈ spec' /\
                               exists P', typing P' Q t' spec' /\ exists p', p' ∈ P' /\ p = p' /\ pre p' c')) ->
                   typing_gen typing P Q t spec
| err : forall t, typing_gen typing P Q t (throw tt)
| ret : forall r1 r2, Q r1 r2 ⊑ P -> typing_gen typing P Q (Ret r1) (Ret r2).

(* Definition typing_perm := paco3 typing_perm_gen bot3. *)
Definition typing {R1 R2} := paco4 (@typing_gen R1 R2) bot4.
