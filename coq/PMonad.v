From Coq Require Import
     Relations.Relation_Definitions
     Setoids.Setoid
     Classes.RelationClasses
     Classes.Morphisms.

From ExtLib Require Import
     Structures.Monads.


Definition PM (A:Type) := A -> Prop.

Definition ret_PM := fun (A:Type) (eqA : relation A) (x:A) => (eqA x).

Definition bind_PM := fun (A B:Type)
                        (eqA : relation A)
                        (eqB : relation B)
                        (f : A -> PM B) (P : PM A)
                      => (fun (y:B) => exists (x:A),
                             eqA x x /\ P x /\ (f x) y).

Definition PM_equiv A (eqA:relation A) : relation (PM A) :=
  fun (P Q: PM A) => ((forall x y:A, eqA x y -> (P x) <-> (Q y))
                   /\ (Proper (eqA ==> iff) P)
                   /\ (Proper (eqA ==> iff) Q)).

Program Instance PER_PM (A:Type) (eqA:relation A) `{PER A eqA} : PER (PM_equiv A eqA).
Next Obligation.
  red. intros x y Heq. red. unfold PM_equiv.
  repeat red in Heq.
  intuition; subst.
  + rewrite H0. apply H4. symmetry. apply H1.
  + eapply H0 in H4. apply H4. symmetry. apply H1.
Qed.
Next Obligation.
  repeat red. intros x y z Hxy Hyz.
  repeat red in Hxy.
  repeat red in Hyz.
  intuition.
  + rewrite <- H2. rewrite <- H0. apply H7. apply H3. eapply transitivity. symmetry. apply H3. apply H3.
  + rewrite H0. rewrite H2. apply H7. apply H3. eapply transitivity. apply H3. symmetry. apply H3.
Qed.

