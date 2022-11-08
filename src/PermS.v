From Heapster Require Import
     Permissions
     PermissionsSpred2.

From Coq Require Import
     Classes.RelationClasses.

Section PermSet.
  Context {config : Type}.

  Record Perms2 :=
    {
      in_Perms2 : forall {spred}, @perm { x | spred x } -> Prop;
      (* Perms_upwards_closed1 : forall (spred1 spred2 : config -> Prop) *)
      (*                           (Hspred : forall x, spred1 x -> spred2 x) *)
      (*                           (p1 : @perm {x | spred1 x}) (p2 : @perm {x | spred2 x}), *)
      (*   in_Perms2 p1 -> *)
      (*   hlte_perm1 config spred1 spred2 Hspred p1 p2 -> *)
      (*   in_Perms2 p2 (* p2 has bigger spred *); *)
      Perms_upwards_closed2 : forall (spred1 spred2 : config -> Prop)
                                (Hspred : forall x, spred1 x -> spred2 x)
                                (p1 : @perm {x | spred2 x}) (p2 : @perm {x | spred1 x}),
        in_Perms2 p1 ->
        hlte_perm2 config spred1 spred2 Hspred p1 p2 ->
        in_Perms2 p2 (* p2 has smaller spred *)
    }.
  Notation "p ∈2 P" := (in_Perms2 P p) (at level 60).


  Definition lte_Perms2 (P Q : Perms2) : Prop :=
    forall spred (p : @perm {x | spred x}), p ∈2 Q -> p ∈2 P.
  Notation "P ⊑2 Q" := (lte_Perms2 P Q) (at level 60).

  Program Definition top_Perms2 : Perms2 :=
    {|
      in_Perms2 := fun _ _ => False
    |}.
  Program Definition bottom_Perms2 : Perms2 :=
    {|
      in_Perms2 := fun _ _ => True
    |}.

  Program Definition sep_conj_Perms2 (P Q : Perms2) : Perms2 :=
    {|
      in_Perms2 := fun spred r =>
                     exists spred' Hspred (p q : @perm {x | spred' x}),
                       in_Perms2 P p /\
                         in_Perms2 Q q /\
                         hlte_perm2 config spred spred' Hspred (p ** q) r
    |}.
  Next Obligation.
    rename H into spred', H1 into Hspred', H2 into p, H3 into q.
    exists spred'. eexists. Unshelve.
    2: { intros. auto. }
    exists p, q. split; [| split]; auto. eapply hlte_perm2_transitive; eauto.
  Qed.

End PermSet.
