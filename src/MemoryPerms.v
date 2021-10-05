(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

From Heapster Require Import
     Utils
     Permissions
     Memory
     SepStep
     Typing.

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
Local Open Scope itree_scope.
(* end hide *)

Section MemoryPerms.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si memory}.

  (** * Memory permissions **)

  (** Gives permission to allocate memory, assuming the last allocated block was [n-1] *)
  Program Definition malloc_perm (n : nat) : (@perm (Si * Ss)) :=
    {|
    (** always valid *)
    pre '(x, _) := length (lget x) = n;
    (** No new blocks are allocated *)
    rely '(x, _) '(y, _) := length (lget x) = length (lget y) /\
                            (forall ptr, fst ptr >= n ->
                                    sizeof (lget x) ptr = sizeof (lget y) ptr /\
                                    read (lget x) ptr = read (lget y) ptr);
    (** Existing blocks do not change *)
    guar '(x, _) '(y, _) :=
      (forall ptr, fst ptr < n ->
              read (lget x) ptr = read (lget y) ptr /\
              sizeof (lget x) ptr = sizeof (lget y) ptr);
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto. intros [] [].
    split; [| split]; try solve [etransitivity; eauto];
      (etransitivity; [apply H0 | apply H2]; eauto).
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; auto.
    split; (etransitivity; [apply H; auto |]); apply H0; auto.
  Qed.

  Program Definition block_perm (size : nat) (ptr : addr) : (@perm (Si * Ss)) :=
    {|
    (** [ptr] points to the first cell of an allocated block of size [size] *)
    pre '(x, _) :=
      (* if we swap the order of the equality then the obligation automatically
      unifies and we lose info... *)
      Some size = sizeof (lget x) ptr;
    (** if [ptr] satisfies the precondition, the size of the block does not change *)
    rely '(x, _) '(y, _) :=
      sizeof (lget x) ptr = sizeof (lget y) ptr;
    (** no updates allowed *)
    guar '(x, _) '(y, _) := x = y;
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; etransitivity; eauto.
  Qed.

  Lemma malloc_block n size ptr :
    size > 0 ->
    fst ptr < n ->
    malloc_perm n ⊥ block_perm size ptr.
  Proof.
    intros Hsize Hn.
    constructor; intros [] [] ?; simpl in *; subst; auto.
    intros. apply H; auto.
  Qed.

  Program Definition read_perm (ptr : addr) (v : Value) : @perm (Si * Ss) :=
    {|
    (** [ptr] points to [v] *)
    pre '(x, _) := read (lget x) ptr = Some v;
    (** only checks if the memory [ptr] points to in the 2 memories are equal *)
    rely '(x, _) '(y, _) := read (lget x) ptr = read (lget y) ptr;
    (** no updates allowed *)
    guar '(x, _) '(y, _) := x = y;
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; subst; auto.
  Qed.

  Program Definition write_perm (ptr : addr) (v : Value) : (@perm (Si * Ss)) :=
    {|
    (* [ptr] points to [v] *)
    pre '(x, _) := Some v = read (lget x) ptr;
    (* only checks if the memory [ptr] points to in the 2 configs are equal *)
    rely '(x, _) '(y, _) := read (lget x) ptr = read (lget y) ptr;
    (* only the pointer we have write permission to may change *)
    guar '(x, _) '(y, _) := (forall ptr', ptr <> ptr' -> read (lget x) ptr' = read (lget y) ptr') /\
                            (forall ptr', sizeof (lget x) ptr' = sizeof (lget y) ptr') /\
                            length (lget x) = length (lget y);
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] |]; auto.
    intros [] [] [] ? ?.
    split; [| split]; (etransitivity; [apply H; auto |]); apply H0; auto.
  Qed.


  Lemma read_lte_write : forall ptr v, read_perm ptr v <= write_perm ptr v.
  Proof.
    constructor; simpl; intros [] []; subst; auto. intros; subst.
    split; [| split]; reflexivity.
  Qed.

  Lemma malloc_write : forall n ptr v,
      fst ptr < n ->
      malloc_perm n ⊥ write_perm ptr v.
  Proof.
    intros n ptr v. constructor; intros [] []; simpl in *; intros.
    - destruct ptr. split; [| intros [] ?; split]; auto; apply H0;
                      intro Heq; inversion Heq; subst; lia.
    - apply H0; auto.
  Qed.

  Lemma write_block : forall b o o' size v,
      block_perm size (b, o) ⊥ write_perm (b, o') v.
  Proof.
    constructor; intros [] [] ?; simpl in *; subst; auto.
    apply H.
  Qed.

  Lemma write_write_sep ptr ptr' v v' :
      ptr <> ptr' ->
      write_perm ptr v ⊥ write_perm ptr' v'.
  Proof.
    intros Hdiff. constructor; intros; destruct x, y; simpl; apply H; auto.
  Qed.

  Program Definition post_malloc_perm n size : @perm (Si * Ss) :=
    {|
    pre '(x, _) :=
      length (lget x) = n + 1 /\
      Some size = sizeof (lget x) (n, 0) /\
      Some (VNum 0) = read (lget x) (n, 0);
    rely x y :=
      rely (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0)) x y;
    rely_PO := rely_PO (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0));
    guar x y :=
      guar (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0)) x y;
    guar_PO := guar_PO (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0));
    |}.

  Lemma sep_step_malloc n size : sep_step (malloc_perm n)
                                          (post_malloc_perm n size).
  Proof.
    apply sep_step_rg.
    - intros [si ss] [si' ss'] ?. induction H; try solve [etransitivity; eauto].
      destruct H.
      2: { destruct x, y. destruct H as (? & ? & ?). split; auto.
           apply H; intro Heq; inversion Heq; subst; simpl in *; lia.
      }
      induction H; try solve [etransitivity; eauto]. destruct H.
      + destruct x, y. split; apply H; lia.
      + destruct x, y. simpl in *. subst; auto.
    - intros [si ss] [si' ss'] [Hlen Hptr]. simpl in *.
      split; [split; [split |] |]; auto; intros; apply Hptr; simpl; lia.
  Qed.

  (** * Memory mermission sets *)
  Definition malloc_Perms :=
    meet_Perms (fun Q => exists n : nat, Q = singleton_Perms (malloc_perm n)).

  Definition read_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : Value, Q = singleton_Perms (read_perm ptr y) * P y).

  Definition write_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : Value, Q = singleton_Perms (write_perm ptr y) * P y).

  (** * Memory operations *)
  Definition load (v : Value) : itree (sceE Si) Value :=
    s <- trigger (Modify id);;
    match v with
    | VNum _ => throw tt
    | VPtr p => match read (lget s) p with
               | None => throw tt
               | Some b => Ret b
               end
    end.

  Definition store (ptr : Value) (v : Value) : itree (sceE Si) Si :=
    match ptr with
    | VNum _ => throw tt
    | VPtr ptr => s <- trigger (Modify (fun s => match write (lget s) ptr v with
                                            | None => s
                                            | Some c => (lput s c)
                                            end)) ;;
                 match write (lget s) ptr v with
                 | None => throw tt
                 | Some c => Ret (lput s c)
               end
    end.

  Definition malloc (size : nat) : itree (sceE Si) Value :=
    s <- trigger (Modify id);; (* do a read first to use length without subtraction *)
    trigger (Modify (fun s =>
                       (lput s ((lget s) ++
                                         [Some (LBlock size
                                                       (fun o => if o <? size
                                                              then Some (VNum 0)
                                                              else None))]))));;
    Ret (VPtr (length (lget s), 0)).

  Definition free (ptr : Value) : itree (sceE Si) unit :=
    match ptr with
    | VNum _ => throw tt
    | VPtr ptr =>
      if snd ptr =? 0
      then
        s <- trigger (Modify id);;
        match nth_error (lget s) (fst ptr) with
        | Some (Some (LBlock size bytes)) =>
          trigger (Modify (fun s =>
                             (lput s (replace_list_index
                                        (lget s)
                                        (fst ptr)
                                        (Some (LBlock size (fun o => if o <? size then None else bytes o)))))));;
          Ret tt
        | _ => throw tt
        end
      else throw tt
    end.

  Example no_error_load s : no_errors (lput s (mem_at (0, 0) (VNum 1)))
                                      (load (VPtr (0, 0))).
  Proof.
    pstep. unfold load. rewritebisim @bind_trigger. constructor.
    left. pstep. rewrite lGetPut. constructor.
  Qed.
  Example no_error_store s : no_errors (lput s (mem_at (0, 0) (VNum 1)))
                                       (store (VPtr (0, 0)) (VNum 2)).
  Proof.
    pstep. unfold store. rewritebisim @bind_trigger. constructor.
    left. pstep. rewrite lGetPut. constructor.
  Qed.

End MemoryPerms.
