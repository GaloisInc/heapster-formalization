From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

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

Section MemoryPerms.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si memory}.

  (** memory helpers **)

  (* Lemma allocated_read c1 c2 ptr : *)
  (*   read c1 ptr = read c2 ptr -> *)
  (*   allocated c1 ptr -> *)
  (*   allocated c2 ptr. *)
  (* Proof. *)
  (*   destruct ptr as [b o]. *)
  (*   unfold read, allocated. simpl. intros. *)
  (*   destruct (m c1 b), (m c2 b); try solve [inversion H; inversion H0]; auto. *)
  (*   - destruct l0, l1. *)
  (*     destruct (bytes o), (bytes0 o); try solve [contradiction]. *)
  (*     + rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H0. *)
  (*       rewrite H0 in H. *)
  (*       destruct (o <? size0) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. auto. *)
  (*       inversion H. *)
  (*     + rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H0. *)
  (*       rewrite H0 in H. *)
  (*       destruct (o <? size0); inversion H. *)
  (*   - destruct l0. destruct (bytes o); try solve [contradiction]. *)
  (*     rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H0. *)
  (*     rewrite H0 in H. inversion H. *)
  (* Qed. *)

  (* Lemma allocated_read' c1 c2 ptr : *)
  (*   read c1 ptr = read c2 ptr -> *)
  (*   allocated c1 ptr = allocated c2 ptr. *)
  (* Proof. *)
  (* Admitted. *)

  (* Definition alloc_invariant (c1 c2 : config) (ptr : addr) : Prop := *)
  (*   allocated c1 ptr = allocated c2 ptr. *)

  (* Lemma alloc_invariant_read c1 c2 ptr : *)
  (*   alloc_invariant c1 c2 ptr -> *)
  (*   read c2 ptr = None -> *)
  (*   read c1 ptr = None. *)
  (* Proof. *)
  (*   destruct ptr as [b o]. *)
  (*   unfold alloc_invariant. unfold allocated. unfold read. simpl in *. intros. *)
  (*   destruct (m c1 b), (m c2 b); try solve [inversion H0]; auto. *)
  (*   - destruct l0, l1. *)
  (*     destruct (bytes o), (bytes0 o). *)
  (*     + destruct (o <? size) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite H in Heqb0. *)
  (*       rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite Heqb0 in H0. inversion H0. *)
  (*     + destruct (o <? size) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite H in Heqb0. inversion Heqb0. *)
  (*     + destruct (o <? size); auto. *)
  (*     + destruct (o <? size); auto. *)
  (*   - destruct l0. destruct (bytes o). *)
  (*     + destruct (o <? size) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite H in Heqb0. inversion Heqb0. *)
  (*     + destruct (o <? size); auto. *)
    (* Qed. *)
  (* Abort. *)

  (* Lemma write_success_allocation c c' ptr val : *)
  (*   write c ptr val = Some c' -> *)
  (*   alloc_invariant c c' ptr. *)
  (* Proof. *)
  (*   destruct ptr as [b o]. *)
  (*   intros. unfold alloc_invariant. unfold allocated. unfold write in H. simpl in *. *)
  (*   destruct (m c b) eqn:?; try solve [inversion H]. destruct l0. *)
  (*   destruct (o <? size) eqn:?; try solve [inversion H]. *)
  (*   destruct (is_some (bytes o)) eqn:?; try solve [inversion H]. *)
  (*   inversion H; subst; clear H. simpl. repeat rewrite Nat.eqb_refl. *)
  (*   destruct (bytes o); auto. inversion Heqb1. *)
  (* Qed. *)


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

  (** memory permissions **)

  (* gives permission to allocate memory, assuming the last allocated block was n-1 *)
  Program Definition malloc_perm (n : nat) : (@perm (Si * Ss)) :=
    {|
    (* always valid *)
    pre '(x, _) := length (lget x) = n;
    (* no new blocks are allocated *)
    rely '(x, _) '(y, _) := length (lget x) = length (lget y) /\
                            (forall ptr, fst ptr >= n ->
                                    sizeof (lget x) ptr = sizeof (lget y) ptr /\
                                    read (lget x) ptr = read (lget y) ptr);
    (* existing blocks do not change *)
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

  Definition malloc_Perms :=
    meet_Perms (fun Q => exists n : nat, Q = singleton_Perms (malloc_perm n)).

  Program Definition block_perm (size : nat) (ptr : addr) : (@perm (Si * Ss)) :=
    {|
    (* the ptr points to the first cell of an allocated block of size `size` *)
    pre '(x, _) :=
      (* if we swap the order of the equality then the obligation automatically
      unifies and we lose info... *)
      Some size = sizeof (lget x) ptr;
    (* if ptr satisfies the precondition, the size of the block does not change *)
    rely '(x, _) '(y, _) :=
      sizeof (lget x) ptr = sizeof (lget y) ptr;
    (* no updates allowed *)
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
    (* ptr points to valid memory *)
    pre '(x, _) := read (lget x) ptr = Some v;
    (* only checks if the memory ptr points to in the 2 memories are equal *)
    rely '(x, _) '(y, _) := read (lget x) ptr = read (lget y) ptr;
    (* no updates allowed *)
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
    (* ptr points to valid memory *)
    pre '(x, _) := Some v = read (lget x) ptr;
    (* only checks if the memory ptr points to in the 2 configs are equal *)
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

  Definition read_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : Value, Q = singleton_Perms (read_perm ptr y) * P y).

  Definition write_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : Value, Q = singleton_Perms (write_perm ptr y) * P y).

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
      (* forall ptr, (allocated (lget x) ptr = false -> allocated (lget y) ptr = false) /\ *)
    (*        (allocated (lget x) ptr = true -> sizeof (lget x) ptr = sizeof (lget y) ptr); *)
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

  Lemma typing_malloc l :
    typing
      malloc_Perms
      (fun v _ => match v with
               | VPtr addr => malloc_Perms *
                             singleton_Perms (block_perm (S l) addr) *
                             write_Perms addr (fun _ => bottom_Perms)
               | _ => top_Perms
               end)
      (malloc (S l))
      (Ret tt).
  Proof.
    intros p si ss Hp Hpre. pstep. unfold malloc.
    destruct Hp as (? & (n & ?) & Hp); subst.
    (* read step *)
    rewritebisim @bind_trigger. econstructor; eauto; try reflexivity.
    (* write step *)
    rewritebisim @bind_trigger. unfold id. econstructor; eauto.
    { apply Hp in Hpre. apply Hp. simpl in *. rewrite lGetPut.
      intros ptr Hn. split.
      - unfold read, allocated. simpl. subst. rewrite nth_error_app_early; auto.
      - unfold sizeof. simpl. subst. rewrite nth_error_app_early; auto.
    }
    (* return *)
    { eapply sep_step_lte. apply Hp. apply sep_step_malloc. }
    { econstructor; eauto.
      - simpl. repeat rewrite lGetPut. apply Hp in Hpre. simpl in Hpre.
        split; [| split].
        + rewrite last_length. lia.
        + unfold sizeof. simpl.
          rewrite nth_error_app_last; auto.
        + unfold read, allocated. simpl. rewrite nth_error_app_last; auto.
      - simpl. apply Hp in Hpre. simpl in Hpre. rewrite Hpre.
        eexists. exists (write_perm (n, 0) (VNum 0)).
        split; [| split].
        + do 2 eexists. split; [| split]; try reflexivity.
          eexists. split.
          * exists (n + 1). reflexivity.
          * simpl. reflexivity.
        + eexists. split; [exists (VNum 0); reflexivity |].
          do 2 eexists. split; [simpl; reflexivity | split]; simpl; auto.
          apply sep_conj_perm_bottom.
        + constructor; auto.
          { intros [] (? & ? & ?). simpl in *. split; split; auto.
            - split; [| apply malloc_block; simpl; lia].
              apply H0.
            - symmetry. apply separate_sep_conj_perm; symmetry.
              + apply malloc_write. simpl. lia.
              + apply write_block.
              + apply malloc_block; simpl; lia.
          }
    }
  Qed.

  Lemma typing_free ptr (Q : Value -> Perms) :
    typing
      (write_Perms ptr Q * singleton_Perms (block_perm 1 ptr))
      (fun _ _ => bottom_Perms)
      (free (VPtr ptr))
      (Ret tt).
  Proof.
    intros p si ss Hp Hpre. pstep. unfold free.
    destruct Hp as (pwrite' & pblock & (? & (v & ?) & Hpwrite) & Hpblock & Hlte); subst.
    destruct Hpwrite as (pwrite & pv & Hpwrite & Hpv & Hlte').
    assert (Hoffset : snd ptr = 0).
    { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      apply Hpblock in Hpre. simpl in Hpre. unfold sizeof in Hpre.
      rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)).
      destruct (snd ptr =? 0); inversion Hpre; auto.
    }
    rewrite Hoffset. simpl.
    (* read step *)
    rewritebisim @bind_trigger. econstructor; auto; try reflexivity.
    pose proof Hpre as Hpre'. apply Hlte in Hpre'.
    destruct Hpre' as (Hprewrite & Hpreblock & Hsep).
    apply Hpblock in Hpreblock. simpl in Hpreblock.
    unfold sizeof in Hpreblock. rewrite Hoffset in Hpreblock. simpl in Hpreblock.
    destruct (nth_error (lget si) (fst ptr)) eqn:?; try solve [inversion Hpreblock].
    destruct o; try solve [inversion Hpreblock].
    destruct l. inversion Hpreblock; clear Hpreblock; subst.
    (* write step *)
    rewritebisim @bind_trigger. unfold id. econstructor; auto.
    - apply Hlte. constructor 1. left.
      apply Hlte'. constructor 1. left.
      apply Hpwrite. simpl.
      split; [| split]; rewrite lGetPut; simpl; auto.
      + intros. unfold read. unfold allocated. simpl.
        destruct ptr as [b o]; destruct ptr' as [b' o'].
        apply addr_neq_cases in H. simpl.
        admit. (* break up the <> into cases, then use nth_error_replace_list_index_eq/neq *)
      + admit.
      + assert (fst ptr < length (lget si)).
        { apply nth_error_Some. intro. rewrite H in Heqo. inversion Heqo. }
        apply replace_list_index_length; auto.
    - apply sep_step_lte'. apply bottom_perm_is_bottom.
    - constructor; simpl; auto.
  Admitted.

  Lemma typing_load {R} ptr (Q : Value -> Perms) (r : R) :
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
    assert (read (lget c1) ptr = Some x0).
    { apply H2 in H0. destruct H0 as (? & _). apply H in H0. auto. }
    rewrite H3. constructor; eauto.
    simpl. exists x, x1. split; [| split]; eauto. eexists. split; eauto.
    simpl. exists x, bottom_perm. split; [| split]; eauto.
    rewrite sep_conj_perm_bottom. reflexivity.
  Qed.

  Lemma typing_store {R} ptr val' (P Q : Value -> Perms) (r : R) :
    typing
      (write_Perms ptr P * Q val')
      (fun _ _ => write_Perms ptr Q)
      (store (VPtr ptr) val')
      (Ret r).
  Proof.
    intros p'' c1 c2 H Hpre. pstep. unfold store. rewritebisim @bind_trigger.
    destruct H as (p' & q & Hwrite & Hq & Hlte). destruct Hwrite as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pw & p & Hwritelte & Hp & Hlte'). simpl in *.
    assert (exists val, read (lget c1) ptr = Some val).
    {
      apply Hlte in Hpre. destruct Hpre as (Hpre & _).
      apply Hlte' in Hpre. destruct Hpre as (Hpre & _).
      apply Hwritelte in Hpre. eexists. symmetry. apply Hpre.
    }
    destruct H as (val & Hread). eapply (read_success_write _ _ _ val') in Hread.
    destruct Hread as (c' & Hwrite).
    assert (Hguar : guar p' (c1, c2) ((lput c1 c'), c2)).
    {
      apply Hlte'. constructor 1. left. apply Hwritelte. simpl.
      rewrite lGetPut.
      split; [| split].
      + eapply write_success_read_neq; eauto.
      + eapply write_success_sizeof; eauto.
      + rewrite lGetPut. eapply write_success_length; eauto.
    }
    econstructor; eauto.
    3: {
      rewrite Hwrite. constructor; eauto.
      2: { simpl. eexists. split. exists val'. reflexivity.
           simpl. eexists. exists q. split; [reflexivity | split]; eauto. reflexivity. }
      split; [| split].
      - symmetry. eapply write_success_read_eq; rewrite lGetPut; eauto.
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

  Lemma typing_store' {R} ptr val' (P : Value -> Perms) (r : R):
    typing
      (write_Perms ptr P)
      (fun _ _ => write_Perms ptr (eq_p val'))
      (store (VPtr ptr) val')
      (Ret r).
  Proof.
    assert (bottom_Perms ≡ @eq_p Si Ss _ val' val').
    { split; repeat intro; simpl; auto. }
    rewrite <- sep_conj_Perms_bottom_identity. rewrite sep_conj_Perms_commut.
    rewrite H. apply typing_store.
  Qed.

End MemoryPerms.
