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

From Heapster2 Require Import
     Utils
     Permissions
     PermissionsSpred2
     Memory
     SepStep
     Typing
     PermType.

From ITree Require Import
     ITree
     Eq.Eqit.

From Paco Require Import
     paco.

Import MonadNotation.
Import ListNotations.
(* end hide *)

Section MemoryPerms.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si memory}.
  Context {Spred : Type}.
  Context {interp_spred : Spred -> Si * Ss -> Prop}.
  Context (Hinv : forall spred si ss m,
              interp_spred spred (si, ss) <->
                interp_spred spred (lput si m, ss)).


  Section asdf.
  Context (spred : Spred).
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

  (** * Memory permissions **)

  (** Gives permission to allocate memory, assuming the last allocated block was [n-1] *)
  Program Definition malloc_perm (n : nat) : (@perm {x : Si * Ss | interp_spred spred x }) :=
    {|
    (** there are exactly n allocated blocks *)
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
    constructor.
    - intros [[] ?]. cbn. split; auto.
    - intros [[] ?] [[] ?] [[] ?]. cbn. intros [] []. split. etransitivity; eauto.
      intros. split.
      + etransitivity. apply H0; auto. apply H2; auto.
      + etransitivity. apply H0; auto. apply H2; auto.
  Qed.
  Next Obligation.
    constructor; [intros [[] ?] | intros [[] ?] [[] ?] [[] ?] ? ?]; cbn in *; auto.
    split; (etransitivity; [apply H; auto |]); apply H0; auto.
  Qed.
  Next Obligation.
    cbn in *. destruct H. rewrite <- H. auto.
  Qed.

  Program Definition block_perm (size : nat) (ptr : addr) : (@perm { x : (Si * Ss) | interp_spred spred x} ) :=
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
    constructor; [intros [[] ?] | intros [[] ?] [[] ?] [[] ?]]; cbn in *; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [[] ?] | intros [[] ?] [[] ?] [[] ?]]; cbn in *; etransitivity; eauto.
  Qed.
  Next Obligation.
    cbn in *. rewrite <- H. auto.
  Qed.

  Lemma malloc_block n size ptr :
    size > 0 ->
    fst ptr < n ->
    malloc_perm n ⊥ block_perm size ptr.
  Proof.
    intros Hsize Hn.
    constructor; intros [[] ?] [[] ?] ?; cbn in *; subst; auto.
    intros. apply H; auto.
  Qed.

  Program Definition read_perm (ptr : addr) (v : Value) : @perm ({ x : Si * Ss | interp_spred spred x}) :=
    {|
    (** [ptr] points to [v] *)
    pre '(x, _) := read (lget x) ptr = Some v;
    (** only checks if the memory [ptr] points to in the 2 memories are equal *)
    rely '(x, _) '(y, _) := read (lget x) ptr = read (lget y) ptr;
    (** no updates allowed *)
    guar '(x, _) '(y, _) := x = y;
    |}.
  Next Obligation.
    constructor; [intros [[] ?] | intros [[] ?] [[] ?] [[] ?]]; cbn in *; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [[] ?] | intros [[] ?] [[] ?] [[] ?]]; cbn in *; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    cbn in *. rewrite <- H. auto.
  Qed.

  Program Definition write_perm (ptr : addr) (v : Value) : (@perm {x : Si * Ss | interp_spred spred x}) :=
    {|
    (** [ptr] points to [v] *)
    pre '(x, _) := Some v = read (lget x) ptr;
    (** only checks if the memory [ptr] points to in the 2 configs are equal *)
    rely '(x, _) '(y, _) := read (lget x) ptr = read (lget y) ptr;
    (** only the pointer we have write permission to may change *)
    guar '(x, _) '(y, _) := (forall ptr', ptr <> ptr' -> read (lget x) ptr' = read (lget y) ptr') /\
                            (forall ptr', sizeof (lget x) ptr' = sizeof (lget y) ptr') /\
                            length (lget x) = length (lget y);
    |}.
  Next Obligation.
    constructor; [intros [[] ?] | intros [[] ?] [[] ?] [[] ?]]; cbn in *; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [[] ?] | intros [[] ?] [[] ?] [[] ?] ? ?]; cbn in *; auto.
    split; [| split]; (etransitivity; [apply H; auto |]); apply H0; auto.
  Qed.
  Next Obligation.
    cbn in *. rewrite <- H. auto.
  Qed.

  Lemma read_lte_write : forall ptr v, read_perm ptr v <= write_perm ptr v.
  Proof.
    constructor; cbn in *; intros [[] ?]; cbn in *; subst; auto. intros [[] ?] ?. cbn in *. subst. auto.
  Qed.

  Lemma malloc_write : forall n ptr v,
      fst ptr < n ->
      malloc_perm n ⊥ write_perm ptr v.
  Proof.
    intros n ptr v. constructor; intros [[] ?] [[] ?]; simpl in *; intros.
    - destruct ptr. split; [| intros [] ?; split]; auto; apply H0;
                      intro Heq; inversion Heq; subst; lia.
    - apply H0; auto.
  Qed.

  Lemma write_block : forall b o o' size v,
      block_perm size (b, o) ⊥ write_perm (b, o') v.
  Proof.
    constructor; intros [[] ?] [[] ?] ?; simpl in *; subst; auto.
    apply H.
  Qed.

  Lemma write_write_sep ptr ptr' v v' :
      ptr <> ptr' ->
      write_perm ptr v ⊥ write_perm ptr' v'.
  Proof.
    intros Hdiff. constructor; intros [[] ?] [[] ?] ?; cbn in *; apply H; auto.
  Qed.

  Program Definition post_malloc_perm n size : (@perm {x : Si * Ss | interp_spred spred x}) :=
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
  Next Obligation.
    cbn in *. destruct H. destruct H0 as (? & ? & ?). split; [| split].
    - rewrite <- H. auto.
    - rewrite <- H2. auto.
    - rewrite <- H1. auto.
  Qed.

  (*
  (* same spred *)
  Lemma sep_step_malloc n size : sep_step _ _ _ (fun _ H => H)
                                          (malloc_perm n)
                                          (post_malloc_perm n size).
  Proof.
    apply sep_step_rg.
    - intros [si ss] [si' ss'] ?. induction H; try solve [etransitivity; eauto].
      destruct H.
      2: { destruct x as [[? ?] ?], y as [[? ?] ?].
           destruct H as (? & ? & ?). split; auto.
           apply H; intro Heq; inversion Heq; subst; cbn in *; lia.
      }
      induction H; try solve [etransitivity; eauto]. destruct H.
      + destruct x as [[? ?] ?], y as [[? ?] ?]. split; apply H; lia.
      + destruct x as [[? ?] ?], y as [[? ?] ?]. cbn in *. subst; auto.
    - intros [[si ss] ?] [[si' ss'] ?] [Hlen Hptr]. simpl in *.
      split; [split; [split |] |]; auto; intros; apply Hptr; cbn; lia.
  Qed.
   *)
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
  End asdf.


  Lemma foo spred spred' Hspred n :
    restrict (Si * Ss) (interp_spred spred) (interp_spred spred') Hspred (malloc_perm spred' n) ≡≡ malloc_perm spred n.
  Proof.
    split; intros.
    - constructor; intros.
      + destruct x. auto.
      + destruct x, y. destruct x, x0. cbn in *. auto.
      + destruct x, y. destruct x, x0. cbn in *. auto.
    - constructor; intros.
      + destruct x. auto.
      + destruct x, y. destruct x, x0. cbn in *. auto.
      + destruct x, y. destruct x, x0. cbn in *. auto.
  Qed.

  (** * Memory mermission sets *)
  Definition malloc_Perms : Perms2 :=
    meet_Perms2 (fun Q => exists (n : nat) spred,
                     Q = singleton_Perms2 (interp_spred spred) (malloc_perm spred n)).

  Definition read_Perms (ptr : addr) (P : Value -> Perms2) : Perms2 :=
    meet_Perms2 (fun Q => exists (y : Value) spred,
                     Q = sep_conj_Perms2
                           (singleton_Perms2 _ (read_perm spred ptr y))
                           (P y)).

  Definition write_Perms (ptr : addr) (P : Value -> Perms2) : Perms2 :=
    meet_Perms2 (fun Q => exists (y : Value) spred,
                     Q = sep_conj_Perms2
                           (singleton_Perms2 _ (write_perm spred ptr y))
                           (P y)).

  Definition block_Perms (ptr : addr) (n : nat) : Perms2 :=
    meet_Perms2 (fun Q => exists spred,
                     Q = singleton_Perms2 _ (block_perm spred n ptr)).

  (* Example no_error_load s : no_errors (lput s (mem_at (0, 0) (VNum 1))) *)
  (*                                     (load (VPtr (0, 0))). *)
  (* Proof. *)
  (*   pstep. unfold load. rewritebisim @bind_trigger. constructor. *)
  (*   left. pstep. rewrite lGetPut. constructor. *)
  (* Qed. *)
  (* Example no_error_store s : no_errors (lput s (mem_at (0, 0) (VNum 1))) *)
  (*                                      (store (VPtr (0, 0)) (VNum 2)). *)
  (* Proof. *)
  (*   pstep. unfold store. rewritebisim @bind_trigger. constructor. *)
  (*   left. pstep. rewrite lGetPut. constructor. *)
  (* Qed. *)

  (* diff spreds *)
  Lemma sep_step_malloc' n size spred1 spred2 Hspred :
    sep_step _ _ _ Hspred
             (malloc_perm spred1 n)
             (post_malloc_perm spred2 n size).
  Proof.
    apply sep_step_rg.
    - intros x y Hx Hy ?. remember (exist _ _ Hx). remember (exist _ _ Hy).
      revert x y Hx Hy Heqs Heqs0.
      induction H; intros; subst; auto.
      2: { destruct y, x. etransitivity; auto. }
      destruct H.
      2: { (* destruct x0 as [[? ?] ?], y0 as [[? ?] ?]. *)
        destruct x0, y0.
        destruct H as (? & ? & ?). split; auto.
        apply H; intro Heq; inversion Heq; subst; cbn in *; lia.
      }
      remember (exist _ _ Hx). remember (exist _ _ Hy).
      revert x0 y0 Hx Hy Heqs Heqs0.
      induction H; intros; subst; auto.
      2: { destruct y, x. etransitivity; auto. }
      destruct H.
      + destruct x0, y0.
        split; apply H; lia.
      + destruct x0, y0.
        cbn in *. subst; auto.
    - intros [] [] Hx Hy [Hlen Hptr]. simpl in *.
      split; [split; [split |] |]; auto; intros; apply Hptr; cbn; lia.
  Qed.

  Lemma typing_malloc l :
    @typing
      Si Ss Spred interp_spred _ _
      malloc_Perms
      (fun v _ => match v with
               | VPtr addr => sep_conj_Perms2
                               (sep_conj_Perms2
                                  malloc_Perms
                                  (block_Perms addr (S l)))
                               (write_Perms addr (fun _ => bottom_Perms2))
               | _ => top_Perms2
               end)
      (malloc (S l))
      (Ret tt).
  Proof.
    intros spred p si ss Hs Hp Hpre. (* cbn in *. Set Printing All. *)
    pstep. unfold malloc.
    destruct Hp as (? & (n & spred' & Hspred) & Hp); subst.
    destruct Hp as (? & Hp).
    (* read step *)
    rewritebisim @bind_trigger. econstructor; eauto; try reflexivity.
    cbn. reflexivity.
    (* write step *)
    rewritebisim @bind_trigger. unfold id. econstructor; eauto.
    { cbn. (* Unshelve. *)
      apply Hp in Hpre. apply Hp. simpl in *. rewrite lGetPut.
      intros ptr Hn. split.
      - unfold read, allocated. simpl. subst. rewrite nth_error_app_early; auto.
      - unfold sizeof. simpl. subst. rewrite nth_error_app_early; auto.
    }
    (* return *)
    { repeat intro. apply sep_step_malloc'. red in Hp.
      symmetry. eapply separate_antimonotone.
      - symmetry in H. apply H.
      - rewrite foo in Hp. apply Hp.
    }
    { econstructor; eauto.
      - cbn. repeat rewrite lGetPut. apply Hp in Hpre. simpl in Hpre.
        split; [| split].
        + rewrite last_length. lia.
        + unfold sizeof. simpl.
          rewrite nth_error_app_last; auto.
        + unfold read, allocated. simpl. rewrite nth_error_app_last; auto.
      - simpl. apply Hp in Hpre. cbn in Hpre. rewrite Hpre.
        eexists. exists (write_perm spred (n, 0) (VNum 0)).
        split; [| split].
        + do 2 eexists. split; [| split]; try reflexivity.
          * eexists. split.
            -- exists (n + 1). eexists. reflexivity.
            -- cbn. eexists. red. reflexivity.
          * eexists. split.
            -- eexists. reflexivity.
            -- cbn. eexists. red. reflexivity.
        + eexists. split.
          * exists (VNum 0). eexists. reflexivity.
          * do 2 eexists. split; [| split]; cbn; auto.
            -- cbn. eexists. red. reflexivity.
            -- rewrite sep_conj_perm_bottom. rewrite restrict_same. reflexivity.
        + do 2 rewrite restrict_same. constructor; auto.
          { intros [[] ?] (? & ? & ?). cbn in *. split; split; auto.
            - split; [| apply malloc_block; simpl; lia].
              apply H0.
            - symmetry. apply separate_sep_conj_perm; symmetry.
              + apply malloc_write. simpl. lia.
              + apply write_block.
              + apply malloc_block; simpl; lia.
          }
    }
    Unshelve. all: try apply Hinv; auto.
  Qed.

  (*
  Lemma typing_free ptr (Q : Value -> Perms2) :
    @typing
      Si Ss Spred interp_spred _ _
      (sep_conj_Perms2 (write_Perms ptr Q) (block_Perms ptr 1))
      (fun _ _ => bottom_Perms2)
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

  (* Lemma typing_load {R} ptr (Q : Value -> Perms) (r : R) : *)
  (*   typing *)
  (*     (read_Perms ptr Q) *)
  (*     (fun x _ => (read_Perms ptr (eq_p x)) * Q x) *)
  (*     (load (VPtr ptr)) *)
  (*     (Ret r). *)
  (* Proof. *)
  (*   repeat intro. pstep. unfold load. rewritebisim @bind_trigger. *)
  (*   econstructor; eauto; try reflexivity. *)
  (*   destruct H as (? & (? & ?) & ?); subst. *)
  (*   destruct H1 as (? & ? & ? & ? & ?). simpl in *. *)
  (*   assert (read (lget c1) ptr = Some x0). *)
  (*   { apply H2 in H0. destruct H0 as (? & _). apply H in H0. auto. } *)
  (*   rewrite H3. constructor; eauto. *)
  (*   simpl. exists x, x1. split; [| split]; eauto. eexists. split; eauto. *)
  (*   simpl. exists x, bottom_perm. split; [| split]; eauto. *)
  (*   rewrite sep_conj_perm_bottom. reflexivity. *)
  (* Qed. *)

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
*)

  (* Lemma typing_store' {R} ptr val' (P : Value -> Perms) (r : R): *)
  (*   typing *)
  (*     (write_Perms ptr P) *)
  (*     (fun _ _ => write_Perms ptr (eq_p val')) *)
  (*     (store (VPtr ptr) val') *)
  (*     (Ret r). *)
  (* Proof. *)
  (*   assert (bottom_Perms ≡ @eq_p Si Ss _ val' val'). *)
  (*   { split; repeat intro; simpl; auto. } *)
  (*   rewrite <- sep_conj_Perms_bottom_identity. rewrite sep_conj_Perms_commut. *)
  (*   rewrite H. apply typing_store. *)
  (* Qed. *)

  Definition offset (v : Value) (o : nat) : Value :=
    match v with
    | VNum n => VNum (n + o)
    | VPtr (blk, n) => VPtr (blk, n + o)
    end.

  Variant RW: Type := R | W.

  Definition ptr_Perms {A} (rw : RW) (p : Value) (a : A) T : @Perms2 (Si * Ss) :=
    match p with
    | VNum _ => top_Perms2
    | VPtr p =>
        meet_Perms2 (fun P => exists v spred,
                         P = (singleton_Perms2 _ (match rw with
                                                  | R => read_perm spred p v
                                                  | W => write_perm spred p v
                                                  end)) *2
                               (v :: T ▷ a))
    end.

  Definition ptr {A} '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => ptr_Perms rw (offset x o) a T;
    |}.

  Fixpoint arr_perm {A} rw o l T : VPermType (Vector.t A l) :=
    match l with
    | 0 => trueP
    | S l' =>
        {| ptApp := fun xi xss =>
                      xi :: ptr (rw, o, T) ▷ Vector.hd xss *2
                      xi :: arr_perm rw (S o) l' T ▷ Vector.tl xss
        |}
    end.
  Notation "'arr' ( rw , o , l , T )":=(arr_perm rw o l T).

  Definition blockPT l : VPermType unit :=
    {| ptApp := fun a _ => match a with
                        | VPtr ptr =>
                            meet_Perms2 (fun Q => exists spred,
                                             Q = singleton_Perms2 _ (block_perm spred l ptr))
                        | _ => top_Perms2
                        end |}.

  Lemma reach_perm_proper {A} r (T : VPermType A) rw o :
    Proper (lte_PermType ==> lte_PermType)
           (fun U : VPermType (list A) => PermType.or (eqp r) (T ⋆ (ptr (rw, o, U)))).
  Proof.
    intros T1 T2 Hlte v l spred p Hp. simpl.
    destruct l as [| ?]; simpl in *; auto.
    destruct Hp as (pt & pptr & Hpt & Hpptr & Hlte').
    exists pt, pptr. split; [| split]; auto.
    clear Hpt. unfold ptr_Perms in *.
    destruct (offset v o) as [? | l]; auto.
    destruct Hpptr as (? & (v' & spred' & ?) & Hpptr); subst.
    destruct Hpptr as (? & ? & ? & ? & ?).
    eexists. split; eauto. do 2 eexists. split; [| split]; eauto. apply Hlte. auto.
  Qed.

  Program Definition reach_perm {A}
          (r : Value) (rw : RW) (o : nat)
          (T : VPermType A)
    : VPermType (list A) :=
    @mu _ _ _ (mu_list A) _ (fixed_point_list _)
        (fun U => PermType.or (eqp r) (T ⋆ (ptr (rw, o, U))))
        (reach_perm_proper _ _ _ _).

  Program Definition list_perm rw A (T : VPermType A) : VPermType (list A) :=
    @mu _ _ _ (mu_list A) _ (fixed_point_list _) (fun U => PermType.or (eqp (VNum 0)) (ptr (rw, 0, T) ⋆ ptr (rw, 1, U))) _.
  Next Obligation.
    repeat intro. cbn. induction b; cbn in *; auto.
    destruct H0 as (? & ? & ? & ? & ?). exists x0, x1. split; auto. split; auto.
    clear H0. unfold ptr_Perms in *. destruct (offset a 1); auto.
    destruct H1. destruct H0. destruct H0 as (? & ? & ?); subst.
    destruct H1 as (? & ? & ? & ? & ?).
    eexists. split; eauto. do 2 eexists. split; eauto. split; eauto. apply H. auto.
  Qed.

  Definition list_reach_perm {A} r rw (T : VPermType A) : VPermType (list A) :=
    reach_perm r rw 1 (ptr (rw, 0, T)).

  Lemma reach_refl {A} x rw o (T : VPermType A) :
    x :: trueP ▷ tt ⊨2 x :: reach_perm x rw o T ▷ nil.
  Proof.
    repeat intro. apply mu_fixed_point. reflexivity.
  Qed.

  Lemma reach_trans {A} x y z rw o (T : VPermType A) xs ys :
    x :: reach_perm y rw o T ▷ xs *2 y :: reach_perm z rw o T ▷ ys ⊨2
    x :: reach_perm z rw o T ▷ (xs ++ ys).
  Proof.
    revert x.
    induction xs.
    - intros x spred p (p1 & p2 & Hp1 & Hp2 & Hlte).
      destruct Hp1 as (? & (U & HU & ?) & Hp1); subst.
      apply HU in Hp1. simpl in Hp1. subst. eapply Perms2_upwards_closed; eauto.
      red. rewrite restrict_same.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
    - intros x spred p (px' & py & Hpx' & Hpy & Hlte).
      eapply mu_fixed_point in Hpx'.
      destruct Hpx' as (pa & px & Hpa & Hpx & Hlte').
      (* x must be a pointer *)
      destruct x; try contradiction. destruct a0 as [b o'].
      destruct Hpx as (? & (v & spred' & ?) & Hpx); subst.
      destruct Hpx as (px'' & pv & Hpx'' & Hpv & Hlte'').

      apply mu_fixed_point. cbn.
      exists pa. exists (px'' ** (pv ** py)). split; [apply Hpa | split].
      2: { repeat rewrite <- sep_conj_perm_assoc.
           etransitivity; eauto.
           eapply sep_conj_perm_monotone; intuition.
           repeat rewrite sep_conj_perm_assoc.
           etransitivity; eauto.
           eapply sep_conj_perm_monotone; intuition.
      }
      eexists; split; [do 2 eexists; reflexivity |].
      apply sep_conj_Perms2_perm; [apply Hpx'' |].
      simpl. exists (v :: reach_perm z rw o T ▷ (xs ++ ys)). split.
      2: { apply IHxs. apply sep_conj_Perms2_perm; auto. }
      eexists; split; eauto.
      repeat intro. eapply mu_fixed_point in H; auto.
      Unshelve. all: auto; apply reach_perm_proper.
  Qed.

  Definition lte_Perms' (P Q : Perms2) : Prop :=
    forall (spred : Spred) (p : @perm {x | interp_spred spred x}), p ∈2 Q -> p ∈2 P.
  Definition entails P Q := lte_Perms' Q P.

  Lemma PtrI A xi yi xs ys rw o (T : VPermType A) :
    xi :: ptr (rw, o, eqp yi) ▷ xs *2 yi :: T ▷ ys ⊨2 xi :: ptr (rw, o, T) ▷ ys.
  Proof.
    destruct xi; simpl.
    - rewrite sep_conj_Perms2_top_absorb. reflexivity.
    - repeat intro. destruct a. rename p into p'.
      destruct H as (p & t & (P & (v & spred' & ?) & Hp) & Hp' & Hlte). subst.
      destruct Hp as (? & ? & ? & ? & ?). cbn in *. subst.
      destruct H as (Hspred & Hhlte).
      eexists. split; [exists v, spred'; reflexivity |].
      eapply Perms2_upwards_closed.
      2: { red. rewrite restrict_same. apply Hlte. }
      do 2 eexists. split; [| split]; cbn; eauto.
      apply sep_conj_perm_monotone; intuition.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
      Unshelve. auto.
  Qed.

  (* TODO PtrE *)

  Lemma ReadDup' o xi yi :
    entails (xi :: ptr (R, o, eqp yi) ▷ tt)
            (xi :: ptr (R, o, eqp yi) ▷ tt *2 xi :: ptr (R, o, eqp yi) ▷ tt).
  Proof.
    repeat intro. cbn in *. destruct xi; [contradiction |].
    destruct a as [b o']. unfold offset in *.
    destruct H as (? & (v & spred' & ?) & ?). subst.
    destruct H0 as (pread & peq & Hpread & Hpeq & Hlte).
    destruct Hpread as (Hspred & Hhlte).
    exists (read_perm spred (b, o' + o) v), (read_perm spred (b, o' + o) v).
    cbn in Hpeq. subst.
    assert (read_perm spred (b, o' + o) v ∈2 ptr_Perms R (VPtr (b, o' + o)) tt (eqp v)).
    {
      eexists. split; eauto. simpl in *. exists (read_perm spred (b, o' + o) v), bottom_perm.
      split; [| split]. 2: reflexivity.
      - exists Hspred. red. constructor.
        + intros []; auto.
        + intros [[]] [[]] ?; cbn in *; auto.
        + intros [[]] [[]] ?; cbn in *; auto.
      - rewrite sep_conj_perm_bottom. reflexivity.
    }
    split; [| split]; auto. clear H.
    constructor; intros.
    - destruct x, x. split; [| split]; auto.
      1: { apply Hlte in H; auto. cbn in H. destruct H. apply Hhlte in H.
           apply H.
      }
      1: { apply Hlte in H; auto. cbn in H. destruct H. apply Hhlte in H.
           apply H.
      }
      split; intros [[]] [[]] ?; cbn in *; subst; auto.
    - destruct x, y, x, x0. split.
      1: { apply Hlte in H; auto. cbn in H. destruct H. apply Hhlte in H.
           apply H.
      }
      1: { apply Hlte in H; auto. cbn in H. destruct H. apply Hhlte in H.
           apply H.
      }
    - destruct x, y, x, x0. apply Hlte. constructor. left. apply Hhlte. cbn.
      remember (exist _ _ i). remember (exist _ _ i0).
      revert s s0 i s1 s2 i0 Heqs3 Heqs4.
      induction H; intros; subst; auto.
      + destruct H; auto.
      + destruct y, x. etransitivity; [eapply IHclos_trans1 | eapply IHclos_trans2]; eauto.
  Qed.

End MemoryPerms.

Notation "'arr' ( rw , o , l , T )" := (arr_perm rw o l T) (at level 40).
