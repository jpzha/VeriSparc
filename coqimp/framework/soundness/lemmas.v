Require Import Coqlib.     
Require Import Maps. 

Require Import Integers.
Open Scope Z_scope. 
Import ListNotations.

Set Asymmetric Patterns.

Require Import state.  
Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.
   
Require Import logic. 
Require Import soundness.
Require Import LibTactics.

Require Import Coq.Logic.FunctionalExtensionality.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Auxiliary Definition +*)
Fixpoint indoms {tp : Type} (ls : list tp) M :=
  match ls with
  | nil => True
  | l :: ls' => indom l M /\ indoms ls' M
  end.

Fixpoint getRs (vl : list (RegName * Word)) :=
  match vl with
  | nil => nil
  | (rn, w) :: vl' => rn :: getRs vl'
  end.

Definition Fmr :=
  r8 :: r9 :: r10 :: r11 :: r12 :: r13 :: r14 :: r15 ::
    r16 :: r17 :: r18 :: r19 :: r20 :: r21 :: r22 :: r23 ::
    r24 :: r25 :: r26 :: r27 :: r28 :: r29 :: r30 :: r31 :: nil.

(*+ Some Tactic +*)
(*********)
(** paste from inv_prop, in order to proof node_OS_TCB_dup_false **)
Ltac simpl_map1 :=
  match goal with
    | H:exists _, _ |- _ => destruct H; simpl_map1
    | H:_ /\ _ |- _ => destruct H; simpl_map1
    | H:(_, _) = (_, _) |- _ => inversion H; clear H; simpl_map1
    | H:?x = ?x |- _ => clear H; simpl_map1
    | |- ?x = ?x => reflexivity
    | H:True |- _ => clear H; simpl_map1
    | |- True => auto
    | _ => try (progress subst; simpl_map1)
  end.

Ltac simpljoin1 := repeat progress simpl_map1.

Ltac destruct_state s :=
  destruct s as [ [ ?m [?r ?f] ] ?d ].

Ltac destruct_addreq :=
  match goal with
  | |- context [AddrEq.eq ?x ?l] =>
    let Heqe := fresh in
    destruct (AddrEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac destruct_rneq :=
  match goal with
  | |- context [RegNameEq.eq ?x ?l] =>
    let Heqe := fresh in
    destruct (RegNameEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac destruct_addreq_H :=
  match goal with
  | H : context [AddrEq.eq ?x ?l] |- _ =>
    let Heqe := fresh in
    destruct (AddrEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac destruct_rneq_H :=
  match goal with
  | H : context [RegNameEq.eq ?x ?l] |- _ =>
    let Heqe := fresh in
    destruct (RegNameEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac get_ins_diff_false :=
  match goal with
  | H1 : ?C ?pc = _, H2 : ?C ?pc = _ |- _ =>
    rewrite H1 in H2; inversion H2;
    tryfalse; subst
  end.

Ltac elim_ins_neq :=
  match goal with
  | H : LookupC _ _ _ _ |- _ =>
    inversion H; subst; get_ins_diff_false
  | _ => idtac
  end.

Ltac reg_val_eval :=
  match goal with
  | |- context[RegMap.set _ _ _ _] =>
    unfold RegMap.set; destruct_rneq; eauto;
    reg_val_eval
  | _ => idtac
  end.

(*+ Some tivial lemmas +*)

Lemma Sn_plus_eq_n_false :
  forall n m,
    S (n + m) = n -> False.
Proof.
  intro n.
  induction n; intros.
  -
    simpls.
    tryfalse.
  -
    simpl in H.
    inversion H.
    eauto.
Qed.

Lemma ls_leneq_cons_neq :
  forall A (l1 l2 l: list A),
    length l1 = length l2 -> l1 = l ++ l2 -> length l <> 0 -> False.
Proof.
  intros A l1.
  induction l1; intros.
  -
    destruct l2.
    destruct l.
    simpl in H1.
    tryfalse.
    simpl in H0.
    tryfalse.
    simpl in H.
    tryfalse.
  -
    destruct l2.
    simpl in H.
    tryfalse.
    simpl in H.
    inversion H.
    eapply IHl1; eauto.
    destruct l.
    simpl in H1.
    tryfalse.
    simpl in H0.
    inversion H0.
    subst.
    rewrite app_length in H.
    simpl in H.
    inversion H.
    clear - H4.
    rewrite <- plus_n_Sm in H4.
    rewrite <- Nat.add_comm in H4.
    eapply Sn_plus_eq_n_false in H4; eauto.
    tryfalse.
Qed.

Lemma ls_leneq_cons :
  forall A (l1 l1' l2 l2' : list A),
    l1 ++ l2 = l1' ++ l2' -> length l2 = length l2' ->
    l1 = l1' /\ l2 = l2'.
Proof.
  intros A l1.
  induction l1; intros.
  -
    destruct l1'.
    {
      simpl in H.
      eauto.
    }
    {
      simpl in H.
      eapply ls_leneq_cons_neq in H0; eauto.
      tryfalse.
      instantiate (1 := a :: l1').
      simpl; eauto.
      intro.
      simpl; tryfalse.
    }
  -
    destruct l1'.
    {
      simpl in H.
      symmetry in H, H0.
      eapply ls_leneq_cons_neq in H0; eauto.
      tryfalse.
      instantiate (1 := a :: l1).
      simpl; eauto.
      intro.
      simpls; tryfalse.
    }
    {
      simpl in H.
      inversion H; eauto.
      subst.
      eapply IHl1 in H3; eauto.
      destruct H3.
      split; eauto.
      subst; eauto.
    }
Qed.

Lemma indom_nor_not :
  forall (tp : Type) (l : tp) m,
    {indom l m} + {~ indom l m}.
Proof.
  intros.
  unfold indom.
  destruct (m l); eauto.
  right.
  intro.
  simpljoin1.
  tryfalse.
Qed.

Lemma in_remove_one_ls_in_ls :
  forall ls x y,
    In x (remove_one sep_reg_dec y ls) ->
    In x ls.
Proof.
  intro ls.
  induction ls; intros.
  -
    simpls.
    tryfalse.

  -
    simpls.
    destruct (sep_reg_dec y a); subst; eauto.
    simpl in H.
    destruct H; eauto.
Qed.

Axiom classic :
  forall P,
    P \/ (~ P).

(*+ Lemmas for Integers +*)
Lemma z_eq_to_int_eq :
  forall z1 z2,
    z1 = z2 -> $ z1 = $ z2.
Proof.
  intros.
  subst; eauto.
Qed.

Lemma int_eq_true_eq :
  forall x y,
    Int.eq x y = true -> x = y.
Proof.
  intros.
  unfolds Int.eq.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)) eqn:Heqe; tryfalse.
  clear Heqe.
  eapply z_eq_to_int_eq in e.
  do 2 rewrite Int.repr_unsigned in e.
  eauto.
Qed.

Lemma int_eq_false_neq :
  forall x y,
    Int.eq x y = false -> x <> y.
Proof.
  intros.
  unfolds Int.eq.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)) eqn:Heqe; tryfalse.
  clear Heqe.
  intro.
  subst; eauto.
Qed.

(*+ Lemmas for Memory +*)
Lemma indom_merge_still :
  forall (tp : Type) (l : tp) M m,
    indom l M ->
    indom l (merge M m).
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  unfold merge in *.
  destruct (M l) eqn:Heqe; eauto.
  tryfalse.
Qed.

Lemma indom_merge_still2 :
  forall (tp : Type) (l : tp) M m,
    indom l m ->
    indom l (merge M m).
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  unfold merge in *.
  destruct (M l) eqn:Heqe; eauto.
Qed.

Lemma indom_m2_disj_notin_m1 :
  forall (tp : Type) (l : tp) m1 m2,
    indom l m2 -> disjoint m1 m2 ->
    ~ indom l m1.
Proof.
  intros.
  intro.
  unfold disjoint in *.
  specialize (H0 l).
  unfold indom in *.
  simpljoin1.
  rewrite H1 in H0.
  rewrite H in H0; eauto.
Qed.
  
Lemma indom_m1_disj_notin_m2 :
  forall (tp : Type) (l : tp) m1 m2,
    indom l m1 -> disjoint m1 m2 ->
    ~ indom l m2.
Proof.
  intros.
  intro.
  unfold disjoint in *.
  specialize (H0 l).
  unfold indom in *.
  simpljoin1.
  rewrite H in H0.
  rewrite H1 in H0; tryfalse.
Qed.

Lemma disj_merge_reverse_eq :
  forall (tp : Type) (m1 m2 : tp -> option Word),
    disjoint m1 m2 ->
    merge m1 m2 = merge m2 m1.
Proof.
  intros.
  eapply functional_extensionality.
  intros.
  unfold merge in *.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; simpl; eauto; tryfalse.
  unfold disjoint in *.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma disj_sym :
  forall (tp : Type) (m1 m2 : tp -> option Word),
    disjoint m1 m2 -> disjoint m2 m1.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
Qed.

Lemma indom_isindom :
  forall (tp : Type) (l : tp) m,
    indom l m -> is_indom l m = true.
Proof.
  intros.
  unfolds.
  unfold indom in H.
  simpljoin1.
  rewrite H.
  eauto.
Qed.

Lemma disj_sep_merge_still :
  forall tp (m m1 m2 : tp -> option Word),
    disjoint m m1 -> disjoint m m2 ->
    disjoint m (merge m1 m2).
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  specialize (H0 x).
  destruct (m x) eqn:Heqe; eauto.
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
Qed.

Lemma disj_merge_disj_sep1 :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m2.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x); eauto.
  unfold merge in *.
  destruct (m2 x); eauto.
  unfold merge in *.
  destruct (m2 x); eauto.
Qed.

Lemma disj_merge_disj_sep2 :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m3.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x).
  unfold merge in *.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  unfold merge in *.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  destruct (m3 x); eauto.
Qed.

Lemma merge_assoc :
  forall tp (m1 m2 m3 : tp -> option Word),
    merge m1 (merge m2 m3) = merge (merge m1 m2) m3.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2;
    simpl; tryfalse; eauto.
Qed.

Lemma merge_lift :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 m2 ->
    merge m1 (merge m2 m3) = merge m2 (merge m1 m3).
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
  unfold disjoint in *.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma get_vl_merge_still :
  forall tp (M m : tp -> option Word) l v,
    M l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfold merge in *.
  rewrite H; eauto.
Qed.

Lemma get_vl_merge_still2 :
  forall tp (M m : tp -> option Word) l v,
    disjoint M m -> m l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfold merge in *.
  destruct (M l) eqn:Heqe; tryfalse.
  unfold disjoint in *.
  specialize (H l).
  rewrite Heqe in H.
  rewrite H0 in H.
  tryfalse.
  eauto.
Qed.

(*+ Lemmas about register state +*)
Definition dom_eq {tp : Type} (M m : tp -> option Word) :=
  (forall l, indom l M -> indom l m) /\ (forall l, indom l m -> indom l M).

Lemma get_R_rn_neq_r0 :
  forall R rn,
    rn <> Rr r0 ->
    get_R R rn = R rn.
Proof.
  intros.
  unfold get_R.
  destruct (R rn); eauto.
  destruct rn; eauto.
  destruct g; eauto.
  tryfalse.
Qed.

Lemma regset_twice :
  forall (A : Type) l (v v1 : A) m,
    RegMap.set l (Some v) (RegMap.set l (Some v1) m) =
    RegMap.set l (Some v) m.
Proof.
  intros.
  eapply functional_extensionality.
  intro.
  unfolds RegMap.set.
  destruct_rneq.
Qed.

(*+ Lemmas about Sep Star +*)
Lemma sep_star_split :
  forall s p1 p2,
    s |= p1 ** p2 ->
    exists s1 s2, s1 |= p1 /\ s2 |= p2 /\ state_union s1 s2 s /\ regdisj p1 p2.
Proof.
  intros.
  simpl in H.
  simpljoin1; eauto 10.
Qed.

Ltac sep_star_split_tac :=
  match goal with
  | H : _ |= ?p1 ** ?p2 |- _ =>
    let x := fresh in
    let x1 := fresh in
    eapply sep_star_split in H;
    destruct H as [ x [x1 H] ]; simpljoin1;
    destruct_state x; destruct_state x1;
    sep_star_split_tac
  | _ => idtac
  end.

(*+ Lemmas for delay list +*)
Lemma not_in_exe_dly_stable :
  forall D R R' D' s,
    exe_delay R D = (R', D') ->
    ~ In s (getRegs D) ->
    ~ In s (getRegs D').
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H.
    inversion H; subst.
    intro.
    simpls.
    tryfalse.
  -
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe1; eauto.
      inversion H; subst.
      eapply IHD in Heqe1; eauto.
      intro.
      eapply H0.
      simpl.
      eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe1; eauto.
      inversion H; subst.
      eapply IHD with (s := s) in Heqe1; eauto.
      intro.
      simpl in H1.
      destruct H1; subst.
      eapply H0.
      simpl; eauto.
      eapply Heqe1; eauto.
      intro.
      eapply H0.
      simpl; eauto.
    }
Qed.

Lemma dlyitem_in_dlyls_reg_in :
  forall D t s w,
    In (t, s, w) D ->
    In s (getRegs D).
Proof.
  intro D.
  induction D; intros.
  -
    simpls; eauto.
  -
    destruct a, p.
    simpl in H.
    destruct H.
    inversion H; subst.
    simpl; eauto.
    simpl.
    right.
    eauto.
Qed.

Lemma dlytime_gt_zero_exe_still :
  forall D t s w D' R R',
    In (S t, s, w) D -> (R', D') = exe_delay R D ->
    In (t, s, w) D'.
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H0.
    inversion H0; subst.
    simpl in H.
    tryfalse.
  -
    destruct a, p.
    simpl in H.
    destruct H.
    {
      inversion H; subst.
      simpl in H0. 
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      simpl; eauto.
    }
    {
      simpl in H0.
      destruct n.
      {
        destruct (exe_delay R D) eqn:Heqe; eauto.
        inversion H0; subst.
        symmetry in Heqe.
        eapply IHD in Heqe; eauto.
      }
      {
        destruct (exe_delay R D) eqn:Heqe; eauto.
        inversion H0; subst.
        symmetry in Heqe.
        eapply IHD in Heqe; eauto.
        simpl; eauto.
      }
    }
Qed.
    
Lemma noDup_exe_dly_stable :
  forall D R R' D' rsp,
    noDup rsp (getRegs D) ->
    exe_delay R D = (R', D') ->
    noDup rsp (getRegs D').
Proof.
  intros.
  unfolds noDup.
  generalize dependent R.
  generalize dependent R'.
  generalize dependent D'.
  generalize dependent rsp.

  induction D; intros.
  -
    simpl in H0.
    inversion H0; subst.
    simpl.
    intro; tryfalse.

  -
    destruct a, p.
    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Hexe_delay.
      inversion H0; subst.
      simpl in H.
      destruct (sep_reg_dec rsp s); subst; eauto.
      {
        eapply IHD; eauto.
        clear - H.
        intro.
        eapply H.
        eapply in_remove_one_ls_in_ls; eauto.
      }
      {
        assert (~ In rsp (remove_one sep_reg_dec rsp (getRegs D))).
        {
          intro.
          eapply H.
          simpl.
          eauto.
        }

        eapply IHD in H1; eauto.
      }
    }
    {
      destruct (exe_delay R D) eqn:Hexe_delay.
      inversion H0; subst.
      simpls.
      destruct (sep_reg_dec rsp s); subst.
      {
        eapply not_in_exe_dly_stable; eauto.
      }
      {
        assert (~ In rsp (remove_one sep_reg_dec rsp (getRegs D))).
        {
          intro.
          eapply H.
          simpl; eauto.
        }

        eapply IHD in H1; eauto.
        intro.
        eapply H1.
        simpl in H2.
        destruct H2; subst; tryfalse; eauto.
      }
    }
Qed.

Lemma regdlySt_dly_nil_false :
  forall n s w M R F,
    regdlySt n s w (M, (R, F), []) -> False.
Proof.
  intro n.
  induction n; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpls; tryfalse.
  -
    simpl in H.
    destruct H.
    unfolds inDlyBuff.
    simpljoin1.
    simpls.
    tryfalse.
    eauto.
Qed.

Lemma regdlySt_dlyls_relevent :
  forall t D s w M M' R R' F F',
    regdlySt t s w (M, (R, F), D) ->
    regdlySt t s w (M', (R', F'), D).
Proof.
  intro t.
  induction t; intros.
  -
    unfolds regdlySt.
    simpls.
    eauto.
  -
    simpls.
    destruct H; eauto.
Qed.

Lemma exe_delay_dlyls_deterministic :
  forall D D' R R' R1,
    (R', D') = exe_delay R D ->
    exists R1', (R1', D') = exe_delay R1 D.
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H; subst.
    eauto.
  -
    destruct a.
    destruct p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      simpl.
      symmetry in Heqe.
      eapply IHD with (R1 := R1) in Heqe; eauto.
      simpljoin1.
      rewrite <- H0.
      eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      symmetry in Heqe.
      eapply IHD with (R1 := R1) in Heqe; eauto.
      simpljoin1.
      simpl.
      rewrite <- H0.
      eauto.
    }
Qed.
    
Lemma dly_reduce_Aemp_stable :
  forall D M R R' F D',
    (M, (R, F), D) |= Aemp -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= Aemp.
Proof.
  intros D.
  induction D; intros.
  -
    simpls.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= Aemp).
    {
      clear - H.
      simpls; eauto.
    }

    simpl in H0.
    destruct d.
    { 
      destruct (exe_delay R D) eqn:Heqe; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
    }
Qed.

Lemma dly_reduce_Amapsto_stable :
  forall D M R R' F D' a w,
    (M, (R, F), D) |= a |-> w -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= a |-> w.
Proof.
  intros D.
  induction D; intros.
  -
    simpls.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= a0 |-> w).
    {
      clear - H.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_Aaexp_stable :
  forall D M R R' F D' a a0,
    (M, (R, F), D) |= a ==ₓ a0 -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= a ==ₓ a0.
Proof. 
  intros D.
  induction D; intros.
  -
    simpls.
    simpljoin1.
    eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= a0 ==ₓ a1).
    {
      clear - H.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.    
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      clear - H1.
      simpls. 
      simpljoin1.
      unfolds eval_addrexp.
      destruct a0; eauto.
      split; eauto.
  
      unfolds eval_opexp.
      destruct o; eauto.
      rewrite <- H.
      unfold RegMap.set.
      simpl.
      destruct g; eauto;
        try solve [destruct_rneq; eauto].
      split; eauto.

      unfolds eval_opexp.
      destruct o; eauto.
      rewrite <- H.
      unfold RegMap.set.
      simpl.
      destruct g; destruct g0;
        try solve [destruct_rneq; destruct_rneq; eauto].
      destruct (($ (-4096)) <=ᵢ w0 && w0 <=ᵢ ($ 4095)); eauto.

      unfolds get_R.
      unfold RegMap.set.
      destruct g; eauto;
        try solve [destruct_rneq; eauto].
    }
    {
      destruct (exe_delay R D) eqn:Heqe; subst.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_Aoexp_stable :
  forall D M R R' F D' o w,
    (M, (R, F), D) |= o ==ₑ w -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= o ==ₑ w.
Proof.
  intros D.
  induction D; intros.
  -
    simpl in H0.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= o ==ₑ w).
    {
      clear - H.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      clear - H1.
      simpls. 
      unfolds eval_opexp.
      destruct o; eauto.
      unfolds RegMap.set.
      unfolds get_R.
      destruct_rneq; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_reg_stable :
  forall D M R R' F D' r w,
    (M, (R, F), D) |= r |=> w -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= r |=> w.
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= r |=> w).
    {
      clear - H.
      simpls.
      unfolds regSt.
      simpljoin1; eauto.
      simpls.
      repeat (split; eauto).
      intro.
      eapply H1.
      unfolds regInDlyBuff.
      destruct r; eauto; tryfalse.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst. 
      eapply IHD with (R' := r0) (D' := d) in H1; eauto.
      clear - H1 H.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      unfold RegMap.set.
      destruct_rneq.
      subst.
      false.
      eapply H4.
      unfold regInDlyBuff.
      simpl; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      eapply IHD with (R' := r0) (D' := d0) in H1; eauto.
      clear - H H1.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1; eauto.
      repeat (split; eauto).
      intro. 
      eapply H2.
      clear - H H4.
      unfolds regInDlyBuff.
      destruct r; eauto; tryfalse.
      simpls; eauto.
      destruct H; eauto.
      subst.
      false.
      eapply H4; eauto.
    }
Qed.
    
Lemma dlytime_zero_exe_dly :
  forall D M R R' F D' s w,
    (M, (R, F), D) |= 0 @ s |==> w ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= s |=> w.
Proof. 
  intro D.
  induction D; intros.
  -
    simpl in H.
    simpljoin1.
    destruct H1.
    {
      unfolds inDlyBuff.
      simpljoin1.
      simpl in H.
      tryfalse.
    }
    {
      simpl in H0. 
      inversion H0; subst.
      unfolds regSt.
      simpls.
      simpljoin1.
      unfold regSt.
      simpl; eauto.
    }
  - 
    destruct a, p.
    simpl in H0. 
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.

      lets Ht : H.
      simpl in Ht.
      simpljoin1.
      destruct H2.
      {
        unfolds inDlyBuff.
        simpljoin1.
        simpl in H0.
        destruct H0.
        { 
          inversion H0; subst.
          simpl in H1.
          unfold noDup in H1.
          simpl in H1.
          destruct (sep_reg_dec s s); tryfalse; eauto.
          clear e.
          simpl.
          unfold regSt.
          simpls.
          repeat (split; eauto).
          unfold RegMap.set.
          destruct_rneq.
          eapply not_in_exe_dly_stable; eauto.
        }
        {
          simpl in H1.
          unfold noDup in H1.
          simpl in H1.
          assert (s <> s0).
          { 
            intro.
            subst.
            eapply H1.
            destruct (sep_reg_dec s0 s0); simpl; eauto.
            eapply dlyitem_in_dlyls_reg_in; eauto.
          }

          assert ((empM, (R, F), D) |= 0 @ s |==> w).
          {
            clear - H H2.
            simpls. 
            simpljoin1.
            destruct H0.
            unfold inDlyBuff in H.
            simpljoin1.
            simpls.
            repeat (split; eauto).
            left.
            destruct H.
            inversion H; subst; tryfalse.
            unfold inDlyBuff.
            simpl; split; eauto.
            unfolds noDup.
            simpls.
            destruct (sep_reg_dec s s0); tryfalse.
            intro.
            eapply H0.
            simpl; eauto.
            repeat (split; eauto).
            right.
            unfolds regSt.
            simpls.
            simpljoin1.
            repeat (split; eauto).
          }

          eapply IHD with (R' := r) (D' := d) in H3; eauto.
          clear - H2 H3.
          simpls.
          unfolds regSt.
          simpls.
          simpljoin1.
          repeat (split; eauto).
          unfold RegMap.set at 1.
          destruct_rneq.
        }
      }
      {
        assert ((empM, (R, F), D) |= 0 @ s |==> w).
        {  
          clear - H0.
          simpl.
          repeat (split; eauto).
          right.
          unfolds regSt.
          simpls.
          simpljoin1.
          repeat (split; eauto).
        }

        eapply IHD with (R' := r) (D' := d) in H1; eauto.

        assert (s <> s0).
        {
          clear - H0.
          unfolds regSt.
          simpls.
          simpljoin1.
          intro.
          eapply H1; eauto.
        }

        clear - H1 H2.
        simpls.
        unfolds regSt.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        unfold RegMap.set.
        destruct_rneq.
      }
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.

      assert ((M, (R, F), D) |= 0 @ s |==> w).
      {
        clear - H.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        destruct H0.
        { 
          unfolds inDlyBuff.
          simpljoin1.
          simpl in H.
          destruct H.
          inversion H.
          simpls.
          unfolds noDup.
          left.
          split; eauto.
          intro.
          eapply H0.
          simpl.
          destruct (sep_reg_dec s s0); simpl; eauto.
          eapply in_remove_one_ls_in_ls; eauto.
        }
        {
          right.
          unfolds regSt.
          simpls.
          simpljoin1.
          repeat (split; eauto).
        }
      }

      eapply IHD with (R' := r) (D' := d0) in H1; eauto.

      assert (s <> s0).
      {   
        clear - H.
        intro.
        subst.
        simpls.
        simpljoin1.
        destruct H0.
        unfolds inDlyBuff.
        simpls; simpljoin1.
        destruct H.
        inversion H; tryfalse.
        unfolds noDup.
        simpls.
        destruct (sep_reg_dec s0 s0); tryfalse.
        clear e.
        eapply dlyitem_in_dlyls_reg_in in H; eauto.
        unfolds regSt.
        simpls.
        simpljoin1.
        eauto.
      }

      clear - H1 H2.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      intro.
      destruct H; tryfalse.
    }
Qed.

Lemma regst_conseq_regdly :
  forall M R F D t (s : SpReg) w,
    (M, (R, F), D) |= s |=> w ->
    (M, (R, F), D) |= t @ s |==> w.
Proof. 
  intros.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  repeat (split; eauto).
Qed.

Lemma regdlySt_dlycons_stable :
  forall t t0 s s0 w w0 M R F D,
    regdlySt t s w (M, (R, F), D) -> s <> s0 ->
    regdlySt t s w (M, (R, F), (t0, s0, w0) :: D).
Proof.
  intro t.
  induction t; intros.
  - 
    simpls.
    unfolds inDlyBuff.
    simpls.
    simpljoin1.
    split; eauto.
    unfolds noDup.
    simpls.
    destruct (sep_reg_dec s s0); subst.
    { 
      eapply dlyitem_in_dlyls_reg_in in H.
      tryfalse.
    }
    {
      intro.
      eapply H1.
      simpl in H2.
      destruct H2; subst; tryfalse; eauto.
    }
  -
    simpls.
    destruct H.
    {
      left.
      unfolds inDlyBuff.
      simpljoin1.
      simpl; eauto.
      split; eauto.
      simpls.
      unfolds noDup.
      simpl.
      destruct (sep_reg_dec s s0); subst; eauto.
      intro.
      eapply H1.
      simpl in H2.
      destruct H2; subst; tryfalse; eauto.
    }
    {
      right.
      eauto.
    }
Qed.

Lemma dlytm_gt_zero_exe_dly :
  forall D R R' D' F t (s : SpReg) w,
    (R', D') = exe_delay R D ->
    inDlyBuff (S t, s, w) D ->
    (empM, (R', F), D') |= t @ s |==> w.
Proof.
  intro D.
  induction D; intros.
  -
    unfolds inDlyBuff.
    simpls.
    simpljoin1; tryfalse.
  -
    destruct a, p.
    unfold inDlyBuff in H0.
    simpljoin1.
    simpl in H0. 
    destruct H0.
    {
      inversion H0; subst.
      simpl in H1.
      simpl in H.
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      unfold noDup in H1.
      simpl in H1.
      destruct (sep_reg_dec s s); tryfalse.
      clear e.
      lets Ht : Heqe.
      eapply not_in_exe_dly_stable in Heqe; eauto.
      simpl.
      repeat (split; eauto).
      left.
      destruct t; simpl; eauto.
      unfold inDlyBuff.
      simpl; eauto.
      split; eauto.
      unfold noDup.
      intro.
      simpl in H2.
      destruct (sep_reg_dec s s); tryfalse. 

      left.
      unfold inDlyBuff.
      split; simpl; eauto.
      unfold noDup.
      simpl.
      destruct (sep_reg_dec s s); tryfalse.
      eapply not_in_exe_dly_stable; eauto.
    }
    {
      simpl in H.
      destruct d.
      {  
        destruct (exe_delay R D) eqn:Heqe.
        inversion H; subst.
        symmetry in Heqe.
        lets Ht : Heqe.
        eapply IHD with (t := t) (w := w) (F := F) in Heqe; eauto.
        Focus 2. 
        unfold inDlyBuff.
        simpl in H1.
        unfold noDup in H1. 
        eapply dlytime_gt_zero_exe_still in Ht; eauto.
        simpl in H1.
        destruct (sep_reg_dec s s0); subst.
        split; eauto.
        simpl.
        unfold noDup.
        intro.
        eapply H1.
        eapply in_remove_one_ls_in_ls; eauto.
        repeat (split; eauto).
        simpl.
        unfold noDup.
        intro.
        eapply H1.
        simpl; eauto.
        simpl in Heqe.
        simpljoin1.
        simpl in H1. 
        destruct H3.
        {
          simpl.
          destruct (sep_reg_dec s s0).
          {
            subst.
            repeat (split; eauto).
            left.
            eapply regdlySt_dlyls_relevent; eauto.
          }
          {
            repeat (split; eauto).
            destruct_rneq.
            left.
            eapply regdlySt_dlyls_relevent; eauto.
          }
        }
        {
          unfold regSt in H.
          simpl in H.
          simpljoin1.
          eapply dlytime_gt_zero_exe_still in H0; eauto.
          eapply dlyitem_in_dlyls_reg_in in H0; eauto.
          tryfalse.
        }
      }
      {
        destruct (exe_delay R D) eqn:Heqe.
        inversion H; subst.
        symmetry in Heqe.

        assert (s <> s0).
        {
          clear - H0 H1.
          intro.
          subst.
          simpl in H1.
          unfold noDup in H1.
          simpl in H1.
          destruct (sep_reg_dec s0 s0); tryfalse.
          eapply dlyitem_in_dlyls_reg_in in H0; eauto.
        }

        lets Ht : Heqe. 
        eapply IHD with (t := t) (w := w) (F := F) in Heqe; eauto.
        Focus 2. 
        clear - H0 H1.
        unfold inDlyBuff.
        simpl in H1.
        simpls; eauto.
        split; eauto.
        unfolds noDup.
        intro.
        eapply H1.
        simpl.
        destruct (sep_reg_dec s s0); subst; simpl; eauto.
        eapply in_remove_one_ls_in_ls; eauto.
  
        simpl in H1. 
        simpls.
        simpljoin1. 
        repeat (split; eauto).
        destruct H4.
        left.
        eapply regdlySt_dlycons_stable; eauto.
        right.
        unfolds regSt.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        intro.
        destruct H; subst; tryfalse.
      }
    }
Qed.

Lemma regdlySt_in_vl_eq :
  forall t s0 w w0 M R F D,
    regdlySt t s0 w (M, (R, F), (0, s0, w0) :: D) ->
    w = w0.
Proof.
  intro t.
  induction t; intros.
  -
    simpl in H.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    inversion H; eauto.
    simpl in H0.
    unfold noDup in H0.
    simpl in H0.
    destruct (sep_reg_dec s0 s0); tryfalse.
    eapply dlyitem_in_dlyls_reg_in in H; eauto.
    tryfalse.
  - 
    simpl in H.
    destruct H.
    {
      unfolds inDlyBuff.
      simpljoin1.
      simpl in H.
      destruct H.
      inversion H; tryfalse.
      simpl in H0.
      unfold noDup in H0.
      simpl in H0.
      destruct (sep_reg_dec s0 s0); tryfalse.
      eapply dlyitem_in_dlyls_reg_in in H; eauto.
      tryfalse.
    }
    {
      eauto.
    }
Qed.

Lemma regdlySt_noDup :
  forall t s w M R F D,
    regdlySt t s w (M, (R, F), D) ->
    noDup s (getRegs D).
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    eauto.
  -
    simpl in H.
    destruct H.
    unfolds inDlyBuff.
    simpljoin1.
    eauto.
    eauto.
Qed.

Lemma regdlySt_cons_notin :
  forall t t' s w M R F D w0,
    regdlySt t s w (M, (R, F), (t', s, w0) :: D) ->
    ~ In s (getRegs D).
Proof.
  intro t.
  induction t; intros.
  - 
    simpl in H.
    unfolds inDlyBuff.
    simpls.
    simpljoin1.
    unfold noDup in H0.
    simpl in H0.
    destruct (sep_reg_dec s s); tryfalse.
    eauto.
  -
    simpls.
    destruct H.
    {
      unfolds inDlyBuff.
      simpls.
      simpljoin1.
      unfold noDup in H0.
      simpl in H0.
      destruct (sep_reg_dec s s); tryfalse.
      eauto.
    }
    {
      eapply regdlySt_noDup in H; eauto.
      simpl in H.
      unfold noDup in H.
      simpl in H.
      destruct (sep_reg_dec s s); tryfalse.
      eauto.
    }
Qed.

Lemma regdlySt_noteq_cons_remove :
  forall t t' s s' w w' M R F D,
    regdlySt t s w (M, (R, F), (t', s', w') :: D) ->
    s <> s' ->
    regdlySt t s w (M, (R, F), D).
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    inversion H; subst.
    tryfalse.
    simpl in H1.
    simpls.
    split; eauto.
    unfolds noDup.
    intro.
    eapply H1.
    simpls.
    destruct (sep_reg_dec s s'); tryfalse; eauto.
    simpl; eauto.
  -
    simpls.
    destruct H.
    {
      unfolds inDlyBuff.
      simpls.
      simpljoin1.
      destruct H.
      inversion H; subst.
      tryfalse.
      left.
      unfolds noDup.
      split; eauto.
      intro.
      eapply H1.
      simpl.
      destruct (sep_reg_dec s s'); tryfalse; eauto.
      simpl; eauto.
    }
    {
      eauto.
    }
Qed.

Lemma regdlySt_cons_same :
  forall t s w M R F D,
    noDup s (s :: getRegs D) ->
    regdlySt t s w (M, (R, F), (t, s, w) :: D).
Proof.
  intros.
  destruct t.
  {
    simpls.
    unfold inDlyBuff.
    simpl; eauto.
  }
  {
    simpl.
    left.
    unfold inDlyBuff.
    simpl; eauto.
  }
Qed.
  
Lemma regdlySt_dlytim_reduce_stable :
  forall t s w M R F D d w0,
    regdlySt t s w (M, (R, F), (S d, s, w0) :: D) ->
    regdlySt t s w (M, (R, F), (d, s, w0) :: D).
Proof. 
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    inversion H; subst.
    simpl in H0.
    split; eauto.
    simpl.
    eauto.
  -
    simpls.
    destruct H.
    {
      unfold inDlyBuff in H.
      simpls.
      simpljoin1.
      destruct H.
      {
        inversion H; subst.
        right.
        eapply regdlySt_cons_same; eauto.
      }
      {
        left.
        unfold inDlyBuff.
        simpl; eauto.
      }
    }
    {
      right; eauto.
    }
Qed.

Lemma regdlySt_notin_subst_sable :
  forall t s0 w w0 M R F D D' d,
    regdlySt t s0 w (M, (R, F), (d, s0, w0) :: D) ->
    noDup s0 (s0 :: getRegs D') ->
    regdlySt t s0 w (M, (R, F), (d, s0, w0) :: D').
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    {
      inversion H; subst.
      simpl; eauto.
    }
    {
      simpl in H1.
      simpls.
      unfolds noDup.
      simpls.
      destruct (sep_reg_dec s0 s0); tryfalse.
      eapply dlyitem_in_dlyls_reg_in in H; eauto.
      tryfalse.
    }
  -
    simpls.
    destruct H.
    {
      left.
      unfolds inDlyBuff.
      simpls.
      simpljoin1.
      destruct H.
      inversion H; subst; eauto.
      unfold noDup in H1, H0.
      simpls.
      destruct (sep_reg_dec s0 s0); tryfalse.
      eapply dlyitem_in_dlyls_reg_in in H; eauto.
      tryfalse.
    }
    {
      eauto.
    }
Qed.
    
Lemma inregdly_exe_dly_stable :
  forall D R R' D' F t (s : SpReg) w,
    (R', D') = exe_delay R D ->
    regdlySt t s w (empM, (R, F), D) ->
    (empM, (R', F), D') |= t @ s |==> w.
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H.
    simpl in H.
    simpls.
    inversion H; subst.
    repeat (split; eauto).
  -    
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H; subst.
      symmetry in Heqe. 
      destruct (sep_reg_dec s s0) eqn:Heqe1.
      {
        subst. 
        lets Ht : H0.
        eapply regdlySt_in_vl_eq in H0; eauto.
        subst.
        simpl.
        repeat (split; eauto).
        symmetry in Heqe.
        eapply regdlySt_cons_notin in Ht; eauto.
        symmetry in Heqe.
        lets Hexe_dly : Heqe.
        right.
        unfold regSt.
        simpl.
        repeat (split; eauto).
        unfold RegMap.set.
        destruct_rneq.
        eapply not_in_exe_dly_stable in Ht; eauto.
      }
      { 
        eapply regdlySt_noteq_cons_remove in H0; eauto.
        eapply IHD with (R' := r) (D' := d) in H0; eauto.
        clear - H0 n. 
        simpls.
        simpljoin1.
        repeat (split; eauto).
        destruct H0.
        left.
        eapply regdlySt_dlyls_relevent; eauto.
        right. 
        unfolds regSt.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        reg_val_eval.
      }
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      destruct (sep_reg_dec s s0) eqn:Heqe1.
      {    
        subst.
        lets Ht : Heqe.
        simpl.
        repeat (split; eauto). 
        left.
        lets Hregdly : H0.
        eapply regdlySt_dlytim_reduce_stable in H0; eauto.
        eapply regdlySt_notin_subst_sable with (D := D); eauto.
        eapply regdlySt_dlyls_relevent; eauto.
        eapply regdlySt_noDup in Hregdly; eauto.
        simpls.
        clear - Ht Hregdly.
        unfolds noDup.
        intro.
        eapply Hregdly.
        simpls.
        destruct (sep_reg_dec s0 s0); simpl; eauto.
        eapply not_in_exe_dly_stable in Ht; eauto.
        tryfalse.
      }
      { 
        lets Hexe_delay : Heqe.
        lets Hnodup : H0. 
        eapply regdlySt_noDup in Hnodup; eauto. simpl in Hnodup.
        unfold noDup in Hnodup.
        simpl in Hnodup.
        destruct (sep_reg_dec s s0); tryfalse.
        eapply regdlySt_noteq_cons_remove in H0; eauto.  
        eapply IHD with (R' := r) (D' := d0) in H0; eauto. 
        clear - H0 n Heqe.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        destruct H0.
        left.
        eapply regdlySt_dlycons_stable; eauto.
        right.
        unfolds regSt.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        intro. 
        eapply H1.
        destruct H.
        subst; tryfalse.
        eauto.  
      }
    }
Qed.
    
Lemma dlytime_gt_zero_reduce_exe_dly :
  forall D M R R' D' F t s w,
    (M, (R, F), D) |= S t @ s |==> w ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= t @ s |==> w.
Proof. 
  intros.
  lets Ht : H.
  simpl in Ht.
  simpljoin1.

  destruct H2.
  { 
    destruct H1.
    {
      eapply dlytm_gt_zero_exe_dly; eauto.
    }
    {
      eapply inregdly_exe_dly_stable; eauto.
    }
  }
  {
    assert ((empM, (R, F), D) |= s |=> w).
    {
      simpl.
      eauto.
    }

    eapply dly_reduce_reg_stable in H2; eauto.
    eapply regst_conseq_regdly; eauto.
  }
Qed.

Lemma dly_reduce_dlyreg_stable :
  forall D M R R' F D' s w n,
    (M, (R, F), D) |= n @ s |==> w ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= (n @ s |==> w ↓).
Proof.
  intros.
  simpls.
  simpljoin1.
  exists R D.
  split; eauto.
Qed.

Lemma dly_reduce_pure_stable :
  forall D M R R' F D' pu,
    (M, (R, F), D) |= [| pu |] ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= [| pu |].
Proof.
  intro D.
  induction D; intros.
  -
    simpls; simpljoin1; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= [| pu |]).
    {
      clear - H.
      simpls.
      simpljoin1.
      split; eauto.
    }
    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
    }
Qed.
    
Lemma Afrmlist_exe_delay_stable :
  forall D D' M R R' F w f,
    (M, (R, F), D) |= {|w, f|} ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= {|w, f|}.
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    simpljoin1.
    repeat (split; eauto).
  -
    destruct a, p.
    assert ((M, (R, F), D) |= {|w, f|}).
    {
      clear - H.
      simpls.
      simpljoin1.
      split; eauto.
    }
    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      clear - H1.
      simpls.
      simpljoin1.
      split; eauto.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      reg_val_eval.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_asrt_stable :
  forall p M R R' F D D',
    (M, (R, F), D) |= p -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= (p ↓).
Proof.
  intros.
  simpls.
  exists R D.
  eauto.
Qed.

Lemma exe_delay_no_abort :
  forall D R,
  exists R' D', exe_delay R D = (R', D').
Proof.
  intro D.
  induction D; intros.
  simpl.
  eauto.
  destruct a, p.
  simpl.
  destruct d.
  {
    specialize (IHD R).
    simpljoin1.
    rewrite H.
    eauto.
  }
  {
    specialize (IHD R).
    simpljoin1.
    rewrite H.
    eauto.
  }
Qed.

Lemma dly_genreg_free_exe_delay_stable :
  forall p D M R R' D' F,
    (M, (R, F), D) |= p -> DlyGenRegFree p ->
    exe_delay R D = (R', D') ->
    (M, (R', F), D') |= p.
Proof.
  intro p.  
  induction p; intros;
    try solve [simpls; eauto; tryfalse].
  eapply dly_reduce_reg_stable; eauto.

  {
    simpls.
    simpljoin1.
    eapply IHp in H2; eauto.
  }

  eapply Afrmlist_exe_delay_stable; eauto.

  {
    simpls; simpljoin1; eauto.
  }

  {
    simpl in H.
    destruct H; simpls; simpljoin1; eauto.
  }

  {
    sep_star_split_tac.
    simpl in H5.
    simpljoin1.
    simpl in H0.
    simpljoin1.
    eapply IHp1 in H; eauto.
    eapply IHp2 in H4; eauto.
    simpl.
    do 2 eexists.
    repeat (split; eauto).
  }

  simpl in H0, H1.
  simpljoin1.
  eapply H in H0; eauto.
  simpl. eauto.
Qed.

Lemma exe_delay_general_reg_stable :
  forall D R R' D' (r : GenReg),
    exe_delay R D = (R', D') ->
    (forall v, R r = v <-> R' r = v).
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H; subst.
    split; eauto.

  -
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
      split.
      intro.
      eapply Heqe in H0.
      reg_val_eval.
      intro.
      eapply Heqe; eauto.
      unfolds RegMap.set.
      destruct_rneq_H.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
    }
Qed.
  
(*+ Lemmas for expression +*)

(*+ Lemmas for regdisj +*)
Lemma regdisj_star_sep1 :
  forall p1 p2 p3,
    regdisj p1 (p2 ** p3) ->
    regdisj p1 p2.
Proof.
  intros.
  unfolds regdisj.
  intros.
  specialize (H rn).
  simpljoin1.
  split.
  {
    intro.
    eapply H in H1.
    intro.
    eapply H1.
    simpl.
    eauto.
  }
  {
    intro.
    eapply H0.
    simpl; eauto.
  }
Qed.

Lemma regdisj_star_sep2 :
  forall p1 p2 p3,
    regdisj p1 (p2 ** p3) ->
    regdisj p1 p3.
Proof.
  intros.
  unfolds regdisj.
  intros.
  specialize (H rn).
  simpljoin1.
  split.
  {
    intro.
    eapply H in H1.
    intro.
    eapply H1.
    simpl; eauto.
  }
  {
    intro.
    eapply H0; eauto.
    simpl; eauto.
  }
Qed.

Lemma regdisj_star_sepl1 :
  forall p1 p2 p3,
    regdisj (p1 ** p2) p3 ->
    regdisj p1 p3.
Proof.
  intros.
  unfolds regdisj.
  intros.
  specialize (H rn).
  simpljoin1.
  split.
  {
    intro.
    eapply H.
    simpl; eauto.
  }
  {
    intro.
    eapply H0 in H1.
    intro.
    eapply H1.
    simpl; eauto.
  }
Qed.

Lemma regdisj_star_sepl2 :
  forall p1 p2 p3,
    regdisj (p1 ** p2) p3 ->
    regdisj p2 p3.
Proof.
  intros.
  unfolds regdisj.
  intros.
  specialize (H rn).
  simpljoin1.
  split.
  {
    intro.
    eapply H.
    simpl; eauto.
  }
  {
    intro.
    eapply H0 in H1.
    intro.
    eapply H1.
    simpl; eauto.
  }
Qed.

Lemma regdisj_sym :
  forall p1 p2,
    regdisj p1 p2 ->
    regdisj p2 p1.
Proof.
  intros.
  unfolds regdisj.
  intros.
  specialize (H rn).
  simpljoin1.
  split; eauto.
Qed.

Lemma regdisj_star_merge :
  forall p1 p2 p3,
    regdisj p1 p2 -> regdisj p1 p3 ->
    regdisj p1 (p2 ** p3).
Proof.
  intros.
  unfolds regdisj.
  intros.
  specialize (H rn).
  simpljoin1.
  split.
  {
    specialize (H0 rn).
    simpljoin1.
    intro.
    intro.
    simpl in H4.
    destruct H4.
    {
      eapply H in H3.
      tryfalse.
    }
    {
      eapply H0 in H3.
      tryfalse.
    }
  }
  {
    specialize (H0 rn).
    simpljoin1.
    intro.
    simpl in H3.
    destruct H3.
    eauto.
    eauto.
  }
Qed.
  
(*+ Lemmas for Sep Star +*)
Lemma disj_sep_star_merge :
  forall m1 m2 R F D p1 p2,
    (m1, (R, F), D) |= p1 ->
    (m2, (R, F), D) |= p2 ->
    disjoint m1 m2 -> regdisj p1 p2 ->
    (merge m1 m2, (R, F), D) |= p1 ** p2.
Proof.
  intros.
  simpl.
  exists (m1, (R, F), D) (m2, (R, F), D).
  repeat (split; eauto).
Qed.
 
Lemma sep_star_assoc :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= (p1 ** p2) ** p3.
Proof.
  intros.
  destruct_state s.
  sep_star_split_tac.
  simpl in H2, H3.
  simpljoin1.
  simpl. 
  exists (merge m0 m2, (r3, f3), d3) (m3, (r3, f3), d3). 
  repeat (split; eauto). 
  eapply disj_sym. 
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto. 
  eapply disj_sym; eauto.
  rewrite merge_assoc; eauto.
 
  exists (m0, (r3, f3), d3) (m2, (r3, f3), d3).
  repeat (split; eauto).
  eapply disj_merge_disj_sep1 in H3; eauto.
  eapply regdisj_star_sep1 in H4; eauto.
  unfolds regdisj; eauto.
  specialize (H4 rn).
  simpljoin1; eauto.
  eapply regdisj_star_sep1 in H4; eauto.
  unfolds regdisj; eauto.
  specialize (H4 rn).
  simpljoin1; eauto.
 
  intro.
  simpl in H5.
  unfolds regdisj.
  specialize (H4 rn).
  simpljoin1.
  destruct H5.
  {
    eapply H4 in H5.
    intro.
    eapply H5.
    simpl; eauto.
  }
  {
    specialize (H7 rn).
    simpljoin1.
    eauto.
  }

  intro.
  intro.
  simpl in H6.
  destruct H6.
  {
    unfold regdisj in H4.
    specialize (H4 rn).
    simpljoin1.
    eapply H4 in H6.
    eapply H6; eauto.
    simpl; eauto.
  }
  {
    unfolds regdisj.
    specialize (H7 rn).
    simpljoin1.
    eapply H7 in H6.
    tryfalse.
  }
Qed.

Lemma sep_star_assoc2 :
  forall s p1 p2 p3,
    s |= (p1 ** p2) ** p3 ->
    s |= p1 ** p2 ** p3.
Proof.
  intros.
  destruct_state s.
  sep_star_split_tac.
  simpls.
  simpljoin1. 
  exists (m2, (r3, f3), d3) (merge m3 m1, (r3, f3), d3).
  split; eauto.
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep1 in H3; eauto.
  eapply disj_sym; eauto.
  
  rewrite merge_assoc; eauto.
  split; eauto.
  split; eauto.
  do 2 eexists.
  split; eauto.
  Focus 2.
  split; eauto.
  split; eauto.
 
  eapply regdisj_star_sepl2; eauto.
  repeat (split; eauto).
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto.

  eapply regdisj_star_merge; eauto.
  eapply regdisj_star_sepl1 in H4; eauto.
Qed.

Lemma sep_star_sym :
  forall s p1 p2,
    s |= p1 ** p2 ->
    s |= p2 ** p1.
Proof.
  intros.
  simpls.
  simpljoin1.
  exists x0 x.
  split; eauto.
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1. 
  repeat (split; eauto).
  eapply disj_sym; eauto.
  rewrite disj_merge_reverse_eq; eauto.
  do 2 (split; eauto).
  eapply regdisj_sym; eauto.
Qed.

Lemma sep_star_lift :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= p2 ** p1 ** p3.
Proof.
  intros.
  sep_star_split_tac.
  simpls; simpljoin1.
 
  exists (m1, (r2, f2), d2) (merge m m2, (r2, f2), d2).
  split; eauto.
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H3.
  eapply disj_sym; eauto.

  rewrite merge_lift; eauto.
  eapply disj_merge_disj_sep1 in H3; eauto.

  split; eauto.
  split; eauto.
  exists (m, (r2, f2), d2) (m2, (r2, f2), d2).
  simpl; eauto.
  split; eauto.
  repeat (split; eauto).
  eapply disj_merge_disj_sep2 in H3; eauto.
  split; eauto.
  split; eauto.
  eapply regdisj_star_sep2; eauto.
  eapply regdisj_star_merge; eauto.
  eapply regdisj_star_sep1 in H4; eauto.
  eapply regdisj_sym; eauto.
Qed.

(*+ Lemmas about instruction +*)
  
