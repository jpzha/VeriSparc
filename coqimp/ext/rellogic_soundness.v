Require Import Coqlib.                     
Require Import Maps.

Require Import Classical_Prop.

Require Import Integers.
Require Import LibTactics.
Open Scope Z_scope.
Import ListNotations.

Require Import state.
Require Import language.
Require Import highlang.
Require Import lowlang.
Require Import logic.
Require Import lemmas.
Require Import reg_lemma.
Require Import soundness.
Require Import refinement.
Require Import rellogic.
Require Import lemmas_comp.
Require Import lemmas_comp2.

Require Import lemmas_ins.
Require Import inssound.
Require Import wf_seq_sound.

(** Auxiliary Lemmas *)
Lemma last_Kq_cons_Q_same :
  forall A (Kq : list A) Q Q',
    last Kq Q = last (Q :: Kq) Q'.
Proof.
  induction Kq; intros; simpl; eauto.
  destruct Kq; eauto.
Qed.

Lemma merge_empThrdPool_r_eq :
  forall T,
    T ⊎ EmpThrdPool = T.
Proof.
  intros.
  eapply FunctionalExtensionality.functional_extensionality; intros.
  unfold merge.
  destruct (T x) eqn:Heqe; eauto.
Qed.

Lemma merge_empThrdPool_l_eq :
  forall T,
    EmpThrdPool ⊎ T = T.
Proof.
  intros.
  eapply FunctionalExtensionality.functional_extensionality; intros.
  unfold merge.
  eauto.
Qed.

Lemma RAlst_down :
  forall S HS A w p,
    (S, HS, A, w) ||= RAlst p ->
    S |= p /\ getHM HS = empM /\ getHThrdPool HS = EmpThrdPool.
Proof.
  intros.
  simpls.
  eauto.
Qed. 

Lemma RAlst_hold :
  forall S A w t K p,
    S |= p -> (S, (EmpThrdPool, t, K, empM), A, w) ||= RAlst p.
Proof.
  intros.
  simpls.
  eauto.
Qed.

Lemma token_inc_asrt_stable :
  forall P w w' S HS A,
    (S, HS, A, w) ||= P -> (w <= w')%nat ->
    (S, HS, A, w') ||= P.
Proof.
  induction P; intros; try solve [simpls; simpljoin1; eauto].
  {
    simpls; simpljoin1.
    destruct_hstate HS; simpljoin1.
    repeat (split; eauto).
    omega.
  }
  {
    simpls.
    destruct H.
    eapply IHP1 in H; eauto.
    eapply IHP2 in H; eauto.
  }
  {
    simpls.
    simpljoin1.
    assert (w' = x3 + (w' - x3)).
    omega.
    rewrite H2 in H0.
    eapply IHP1 in H3; eauto.
    eapply IHP2 in H4; eauto.
    do 4 eexists.
    exists x3 (w' - x3).
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    eapply IHP2; eauto.
    omega.
  }
Qed.

Lemma token_consume :
  forall S HS A w w' P,
    (S, HS, A, w) ||= P ⋆ RAtoken w' ->
    (S, HS, A, w - w') ||= P.
Proof.
  intros.
  simpls.
  simpljoin1.
  destruct x0.
  destruct p.
  destruct p.
  simpljoin1.
  destruct_state x1.
  destruct_state x2.
  simpls; simpljoin1.
  destruct_hstate x.
  simpls; simpljoin1.
  do 2 rewrite empM_merge_still_r; eauto.
  rewrite sep_lemma.merge_empR_r_eq; eauto.
  rewrite merge_empThrdPool_r_eq.
  assert (x3 <= x3 + x4 - w').
  {
    omega.
  }
  eapply token_inc_asrt_stable; eauto.
Qed.

(** Auxiliary Lemmas about exec delay *)
Lemma dly_reduce_relasrt_stable :
  forall P M R R' F D D' HS A w,
    ((M, (R, F), D), HS, A, w) ||= P -> (R', D') = exe_delay R D ->
    ((M, (R', F), D'), HS, A, w) ||= (P ⤈).
Proof.
  intros.
  simpls.
  exists R D.
  eauto.
Qed.  

(** Auxiliary Lemmas about SepStar *) 
Lemma sep_star_assoc :
  forall P Q R,
    (P ⋆ Q) ⋆ R ⇔ P ⋆ (Q ⋆ R).
Proof.
  intros.
  split; intros.
  {
    simpl in H.
    destruct rls.
    destruct p.
    destruct p.
    simpljoin1.
    destruct_state x1.
    destruct_state x2.
    simpl in H0; simpljoin1.
    destruct_state x7.
    destruct_state x8.
    simpl in H4; simpljoin1.

    destruct_hstate x.
    destruct_hstate x0.
    destruct_hstate x5.
    destruct_hstate x6.
    simpl in H, H2; simpljoin1.
 
    repeat (rewrite <- merge_assoc).
    simpl.
    exists (T1, t2, K2, M1) ((T2 ⊎ T0), t2, K2, (M2 ⊎ M0)).
    exists (m1, (r1, f1), d1) ((m2 ⊎ m0), ((r2 ⊎ r0), f1), d1).
    exists x9 (x10 + x4); simpl.
    repeat (split; eauto).

    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H. 
    eapply disj_sym.
    eapply disj_merge_disj_sep1; eauto.
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H12.
    eapply disj_sym.
    eapply disj_merge_disj_sep1 in H12; eauto. 
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H0.
    eapply disj_sym.
    eapply disj_merge_disj_sep1 in H0; eauto.
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H1.
    eapply disj_sym.
    eapply disj_merge_disj_sep1 in H1; eauto.

    rewrite plus_assoc_reverse; eauto.
    exists (T2, t2, K2, M2) (T0, t2, K2, M0).
    exists (m2, (r2, f1), d1) (m0, (r0, f1), d1).
    exists x10 x4.
    simpl.
    repeat (split; eauto).
    eapply disj_sym in H.
    eapply disj_sym.
    eapply disj_merge_disj_sep2; eauto.
    eapply disj_sym in H12.
    eapply disj_sym.
    eapply disj_merge_disj_sep2; eauto.
    eapply disj_sym in H0.
    eapply disj_sym.
    eapply disj_merge_disj_sep2; eauto.
    eapply disj_sym in H1.
    eapply disj_sym.
    eapply disj_merge_disj_sep2; eauto.
  }
  {
    simpl in H.
    destruct rls.
    destruct p.
    destruct p.
    simpljoin1.

    destruct_state x1.
    destruct_state x2.
    destruct_state x7.
    destruct_state x8.
    simpl in H0, H4.
    simpljoin1.
    destruct_hstate x.
    destruct_hstate x0.
    destruct_hstate x5.
    destruct_hstate x6.
    simpl in H, H3; simpljoin1.

    repeat (rewrite merge_assoc); eauto.
    simpl.
    exists ((T ⊎ T1), t2, K2, (M ⊎ M1)) (T2, t2, K2, M2).
    exists ((m ⊎ m1), (r ⊎ r1, f2), d2) (m2, (r2, f2), d2). 
    exists (x3 + x9) x10.
    simpl.
    repeat (split; eauto).

    eapply disj_sym.
    eapply disj_sep_merge_still; eauto.
    eapply disj_merge_disj_sep2 in H; eapply disj_sym; eauto.
    eapply disj_sym; eauto. 
    eapply disj_sym.
    eapply disj_sep_merge_still; eauto.
    eapply disj_merge_disj_sep2 in H12; eapply disj_sym; eauto.
    eapply disj_sym; eauto.
    eapply disj_sym.
    eapply disj_sep_merge_still; eauto.
    eapply disj_merge_disj_sep2 in H0; eapply disj_sym; eauto.
    eapply disj_sym; eauto.
    eapply disj_sym.
    eapply disj_sep_merge_still; eauto.
    eapply disj_merge_disj_sep2 in H10; eapply disj_sym; eauto.
    eapply disj_sym; eauto.

    rewrite plus_assoc_reverse; eauto.

    exists (T, t2, K2, M) (T1, t2, K2, M1).
    exists (m, (r, f2), d2) (m1, (r1, f2), d2).
    exists x3 x9.
    simpl.
    repeat (split; eauto).
    eapply disj_merge_disj_sep1; eauto.
    eapply disj_merge_disj_sep1; eauto.
    eapply disj_merge_disj_sep1; eauto.
    eapply disj_merge_disj_sep1; eauto.
  }
Qed.

Lemma sep_star_hold :
  forall S S1 S2 HS HS1 HS2 A w1 w2 w P Q,
    (S1, HS1, A, w1) ||= P -> (S2, HS2, A, w2) ||= Q ->
    state_union S1 S2 S -> hstate_union HS1 HS2 HS -> w = w1 + w2 ->
    (S, HS, A, w) ||= P ⋆ Q.
Proof.
  intros.
  simpl.
  do 6 eexists.
  repeat (split; eauto).
Qed.

Lemma sep_star_imply :
  forall P P' Q Q',
    P ⇒ P' -> Q ⇒ Q' -> P ⋆ Q ⇒ P' ⋆ Q'.
Proof.
  intros.
  simpls.
  destruct rls.
  destruct p.
  destruct p.
  simpljoin1.
  do 6 eexists.
  repeat (split; eauto).
Qed.

Lemma sep_star_split :
  forall P Q S HS A w,
    (S, HS, A, w) ||= P ⋆ Q ->
    exists S1 S2 HS1 HS2 w1 w2, state_union S1 S2 S /\ hstate_union HS1 HS2 HS /\ w = w1 + w2 /\
                           (S1, HS1, A, w1) ||= P /\ (S2, HS2, A, w2) ||= Q.
Proof.
  intros.
  simpls.
  simpljoin1.
  do 6 eexists.
  repeat (split; eauto).
Qed.

Lemma sep_star_sym :
  forall P Q,
    P ⋆ Q ⇒ Q ⋆ P.
Proof.
  intros.
  destruct rls.
  destruct p.
  destruct p.
  eapply sep_star_split in H.
  simpljoin1.
  eapply sep_star_hold; eauto.

  clear - H.
  destruct_state x.
  destruct_state x0.
  simpls; simpljoin1.
  repeat (split; eauto).
  eapply disj_sym; eauto.
  eapply disj_sym; eauto.
  rewrite disj_merge_reverse_eq; eauto. 
  rewrite disj_merge_reverse_eq with (m1 := r); eauto.

  clear - H0.
  destruct_hstate x1.
  destruct_hstate x2; simpls; simpljoin1.
  repeat (split; eauto).
  eapply disj_sym; eauto.
  eapply disj_sym; eauto.
  rewrite disj_merge_reverse_eq; eauto. 
  rewrite disj_merge_reverse_eq with (m1 := M); eauto.

  rewrite Nat.add_comm; eauto.
Qed.

(** Auxiliary Lemmas about Register *)
Lemma reg_vl_rel_change :
  forall M R F D rn v v1 HS A w P,
    ((M, (R, F), D), HS, A, w) ||= RAlst (rn |=> v) ⋆ P ->
    ((M, (set_R R rn v1, F), D), HS, A, w) ||= RAlst (rn |=> v1) ⋆ P.
Proof.
  intros.
  eapply sep_star_split in H.
  simpljoin1.
  eapply RAlst_down in H2; simpljoin1.
  eapply sep_lemma.astar_emp_intro_r in H1.
  destruct_state x.
  destruct_state x0.
  simpl in H; simpljoin1.
  eapply reg_vl_change with (v1 := v1) in H1; eauto.
  eapply sep_lemma.astar_emp_elim_r in H1.
  destruct_hstate x1.
  destruct_hstate x2.
  simpl in H0, H2, H4; simpljoin1.
  eapply sep_star_hold; eauto.
  eapply RAlst_hold; eauto.
  simpl.
  repeat (split; eauto).
  eapply disjoint_setR_still1; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  clear - H1.
  simpl in H1.
  unfolds regSt; simpls.
  simpljoin1.
  unfolds set_R.
  unfold is_indom in *.
  destruct (r rn) eqn:Heqe; tryfalse.
  unfold indom; eauto.
  subst.
  rewrite RegMap.gss in Heqe; tryfalse.
  simpl.
  split; eauto.
Qed.

(** Well formed Instruction *)
Lemma wf_ins_rel_soundness :
  forall P i Q,
    ⊩ {{ P }} i {{ Q }} -> rel_ins_sound P Q i.
Proof.
  intros.
  inv H.
  eapply ins_rule_sound in H1.
  unfold rel_ins_sound; intros.
  eapply H0 in H.
  simpl in H.
  simpljoin1.
  unfold ins_sound in H1.
  eapply H1 in H5; simpljoin1.
  destruct_hstate x.
  destruct_hstate x0.
  simpl in H, H7, H8; simpljoin1.
  eapply legal_com_ins_safety_property_relasrt' in H4; eauto.
  simpljoin1.
  exists x.
  split; eauto.
  eapply H2.
  simpl.
  exists (EmpThrdPool, t0, K0, empM) (T0, t0, K0, M0) x5 x0 x3 x4.

  split.
  simpl.
  split; eauto.

  split; eauto.
Qed.

(** Well formed Instruction Seqence Soundness *)
Definition get_index_fcall (rls : RelState) :=
  match rls with
  | (LS, HS, A, w) => w
  end. 

Fixpoint get_insSeqLen (I : InsSeq) :=
  match I with
  | consSeq i I' => (1 + get_insSeqLen I')%nat
  | consJ aexp rr i => 2%nat
  | consCall f i I' => (2 + get_insSeqLen I')%nat
  | consRetl i => 2%nat
  | consRet i => 2%nat
  | consBe f i I' => (2 + get_insSeqLen I')%nat
  | consBne f i I' => (2 + get_insSeqLen I')%nat
  end.

Lemma LookupXC_hold_legal_com :
  forall C pc I,
    LookupXC C pc I ->
    legal_com (C pc) /\ legal_com (C pc +ᵢ ($ 4)).
Proof.
  intros.
  inv H.
  {
    unfold legal_com at 1.
    rewrite H0; eauto.
    inv H1; unfold legal_com; try rewrite H; eauto.
  }
  {
    unfold legal_com; rewrite H0, H1; eauto.
  }
  {
    unfold legal_com; rewrite H0, H1; eauto.
  }
  {
    unfold legal_com; rewrite H0, H1; eauto.
  }
  {
    unfold legal_com; rewrite H0, H1; eauto.
  }
Qed.

Lemma rel_safety_insSeq_frame_property :
  forall I Spec C pc S1 S2 S HS1 HS2 HS w1 w2 Q Pr A,
    GoodFrm Pr ->
    LookupXC C pc I -> (S2, HS2, A, w2) ||= Pr -> Sta A Pr ->
    state_union S1 S2 S -> hstate_union HS1 HS2 HS ->
    rel_safety_insSeq Spec w1 (C, S1, pc, pc +ᵢ ($ 4)) (A, HS1) Q ->
    rel_safety_insSeq Spec (w1 + w2)%nat (C, S, pc, pc +ᵢ ($ 4)) (A, HS) (Q ⋆ Pr).
Proof.
  induction I;
  introv HGoodFrmPr; intros.
  {
    (** i *)
    inv H.
    inv H4.
    lets Hcont : H9.
    eapply H14 in Hcont; clear H14 H16 H17 H18 H19.
    simpljoin1.
    econstructor; try solve [intros; CElim C].

    intros.
    rewrite H9 in H5; inv H5.
    split.
    {
      eapply legal_com_safety_property in H; eauto.
      2 : unfold legal_com; rewrite H9; eauto.
      destruct H as (S' & S2' & HLP__ & Hstate_union & HPr').
      do 3 eexists; eauto.
    }
    {
      intros.
      lets Hcont : H.
      eapply legal_com_safety_property in H; eauto.
      2 : unfold legal_com; rewrite H9; eauto.
      destruct H as (S'0 & S2' & HLP__ & Hstate_union & HPr').
      assert ((C, (S', pc', npc')) = (C, (S'0, x0, x1))).
      {
        eapply LP_deterministic; eauto.
        simpl; eauto.
      }
      inv H; clear H5.

      eapply H4 in Hcont; eauto.
      inv HLP__.
      inv H15; CElim C.
      destruct Hcont as [Hcon | Hcont].
      {
        left.
        eapply IHI; eauto.
      }
      { 
        destruct Hcont as (HS1' & Hexec_prim & Hrel_safety_insSeq).
        lets Hexec_prim' : Hexec_prim.
        inv Hexec_prim'.
        inv H1.
        destruct H; tryfalse.
        assert (Pm prim lv = Pm prim lv).
        eauto.
        eapply H in H1; eauto.
        destruct H1 as (HS' & HS2' & Hexec_prim' & Hhstate_union' & HPr'').
        right.
        exists HS'.
        split; eauto. 
        eapply IHI; eauto.
        econstructor; eauto.
      }
    }
  }
  {
    (** jmpl aexp rd *)
    inv H.
    inv H4.
    lets Hcont : H9.
    eapply H17 in Hcont; clear H14 H16 H17 H18 H19.
    simpljoin1.
    lets Hcont : H.
    eapply H4 with (S2 := x) in Hcont; eauto; clear H4.
    destruct Hcont as (Fp & Fq & L & r & A' & HS1' & Hexec_prim & HSpec & HFp & HFq & HGoodFrm & Hw1 & Hnpc).
    econstructor; try solve [intros; tryfalse].

    intros.
    rewrite H9 in H4; inv H4.
    split.
    eapply legal_com_safety_property in H; eauto.
    2 : unfold legal_com; rewrite H9; eauto.
    destruct H as (S' & S2' & HLP__ & Hstate_union & HPr).
    eapply legal_com_safety_property in H5; eauto.
    destruct H5 as (S'' & S2'' & HLP__' & Hstate_union' & HPr').
    do 6 eexists.
    split; eauto.
    inv HLP__.
    inv H15; CElim C.
    unfold legal_com; rewrite H11; eauto.
 
    intros.
    eapply legal_com_safety_property in H; eauto.
    2 : unfold legal_com; rewrite H9; eauto.
    destruct H as (S' & S2' & HLP__ & Hstate_union & HPr).
    assert ((C, (S0, pc1, npc1)) = (C, (S', x1, x2))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H.
    assert (x1 = pc +ᵢ ($ 4)).
    {
      inv H4.
      inv H17; CElim C; eauto.
    }
    subst x1.
    eapply legal_com_safety_property in H5; eauto.
    2 : unfold legal_com; rewrite H11; eauto.
    destruct H5 as (S'' & S2'' & HLP__' & Hstate_union' & HPr').
    assert ((C, (S3, pc2, npc2)) = (C, (S'', x3, x3 +ᵢ ($ 4)))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H.
    
    destruct Hexec_prim as [Hexec_prim | Hexec_prim]; simpljoin1.
    {
      exists Fp Fq L (r ⋆ Pr) A HS. 
      split.
      left; eauto.
      split; eauto.
      split; eauto.
      assert (Nat.pred (w1 + w2) = Nat.pred w1 + w2).
      {
        destruct w1; try omega; eauto.
      }
      rewrite H.
      eapply sep_star_assoc.
      eapply sep_star_hold; eauto.

      split.
      intros.
      eapply sep_star_assoc in H.
      eapply sep_star_imply with (P := (Fq L ⋆ r)) (P' := Q); eauto.
      split; simpl; eauto.
      split; eauto.
      omega.
    }
    {
      lets Hexec_prim' : Hexec_prim.
      inv Hexec_prim'.
      inv H1.
      destruct H; tryfalse.
      assert (Pm prim lv = Pm prim lv); eauto.
      eapply H in H1; eauto; clear H.
      destruct H1 as (HS' & HS2' & Hexec_prim' & Hhstate_union & HPr'').
      exists Fp Fq L (r ⋆ Pr) Pdone HS'.
      split.
      right; eauto.
      split; eauto.
      split; eauto.

      assert (Nat.pred (w1 + w2) = Nat.pred w1 + w2).
      {
        destruct w1; try omega; eauto.
      }
      rewrite H.
      eapply sep_star_assoc.
      eapply sep_star_hold; eauto.

      split; eauto.
      intros.
      eapply sep_star_assoc in H.
      eapply sep_star_imply with (P := (Fq L ⋆ r)) (P' := Q); eauto.

      split; eauto.
      simpl; eauto.
      split; try omega.
      eauto.
    }
  }
  {
    (** call f *)
    inv H.
    inv H4.
    lets Hcont : H10.
    eapply H17 in Hcont; clear H15 H17 H18 H19 H20.
    simpljoin1.
    lets Hcont : H.
    eapply H4 with (S2 := x) in Hcont; eauto; clear H4. 
    destruct Hcont as (Fp & Fq & L & r & A' & HS1' & Hcont).
    simpljoin1.
    econstructor; try solve [intros; tryfalse].

    intros.
    rewrite H10 in H4; inv H4.
    eapply legal_com_safety_property in H; eauto.
    2 : unfold legal_com; rewrite H10; eauto.
    destruct H as (S' & S2' & HLP__ & Hstate_union & HPr).
    assert (x1 = pc +ᵢ ($ 4)).
    {
      inv HLP__.
      inv H23; CElim C; eauto.
    }
    subst x1. 
    eapply legal_com_safety_property in H5; eauto.
    2 : unfold legal_com; rewrite H11; eauto.
    destruct H5 as (S'' & S2'' & HLP__' & Hstate_union' & HPr'). 

    split.
    do 6 eexists; eauto.

    intros.
    assert ((C, (S', pc +ᵢ ($ 4), x2)) = (C, (S0, pc1, npc1))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    } 
    inv H5.
    assert ((C, (S'', f, f +ᵢ ($ 4))) = (C, (S3, pc2, npc2))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H5.
    clear H H4.
    assert (Nat.pred (w1 + w2) = Nat.pred w1 + w2).
    {
      destruct w1; simpls; try omega.
    }

    destruct H9; simpljoin1.
    { 
      exists Fp Fq L (r ⋆ Pr) A HS.
      split; eauto.
      split; eauto.
      split; eauto.
      split.
      omega.

      split.
      left; eauto.

      split.
      rewrite H.
      eapply sep_star_assoc.
      eapply sep_star_hold; eauto.

      split.
      simpl; eauto.
 
      split; intros.
      assert (pc +ᵢ ($ 12) = (pc +ᵢ ($ 8)) +ᵢ ($ 4)).
      rewrite Int.add_assoc; eauto.
      rewrite H6.
      eapply sep_star_assoc in H4.
      eapply sep_star_split in H4.
      destruct H4 as (S_1 & S_2 & HS_1 & HS_2 & w1' & w2' & Hstate_union'' & Hhstate_union'' &
                      Hw' & HFq_r & HPr'').
      subst w'.
      eapply IHI; eauto.
      eapply H15 in HFq_r; eauto.
      rewrite <- H6; eauto.
      eapply H16 in H4; eauto.
    }
    {
      lets Hexec_prim : H4.
      inv H4.
      lets HSta_Pr : H1.
      inv HSta_Pr.
      destruct H4; tryfalse.
      assert (Pm prim lv = Pm prim lv); eauto.
      eapply H4 in H5; simpljoin1; eauto.

      exists Fp Fq L (r ⋆ Pr) Pdone x1.
      split; eauto.
      split; eauto.
      split; eauto.
      split.
      omega.
      split.
      right; eauto.
      split; eauto.

      eapply sep_star_assoc.
      rewrite H.
      eapply sep_star_hold; eauto.

      split.
      simpl; eauto.

      split.
      intros.
      assert (pc +ᵢ ($ 12) = (pc +ᵢ ($ 8)) +ᵢ ($ 4)).
      rewrite Int.add_assoc; eauto.
      rewrite H20.
      eapply sep_star_assoc in H18.
      eapply sep_star_split in H18.
      simpljoin1.
      eapply IHI; eauto.
      rewrite <- H20.
      eapply H15; eauto.

      intros.
      eapply H16 in H18; eauto.
    }
  }
  { 
    (** retl *)
    inv H.
    inv H4.
    lets Hcont : H6.
    eapply H19 in Hcont; clear H14 H16 H17 H18 H19.
    simpljoin1.
    lets Hcont : H.
    eapply H4 with (S2 := x) in Hcont; eauto. 
    destruct Hcont as (A' & HS1' & Hexec_prim & HQ & f & Hret & Hpc & Hnpc); subst.

    econstructor; try solve [intros; CElim C].
    intros.
    clear H7.

    eapply legal_com_safety_property in H; eauto.
    2 : unfold legal_com; rewrite H6; eauto.
    destruct H as (S' & S2' & HLP__ & Hstate_union & HPr).
    assert (x1 = pc +ᵢ ($ 4)).
    {
      inv HLP__.
      inv H16; CElim C; eauto.
    }
    subst x1.
    eapply legal_com_safety_property in H5; eauto.
    2 : unfold legal_com; rewrite H9; eauto.
    destruct H5 as (S'' & S2'' & HLP__' & Hstate_union' & HPr').
    lets Hcont : HLP__.

    split.
    do 6 eexists; eauto.

    intros.
    assert ((C, (S', pc +ᵢ ($ 4), x2)) = (C, (S0, pc1, npc1))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H7.
    assert ((C, (S3, pc2, npc2)) = (C, (S'', f +ᵢ ($ 8), f +ᵢ ($ 12)))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H7.
    clear H H5.

    destruct Hexec_prim as [Hexec_prim | Hexec_prim].
    {
      simpljoin1.
      do 2 eexists.
      split; eauto.
      split.
      simpl.
      do 6 eexists.
      split; eauto.

      exists f.
      split; eauto.
      clear - Hret Hstate_union'.
      unfolds get_R.
      destruct_state x0.
      destruct_state S2''.
      simpl in Hstate_union'; simpljoin1; simpls.
      destruct (r r15) eqn:Heqe; tryfalse.
      inv Hret.
      eapply get_vl_merge_still in Heqe; eauto.
      rewrite Heqe; eauto.
    }
    {
      lets Hexec_prim' : Hexec_prim.
      inv Hexec_prim'.
      inv H1.
      destruct H; tryfalse.
      eapply H in Hexec_prim; eauto.
      simpljoin1.
      do 2 eexists.
      split.
      right; eauto.
      split.
      simpl.
      do 6 eexists.
      split; eauto.

      exists f.
      split; eauto.
      clear - Hret Hstate_union'.
      destruct_state x0.
      destruct_state S2''.
      simpls; simpljoin1; simpls.
      unfolds get_R.
      destruct (r r15) eqn:Heqe; tryfalse.
      inv Hret.
      eapply get_vl_merge_still in Heqe; eauto.
      rewrite Heqe; eauto.
    }
  }
  {
    inv H.
  }
  {
    (** be f *)
    inv H.
    inv H4.
    lets Hcont : H10.
    eapply H19 in Hcont; eauto; clear H15 H17 H18 H19 H20.
    simpljoin1.
    lets Hcont : H.
    eapply H4 with (S2 := x) in Hcont; eauto; clear H4.
    simpljoin1.

    econstructor; try solve [intros; CElim C].
    intros.
    rewrite H10 in H9.
    inv H9.

    eapply legal_com_safety_property in H; eauto.
    2 : unfold legal_com; rewrite H10; eauto.
    destruct H as (S' & S2' & HLP__ & Hstate_union & HPr).
    assert (x1 = pc +ᵢ ($ 4)).
    {
      inv HLP__.
      inv H20; CElim C; eauto.
    }
    subst x1. 
    eapply legal_com_safety_property in H5; eauto.
    2 : unfold legal_com; rewrite H11; eauto.
    destruct H5 as (S'' & S2'' & HLP__' & Hstate_union' & HPr').

    split.
    do 6 eexists.
    split; eauto.

    intros.
    assert ((C, (S0, pc1, npc1)) = (C, (S', pc +ᵢ ($ 4), x2))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H9.
    assert ((C, (S3, pc2, npc2)) = (C, (S'', x3, x4))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H9; clear H H5.

    destruct H4; simpljoin1.
    {
      do 3 eexists.
      split; eauto.
      split; eauto.
      instantiate (1 := x5).
      clear - H2 H6.
      destruct_state S1.
      destruct_state S2.
      simpls; simpljoin1; simpls.
      unfolds get_R.
      destruct (r z) eqn:Heqe; tryfalse.
      inv H6.
      eapply get_vl_merge_still in Heqe; eauto.
      rewrite Heqe; eauto.

      split; intros.
      {
        eapply H7 in H.
        destruct H as (Fp & Fq & L & r & H); simpljoin1.
        assert (Nat.pred (w1 + w2) = Nat.pred w1 + w2).
        destruct w1; omega.
        exists Fp Fq L (r ⋆ Pr).
        split; eauto.
        split.
        eapply sep_star_assoc.
        eapply sep_star_hold; eauto.

        split.
        intros.
        eapply sep_star_assoc in H15.
        eapply sep_star_imply; eauto.
        split; eauto.
        simpl; eauto.
        split; eauto.
        omega.
      }
      {
        lets Hv : H.
        inv HLP__.
        inv H19; CElim C.
        clear - H2 H6 H15 H24 H25.
        destruct_state S1.
        destruct_state S2.
        simpls; simpljoin1.
        unfolds get_R.
        destruct (r z) eqn:Heqe; tryfalse.
        inv H6.
        eapply regz_exe_delay_stable with (v := W ($ 0)) in H15; eauto.
        2 : eapply get_vl_merge_still; eauto.
        rewrite H15 in H24; simpls.
        inv H24; tryfalse.
        
        inv HLP__'.
        inv H22; CElim C.
        eapply IHI; eauto.
        rewrite Int.add_assoc; eauto.
      }
    }
    {
      lets Hexec_prim : H.
      inv H.
      inv H1.
      destruct H; tryfalse.
      eapply H in Hexec_prim; eauto.
      clear H; simpljoin1.

      do 3 eexists.
      split.
      right; eauto.
      split.
      instantiate (1 := x5).
      clear - H6 H2.
      destruct_state S1.
      destruct_state S2.
      simpls; simpljoin1; simpls.
      unfolds get_R.
      destruct (r z) eqn:Heqe; tryfalse.
      inv H6.
      eapply get_vl_merge_still in Heqe; eauto.
      rewrite Heqe; eauto.

      split.
      {
        intros.
        eapply H7 in H9.
        destruct H9 as (Fp & Fq & L & r & HSpec & HFp & HFq & HGoodFrm & Hw1 & Hnpc); subst.
        assert (Nat.pred (w1 + w2) = Nat.pred w1 + w2).
        {
          destruct w1; try omega.
        }
        exists Fp Fq L (r ⋆ Pr).
        split; eauto.
        split.
        eapply sep_star_assoc.
        rewrite H9.
        eapply sep_star_hold; eauto.

        split; intros.
        eapply sep_star_assoc in H13.
        eapply sep_star_imply; eauto.

        split; eauto.
        simpl; eauto.

        split; eauto.
        omega.
      }
      {
        intros.
        lets Hrel_safety_insSeq : H9.
        eapply H8 in Hrel_safety_insSeq; eauto; subst.
        inv HLP__.
        inv H21; CElim C.
        clear - H2 H6 H17 H27 H28.
        destruct_state S1.
        destruct_state S2.
        simpl in H2; simpljoin1; simpls.
        unfolds get_R.
        destruct (r z) eqn:Heqe; tryfalse.
        inv H6.
        eapply regz_exe_delay_stable with (v := W ($ 0)) in H17; eauto.
        2 : eapply get_vl_merge_still; eauto.
        rewrite H17 in H27; eauto.
        inv H27; tryfalse.

        inv HLP__'.
        inv H25; CElim C.
        eapply IHI; eauto.
        rewrite Int.add_assoc; eauto.
        econstructor; eauto.
      }
    }
  }
  {
    inv H.
  }
Qed.

Lemma rel_safety_insSeq_conseq :
  forall I Spec C pc npc S Q Q' w A HS,
    LookupXC C pc I ->
    rel_safety_insSeq Spec w (C, S, pc, npc) (A, HS) Q -> Q ⇒ Q' ->
    rel_safety_insSeq Spec w (C, S, pc, npc) (A, HS) Q'.
Proof.
Admitted.

(* soundness of seqence rule *)
Lemma wf_seq_rule_relsound :
  forall P P' i Q f Spec I,
    rel_ins_sound (P ⤈) P' i -> insSeq_rel_sound Spec P' f +ᵢ ($ 4) I Q ->
    insSeq_rel_sound Spec P f (i;; I) Q.
Proof.
  intros.
  unfolds insSeq_rel_sound, rel_ins_sound; intros.
  inv H1.
  econstructor; try solve [intros; CElim C].

  intros.
  rewrite H7 in H1; inv H1.
  destruct_state S.
  assert (exists R' D', exe_delay r d = (R', D')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H1 as (R' & D' & Hexe_delay).
  lets HP_nxt : Hexe_delay.
  symmetry in HP_nxt.
  eapply dly_reduce_relasrt_stable in HP_nxt; eauto.
  eapply H in HP_nxt; simpljoin1.

  split.
  (* Progress *)
  exists x (f +ᵢ ($ 4)) (f +ᵢ ($ 4)) +ᵢ ($ 4).
  destruct_state x.
  econstructor; eauto.
  eapply LNTrans; eauto.

  (* preservation *)
  intros.
  inv H4.
  eapply dly_reduce_relasrt_stable in H15; eauto.
  inv H19; CElim C.
  eapply H in H15; simpljoin1.
  assert (x0 = (LM', (LR'', F'), D'')).
  {
    eapply lemmas_ins.ins_exec_deterministic; eauto.
  }
  subst.
  left.
  eapply H0; eauto.
Qed.

(* soundness of call rule *)
Lemma wf_call_rule_relsound :
  forall f f' Spec Fp Fq P P1 P2 Pr P' v i Q L I,
    Spec f' = Some (Fp, Fq) -> P ⤈ ⇒ RAlst (r15 |=> v) ⋆ P1 ->
    rel_ins_sound ((RAlst (r15 |=> W f) ⋆ P1) ⤈) (P2 ⋆ RAtoken 1%nat) i ->
    P2 ⇒ Fp L ⋆ Pr -> Fq L ⋆ Pr ⇒ P' -> Fq L ⇒ RAlst (Or r15 ==ₑ W f) -> GoodFrm Pr ->
    insSeq_rel_sound Spec P' f +ᵢ ($ 8) I Q ->
    insSeq_rel_sound Spec P f (call f'#i#I) Q.
Proof.
  intros.
  unfold insSeq_rel_sound; intros.
  inv H7.
  econstructor; try solve [intros; CElim C].

  intros.
  rewrite H14 in H7; inv H7.
  unfold rel_ins_sound in H1.

  split.
  (* progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r d = (R', D')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H7 as (R' & D' & Hexe_delay).
  lets HP_nxt : Hexe_delay.
  symmetry in HP_nxt.
  eapply dly_reduce_relasrt_stable in HP_nxt; eauto.
  eapply H0 in HP_nxt.
  lets Hreg_ret : HP_nxt.
  eapply reg_vl_rel_change with (v1 := W f) in HP_nxt.
  assert (exists R'' D'', exe_delay (set_R R' r15 (W f)) D' = (R'', D'')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H7 as (R'' & D'' & Hexe_delay').
  lets HP_nxt' : Hexe_delay'.
  symmetry in HP_nxt'.
  eapply dly_reduce_relasrt_stable in HP_nxt'; eauto.
  eapply H1 in HP_nxt'; eauto.
  simpljoin1.
  destruct_state x.
  do 6 eexists.
  split.
  {
    econstructor; eauto.
    eapply LCall; eauto.
    clear - Hreg_ret.
    simpls.
    simpljoin1.
    destruct_state x1.
    destruct_state x2.
    simpls; simpljoin1.
    unfolds regSt; simpls; simpljoin1.

    unfold indom, merge.
    rewrite RegMap.gss; eauto.
  }
  {
    econstructor; eauto.
    eapply LNTrans; eauto.
  }

  (* preservation *)
  intros.
  inv H7.
  inv H22; CElim C.
  inv H9.
  inv H25; CElim C.
  symmetry in H18.
  eapply dly_reduce_relasrt_stable in H8; eauto.
  eapply H0 in H8.
  eapply reg_vl_rel_change with (v1 := W f) in H8; eauto.
  eapply dly_reduce_relasrt_stable in H8; eauto.
  eapply H1 in H8.
  simpljoin1.
  assert (x = (LM'0, (LR'', F'0), D''0)).
  {
    eapply ins_exec_deterministic; eauto.
  }
  subst x.
  assert (Hw : w > 0%nat).
  {
    clear - H8.
    simpl in H8.
    simpljoin1.
    destruct x0.
    destruct p.
    destruct p; simpljoin1.
    omega.
  }
  exists Fp Fq L Pr A HS.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.

  split.
  left; eauto.
  eapply token_consume in H8.
  assert (w - 1 = Nat.pred w).
  {
    destruct w; omega.
  }
  rewrite H9 in H8.
  eapply H2 in H8.
  split; eauto.
  split; eauto.

  split.
  intros.
  eapply H3 in H10.
  unfold insSeq_rel_sound in H6.
  eapply H6 in H10; eauto.
  rewrite Int.add_assoc in H10; eauto.

  intros.
  eapply H4 in H10.
  clear - H10.
  simpls; simpljoin1; eauto.
Qed.

Lemma wf_insSeq_rel_soundness :
  forall (I : InsSeq) Spec P Q f,
    Spec ⊩ {{ P }} f # I {{ Q }} ->
    insSeq_rel_sound Spec P f I Q.
Proof.
  intros.
  induction H; intros.
  {
    (* seq rule *)
    eapply wf_ins_rel_soundness in H.
    eapply wf_seq_rule_relsound; eauto.
  }
  {
    (* call rule *)
    eapply wf_ins_rel_soundness in H1.
    eapply wf_call_rule_relsound; eauto.
  }  
Admitted.

(** Well formed CodeHeap Soundness *)
Lemma wf_cdhp_rel_sound : forall Spec C,
    rel_wf_cdhp Spec C -> cdhp_rel_sound Spec C.
Proof.
  intros.
  unfolds rel_wf_cdhp, cdhp_rel_sound; intros.
  eapply H with (L := L) in H0; eauto; simpljoin1.
  exists x.
  split; eauto.
  eapply wf_insSeq_rel_soundness; eauto.
Qed.

(** Functional Safety *)
Fixpoint WFST (Q : relasrt) (Kq : list relasrt) (Spec : Funspec) (C : XCodeHeap) :=
  match Kq with
  | nil => (Q ⇒ RAprim Pdone ⋆ RAtrue)
  | Q' :: Kq' => forall S HS A w, (S, HS, A, w) ||= Q -> (forall Pr, GoodFrm Pr -> Sta A Pr) ->
                              exists f I, (getregs S) r15 = Some (W f) /\ LookupXC C (f +ᵢ ($ 8)) I /\ 
                                   rel_safety_insSeq Spec w
                                                     (C, S, f +ᵢ ($ 8), f +ᵢ ($ 12)) (A, HS) Q' /\
                                   WFST Q' Kq' Spec C
  end.

CoInductive rel_safety_WFST : Index -> (XCodeHeap * State * Word * Word) -> (primcom * HState) ->
                              relasrt -> list relasrt -> Funspec -> Prop :=
| cons_safety : forall idx C S pc npc A HS Q Kq Spec,  
    legal_com (C pc) -> legal_com (C npc) -> WFST Q Kq Spec C -> 
    (* not call ret *)
    (
      forall f aexp rd i,
        (C pc = Some (c (cntrans i)) \/ C pc = Some (c (cjumpl aexp rd)) \/ C pc = Some (c (cbe f))) ->
        (
          (* progress *)
          exists S' pc' npc',
            LP__ (C, (S, pc, npc)) tau (C, (S', pc', npc'))
        ) /\
        (
          (* preservation *)
          forall S' pc' npc',
            LP__ (C, (S, pc, npc)) tau (C, (S', pc', npc')) ->
            (
              (
                exists idx1, (idx1 ⩹ idx) /\ rel_safety_WFST idx1 (C, S', pc', npc') (A, HS) Q Kq Spec
              )
              \/
              (
                exists HS' idx1, exec_prim (A, HS) (Pdone, HS')
                            /\ rel_safety_WFST idx1 (C, S', pc', npc') (Pdone, HS') Q Kq Spec
              )
            )
        )
    ) ->
    (* call *)
    (
      forall f,
        C pc = Some (c (ccall f)) ->
        (
          (* progress *)
          exists S1 S2 pc1 pc2 npc1 npc2,
            LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
            LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2))
        ) /\
        (
          (* preservation *)
          forall S1 S2 pc1 pc2 npc1 npc2,
            LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) ->
            LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2)) ->
            exists idx1 idx2 A' HS' Q0,
              ((idx1 ⩹ idx2 /\ idx2 ⩹ idx /\  A' = A /\ HS = HS') \/ (exec_prim (A, HS) (A', HS'))) /\
              rel_safety_WFST idx1 (C, S2, pc2, npc2) (A', HS') Q0 (Q :: Kq) Spec
        )
    ) ->
    (* retl *)
    (
      C pc = Some (c cretl) ->
      (
          (* progress *)
          exists S1 S2 pc1 pc2 npc1 npc2,
            LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
            LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2))
      ) /\
      (
          (* preservation *)
          forall S1 S2 pc1 pc2 npc1 npc2,
            LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) ->
            LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2)) ->
            exists idx1 idx2 A' HS' w ,
              ((idx1 ⩹ idx2 /\ idx2 ⩹ idx /\ A' = A /\ HS = HS') \/ (exec_prim (A, HS) (A', HS'))) /\
              (S2, HS', A', w) ||= Q /\ 
              (
                (Kq = nil /\ A' = Pdone /\ (0%nat, (0%nat, 0%nat)) ⩹ idx1 /\
                 (exists f', getregs S2 r15 = Some (W f') /\ pc2 = f' +ᵢ ($ 8) /\ npc2 = f' +ᵢ ($ 12))) \/
                (exists Q' Kq', Kq = Q' :: Kq' /\ rel_safety_WFST idx1 (C, S2, pc2, npc2) (A', HS') Q' Kq' Spec)
              )
      )
    ) ->
    rel_safety_WFST idx (C, S, pc, npc) (A, HS) Q Kq Spec.

Lemma function_correctness_aux' :
    forall Q Spec S HS A pc I C Kq w,
      rel_safety_insSeq Spec w (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q -> 
      LookupXC C pc I ->  WFST Q Kq Spec C -> cdhp_rel_sound Spec C ->
      (forall Pr, GoodFrm Pr -> Sta A Pr) ->
      rel_safety_WFST (w, (length Kq, (1 + get_insSeqLen I)%nat)) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q Kq Spec.
Proof.
  cofix Hp; intros.
  rename H3 into Hwdprim.
  econstructor; intros; eauto.
  {
    eapply LookupXC_hold_legal_com in H0; eauto; simpljoin1; eauto.
  }
  {
    eapply LookupXC_hold_legal_com in H0; eauto; simpljoin1; eauto.
  }
  {
    (* C pc = i \/ C pc = jmpl aexp rd \/ C pc = cbe f *)
    inv H.
    destruct H3.
    {
      (* C pc = i *)
      lets Hcom : H.
      eapply H12 in H; clear H12 H14 H15 H16 H17.
      simpljoin1.
      inv H0; CElim C.
      
      split.
      do 3 eexists; eauto.

      intros.
      assert (pc' = pc +ᵢ ($ 4) /\ npc' = (pc +ᵢ ($ 4)) +ᵢ ($ 4)).
      {
        inv H0.
        inv H14; CElim C.
        eauto.
      }
      eapply H3 in H0; eauto.
      destruct H0; simpljoin1.
      left.
      exists (w, (length Kq, (1 + get_insSeqLen I0)%nat)).
      split.
      unfold LtIndex.
      do 2 eapply lex_ord_right.
      simpl; unfold Nat.lt.
      omega.
      eapply Hp; eauto.

      right.
      exists x2 (w, (length Kq, (1 + get_insSeqLen I0)%nat)).
      split; eauto.
      eapply Hp; eauto.
      intros.
      econstructor; eauto.
    }
    destruct H.
    {
      (* C pc = jmpl aexp rd *)
      lets Hcom : H.
      eapply H15 in H; clear H12 H14 H15 H16 H17.
      inv H0; CElim C.
      simpljoin1.
      split.
      do 3 eexists; eauto.

      intros.
      left.
      exists (w, (length Kq, 2%nat)).
      split; simpl.
      unfold LtIndex.
      do 2 eapply lex_ord_right; eauto.

      assert ((C, (x, x1, x2)) = (C, (S', pc', npc'))).
      {
        eapply LP_deterministic; eauto.
        simpl; eauto.
      }
      inv H6.
      assert (pc' = pc +ᵢ ($ 4)).
      {
        inv H.
        inv H15; CElim C; eauto.
      }
      subst. 

      eapply H0 with (S1 := S') in H5; eauto. 
      destruct H5 as (Fp & Fq & L & r & A' & HS' & Hh_exec & HSpec & Hfpre & Hfpost & HGoodFrm & Hw & Hnpc).
      renames x3 to f', x4 to pc'; subst.
      simpl in Hfpre.
      destruct Hfpre as (HS1 & HS2 & S1 & S2 & w1 & w2 & Hhstate_union & Hstate_union & Hw' & HFp & Hr).
      lets Hnxt_block : H2.
      unfold cdhp_rel_sound in Hnxt_block.
      lets Hnxt_block_ver : HSpec. 
      eapply Hnxt_block with (L := L) in Hnxt_block_ver; eauto.
      destruct Hnxt_block_ver as (I0 & HlookupI0 & HI0_sound).
      assert (npc' = f').
      {
        inv H3.
        inv H14; CElim C; eauto.
      }
      subst npc'.
 
      econstructor; eauto.
      {
        unfold legal_com; rewrite H4; eauto.
      }
      {        
        eapply LookupXC_hold_legal_com in HlookupI0; eauto.
        simpljoin1; eauto.
      }
      {
        intros.
        destruct H5.
        rewrite H4 in H5; inv H5.
 
        split. 
        do 3 eexists; eauto.
        intros.
        assert ((C, (S'0, pc', npc')) = (C, (x0, f', f' +ᵢ ($ 4)))).
        { 
          eapply LP_deterministic; eauto.
          simpl; eauto.
        }
        inv H6.
        clear H5.
        unfold insSeq_rel_sound in HI0_sound.
        lets Hrel_safety_insSeq' : HlookupI0.
        eapply HI0_sound in Hrel_safety_insSeq'; eauto.
         
        destruct Hh_exec as [Hh_exec | Hh_exec]; simpljoin1; subst.
        (* high-level doesn't execute *)
        left. 
        exists (Nat.pred w, (length Kq, (1 + get_insSeqLen I0)%nat)).
        split.
        econstructor; eauto.
        unfold Nat.lt.
        destruct w; omega.

        eapply Hp; eauto.
        eapply rel_safety_insSeq_frame_property with (w2 := w2) (Pr := r) in Hrel_safety_insSeq'; eauto.
        rewrite <- Hw' in Hrel_safety_insSeq'.
        eapply rel_safety_insSeq_conseq; eauto.

        (* high-level executes *)
        right.
        exists HS' (Nat.pred w, (length Kq, (1 + get_insSeqLen I0)%nat)).
        assert (A' = Pdone).
        {
          clear - Hh_exec.
          inv Hh_exec; eauto.
        } 
        subst A'.
        split; eauto.
        eapply rel_safety_insSeq_frame_property with (w2 := w2) (Pr := r) in Hrel_safety_insSeq'; eauto.
        rewrite <- Hw' in Hrel_safety_insSeq'.
        eapply Hp; eauto.
        eapply rel_safety_insSeq_conseq; eauto.
        intros.
        econstructor; eauto.
        econstructor; eauto.

        (* contradiction case *)
        destruct H5; CElim C.
      }

      (* contradiction cases *)
      intros; CElim C.
      intros; CElim C.
    }
    {
      (* C pc = cbe f *)
      lets Hcom : H.
      eapply H16 in H; clear H12 H14 H15 H16 H17.
      simpljoin1.
      split.
      do 2 eexists; eauto.

      intros.
      assert ((C, (x, x1, x2)) = (C, (S', pc', npc'))).
      {
        eapply LP_deterministic; eauto.
        simpl; eauto.
      }
      inv H6.
      assert (pc' = pc +ᵢ ($ 4)).
      {
        inv H5.
        inv H15; CElim C; eauto.
      }
      subst pc'.
      inv H0; CElim C.
      left.
      exists (w, (length Kq, (2 + get_insSeqLen I0)%nat)).
      split.
      do 2 eapply lex_ord_right.
      unfold Nat.lt; simpl; eauto.

      econstructor; eauto.
      {
        unfold legal_com; rewrite H7; eauto.
      }
      {
        inv H5.
        inv H16; CElim C. 

        lets Hcont : H.
        eapply H3 with (pc1 := pc +ᵢ ($ 4)) in Hcont; eauto.
        simpljoin1.
        eapply regz_exe_delay_stable with (v := W x) in H12; eauto.
        unfold get_R in H21; rewrite H12 in H21; inv H21; subst.
        eapply H6 in H22.
        destruct H22 as (Fp & Fq & L & r & HSpec & Hfpre & Hfq & HGoodFrm & Hw & Hnpc); subst.
        unfold cdhp_rel_sound in H2.
        eapply H2 with (L := L) in HSpec; simpljoin1.
        assert (x3 = npc').
        {
          inv H4.
          inv H25; CElim C; eauto.
        }
        subst x3.
        eapply LookupXC_hold_legal_com in H10; simpljoin1; eauto.
        clear - H5; simpls.
        unfolds get_R.
        destruct (LR z) eqn:Heqe; tryfalse.
        inv H5; eauto.

        eapply LookupXC_hold_legal_com in H8; eauto.
        simpljoin1; eauto.
        rewrite Int.add_assoc; eauto.
      }
      {
        intros.
        destruct H0.

        assert (x3 = npc' /\ x4 = npc' +ᵢ ($ 4)).
        {
          inv H4.
          inv H17; CElim C; eauto.
        }
        destruct H6; subst.

        split.
        do 3 eexists; eauto.
        intros.
        assert ((C, (x0, npc', npc' +ᵢ ($ 4))) = (C, (S'0, pc', npc'0))).
        {
          eapply LP_deterministic; eauto.
          simpl; eauto.
        }
        inv H9.
        rewrite H7 in H0; inv H0.
        eapply H3 with (S1 := S') in H6; eauto.
        clear H5.
        destruct H6 as (v & A' & HS' & Hexec_prim & Hz & Hv_not_0 & Hv_0).
        (* high-level doesn't execute *)
        destruct Hexec_prim as [Hexec_prim | Hexec_prim]; simpljoin1.
        left.
        destruct (classic (v = $ 0)).
        {
          lets Hrel_safety_insSeq : H0.
          eapply Hv_0 in Hrel_safety_insSeq; eauto.
          exists (w, (length Kq, 1 + get_insSeqLen I0)%nat).
          split.
          do 2 eapply lex_ord_right.
          unfold Nat.lt; omega.
          eapply Hp; eauto.
          inv H.
          inv H16; CElim C. 
          clear - Hz H20 H12 H21; simpls.
          unfolds get_R.
          destruct (LR z) eqn:Heqe; tryfalse.
          eapply regz_exe_delay_stable in H12; eauto.
          inv Hz.
          rewrite H12 in H20; simpls; tryfalse.
          rewrite Int.add_assoc; eauto.
        }
        {
          lets Hcont : H0.
          eapply Hv_not_0 in Hcont; eauto.
          destruct Hcont as (Fp & Fq & L & r & HSpec & HFp & HFq & HGoodFrm & Hw & Hpc').
          simpl in HFp.
          destruct HFp as (HS1 & HS2 & S1 & S2 & w1 & w2 & Hhstate_union & Hstate_union & Hw' &
                           HFp & Hr).
          lets Hcdhp_rel_sound : H2.
          unfold cdhp_rel_sound in Hcdhp_rel_sound.
          eapply Hcdhp_rel_sound with (L := L) in HSpec; clear Hcdhp_rel_sound.
          destruct HSpec as (I' & HlookupXC_I' & HinsSeq_rel_sound).
          exists (Nat.pred w, (length Kq, (1 + get_insSeqLen I')%nat)).

          split.
          econstructor; eauto.
          unfold Nat.lt; destruct w; omega.

          unfold insSeq_rel_sound in HinsSeq_rel_sound.
          eapply HinsSeq_rel_sound in HFp; eauto.
          eapply rel_safety_insSeq_frame_property with (Pr := r) in HFp; eauto.
          eapply rel_safety_insSeq_conseq with (Q' := Q) in HFp; eauto.
          eapply Hp; eauto.
          rewrite Hw'; eauto.
        }

        (* high-level executes *)
        assert (A' = Pdone).
        {
          inv Hexec_prim; eauto.
        }
        subst A'.
        right.
        destruct (classic (v = $ 0)).
        {
          lets Hrel_safety_insSeq : H0.
          eapply Hv_0 in Hrel_safety_insSeq; eauto.
          exists HS' (w, (length Kq, 1 + get_insSeqLen I0)%nat).
          split; eauto.
          eapply Hp; eauto.
          inv H.
          inv H16; CElim C. 
          clear - Hz H20 H12 H21; simpls.
          unfolds get_R.
          destruct (LR z) eqn:Heqe; tryfalse.
          eapply regz_exe_delay_stable in H12; eauto.
          inv Hz.
          rewrite H12 in H20; simpls; tryfalse.
          rewrite Int.add_assoc; eauto.
          intros.
          econstructor; eauto.
        }
        {
          lets Hcont : H0.
          eapply Hv_not_0 in Hcont; eauto.
          destruct Hcont as (Fp & Fq & L & r & HSpec & HFp & HFq & HGoodFrm & Hw & Hpc').
          simpl in HFp.
          destruct HFp as (HS1 & HS2 & S1 & S2 & w1 & w2 & Hhstate_union & Hstate_union & Hw' &
                           HFp & Hr).
          lets Hcdhp_rel_sound : H2.
          unfold cdhp_rel_sound in Hcdhp_rel_sound.
          eapply Hcdhp_rel_sound with (L := L) in HSpec; clear Hcdhp_rel_sound.
          destruct HSpec as (I' & HlookupXC_I' & HinsSeq_rel_sound).
          exists HS' (Nat.pred w, (length Kq, (1 + get_insSeqLen I')%nat)).

          split; eauto.

          unfold insSeq_rel_sound in HinsSeq_rel_sound.
          eapply HinsSeq_rel_sound in HFp; eauto.
          eapply rel_safety_insSeq_frame_property with (Pr := r) in HFp; eauto.
          eapply rel_safety_insSeq_conseq with (Q' := Q) in HFp; eauto.
          eapply Hp; eauto.
          rewrite Hw'; eauto.
          intros.
          econstructor; eauto.
          econstructor; eauto.
        }

        destruct H0; CElim C.
      }
      {
        intros; CElim C.
      }
      {
        intros; CElim C.
      }
    }
  }
  {
    (* C pc = call f *)
    lets Hcom : H3.
    inv H. 
    eapply H14 in H3; eauto; clear H12 H14 H15 H16 H17; eauto.
    simpljoin1.

    split.
    do 6 eexists.
    split; eauto.

    assert (x1 = pc +ᵢ ($ 4) /\ x2 = f).
    {
      inv H.
      inv H14; CElim C; eauto.
    }
    destruct H5; subst x1 x2.
    inv H0; CElim C.

    intros.
    assert ((C, (x, pc +ᵢ ($ 4), f')) = (C, (S1, pc1, npc1))).
    { 
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H8.
    assert ((C, (S2, pc2, npc2)) = (C, (x0, x3, x4))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H8.
    clear H5.

    eapply H3 with (S1 := S1) in H0; eauto.
    destruct H0 as (Fp & Fq & L & r & A' & HS' & H0).
    simpljoin1.
    lets Hcdhp_spec : H2.
    unfold cdhp_rel_sound in Hcdhp_spec.
    lets Hnxt_block : H8.
    eapply Hcdhp_spec with (L := L) in Hnxt_block; clear Hcdhp_spec.
    destruct Hnxt_block as (I' & HlookupI' & HinsSeq_rel_sound).
    
    exists (Nat.pred w, (length (Q :: Kq), (1 + get_insSeqLen I')%nat))
      (w, (length Kq, (1 + get_insSeqLen I0)%nat)).
    unfold insSeq_rel_sound in HinsSeq_rel_sound.
    simpl in H11.
    destruct H11 as (HS1 & HS2 & S1' & S2' & w1 & w2 & Hhstate_union & Hstate_union & Hw' & Hfp & Hr).
    lets Hrel_safety_insSeq : Hfp. 
    eapply HinsSeq_rel_sound in Hrel_safety_insSeq; eauto.
    clear HinsSeq_rel_sound.

    destruct H10; simpljoin1.
    (* high-level doesn't execute *)
    exists A HS' (Fq L ⋆ r).
    split.
    left; eauto.
    split; eauto.
    econstructor; eauto.
    unfold Nat.lt.
    destruct w; omega.
    split; eauto.
    unfold LtIndex. 
    do 2 eapply lex_ord_right; eauto.
    eapply rel_safety_insSeq_frame_property with (w2 := w2) (Pr := r) in Hrel_safety_insSeq; eauto.
    rewrite <- Hw' in Hrel_safety_insSeq. 
    eapply Hp; eauto.
    unfold WFST.
    fold WFST.
    intros.
    lets Hret : H0. 
    eapply H13 in H0; eauto.
    simpl in Hret.
    simpljoin1.
    eapply H14 in H16.
    exists pc I0.
    split; eauto.
    destruct_state x2.
    destruct_state x3.
    simpl in H11.
    simpljoin1.
    simpls.
    eapply get_vl_merge_still; eauto.
    clear - H16.
    unfolds get_R.
    destruct (r0 r15) eqn:Heqe; tryfalse.
    inv H16; eauto.

    (* high-level execute *)
    assert (A' = Pdone).
    {
      inv H0; eauto.
    }
    subst A'.
    exists Pdone HS' (Fq L ⋆ r).
    split. 
    right; eauto.
    eapply rel_safety_insSeq_frame_property with (w2 := w2) (Pr := r) in Hrel_safety_insSeq; eauto.
    rewrite <- Hw' in Hrel_safety_insSeq.
    eapply Hp; eauto.
    unfold WFST; fold WFST; intros.
    lets Hret : H5.
    simpl in Hret.
    simpljoin1.
    eapply H13 in H5; eauto.
    eapply H14 in H17; eauto.
    exists pc I0.
    split; eauto.
    destruct_state x2.
    destruct_state x3.
    simpls; simpljoin1.
    simpl; eauto.
    clear - H17.
    unfolds get_R.
    destruct (r0 r15) eqn:Heqe; tryfalse.
    inv H17.
    eapply get_vl_merge_still; eauto.
    intros.
    econstructor; eauto.
    econstructor; eauto.
  }
  { 
    (* C pc = retl *)
    lets Hcom : H3.
    inv H.
    eapply H17 in H3; clear H12 H14 H15 H16 H17.
    simpljoin1.
    inv H0; CElim C.

    split.
    do 6 eexists.
    split; eauto.

    intros.
    assert ((C, (x, x1, x2)) = (C, (S1, pc1, npc1))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H7.
    assert (pc1 = pc +ᵢ ($ 4)).
    {
      inv H0.
      inv H16; CElim C; eauto.
    }
    subst pc1.
    assert ((C, (x0, x3, x4)) = (C, (S2, pc2, npc2))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H7.
    clear H5.

    eapply H3 with (S1 := S1) in H0; eauto.
    simpljoin1.
    destruct Kq as [ | Q' Kq'].
    {
      destruct H0; simpljoin1.
      (* high-level doesn't execute *)
      exists (w, (0%nat, 1%nat)) (w, (0%nat, 2%nat)).
      do 3 eexists.
      split.
      left; eauto.
      split; eauto.
      unfold LtIndex.
      do 2 eapply lex_ord_right; eauto.
      split; eauto.
      unfold LtIndex.
      do 2 eapply lex_ord_right; eauto.
      split; eauto.
      left.
      split; eauto.
      split.
      simpl in H1.
      eapply H1 in H5; eauto.
      simpljoin1.
      split.
      destruct w.
      unfold LtIndex.
      do 2 eapply lex_ord_right; eauto.
      econstructor; eauto.
      unfold Nat.lt; omega.
      exists x1.
      split; eauto.
      clear - H7.
      destruct_state S2; simpls.
      unfolds get_R.
      destruct (r r15) eqn:Heqe; tryfalse.
      inv H7; eauto.

      (* high-level execute *)
      exists (w, (0%nat, 1%nat)) (w, (0%nat, 2%nat)).
      do 3 eexists.
      split; eauto.
      split; eauto.
      left.
      split; eauto.
      assert (x = Pdone).
      {
        inv H0; subst; eauto.
      }
      subst x.
      split; eauto.
      split; eauto.
      destruct w.
      unfold LtIndex.
      do 2 eapply lex_ord_right; eauto.
      econstructor; eauto.
      unfold Nat.lt; omega.
      exists x1.
      split; eauto.
      clear - H7.
      unfolds get_R.
      destruct_state S2; simpls.
      destruct (r r15) eqn:Heqe; tryfalse.
      inv H7; eauto.
    }
    {
      unfold WFST in H1; fold WFST in H1.
      lets Hcont : H5.
      eapply H1 in Hcont; clear H1.
      destruct Hcont as (f' & I0' & Hget_ret & HlookupI0' & Hrel_safety_insSeq & Hwfst).
      assert (x1 = f').
      {
        clear - H7 Hget_ret.
        unfolds get_R.
        rewrite Hget_ret in H7; simpls.
        inv H7; eauto.
      }
      subst x1.
      exists (w, (length Kq', (1 + get_insSeqLen I0')%nat)) (w, (length (Q' :: Kq'), 1%nat)).

      destruct H0; simpljoin1.
      {
        do 3 eexists.
        split.
        left.
        split.
        simpl.
        eapply lex_ord_right.
        econstructor; eauto.
        split.
        do 2 eapply lex_ord_right.
        simpl.
        unfold Nat.lt; omega.
        split; eauto.

        split; eauto.
        right.
        do 2 eexists.
        split; eauto.
        assert (f' +ᵢ ($ 12) = (f' +ᵢ ($ 8)) +ᵢ ($ 4)).
        {
          rewrite Int.add_assoc; eauto.
        }
        rewrite H0.
        eapply Hp; eauto.
        rewrite <- H0; eauto.
      }
      {
        do 3 eexists.
        split.
        right; eauto.
        split; eauto.
        right.
        assert (x = Pdone).
        {
          inv H0; eauto.
        }
        subst x.
        do 2 eexists.
        split; eauto.
        assert (f' +ᵢ ($ 12) = (f' +ᵢ ($ 8)) +ᵢ ($ 4)).
        {
          rewrite Int.add_assoc; eauto.
        } 
        rewrite H1.
        eapply Hp; eauto.
        rewrite <- H1; eauto.
        intros. 
        econstructor; eauto.
      }

      destruct H0; simpljoin1; eauto.
      inv H0.
      intros.
      econstructor; eauto.
    }
  }
Qed.

Lemma function_correctness_aux :
  forall P Q Spec S HS A w pc I C Kq,
    insSeq_rel_sound Spec P pc I Q -> LookupXC C pc I ->
    cdhp_rel_sound Spec C -> (S, HS, A, w) ||= P -> WFST Q Kq Spec C ->
    (forall Pr, GoodFrm Pr -> Sta A Pr) ->
    rel_safety_WFST (w, (length Kq, (1 + get_insSeqLen I)%nat)) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q Kq Spec.
Proof.
  intros.
  unfolds insSeq_rel_sound.
  lets Hrel_safety_insSeq : H0.
  eapply H in Hrel_safety_insSeq; clear H; eauto.
  eapply function_correctness_aux'; eauto.
Qed. 

Lemma rel_safety_WFST_impl_rel_safety :
  forall idx C S pc npc A HS Q Kq Spec Q',
    rel_safety_WFST idx (C, S, pc, npc) (A, HS) Q Kq Spec ->
    Q' = last Kq Q ->
    rel_safety (length Kq) idx (C, S, pc, npc) (A, HS) Q'.
Proof.
  cofix Hp; intros.
  inv H.
  econstructor; intros; eauto.
  {
    (* C pc = i \/ jmpl aexp rd \/ be f *)
    clear H15 H16.
    eapply H14 in H.
    simpljoin1.
    split; eauto.

    intros.
    eapply H0 in H1; eauto.
    destruct H1.
    {
      simpljoin1; left.
      exists x2.
      split; eauto.
    }
    {
      simpljoin1.
      right.
      exists x2 x3.
      eauto.
    }
  }
  {
    (* C pc = call f *)
    clear H14 H16.
    eapply H15 in H.
    simpljoin1.
    split.
    do 6 eexists.
    split; eauto.

    intros.
    eapply H0 with (S1 := S1) in H2; eauto.
    simpljoin1.
    destruct H2.
    do 4 eexists.
    split; eauto.
    assert ((Nat.succ (length Kq) = length (Q :: Kq))%nat); eauto.
    rewrite H5.
    eapply Hp; eauto.
    eapply last_Kq_cons_Q_same; eauto.

    do 4 eexists.
    split; eauto.
    assert ((Nat.succ (length Kq) = length (Q :: Kq))%nat); eauto.
    rewrite H5.
    eapply Hp; eauto.
    eapply last_Kq_cons_Q_same; eauto.
  }
  {
    (* C pc = retl *)
    eapply H16 in H; clear H14 H15 H16.
    simpljoin1.
    split; eauto.
    do 6 eexists; eauto.

    intros. 
    eapply H0 with (S1 := S1) in H2; eauto; simpljoin1.
    do 6 eexists. 
    destruct H2; eauto.
    instantiate (1 := x9).
    destruct H5; simpljoin1.
    {
      left.
      repeat (split; eauto).
    }
    {
      right.
      split; eauto.
      assert ((Nat.pred (length (x10 :: x11)) = length x11)%nat); eauto.
      rewrite H5; eauto.
      assert (last x11 x10 = last (x10 :: x11) Q).
      eapply last_Kq_cons_Q_same; eauto.
      rewrite <- H7.
      eapply Hp; eauto.
    }
  }
  Unshelve.
  exact (5%nat, (6%nat, 6%nat)).
Qed.
   
Theorem function_correctness :
  forall P Q Spec S HS A w pc I C,
    insSeq_rel_sound Spec P pc I Q -> LookupXC C pc I ->
    cdhp_rel_sound Spec C -> (S, HS, A, w) ||= P -> Q ⇒ RAprim Pdone ⋆ RAtrue ->
    (forall Pr, GoodFrm Pr -> Sta A Pr) ->
    rel_safety 0%nat (w, (0%nat, (1 + get_insSeqLen I)%nat)) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q.
Proof.
  intros.
  eapply function_correctness_aux with (Kq := nil) in H; eauto.
  eapply rel_safety_WFST_impl_rel_safety in H; eauto.
Qed.
