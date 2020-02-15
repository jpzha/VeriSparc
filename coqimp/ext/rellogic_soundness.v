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
Lemma ImplyPrim'_trans :
  forall P R Q,
    ImplyPrim' P R -> ImplyPrim' R Q -> ImplyPrim' P Q.
Proof.
  intros.
  unfolds ImplyPrim'; intros.
  eapply H in H1; eauto.
  destruct H1.
  {
    simpljoin1.
    lets Hexec_prim : H1.
    inv H1.
    eapply H0 in H3; eauto.
    2 : intros; econstructor; eauto.
    destruct H3; simpljoin1.
    inv H1.
    left.
    do 3 eexists.
    split; eauto.
  }
  {
    eapply H0 in H1; eauto.
  }
Qed.

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

Lemma sep_star_ImplyPrim'_hold :
  forall P Q Pr,
    ImplyPrim' P Q -> GoodFrm Pr ->
    ImplyPrim' (P ⋆ Pr) (Q ⋆ Pr).
Proof.
  intros.
  unfolds ImplyPrim'; intros.
  simpl in H1.
  simpljoin1.
  eapply H in H5; eauto.
  destruct H5; simpljoin1.
  {
    lets Hexec_prim : H4.
    inv H4.
    eapply H2 in H0.
    inv H0.
    destruct H4; tryfalse.
    eapply H0 in Hexec_prim; eauto.
    simpljoin1.
    left.
    do 3 eexists.
    split; eauto.
    eapply sep_star_hold; eauto.
  }
  {
    right.
    eapply sep_star_hold; eauto.
  }
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
        destruct Hcont as (HS1' & w' & Hexec_prim & Hrel_safety_insSeq).
        lets Hexec_prim' : Hexec_prim.
        inv Hexec_prim'.
        inv H1.
        destruct H; tryfalse.
        assert (Pm prim lv = Pm prim lv).
        eauto.
        eapply H in H1; eauto.
        destruct H1 as (HS' & HS2' & Hexec_prim' & Hhstate_union' & HPr'').
        right.
        exists HS' (w' + w2).
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
    destruct Hcont as (Fp & Fq & L & r & A' & HS1' & w' & Hexec_prim & HSpec & HFp & HGoodFrm & HFq & Hw1 & Hnpc).
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
      exists (w' + w2).
      split.
      left; eauto.
      split; eauto.
      split; eauto.
      assert (Nat.pred (w' + w2) = Nat.pred w' + w2).
      {
        destruct w'; try omega; eauto.
      }
      rewrite H.
      eapply sep_star_assoc.
      eapply sep_star_hold; eauto.
      split; simpl; eauto.
      split.
      eapply sep_star_ImplyPrim'_hold with (Pr := Pr) in HFq; eauto.
      clear - HFq.
      unfolds ImplyPrim'; intros.
      eapply sep_star_assoc in H; eauto.
      split; simpl; eauto.
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
      exists (w' + w2).
      split.
      right; eauto.
      split; eauto.
      split; eauto.

      assert (Nat.pred (w' + w2) = Nat.pred w' + w2).
      {
        destruct w'; try omega; eauto.
      }
      rewrite H.
      eapply sep_star_assoc.
      eapply sep_star_hold; eauto.

      split.
      simpl; eauto.
      split.
      eapply sep_star_ImplyPrim'_hold with (Pr := Pr) in HFq; eauto.
      clear - HFq.
      unfolds ImplyPrim'; intros.
      eapply sep_star_assoc in H.
      eapply HFq; eauto.
 
      split; eauto.
      omega.
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
    destruct Hcont as (Fp & Fq & L & r & A' & HS1' & w'' & Hcont).
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
    assert (Nat.pred (w'' + w2) = Nat.pred w'' + w2).
    {
      destruct w''; simpls; try omega.
    }

    destruct H9; simpljoin1.
    { 
      exists Fp Fq L (r ⋆ Pr) A HS.
      exists (w1 + w2).
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
      exists (w'' + w2).
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
    lets Hcont1 : H.
    lets Hcont2 : H5.

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
    lets Hcont' : HLP__.

    split.
    do 6 eexists; eauto.
 
    intros. 
    eapply H4 with (S2 := x) in Hcont1; eauto.  
    destruct Hcont1 as (A' & HS1' & w' & Hexec_prim & HQ & f & Hret & Hpc & Hnpc); subst.
    assert ((C, (S', pc +ᵢ ($ 4), x2)) = (C, (S0, pc1, npc1))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H8.
    assert ((C, (S3, pc2, npc2)) = (C, (S'', f +ᵢ ($ 8), f +ᵢ ($ 12)))).
    {
      eapply LP_deterministic; eauto.
      simpl; eauto.
    }
    inv H8.
    clear H H5.

    destruct Hexec_prim as [Hexec_prim | Hexec_prim].
    {
      simpljoin1.
      do 3 eexists.
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
      do 3 eexists.
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
      do 4 eexists.
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
        assert (Nat.pred (x8 + w2) = Nat.pred x8 + w2).
        destruct x8; omega.
        exists Fp Fq L (r ⋆ Pr).
        split; eauto.
        split.
        eapply sep_star_assoc.
        eapply sep_star_hold; eauto.

        split.
        eapply sep_star_ImplyPrim'_hold with (Pr := Pr) in H5; eauto.
        clear - H5.
        unfolds ImplyPrim'; intros.
        eapply sep_star_assoc in H; eauto.
        split.
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

      do 4 eexists.
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
        assert (Nat.pred (x8 + w2) = Nat.pred x8 + w2).
        {
          destruct w1; try omega.
        }
        exists Fp Fq L (r ⋆ Pr).
        split; eauto.
        split.
        eapply sep_star_assoc.
        rewrite H9.
        eapply sep_star_hold; eauto.

        split.
        eapply sep_star_ImplyPrim'_hold with (Pr := Pr) in HFq; eauto.
        clear - HFq; unfolds ImplyPrim'; intros.
        eapply sep_star_assoc in H; eauto.

        split; simpl; eauto.
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
  forall I Spec C pc S Q Q' w A HS,
    LookupXC C pc I ->
    rel_safety_insSeq Spec w (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q -> ImplyPrim' Q Q' ->
    rel_safety_insSeq Spec w (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q'.
Proof.
  induction I; intros;
    match goal with
    | H : LookupXC _ _ _ |- _ => inv H
    end.
  {
    (* i *)
    econstructor; intros; try solve [CElim C].
    rewrite H6 in H; inv H.
    inv H0.
    lets Hcom : H6.
    eapply H11 in H6; clear H11 H13 H14 H15 H16.
    simpljoin1.
    split; eauto.
    intros.
    lets HLP__ : H2.
    inv HLP__. 
    inv H13; CElim C.
    eapply H0 in H2. 
    destruct H2; eauto.

    simpljoin1.
    right.
    do 2 eexists.
    split; eauto.
  }
  {
    (* jmpl aexp rd; i *)
    inv H0.
    lets Hcont : H6.
    eapply H14 in Hcont; clear H11 H13 H14 H15 H16.
    econstructor; intros; try solve [CElim C].
    simpljoin1.
    split; eauto.
    do 6 eexists.
    split; eauto.

    intros.
    lets Hcont : H4.
    eapply H2 with (S1 := S1) in Hcont; eauto.
    inv H4.
    inv H17; CElim C.
    inv H5.
    inv H20; CElim C.

    destruct Hcont as (Fp & Fq & L & r & A' & HS' & w' & Hexe_prim & HSpec & HFp & HGoodFrm & HimplyPrim' &
                       Hw' & Hnpc).
    exists Fp Fq L r A' HS'.
    exists w'.
    destruct Hexe_prim as [Hexe_prim | Hexe_prim].
    {
      do 5 (split; eauto).
      eapply ImplyPrim'_trans; eauto.
    }
    {
      do 5 (split; eauto).
      eapply ImplyPrim'_trans; eauto.
    }
  }
  {
    (* call f *)
    inv H0.
    lets Hcont : H7.
    eapply H14 in Hcont; clear H12 H14 H15 H16 H17.
    simpljoin1.
    econstructor; intros; try solve [CElim C].
    split.
    do 6 eexists.
    split; eauto.

    intros.
    lets Hcont : H4.
    eapply H0 with (S1 := S1) in Hcont; eauto; clear H0.
    destruct Hcont as (Fp & Fq & L & r & A' & HS' & w' & Hcont).
    simpljoin1.
    rewrite H7 in H3; inv H3.

    exists Fp Fq L r A' HS'.
    exists w'.
    do 7 (split; eauto).
    split; eauto.

    intros.
    eapply H15 in H0; eauto.
    assert (pc +ᵢ ($ 12) = (pc +ᵢ ($ 8)) +ᵢ ($ 4)).
    {
      rewrite Int.add_assoc; eauto.
    }
    rewrite H6.
    eapply IHI; eauto.
    rewrite <- H6; eauto.
  }
  {
    (* retl *)
    inv H0.
    lets Hcont : H3.
    eapply H16 in Hcont; eauto; clear H11 H13 H14 H15 H16.
    simpljoin1.
    econstructor; intros; CElim C.
    split.
    do 6 eexists.
    split; eauto.

    intros.
    lets Hcont : H4.
    eapply H0 with (S1 := S1) in Hcont; eauto.
    destruct Hcont as (A' & HS' & w' & Hexe_prim & HQ & Hret).
    simpljoin1.
    unfolds ImplyPrim'.
    lets HQ' : HQ.
    destruct Hexe_prim as [Hexe_prim | Hexe_prim].
    {
      simpljoin1.
      eapply H1 in HQ'; eauto.
      destruct HQ'.
      {
        simpljoin1.
        exists x7 x6 x8.
        split; eauto.
      }
      {
        exists A HS' w.
        split; eauto.
      }
    }
    {
      lets Htmp : Hexe_prim.
      inv Htmp.
      exists Pdone HS' w'.
      split; eauto.
      split; eauto.
      eapply H1 in HQ'; eauto.
      2 : intros; econstructor; eauto.
      destruct HQ'; eauto.
      simpljoin1.
      inv H9.
    }
  }
  {
    (* be l *)
    econstructor; intros; CElim C.
    lets Hcont : H7.
    inv H0.
    eapply H16 in Hcont; eauto; clear H12 H14 H15 H16 H17.
    simpljoin1.
    split.
    do 6 eexists; eauto.
    intros.
    lets Hcont : H3.
    eapply H0 with (S1 := S1) in Hcont; eauto; clear H0. 
    destruct Hcont as (v & A' & HS' & w' & Hcont).
    simpljoin1. 
    exists v A' HS' w'.
    split; eauto.
    split; eauto.
    split; intros.
    {
      eapply H6 in H11.
      destruct H11 as (Fp & Fq & L & r & HSpec & HFp & Himpl & HGoodFrm & Hw & Hnpc); subst.
      exists Fp Fq L r.
      do 3 (split; eauto).
      eapply ImplyPrim'_trans; eauto.
    }
    {
      lets Hv : H11.
      eapply H10 in H11; subst.
      inv H3; CElim C.
      inv H21; CElim C.
      simpl in H5.
      eapply regz_exe_delay_stable2 with (v := W v) in H17; eauto.
      unfold get_R in H5; rewrite H17 in H5.
      inv H5; tryfalse.
      unfold get_R in H27.
      destruct (LR'' z) eqn:Heqe; tryfalse.
      inv H27; eauto.

      inv H4; CElim C.
      inv H24; CElim C.
      eapply IHI; eauto.
      rewrite Int.add_assoc; eauto.
    }
  }
Qed.

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
  exists w.
  do 5 (split; eauto).

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

Lemma wf_retl_rule_relsound :
  forall P P' Q Spec f i,
    rel_ins_sound ((P ⤈) ⤈) P' i ->
    P' ⭆ Q -> FretSta ((P ⤈) ⤈) P' ->
    insSeq_rel_sound Spec P f (retl ;; i) Q.
Proof.
  intros.
  unfolds insSeq_rel_sound; intros.
  inv H2.
  unfolds rel_ins_sound.
  econstructor; try solve [intros; CElim C].

  intros.
  rewrite H5 in H2; inv H2.
  unfold FretSta in H1.

  split.
  (* progress *)
  destruct_state S.
  assert (exists R' D', exe_delay r d = (R', D')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H2 as (R' & D' & Hexe_delay).
  lets HP_nxt : Hexe_delay.
  symmetry in HP_nxt.
  eapply dly_reduce_relasrt_stable in HP_nxt; eauto.
  assert (exists R'' D'', exe_delay R' D' = (R'', D'')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H2 as (R'' & D'' & Hexe_delay').
  lets HP_nxt' : Hexe_delay'.
  symmetry in HP_nxt'.
  eapply dly_reduce_relasrt_stable in HP_nxt'; eauto.
  lets Hfinal : HP_nxt'.
  eapply H in Hfinal; eauto.
  simpljoin1.
  lets Hret : HP_nxt'.
  eapply H1 in Hret; eauto.
  simpljoin1.
  simpl in H6, H7.
  destruct_state x.
  do 6 eexists.
  split.
  econstructor; eauto.
  eapply LRetl; eauto.
  unfold get_R.
  eapply exe_delay_general_reg_stable with (R' := R'') in Hexe_delay'.
  eapply Hexe_delay' in H6.
  rewrite H6; eauto.

  econstructor; eauto.
  eapply LNTrans; eauto.
 
  (* preservation *)
  intros.
  renames H6 to HSta.
  inv H2.
  inv H16; CElim C.
  inv H4.
  inv H19; CElim C. 
  eapply dly_reduce_relasrt_stable in H3; eauto.
  eapply dly_reduce_relasrt_stable in H3; eauto.
  lets HP' : H3.
  eapply H in HP'; eauto.
  simpljoin1.
  assert (x = (LM'0, (LR''0, F'0), D''0)).
  {
    eapply ins_exec_deterministic; eauto.
  }
  subst x.
  lets HP' : H4.
  eapply H0 in H4.
  
  destruct H4; simpljoin1.
  {
    lets Hexe_prim : H4.
    inv H4.
    exists Pdone x x1.
    do 2 (split; eauto).
    exists f0.
    split; eauto.

    eapply H1 in H3; eauto.
    simpls; simpljoin1.
    clear - H3 H4 H15 H22.
    symmetry in H15.
    eapply exe_delay_general_reg_stable with (r := r15) (v := W x0) in H15; eauto.
    eapply H15 in H3.
    unfolds get_R.
    rewrite H3 in H22; inv H22.
    rewrite H4; eauto.

    split; eauto.
    rewrite Int.add_assoc; eauto.
  }

  lets HQ : HP'.
  eapply H0 in HQ.
  destruct HQ as [HQ | HQ].
  {
    destruct HQ as (HS' & A' & w' & Hexec_prim & HQ).
    do 3 eexists.
    do 2 (split; eauto).

    simpl.
    eapply H1 in H3; eauto.
    simpl in H3; simpljoin1.
    symmetry in H15.
    eapply exe_delay_general_reg_stable with (r := r15) (v := W x) in H15; eauto.
    eapply H15 in H3.
    unfold get_R in H22; rewrite H3 in H22; inv H22.
    exists f0.
    unfold get_R; rewrite H6; eauto.
    do 2 (split; eauto).
    rewrite Int.add_assoc; eauto.
  }
  {
    do 3 eexists.
    split; eauto.
    split; eauto.
    eapply H1 in H3; eauto.
    simpl in H3; simpljoin1.
    exists f0.
    simpl; rewrite Int.add_assoc; split; eauto.
    symmetry in H15.
    eapply exe_delay_general_reg_stable with (r := r15) (v := W x) in H15; eauto.
    eapply H15 in H3.
    unfold get_R in H22; rewrite H3 in H22; inv H22.
    unfold get_R; rewrite H6; eauto.
  }
Qed.

Lemma wf_jmpl_rule_relsound :
  forall P P' aexp f' f Fp Fq P1 (r1 : GenReg) i Pr L v Q Spec,
    P ⤈ ⇒ RAlst (aexp ==ₓ W f') ->
    Spec f' = Some (Fp, Fq) -> P ⤈ ⇒ RAlst (r1 |=> v) ⋆ P1 ->
    rel_ins_sound ((RAlst (r1 |=> W f) ⋆ P1) ⤈) (P' ⋆ RAtoken 1) i ->
    P' ⇒ Fp L ⋆ Pr -> Fq L ⋆ Pr ⭆ Q -> GoodFrm Pr ->
    insSeq_rel_sound Spec P f (consJ aexp r1 i) Q.
Proof.
  intros.
  unfold insSeq_rel_sound; intros.
  inv H6.
  destruct_state S.
  econstructor; intros; try solve [CElim C].
  rewrite H12 in H6; inv H6.

  split.
  (* progress *)
  assert (exists R' D', exe_delay r d = (R', D')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H6 as (R' & D' & Hexe_delay).
  lets HP_nxt : Hexe_delay.
  symmetry in HP_nxt.
  eapply dly_reduce_relasrt_stable in HP_nxt; eauto.
  lets Haexp : HP_nxt.
  eapply H1 in HP_nxt.
  lets Hf : HP_nxt.
  eapply reg_vl_rel_change with (v1 := W f) in Hf; eauto.
  eapply H in Haexp.
  assert (exists R'' D'', exe_delay (set_R R' rd (W f)) D' = (R'', D'')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H6 as (R'' & D'' & Hexe_delay'').
  lets HP_nxt' : Hexe_delay''.
  symmetry in HP_nxt'.
  eapply dly_reduce_relasrt_stable in HP_nxt'; eauto.
  unfold rel_ins_sound in H2.
  eapply H2 in HP_nxt'; eauto.
  simpljoin1.
  destruct_state x.
  do 6 eexists.
  split.
  econstructor; eauto. 
  eapply LJumpl with (f := f'); eauto.
  {
    clear - Haexp.
    simpls; simpljoin1; eauto.
  }
  {
    clear - Haexp.
    simpls; simpljoin1; eauto.
  }
  {
    clear - HP_nxt.
    eapply sep_star_split in HP_nxt.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    simpls.
    simpljoin1.
    unfolds regSt; simpls; simpljoin1.
    eapply indom_merge_still; eauto.
    unfold indom.
    rewrite RegMap.gss; eauto.
  }
  econstructor; eauto.
  eapply LNTrans; eauto.

  (* preservation *)
  intros.
  inv H6.
  inv H23; CElim C.
  inv H8.
  inv H23; CElim C.
  eapply dly_reduce_relasrt_stable in H7; eauto.
  lets Haexp : H7.
  lets Hrd : H7.
  eapply H in Haexp; eauto.
  eapply H1 in Hrd; eauto.
  assert (pc2 = f').
  {
    clear - Haexp H26.
    simpls; simpljoin1.
    rewrite H26 in H; inv H; eauto.
  }
  subst pc2.
  eapply reg_vl_rel_change with (v1 := W f) in Hrd; eauto.
  eapply dly_reduce_relasrt_stable in Hrd; eauto.
  exists Fp Fq L Pr A HS.
  exists w.
  do 2 (split; eauto).
  unfold rel_ins_sound in H2.
  eapply H2 in Hrd; eauto.
  simpljoin1.
  destruct_state x.
  eapply sep_star_split in H8.
  simpljoin1.
  destruct_hstate x1.
  destruct_hstate x2.
  simpl in H9.
  simpljoin1.
  simpl in H13; simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H8, H20, H21.
  simpljoin1. 
  rewrite empM_merge_still_r, sep_lemma.merge_empR_r_eq in H6.
  assert ((LM'0, (LR'', F'0), D''0) = (m0, (r1, f2), d2)).
  {
    eapply ins_exec_deterministic; eauto.
  }
  inv H16.
  rewrite empM_merge_still_r, merge_empThrdPool_r_eq; eauto.
  eapply H3 in H11.
  eapply token_inc_asrt_stable with (w' := Nat.pred (x3 + x4)) in H11; eauto.
  split; eauto.
  split; eauto.

  split.
  clear - H4; unfold ImplyPrim'; intros; eauto.
  
  split; try omega; eauto.
  destruct x4; omega.
Qed.

Lemma wf_be_rule_relsound :
  forall f' Fp Fq P P' f I bv i Q Spec Pr L,
    Spec f' = Some (Fp, Fq) -> P ⇒ RAlst (z |=> W bv) ⋆ RAtrue ->
    rel_ins_sound ((P ⤈) ⤈) (P' ⋆ RAtoken 1) i ->
    (bv =ᵢ ($ 0) = true -> insSeq_rel_sound Spec (P' ⋆ RAtoken 1) f +ᵢ ($ 8) I Q) ->
    (bv =ᵢ ($ 0) = false -> P' ⇒ Fp L ⋆ Pr /\ Fq L ⋆ Pr ⭆ Q /\ GoodFrm Pr) ->
    insSeq_rel_sound Spec P f (be f'#i#I) Q.
Proof.
  intros.
  unfold insSeq_rel_sound; intros.
  inv H4.
  econstructor; intros; try solve [CElim C].

  split.
  (* progress *)
  rewrite H11 in H4; inv H4.
  destruct_state S.
  assert (exists R' D', exe_delay r d = (R', D')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H4 as (R' & D' & Hexe_delay).
  lets HP_nxt : Hexe_delay.
  symmetry in HP_nxt.
  eapply dly_reduce_relasrt_stable in HP_nxt; eauto.
  lets Hbv : H5.
  eapply H0 in Hbv.
  assert (exists R'' D'', exe_delay R' D' = (R'', D'')).
  {    
    eapply exe_delay_no_abort; eauto.
  }
  destruct H4 as (R'' & D'' & Hexe_delay').
  lets HP_nxt' : Hexe_delay'.
  symmetry in HP_nxt'.
  eapply dly_reduce_relasrt_stable in HP_nxt'; eauto.
  unfold rel_ins_sound in H1.
  eapply H1 in HP_nxt'; eauto.
  simpljoin1.
  destruct_state x.
  destruct (Int.eq bv $ 0) eqn:Heqe.
  { 
    do 6 eexists.
    split.
    econstructor; eauto.
    eapply LBe_false; eauto.
    eapply int_eq_true_eq in Heqe; subst.
    clear - Hbv Hexe_delay.
    eapply sep_star_split in Hbv; simpljoin1.
    simpl in H2. 
    destruct_state x; destruct_state x0; simpls; simpljoin1.
    unfold regSt in H1; simpls; simpljoin1.
    symmetry in Hexe_delay.
    eapply regz_exe_delay_stable in Hexe_delay; eauto.
    unfold get_R; rewrite Hexe_delay; eauto.
    eapply get_vl_merge_still; eauto.
    rewrite RegMap.gss; eauto.

    econstructor; eauto.
    eapply LNTrans; eauto.
  }
  {
    do 6 eexists.
    split.
    econstructor; eauto.
    eapply LBe_true; eauto.
    instantiate (1 := bv).
    clear - H0 H5 Hexe_delay.
    eapply H0 in H5.
    eapply sep_star_split in H5; eauto.
    simpljoin1.
    destruct_state x; destruct_state x0; simpl in H; simpljoin1.
    simpl in H3; simpljoin1.
    unfolds regSt; simpls; simpljoin1.
    symmetry in Hexe_delay.
    eapply regz_exe_delay_stable in Hexe_delay; eauto.
    unfold get_R; rewrite Hexe_delay; eauto.
    eapply get_vl_merge_still; eauto.
    rewrite RegMap.gss; eauto.
    intro; subst; tryfalse.

    econstructor; eauto.
    eapply LNTrans; eauto.
  }

  (* preservation *)
  intros.
  lets HPre : H5.
  eapply H0 in H5.
  inv H6.
  inv H20; CElim C.
  {
    assert (bv = v).
    {
      clear - H16 H26 H5.
      eapply sep_star_split in H5; simpljoin1.
      destruct_state x; destruct_state x0; simpl in H; simpljoin1.
      simpl in H2; unfolds regSt; simpl in H2; simpljoin1. 
      eapply regz_exe_delay_stable with (v := W bv) in H16; eauto.
      unfold get_R in H26; rewrite H16 in H26; inv H26; eauto.
      eapply get_vl_merge_still; eauto.
      rewrite RegMap.gss; eauto.
    }
    subst bv.

    inv H7.
    inv H23; CElim C.
    eapply dly_reduce_relasrt_stable in HPre; eauto.
    eapply dly_reduce_relasrt_stable in HPre; eauto.
    eapply Int.eq_false in H27.
    unfold rel_ins_sound in H1.
    eapply H1 in HPre; eauto. 
    simpljoin1.
    destruct_state x.
    eapply sep_star_split in H7; simpljoin1.
    destruct_state x; destruct_state x0; simpl in H7; simpljoin1.
    destruct_hstate x1; destruct_hstate x2; simpl in H8; simpljoin1.
    simpl in H14; simpljoin1. 
    rewrite sep_lemma.merge_empM_r_eq, sep_lemma.merge_empR_r_eq in H6.
    assert ((LM'0, (LR''0, F'0), D''0) = (m0, (r0, f2), d1)).
    {
      eapply ins_exec_deterministic; eauto.
    }
    inv H17.
    do 4 eexists.
    split.
    left; eauto.

    split.
    simpl; eauto.
    unfold get_R in H26.
    destruct (LR'' z) eqn:Heqe; tryfalse.
    inv H26. 
    eapply regz_exe_delay_stable2 in H16; eauto.
    unfold get_R; rewrite H16; eauto.
    lets Hspec : H27.
    eapply int_eq_false_neq in H27; eauto.
    split; intros; tryfalse.

    eapply H3 in Hspec; eauto.
    rewrite H11 in H4; inv H4.
    exists Fp Fq L Pr.
    split; eauto.
    simpljoin1.
    rewrite merge_empThrdPool_r_eq, sep_lemma.merge_empM_r_eq; eauto.
    split.
    eapply token_inc_asrt_stable with (w := x3); eauto.
    destruct x4; omega.
    split; eauto.
    unfold ImplyPrim'; intros.
    eapply H20; eauto.
    split; eauto.
    split; eauto.
    omega.
  }
  {
    assert (bv = $ 0).
    {
      clear - H16 H26 H5.
      eapply sep_star_split in H5; simpljoin1.
      destruct_state x; destruct_state x0; simpl in H; simpljoin1.
      simpl in H2; unfolds regSt; simpl in H2; simpljoin1. 
      eapply regz_exe_delay_stable with (v := W bv) in H16; eauto.
      unfold get_R in H26; rewrite H16 in H26; inv H26; eauto.
      eapply get_vl_merge_still; eauto.
      rewrite RegMap.gss; eauto.
    }
    subst bv.
    rewrite H11 in H4; inv H4.
    inv H7.
    do 2 eapply dly_reduce_relasrt_stable in HPre; eauto.
    unfold rel_ins_sound in H1.
    eapply H1 in HPre; eauto.
    simpljoin1.
    destruct_state x.

    do 4 eexists.
    split; eauto.
    split.
    simpl.
    instantiate (1 := $ 0).
    unfold get_R in H26.
    destruct (LR'' z) eqn:Heqe; tryfalse.
    inv H26.
    eapply regz_exe_delay_stable2 in H16; eauto.
    unfold get_R; rewrite H16; eauto.
    split; intro; tryfalse.

    assert (HinsSeq_rel_sound : ($ 0) =ᵢ ($ 0) = true); eauto.
    eapply H2 in HinsSeq_rel_sound; eauto.
    unfold insSeq_rel_sound in HinsSeq_rel_sound.
    eapply HinsSeq_rel_sound in H6; eauto.
    inv H22; CElim C.
    assert ((LM'0, (LR''0, F'0), D''0) = (m, (r, f0), d)).
    {
      eapply ins_exec_deterministic; eauto.
    }
    inv H8.
    rewrite Int.add_assoc; eauto.
  }
Qed.

Lemma rel_safety_conseq_exe_prim :
  forall Spec w w' C S A A' HS HS' Q f I,
    rel_safety_insSeq Spec w (C, S, f, f +ᵢ ($ 4)) (A', HS') Q -> 
    exec_prim (A, HS) (A', HS') -> LookupXC C f I ->
    rel_safety_insSeq Spec w' (C, S, f, f +ᵢ ($ 4)) (A, HS) Q.
Proof.
  intros.
  inv H.
  econstructor; intros.
  {
    (* i *)
    eapply H10 in H; clear H10 H12 H13 H14 H15.
    destruct H.
    split; eauto.
    intros.
    eapply H2 in H3; eauto.
    lets Hexe_prim : H0.
    inv H0.
    destruct H3.
    {
      right; eauto.
    }
    {
      simpljoin1.
      inv H0.
    }
  }
  {
    (* call f *)
    eapply H12 in H; clear H10 H12 H13 H14 H15.
    destruct H.
    split; eauto.
    intros.
    lets Hexe_prim : H0.
    inv H0.

    eapply H2 with (S1 := S1) in H3; eauto.
    simpljoin1.
    do 7 eexists.
    do 4 (split; eauto).
    split.
    right; eauto.
    destruct H8; simpljoin1.
    split; eauto.

    inv e.
  }
  {
    (* jumpl aexp rd; i *)
    eapply H13 in H; clear H10 H12 H13 H14 H15.
    destruct H; split; eauto.
    intros.
    eapply H2 with (S1 := S1) in H3; eauto.
    simpljoin1.
    do 7 eexists.
    split.
    right; eauto.
    split; eauto.
    split; eauto.

    lets Hexec_prim : H0.
    inv H0.
    destruct H3; simpljoin1; eauto.

    inv H0.
  }
  {
    (* be f; i; I *)
    eapply H14 in H; clear H10 H12 H13 H14 H15.
    destruct H; split; eauto.
    intros.
    eapply H2 with (S1 := S1) in H3; eauto.
    simpljoin1. 
    do 3 eexists.
    exists x2.
    split.
    right; eauto.
    split; eauto.
    lets Hexe_prim : H0.
    inv H0.
    split; eauto.
    {
      intros.
      eapply H6 in H0; eauto.
      destruct H3; simpljoin1; eauto.
      {
        do 4 eexists.
        split; eauto.
      }
      {
        inv H3.
      }
    }
    {
      intros.
      eapply H7 in H0.
      destruct H3; simpljoin1; eauto.

      inv H3.
    }
  }
  {
    (* retl *)
    eapply H15 in H; clear H10 H12 H13 H14 H15.
    destruct H; split; eauto.
    intros.
    lets Hexe_prim : H0.
    inv H0.
    eapply H2 with (S1 := S1) in H3; eauto.
    2 : intros; econstructor; eauto.
    simpljoin1.
    do 3 eexists.
    split.
    right; eauto.
    destruct H0; simpljoin1; eauto.

    inv e.
  }
Qed.

Lemma ImplyPrim'_implyprim :
  forall P Q Q',
    Q' ⭆ Q -> ImplyPrim' P Q' ->
    ImplyPrim' P Q.
Proof.
  intros. 
  unfolds ImplyPrim'; intros.
  eapply H0 in H1; eauto.
  destruct H1; eauto.
  simpljoin1.
  inv H1.
  left.
  exists x Pdone x1.
  split.
  econstructor; eauto.
  eapply H in H3; eauto.
  destruct H3; eauto.
  simpljoin1.
  inv H1.
Qed.

Lemma rel_safety_conseq_exe_prim2 :
  forall C S A HS Q Q' w Spec pc npc,
    Q' ⭆ Q ->
    rel_safety_insSeq Spec w (C, S, pc, npc)
                      (A, HS) Q' ->
    rel_safety_insSeq Spec w (C, S, pc, npc)
                      (A, HS) Q.
Proof.
  cofix Hp; intros.
  inv H0.
  econstructor; intros.
  {
    (* i *)
    lets Hcomm : H0.
    clear H11 H12 H13 H14.
    eapply H9 in H0; clear H9.
    destruct H0; split; eauto.
    intros.
    lets Hstep : H2.
    eapply H1 in H2; clear H0 H1.
    inv Hstep. inv H10; CElim C. 
    destruct H2; eauto.
    right.
    simpljoin1.
    do 2 eexists; split; eauto.
  }
  {
    (* call f *)
    lets Hcomm : H0.
    clear H9 H12 H13 H14.
    eapply H11 in H0.
    destruct H0; split; eauto.
    intros.
    eapply H1 with (S1 := S1) (S2 := S2) in H2; clear H1; eauto.
    destruct H2 as (Fp & Fq & L & r & A' & HS' & w'' & H2); simpljoin1.
    exists Fp Fq L r A'. exists HS' w''.
    do 8 (split; eauto).
  }
  {
    (* jumpl aexp rd *)
    lets Hcomm : H0.
    clear H9 H11 H13 H14.
    eapply H12 in H0; eauto.
    destruct H0; split; eauto.
    intros.
    eapply H1 with (S1 := S1) (S2 := S2) in H3; clear H0 H1; eauto.
    destruct H3 as (Fp & Fq & L & r & A' & HS' & w' & H3); simpljoin1.
    exists Fp Fq L r A'. exists HS' w'.
    do 5 (split; eauto).
    eapply ImplyPrim'_implyprim; eauto.
  }
  {
    (* cbe f *)
    lets Hcomm : H0.
    clear H9 H11 H12 H14.
    eapply H13 in H0; eauto.
    destruct H0; split; eauto.
    intros.
    eapply H1 with (S1 := S1) (S2 := S2) in H2; eauto.
    destruct H2 as (v & A' & HS' & w' & H2).
    exists v A' HS' w'.
    destruct H2; split; eauto.
    simpljoin1.
    split; eauto.
    split.
    {
      intros.
      eapply H5 in H8.
      destruct H8 as (Fp & Fq & L & r & H8).
      simpljoin1.
      exists Fp Fq L r.
      do 3 (split; eauto).
      clear - H H10.
      eapply ImplyPrim'_implyprim; eauto.    
    }
    {
      intros.
      eapply H6 in H8; eauto.
    }
  }
  {
    (* retl *)
    lets Hcomm : H0.
    clear H9 H11 H12 H13.
    eapply H14 in H0; eauto; clear H14.
    destruct H0; split; eauto.
    intros.
    eapply H1 with (S1 := S1) (S2 := S2) in H2; eauto.
    destruct H2 as (A' & HS' & w' & H2).
    simpljoin1.
    destruct H2.
    {
      simpljoin1.
      clear - H H5 H6.
      eapply H in H5.
      destruct H5.
      simpljoin1.
      do 3 eexists.
      split; eauto.
      do 3 eexists.
      split; eauto.
    }
    {
      inv H2.
      eapply H in H5; eauto.
      destruct H5.
      simpljoin1. 
      inv H2.
      exists Pdone HS' w'.
      split; eauto.
      right; econstructor; eauto.
    }
  }
Qed.

Lemma wf_abscseq_rule_relsound :
  forall P P' Q Q' f I Spec,
    P ⭆ P' -> insSeq_rel_sound Spec P' f I Q' -> Q' ⭆ Q ->
    insSeq_rel_sound Spec P f I Q.
Proof.
  intros.
  unfolds insSeq_rel_sound.
  intros.
  eapply H in H3; eauto.
  destruct H3; eauto.

  destruct H3 as (HS' & A' & w' & Hexe_prim & HP').
  eapply H0 in HP'; eauto.
  eapply rel_safety_conseq_exe_prim in HP'; eauto.
  eapply rel_safety_conseq_exe_prim2; eauto.
  eapply rel_safety_conseq_exe_prim2; eauto.
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
  {
    (* retl rule *) 
    eapply wf_ins_rel_soundness in H.
    eapply wf_retl_rule_relsound; eauto.
    unfold ImplyPrim; intros; eauto.
  }
  {
    (* Jmpl rule *)
    eapply wf_ins_rel_soundness in H2.
    eapply wf_jmpl_rule_relsound; eauto.
    unfold ImplyPrim; intros; eauto.
  } 
  {
    (* Be rule *)
    eapply wf_ins_rel_soundness in H1.
    eapply wf_be_rule_relsound; eauto.
    intros.
    eapply H4 in H5; simpljoin1; do 2 (split; eauto).
    unfold ImplyPrim; intros; eauto.
  }
  {
    (* ABScsq rule *) 
    eapply wf_abscseq_rule_relsound; eauto.
  }
Qed.

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
      exists x2 (x3, (length Kq, (1 + get_insSeqLen I0)%nat)).
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
      destruct H5 as (Fp & Fq & L & r & A' & HS' & w' & Hh_exec & HSpec & Hfpre & HGoodFrm & Hfpost & Hw & Hnpc).
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
        exists (Nat.pred w', (length Kq, (1 + get_insSeqLen I0)%nat)).
        split.
        econstructor; eauto.
        unfold Nat.lt.
        destruct w'; omega.
 
        eapply Hp; eauto.
        eapply rel_safety_insSeq_frame_property with (w2 := w2) (Pr := r) in Hrel_safety_insSeq'; eauto.
        rewrite <- Hw' in Hrel_safety_insSeq'.
        eapply rel_safety_insSeq_conseq; eauto.
 
        (* high-level executes *)
        right.
        exists HS' (Nat.pred w', (length Kq, (1 + get_insSeqLen I0)%nat)).
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
        destruct H6 as (v & A' & HS' & w' & Hexec_prim & Hz & Hv_not_0 & Hv_0).
        (* high-level doesn't execute *)
        destruct Hexec_prim as [Hexec_prim | Hexec_prim]; simpljoin1.
        left.
        destruct (classic (v = $ 0)).
        {
          lets Hrel_safety_insSeq : H0.
          eapply Hv_0 in Hrel_safety_insSeq; eauto.
          exists (w', (length Kq, 1 + get_insSeqLen I0)%nat).
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
          exists (Nat.pred w', (length Kq, (1 + get_insSeqLen I')%nat)).

          split.
          econstructor; eauto.
          unfold Nat.lt; destruct w'; omega.

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
          exists HS' (w', (length Kq, 1 + get_insSeqLen I0)%nat).
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
          exists HS' (Nat.pred w', (length Kq, (1 + get_insSeqLen I')%nat)).

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
    
    exists (Nat.pred x, (length (Q :: Kq), (1 + get_insSeqLen I')%nat))
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
    destruct_state x3.
    destruct_state x4.
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
      exists x2.
      split; eauto.
      clear - H7.
      destruct_state S2; simpls.
      unfolds get_R.
      destruct (r r15) eqn:Heqe; tryfalse.
      inv H7; eauto.

      (* high-level execute *)
      exists (x1, (0%nat, 1%nat)) (w, (0%nat, 2%nat)).
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
      destruct x1.
      unfold LtIndex.
      do 2 eapply lex_ord_right; eauto.
      econstructor; eauto.
      unfold Nat.lt; omega.
      exists x2.
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
      assert (x2 = f').
      {
        clear - H7 Hget_ret.
        unfolds get_R.
        rewrite Hget_ret in H7; simpls.
        inv H7; eauto.
      }
      subst x2.
      exists (x1, (length Kq', (1 + get_insSeqLen I0')%nat)) (w, (length (Q' :: Kq'), 1%nat)).

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
