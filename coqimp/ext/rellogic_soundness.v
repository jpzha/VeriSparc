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

Require Import wf_seq_sound.

(** Auxiliary Lemmas *)
Lemma last_Kq_cons_Q_same :
  forall A (Kq : list A) Q Q',
    last Kq Q = last (Q :: Kq) Q'.
Proof.
  induction Kq; intros; simpl; eauto.
  destruct Kq; eauto.
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
 
Definition insSeq_rel_sound Spec P f I Q :=
  forall C S HS A w,
    LookupXC C f I -> (S, HS, A, w) ||= P ->
    rel_safety_insSeq Spec w (C, S, f, f +ᵢ ($ 4)) (A, HS) Q.

Definition cdhp_rel_sound Spec C :=
  forall f Fp Fq L,
    Spec f = Some (Fp, Fq) -> 
    exists I : InsSeq, LookupXC C f I /\ insSeq_rel_sound Spec (Fp L) f I (Fq L).

Lemma wf_insSeq_rel_soundness :
  forall (I : InsSeq) Spec P Q f,
    Spec ⊩ {{ P }} f # I {{ Q }} ->
    insSeq_rel_sound Spec P f I Q.
Proof.
Admitted.

Lemma rel_safety_insSeq_frame_property :
  forall I Spec C pc S1 S2 S HS1 HS2 HS w1 w2 Q Pr A,
    LookupXC C pc I -> (S2, HS2, A, w2) ||= Pr -> Sta A Pr ->
    state_union S1 S2 S -> hstate_union HS1 HS2 HS ->
    rel_safety_insSeq Spec w1 (C, S1, pc, pc +ᵢ ($ 4)) (A, HS1) Q ->
    rel_safety_insSeq Spec (w1 + w2)%nat (C, S, pc, pc +ᵢ ($ 4)) (A, HS) (Q ⋆ Pr).
Proof.
Admitted.

Lemma rel_safety_insSeq_conseq :
  forall I Spec C pc npc S Q Q' w A HS,
    LookupXC C pc I ->
    rel_safety_insSeq Spec w (C, S, pc, npc) (A, HS) Q -> Q ⇒ Q' ->
    rel_safety_insSeq Spec w (C, S, pc, npc) (A, HS) Q'.
Proof.
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
  | Q' :: Kq' => forall S HS A w, (S, HS, A, w) ||= Q ->
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
    eapply H13 in H0.
    simpl in Hret.
    simpljoin1.
    eapply H14 in H15.
    exists pc I0.
    split; eauto.
    destruct_state x2.
    destruct_state x3.
    simpl in H10.
    simpljoin1.
    simpls.
    eapply get_vl_merge_still; eauto.
    clear - H15.
    unfolds get_R.
    destruct (r0 r15) eqn:Heqe; tryfalse.
    inv H15; eauto.

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
    eapply H14 in H16; eauto.
    exists pc I0.
    split; eauto.
    destruct_state x2.
    destruct_state x3.
    simpls; simpljoin1.
    simpl; eauto.
    clear - H16.
    unfolds get_R.
    destruct (r0 r15) eqn:Heqe; tryfalse.
    inv H16.
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
    }
  }
Admitted.

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
