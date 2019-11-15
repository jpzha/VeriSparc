(*+ Compositionality +*)            
Require Import Coqlib.                   
Require Import Maps.

Require Import Classical_Prop.

Require Import Integers.
Require Import LibTactics.
Open Scope Z_scope.
Import ListNotations.

Require Import state.
Require Import language.
Require Import lemmas_ins.
Require Import highlang.
Require Import lowlang.
Require Import logic.
Require Import lemmas.
Require Import reg_lemma.
Require Import soundness.
Require Import refinement.
Require Import rellogic.
Require Import integer_lemma.
Require Import lemmas_comp.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(** Auxiliary Lemmas about Rinj *)
Lemma Rinj_GenReg_LH' :
  forall (HR : HRegFile) (R : RegFile) (rr : GenReg) (v : Val),
    Rinj R HR -> R rr = Some v -> HR rr = Some v.
Proof.
  intros.
  inv H.
  specialize (H1 rr).
  simpljoin1.
  rewrite H0 in H; inv H.
  eauto.
Qed.

Lemma Rinj_GenReg_LH :
  forall (HR : HRegFile) (R : RegFile) (rr : GenReg) (v : Val),
    Rinj R HR -> get_R R rr = Some v -> get_HR HR rr = Some v.
Proof.
  intros.
  unfolds get_R.
  unfold get_HR.
  destruct (R rr) eqn:Heqe; tryfalse.
  eapply Rinj_GenReg_LH' in Heqe; eauto.
  rewrite Heqe.
  destruct rr; simpls; eauto.
Qed.

Lemma Rinj_eval_impl_Heval_opexp :
  forall (HR : HRegFile) (R : RegFile) (oexp : OpExp) (v : Val),
    Rinj R HR -> eval_opexp R oexp = Some v -> Heval_opexp HR oexp = Some v.
Proof.
  intros.
  unfolds eval_opexp.
  unfold Heval_opexp.
  destruct oexp.
  eapply Rinj_GenReg_LH; eauto.
  destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
Qed.

Lemma Rinj_eval_impl_Heval_addrexp :
  forall (HR : HRegFile) (R : RegFile) (aexp : AddrExp) (v : Val),
    Rinj R HR -> eval_addrexp R aexp = Some v -> Heval_addrexp HR aexp = Some v.
Proof.
  intros.
  unfolds eval_addrexp.
  unfold Heval_addrexp.
  destruct aexp.
  eapply Rinj_eval_impl_Heval_opexp; eauto.
  destruct (get_R R g) eqn:Heqe; tryfalse.
  eapply Rinj_GenReg_LH in Heqe; eauto.
  rewrite Heqe; eauto.
  destruct (eval_opexp R o) eqn:Heqe1; tryfalse.
  eapply Rinj_eval_impl_Heval_opexp in Heqe1; eauto.
  rewrite Heqe1; eauto.
Qed.

Lemma Rinj_indom_GenReg_LH:
  forall (HR : HRegFile) (R : RegFile) (rd : GenReg),
    Rinj R HR -> indom rd R -> indom rd HR.
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  inv H.
  simpljoin1; eauto.
  specialize (H1 rd); simpljoin1; eauto.
Qed.

Lemma Rinj_set_sameLH_stable :
  forall R HR (rd : GenReg) v,
    Rinj R HR -> Rinj (set_R R rd v) (set_HR HR rd v).
Proof.
  intros.
  inv H.
  econstructor; eauto.
  intros.
  lets Ht1 : H0 rd.
  lets Ht2 : H0 rr.
  simpljoin1.
  unfold set_R.
  unfold set_HR.
  unfold is_indom.
  destruct (RegName_eq rr rd); destruct (HRegName_eq rr rd).
  {
    inv e.
    exists v.
    rewrite H, H3.
    rewrite RegMap.gss.
    rewrite HRegMap.gss.
    eauto.
  }
  {
    inv e; tryfalse.
  }
  {
    inv e; tryfalse.
  }
  {
    rewrite H2, H4.
    rewrite RegMap.gso; eauto.
    rewrite HRegMap.gso; eauto.
  }
  simpljoin1.
  split.
  intros.
  specialize (H sr).
  simpljoin1.
  exists x2.
  unfold set_R.
  unfold is_indom.
  specialize (H0 rd).
  simpljoin1.
  rewrite H0; eauto.
  rewrite RegMap.gso; eauto.
  intro; tryfalse.
  split.
  unfold set_R.
  unfold is_indom.
  specialize (H0 rd).
  simpljoin1.
  rewrite H0; eauto.
  exists x.
  rewrite RegMap.gso; eauto.
  intro; tryfalse.
  split.
  exists x1.
  unfold set_R, set_HR.
  unfold is_indom.
  lets Ht1 : H0 rd.
  simpljoin1.
  rewrite H6, H7.
  rewrite RegMap.gso; eauto; try intro; tryfalse.
  rewrite HRegMap.gso; eauto; try intro; tryfalse.
  exists x0.
  unfold set_R, set_HR.
  unfold is_indom.
  lets Ht1 : H0 rd.
  simpljoin1.
  rewrite H6, H7.
  rewrite RegMap.gso; eauto; try intro; tryfalse.
  rewrite HRegMap.gso; eauto; try intro; tryfalse.
Qed.

(** Proof of Compositionality *)
Lemma HProgSafe_progress_and_preservation :
  forall C PrimSet HS,
    HProgSafe (C, PrimSet, HS) ->
    (exists HS' m, HP__ (C, PrimSet, HS) m (C, PrimSet, HS')) /\
    (forall HS' m, HP__ (C, PrimSet, HS) m (C, PrimSet, HS') -> HProgSafe (C, PrimSet, HS')).
Proof.
  intros.
  unfold HProgSafe in H.
  assert (star_step HP__ (C, PrimSet, HS) (C, PrimSet, HS)).
  econstructor; eauto.
  eapply H in H0; eauto.
  split; eauto.
  clear - H0.
  simpljoin1.
  lets HHP : H.
  inv H; eauto.
  clear - H; intros.
  assert (star_step HP__ (C, PrimSet, HS) (C, PrimSet, HS')).
  {
    eapply multi_step; eauto.
    econstructor; eauto.
  }
  unfold HProgSafe; intros. 
  eapply multi_step_cons with (P' := (C, PrimSet, HS')) in H1; eauto.  
Qed.

Lemma rel_safety_imp_rel_safety_aux' :
  forall k idx C S pc npc A HS Q,
    rel_safety k idx (C, S, pc, npc) (A, HS) Q ->
    well_founded LtIndex -> A <> Pdone ->
    exists k' S' pc' npc' idx' HS' n, Lsafety n (k, (C, (S, pc, npc))) (k', (C, (S', pc', npc'))) /\ 
                                 exec_prim (A, HS) (Pdone, HS') /\
                                 rel_safety k' idx' (C, S', pc', npc') (Pdone, HS') Q /\
                                 (Nat.eqb k 0 = true -> C pc = Some (c cretl) -> (n = 0)%nat). 
Proof.
  intros.
  unfolds well_founded.
  specialize (H0 idx).
  generalize dependent k.
  generalize dependent C.
  generalize dependent S.
  generalize dependent pc.
  generalize dependent npc.
  generalize dependent A.
  generalize dependent HS.
  generalize dependent Q.
  induction H0; intros. 
  inv H2.
  lets Hwf_com : H11.
  assert (exists i aexp rd f,
             (C pc = Some (c (cntrans i)) \/ C pc = Some (c (cjumpl aexp rd)) \/ C pc = Some (c (cbe f)))
            \/ C pc = Some (c (ccall f)) \/ C pc = Some (c cretl)).
  {
   clear - Hwf_com.
   eapply legel_pc_; eauto.
  }
  
  destruct H2 as (i & aexp & rd & f & Hcom).
  destruct Hcom as [Hcom | Hcom].
  {
   lets Ht : Hcom.
   eapply H14 in Ht; clear H14 H15 H16.
   simpljoin1.
   lets Hcont : H2.
   eapply H3 in Hcont; eauto.
   clear H3.
   destruct Hcont as [Hcont | Hcont].
   {
     simpljoin1.
     eapply H0 in H4; eauto.
     simpljoin1.
     do 6 eexists.
     exists (Nat.succ x10).
     split. 
     econstructor; eauto.
     intros.
     do 4 eexists.
     split; eauto.
     intros.
     repeat (destruct Hcom as [Hcom | Hcom]; CElim C).
     intros.
     repeat (destruct Hcom as [Hcom | Hcom]; CElim C).
     split; eauto.
     split; eauto.
     intros.
     repeat (destruct Hcom as [Hcom | Hcom]; CElim C).
   }
   { 
     simpljoin1.
     do 6 eexists.
     exists 1%nat.
     split.
     econstructor; eauto.
     intros.
     clear H5. 
     do 4 eexists.
     split; eauto.
     instantiate (1 := 0%nat).
     split; eauto.
     econstructor; eauto.
     intros.
     repeat (destruct Hcom as [Hcom | Hcom]; CElim C).
     intros.
     repeat (destruct Hcom as [Hcom | Hcom]; CElim C).
     split; eauto.
     split; eauto.
     intros.
     repeat (destruct Hcom as [Hcom | Hcom]; CElim C).
   }
 } 
  destruct Hcom as [Hcom | Hcom].
  {
   lets Ht : Hcom.
   eapply H15 in Ht; clear H14 H15 H16.
   simpljoin1. 
   assert (Hnpc : x2 = npc).
   {
     clear - Hcom H2.
     inv H2.
     inv H9; CElim C.
     eauto.
   }
   subst x2.

   lets Hcont : H4.
   eapply H3 in Hcont; eauto; clear H3.
   simpljoin1.
   destruct H3.
   {
     simpljoin1; subst.
     eapply H0 in H5; eauto.
     simpljoin1.
     do 6 eexists.   
     exists (Nat.succ (Nat.succ x14)).
     split. 
     econstructor; eauto.
     intros.
     repeat (destruct H10 as [H10 | H10]; CElim C).
     intros; CElim C. 
     do 7 eexists.
     split; eauto.
     
     intros; CElim C.
     split; eauto.
     split; eauto.
     intros; tryfalse.
     eapply LtIndex_Trans; eauto.
   }
   {
     do 6 eexists.
     exists 2%nat.
     split.
     econstructor; eauto.
     intros.
     repeat (destruct H6 as [H6 | H6]; CElim C).
     Focus 2.
     intros; CElim C.
     intros.
     clear H6.
     do 7 eexists.
     split; eauto.
     split; eauto.
     split; eauto.
     econstructor; eauto. 
     assert (x7 = Pdone).
     {
       inv H3; eauto.
     }
     subst x7.
     split; eauto.
     split; eauto.
     intros; CElim C.
   }
  } 
  {
   lets Ht : Hcom.
   eapply H16 in Ht; eauto; clear H14 H15 H16.
   simpljoin1.
   lets Hcont : H2. 
   eapply H3 with (S1 := x0) in Hcont; eauto; clear H3.
   simpljoin1.
   destruct H3.
   {
     simpljoin1.
     destruct H5.
     simpljoin1; tryfalse.
     simpljoin1.
     eapply H0 in H7; eauto.
     simpljoin1.
     do 6 eexists.
     exists (Nat.succ (Nat.succ x16)).
     split.
     econstructor; eauto.
     intros.
     repeat (destruct H12 as [H12 | H12]; CElim C).
     intros; CElim C.
     intros.
     clear H12.
     do 7 eexists.
     split; eauto.
     split; eauto.
     split; eauto.
     intros; tryfalse.
     eapply LtIndex_Trans; eauto.
   }
   {
     destruct H5.
     {  
       simpljoin1; subst.
       destruct x6.
       do 4 eexists. 
       exists (Nat.succ (Nat.succ n), n0).
       exists x9 0%nat. 
       split.
       econstructor; eauto.
       split; eauto.
       split; intros; eauto.
       econstructor; eauto.
       intros. 
       repeat (destruct H7 as [H7 | H7]; CElim C).
       intros; CElim C.
       intros.
       clear H7. 
       split; eauto.
       do 6 eexists; eauto.
       intros. 
       assert ((C, (x0, x2, x4)) = (C, (S1, pc1, npc1))).
       {
         eapply LP_deterministic; eauto.
         simpl; eauto.
       } 
       inv H12.
       assert (pc1 = npc).
       { 
         clear - Hcom H2.
         inv H2.
         inv H9; CElim C.
         eauto.
       }
       subst pc1.
       assert (exists i aexp rd f,
            (C npc = Some (c (cntrans i)) \/ C npc = Some (c (cjumpl aexp rd)) \/ C npc = Some (c (cbe f)))
            \/ C npc = Some (c (ccall f)) \/ C npc = Some (c cretl)).
       { 
         clear - H13.
         eapply legel_pc_; eauto.
       }
       assert ((C, (x1, x11 +ᵢ ($ 8), x11 +ᵢ ($ 12))) = (C, (S2, pc2, npc2))).
       {
         simpljoin1.
         assert (exists cc', C npc = Some (c cc')).
         {
           destruct H12; eauto.
           repeat (destruct H12 as [H12 | H12]; eauto).
           destruct H12; eauto.
         }
         simpljoin1.
         eapply LP_deterministic; eauto.
         simpl; eauto.
       }
       inv H14.
       do 5 eexists.
       split.
       left.  
       instantiate (3 := (Nat.succ n, n0)).
       instantiate (3 := (n, n0)).
       split.
       econstructor; eauto.
       split.
       econstructor; eauto.
       split; eauto.
  
       left.
       split; eauto.
       split; eauto.
       split; eauto.
     }
     {
       simpljoin1.
       do 6 eexists.
       exists 2%nat.
       split.
       econstructor; eauto.
       intros. 
       repeat (destruct H7 as [H7 | H7]; CElim C).
       intros; CElim C.
       intros.
       do 7 eexists.
       split; eauto.
       split; eauto.
       split; eauto.
       split; eauto.
       econstructor; eauto.
       assert (x8 = Pdone).
       {
         inv H3; eauto.
       }
       subst x8.
       split; eauto.
       split; eauto.
       intros; tryfalse.
     }
   }
  }
Qed.
 
(** equivalence between rel_safety and rel_safety_aux *)
Lemma rel_safety_imp_rel_safety_aux1 :
  forall k C S pc npc HS HS' Q idx A,
    rel_safety k idx (C, S, pc, npc) (Pdone, HS') Q -> A <> Pdone -> exec_prim (A, HS) (Pdone, HS') ->
    rel_safety_aux k idx (C, S, pc, npc) (A, HS) Q.
Proof.
  cofix Hp; intros.
  inv H.
  assert (exists i aexp rd f,
            (C pc = Some (c (cntrans i)) \/ C pc = Some (c (cjumpl aexp rd)) \/ C pc = Some (c (cbe f)))
            \/ C pc = Some (c (ccall f)) \/ C pc = Some (c cretl)).
  {
    eapply legel_pc_; eauto.
  }
  simpljoin1. 
  econstructor; eauto.
  {
    intros.
    eapply H13 in H2; clear H13 H14 H15 H.
    simpljoin1.
    split.
    do 3 eexists; eauto.
    intros.
    eapply H2 in H3.
    destruct H3.
    simpljoin1.
    eexists.
    split; eauto.
    simpljoin1.
    inv H3.
  }
  {
    intros.
    eapply H14 in H2; clear H13 H14 H15 H.
    simpljoin1.
    split.
    do 6 eexists.
    split; eauto.
    intros. 
    eapply H2 with (S1 := S1) in H4; eauto.
    simpljoin1.
    destruct H4.
    simpljoin1.
    exists x9 x10. 
    split; eauto.
    inv H4.
  }
  {
    intros.
    eapply H15 in H2; clear H13 H14 H15 H.
    simpljoin1.
    split.
    do 6 eexists.
    split; eauto.
    intros.
    eapply H2 with (S1 := S1) in H4; eauto.
    simpljoin1.
    destruct H4.
    simpljoin1.
    destruct H6.
    simpljoin1. 
    do 5 eexists.
    left; eauto.
    repeat (split; eauto).
    eapply LtIndex_Trans in H4; eauto.
    eapply LtIndex_Trans; eauto.
    simpljoin1.
    exists x9 x10.
    do 3 eexists.
    right.
    split; eauto.
    split; eauto.
    inv H4.
  }
  Unshelve.
  exact (4%nat, 4%nat).
  exact (4%nat, 4%nat).
  exact 4%nat.
Qed.

Lemma Lsafety_imp_rel_safety_aux :
  forall n k C S pc npc S' pc' npc' HS HS' k' idx Q A,
    Lsafety n (k, (C, (S, pc, npc))) (k', (C, (S', pc', npc'))) ->
    exec_prim (A, HS) (Pdone, HS') -> rel_safety k' idx (C, S', pc', npc') (Pdone, HS') Q ->
    A <> Pdone ->
    (Nat.eqb k 0 = true -> C pc = Some (c cretl) -> (n = 0)%nat) ->
    rel_safety_aux k (idx_sum (0%nat, n) idx) (C, S, pc, npc) (A, HS) Q.
Proof.
  cofix Hp; intros.
  renames H3 to Hstrong.
  inv H.
  {
    destruct idx; simpl.
    eapply rel_safety_imp_rel_safety_aux1; eauto.
  }
  {
    assert (exists i aexp rd f,
            (C pc = Some (c (cntrans i)) \/ C pc = Some (c (cjumpl aexp rd)) \/ C pc = Some (c (cbe f)))
            \/ C pc = Some (c (ccall f)) \/ C pc = Some (c cretl)).
    {
      clear - H10.
      eapply legel_pc_; eauto.
    }
    destruct H as (i & aexp & rd & f & Hcom).
    destruct Hcom as [Hcom | Hcom].
    {
      lets Hcom' : Hcom.
      eapply H15 in Hcom; clear H15 H16 H17.
      simpljoin1. 
      econstructor; eauto.
      { 
        intros.
        clear H4.
        split; eauto.
        intros.
        exists (idx_sum (0%nat, x2) idx).
        split.
        eapply idx_sum_pre_lt.
        unfold LtIndex.
        eapply lex_ord_right.
        unfold Nat.succ.
        eapply Nat.lt_succ_diag_r.
        assert ((C, (x, x0, x1)) = (C, (S'0, pc'0, npc'0))).
        {
          destruct Hcom' as [Hcom' | Hcom'].
          eapply LP_deterministic; eauto.
          simpl; eauto.
          destruct Hcom' as [Hcom' | Hcom'].
          eapply LP_deterministic; eauto.
          simpl; eauto.
          eapply LP_deterministic; eauto.
          simpl; eauto.
        }  
        inv H5; eauto.
        eapply Hp; eauto.
        intros.
        clear - H3 H5 H6.
        inv H3; eauto.
        eapply H16 in H6.
        clear - H5 H6.
        simpljoin1.
        tryfalse.
      }

      intros.
      repeat (destruct Hcom' as [Hcom' | Hcom']; CElim C).
      intros.
      repeat (destruct Hcom' as [Hcom' | Hcom']; CElim C).
    }
    assert (exists i aexp rd f,
            (C npc = Some (c (cntrans i)) \/ C npc = Some (c (cjumpl aexp rd)) \/ C npc = Some (c (cbe f)))
            \/ C npc = Some (c (ccall f)) \/ C npc = Some (c cretl)).
    {
      clear - H14.
      eapply legel_pc_; eauto.
    }
    destruct H as (i0 & aexp0 & rd0 & f0 & Hcom_npc).
    destruct Hcom as [Hcom | Hcom].
    {
      lets Hcom' : Hcom.
      eapply H16 in Hcom; clear H15 H16 H17.
      simpljoin1.
      econstructor; eauto.
      intros.
      repeat (destruct H5 as [H5 | H5]; CElim C).
      intros.
      clear H5.
      split; eauto.
      do 6 eexists.
      split; eauto.
      intros.
      assert ((C, (x, x0, x1)) = (C, (S1, pc1, npc1))).
      {
        eapply LP_deterministic; eauto.
        simpl; eauto.
      }
      inv H7.
      assert (pc1 = npc).
      {
        clear - H Hcom'.
        inv H.
        inv H9; CElim C.
        eauto.
      }
      subst pc1.
      assert ((C, (x2, x3, x4)) = (C, (S2, pc2, npc2))).
      {
        destruct Hcom_npc as [Hcom_npc | Hcom_npc].
        repeat (destruct Hcom_npc as [Hcom_npc | Hcom_npc];
                [eapply LP_deterministic; eauto; simpl; eauto | idtac]).
        eapply LP_deterministic; eauto; simpl; eauto.
        destruct Hcom_npc;
          eapply LP_deterministic; eauto; simpl; eauto.
      }
      inv H7.

      exists (idx_sum (0%nat, x5) idx) (idx_sum (0%nat, Nat.succ x5) idx).
      split.
      eapply idx_sum_pre_lt.
      unfold LtIndex.
      eapply lex_ord_right.
      unfold Nat.succ.
      eapply Nat.lt_succ_diag_r.
      split.
      eapply idx_sum_pre_lt.
      unfold LtIndex.
      eapply lex_ord_right.
      unfold Nat.succ.
      eapply Nat.lt_succ_diag_r.

      eapply Hp; eauto.
      intros.
      clear - H7.
      simpls; tryfalse.

      intros; CElim C.
    }
    {
      lets Hcom' : Hcom.
      eapply H17 in Hcom; clear H15 H16 H17.
      simpljoin1.
      econstructor; eauto.
      {
        intros.
        repeat (destruct H6 as [H6 | H6]; CElim C).
      }
      {
        intros; CElim C.
      }
      {
        intros.
        clear H6.
        split; eauto.
        do 6 eexists.
        split; eauto.
        intros.
        assert ((C, (x, x0, x1)) = (C, (S1, pc1, npc1))).
        {
          eapply LP_deterministic; eauto.
          simpl; eauto.
        }
        inv H8.
        assert (npc = pc1).
        { 
          clear - Hcom' H.
          inv H.
          inv H9; CElim C.
          eauto.
        }
        subst npc.
        assert ((C, (x2, x3, x4)) = (C, (S2, pc2, npc2))).
        { 
          destruct Hcom_npc as [Hcom_npc | Hcom_npc].
          repeat (destruct Hcom_npc as [Hcom_npc | Hcom_npc];
                  [eapply LP_deterministic; eauto; simpl; eauto | idtac]).
          eapply LP_deterministic; eauto; simpl; eauto.
          destruct Hcom_npc; eapply LP_deterministic; eauto; simpl; eauto.
        }
        inv H8.
        exists (idx_sum (0%nat, x5) idx) (idx_sum (0%nat, Nat.succ x5) idx).
        do 3 eexists.
        right; eauto.
        split; eauto.
        split; eauto.
        eapply idx_sum_pre_lt; eauto.
        eapply lex_ord_right.
        eapply Nat.lt_succ_diag_r; eauto.
        split; eauto.
        eapply idx_sum_pre_lt; eauto.
        eapply lex_ord_right.
        eapply Nat.lt_succ_diag_r; eauto.

        split; eauto.
        split; eauto. 

        eapply Hp; eauto.
        clear - H5; intros.
        inv H5; eauto.
        eapply H16 in H0; clear H14 H15 H16.
        simpljoin1; tryfalse.
      }
    }
  }
  Unshelve.
  exact 5%nat.
Qed.

Lemma rel_safety_imp_rel_safety_aux2 :
  forall k C S pc npc HS Q idx A,
    rel_safety k idx (C, S, pc, npc) (A, HS) Q -> A <> Pdone ->
    exists idx', rel_safety_aux k idx' (C, S, pc, npc) (A, HS) Q.
Proof.
  intros.
  eapply rel_safety_imp_rel_safety_aux' in H; eauto.
  Focus 2.
  eapply well_founded_LtIndex; eauto.
  simpljoin1.
  exists (idx_sum (0%nat, x5) x3).
  eapply Lsafety_imp_rel_safety_aux; eauto.
Qed.

(** Define Well-formed Current Thread and Well-formed Ready *)
Inductive wfIndex : XCodeHeap -> State -> Word -> Index -> Prop :=
| cons_wfIndex : forall C M R F D idx pc,
    (
      forall w k v, 
        C pc = Some (Psave w) ->
        get_R R cwp = Some (W k) -> get_R R Rwim = Some (W v) ->
        win_masked (pre_cwp k) v = true ->
        (0%nat, 0%nat) ⩹ idx
    ) ->
    (
      forall k v, 
        C pc = Some Prestore ->
        get_R R cwp = Some (W k) -> get_R R Rwim = Some (W v) ->
        win_masked (pre_cwp k) v = true ->
        (0%nat, 0%nat) ⩹ idx
    ) ->
    wfIndex C (M, (R, F), D) pc idx.

Inductive wfHPrimExec : XCodeHeap -> primcom -> HState -> apSet -> Prop :=
| cons_wfHPrimExec : forall C A HS PrimSet,
    (
      forall hprim lv T t HQ pc npc HM,
        A = Pm hprim lv -> HS = (T, t, (HQ, pc, npc), HM) -> 
        HH__ C (HQ, pc, npc, HM) (Callevt pc lv) (HQ, pc, npc, HM) /\
        (exists HS' pc' npc', hprim lv HS HS' /\ get_Hs_pcont HS' = (pc', npc')) /\ PrimSet pc = Some hprim 
    ) ->
    wfHPrimExec C A HS PrimSet.

(** Well-formed Current Thread *)
Inductive wfCth : Index -> XCodeHeap * XCodeHeap -> LProg -> HProg -> Prop :=
| clt_wfCth : forall C Cas S HS pc npc PrimSet idx,
    wp_stateRel S HS -> wfIndex C S pc idx -> 
    get_Hs_pcont HS = (pc, npc) -> indom pc C ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS)

| prim_wfCth : forall C Cas Sc HSc S HS Sr HSr w Q Pr A pc npc PrimSet idx k,
    state_union Sc Sr S -> hstate_union HSc HSr HS ->
    rel_safety_aux k idx (Cas, Sc, pc, npc) (A, HSc) Q ->
    (Sr, HSr, A, w) ||= Pr -> 
    wfHPrimExec C A HS PrimSet -> Sta A Pr ->
    (
      forall S' HS' w' f, (S', HS', Pdone, w') ||= Q ⋆ Pr -> getregs S' r15 = Some (W f) ->
                     HProgSafe (C, PrimSet, HS') -> (exec_prim (A, HS) (Pdone, HS')) -> 
                     wp_stateRel S' HS' /\ get_Hs_pcont HS' = (f +ᵢ ($ 8), f +ᵢ ($ 12)) 
    ) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).

(* Well-formed Ready Thread *)
Inductive wfRdy : XCodeHeap * XCodeHeap -> XCodeHeap * apSet -> Tid -> tlocst -> Prop :=
| cons_wfRdy : forall t K PrimSet C Cas,
    (
      forall S HS f T HM pc npc, 
        wp_stateRel S HS -> HS = (T, t, K, HM) -> HProgSafe (C, PrimSet, HS) ->
        getregs S r15 = Some (W f) -> pc = f +ᵢ ($ 8) -> npc = f +ᵢ ($ 12) ->
        get_Hs_pcont HS = (pc, npc) ->
        exists idx, wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS)
    ) ->
    wfRdy (C, Cas) (C, PrimSet) t K.

Lemma indom_get_left :
  forall tp tp' (M M' : tp -> option tp') l v,
    (M ⊎ M') l = v -> indom l M ->
    M l = v.
Proof.
  intros.
  unfold merge in *.
  destruct (M l) eqn:Heq; eauto.
  unfold indom in *.
  destruct H0; tryfalse.
Qed.

Lemma LP_step_indom : forall C S S' pc npc pc' npc' m,
    LP__ (C, (S, pc, npc)) m (C, (S', pc', npc')) ->
    indom pc C.
Proof.
  intros.
  inv H.
  inv H9; unfold indom; eauto.
Qed.
  
Lemma LP__local1 :
  forall S S' pc npc pc' npc' C C' m,
    indom pc C ->
    LP__ (C ⊎ C', (S, pc, npc)) m (C ⊎ C', (S', pc', npc')) ->
    LP__ (C, (S, pc, npc)) m (C, (S', pc', npc')).
Proof.
  intros.
  inv H0.
  inv H10.
  econstructor; eauto.
  eapply LNTrans; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LJumpl; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LCall; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LRetl; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LBe_true; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LBe_false; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LPrint; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LPsave_no_trap; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LPsave_trap; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LPrestore_no_trap; eauto.
  eapply indom_get_left; eauto.
  econstructor; eauto.
  eapply LPrestore_trap; eauto.
  eapply indom_get_left; eauto.
Qed.

Lemma HProg_not_clt_exec_prim :
  forall C PrimSet HS pc npc,
    HProgSafe (C, PrimSet, HS) -> ~ indom pc C -> get_Hs_pcont HS = (pc, npc) ->
    exists lv hprim, PrimSet pc = Some hprim /\ wfHPrimExec C (Pm hprim lv) HS PrimSet
                /\ npc = pc +ᵢ ($ 4).
Proof.
  intros.
  unfolds HProgSafe.
  assert (star_step HP__ (C, PrimSet, HS) (C, PrimSet, HS)).
  econstructor; eauto.
  eapply H in H2. 
  unfold indom in *.
  destruct H2 as (HP' & m & HHP__).
  inv HHP__.
  {
    inv H7; try solve [simpls; inv H1; contradiction H0; eauto].
  }
  {
    inv H7; simpls; inv H1.
    contradiction H0; eauto.
  }
  {   
    exists lv prim.
    inv H5; simpls; inv H1. 
    split; eauto.
    split; eauto.
    econstructor; intros.
    inv H2.
    inv H1.
    split; eauto. 
    econstructor; eauto.
    destruct K''.
    destruct p.
    split; eauto.
    do 3 eexists.
    split; eauto.
    split; simpl; eauto.
  }
Qed.

Lemma inital_wfCth_holds :
  forall Spec C Cas PrimSet S HS pc npc,
    simImpsPrimSet Spec Cas PrimSet ->
    wp_stateRel S HS -> HProgSafe (C, PrimSet, HS) ->
    get_Hs_pcont HS = (pc, npc) -> C ⊥ Cas ->
    exists idx, wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).
Proof.
  intros.
  destruct HS.
  destruct p.
  renames t to K.
  destruct p.
  renames t to T, t0 to t.
  lets Ht : (classic (indom pc C)).
  destruct Ht as [Ht | Ht].
  {
    exists (5%nat, 6%nat).
    eapply clt_wfCth; eauto.
    destruct S.
    destruct p.
    destruct r.
    econstructor; intros.
    econstructor; simpl; unfold Nat.lt.
    omega.
    econstructor; simpl; unfold Nat.lt.
    omega.
  }
  {
    lets Hprim_exec : H1.
    eapply HProg_not_clt_exec_prim in Hprim_exec; eauto.
    destruct Hprim_exec as (lv & hprim & Hprimset & HwfHPrimExec & Hnpc).
    unfolds simImpsPrimSet.
    lets HSpec : Hprimset.
    assert (HwdSpec : exists Fp Fq, Spec pc = Some (Fp, Fq) /\ wdSpec Fp Fq hprim).
    { 
      clear - H HSpec.
      eapply H with (L := nil) in HSpec.
      destruct HSpec as (lv & Fp & Fq & HSpec & HPrimSet & HAprim & HwdSpec & HsimImpPrim).
      do 2 eexists.
      split; eauto.
    } 
    destruct HwdSpec as (Fp & Fq & HSpec_pc & HwdSpec).
    inv HwdSpec.
    rename H4 into Hret.
    specialize (H5 lv). 
    destruct H5 as (num & Pr & L & Hwf_pre & Hwf_post & HSta).
    assert (Hinv : INV (Pm hprim lv) num lv (S, (T, t, K, m), (Pm hprim lv), num)).
    unfold INV.
    split; eauto. 
    clear - HwfHPrimExec. 
    inv HwfHPrimExec.
    assert (Pm hprim lv = Pm hprim lv); eauto.
    destruct K.
    destruct p.
    assert ((T, t, (h, w0, w), m) = (T, t, (h, w0, w), m)); eauto.
    eapply H in H0; eauto.
    destruct H0.
    simpljoin1.
    inv H0.
    split.
    left.
    eexists.
    split.
    econstructor; eauto.
    intro; tryfalse.
    simpl; eauto.
    lets Hpre_hold : Hinv.
    eapply Hwf_pre in Hpre_hold; eauto.
    (*lets Hpre_tmp : Hpre_hold.*)
    eapply rel_sep_star_split in Hpre_hold.
    destruct Hpre_hold as (S1 & S2 & HS1 & HS2 & w1 & w2 & Hstate_union & Hhstate_union & Hfp & Hpr & Hnum).
    lets Hsim : HSpec.
    eapply H with (L := L) in Hsim; eauto.
    destruct Hsim as (lv0 & Fp0 & Fq0 & HSpec0 & HPrimSet0 & HFp_imp_prim & HwdSpec0 & Hsim).
    rewrite HSpec_pc in HSpec0.
    inv HSpec0.
    assert (lv = lv0).
    {
      clear - Hwf_pre Hfp HFp_imp_prim Hpr.
      eapply HFp_imp_prim in Hfp; eauto.
      clear - Hfp; simpls.
      simpljoin1.
      inv H2; eauto.
    } 
    subst lv.
    unfold simImpPrim in Hsim.
    eapply Hsim in Hfp.
    destruct Hfp as [idx HsimM].
    lets HsimM' : HsimM.
    eapply rel_safety_imp_rel_safety_aux2 in HsimM'; eauto.
    Focus 2.
    intro; tryfalse.
    destruct HsimM' as [idx' HsimM'].
    exists idx'.
    eapply prim_wfCth; eauto.

    intros. 
    assert (wp_stateRel S' HS').
    {
      clear - Hwf_post H4.
      eapply Hwf_post in H4.
      simpljoin1.
      inv H; eauto.
    }
    split; eauto. 
    eapply Hwf_post in H4.  
    clear - H4 H5 H7 H8 Hret.
    inv H8.
    inv H3.
    inv H15.
    specialize (H r15).
    destruct H11 as [H11 Hdisj_ctx_k].
    simpljoin1.
    simpl in H5.
    simpl.
    lets Hexec_prim : H7.
    inv H7.
    eapply Hret in H18; eauto.
    simpl.
    rewrite H5 in H.
    inv H; eauto.
  }
Qed.
  
Lemma LH__progress_HH_progress :
  forall C Cas Spec Mc Mr LR F pc npc LM' LR' F' D' pc' npc' T t HR b HF M PrimSet idx,
    simImpsPrimSet Spec Cas PrimSet -> C ⊥ Cas -> 
    LH__ C ((Mc ⊎ Mr ⊎ M, (LR, F), []), pc, npc) tau
         ((LM', (LR', F'), D'), pc', npc') ->
    HProgSafe (C, PrimSet, (T, t, ((HR, b, HF), pc, npc), M)) ->
    indom pc C -> Mc ⊥ Mr -> (Mc ⊎ Mr) ⊥ M ->
    curTRel (Mc, (LR, F)) (t, (HR, b, HF, pc, npc)) ->
    wfIndex C (Mc ⊎ Mr ⊎ M, (LR, F), []) pc idx ->
    exists Mc' M' K' idx',
      LM' = Mc' ⊎ Mr ⊎ M' /\ Mc' ⊥ Mr /\ (Mc' ⊎ Mr) ⊥ M'
      /\
      (
        HP__ (C, PrimSet, (T, t, ((HR, b, HF), pc, npc), M)) tau (C, PrimSet, (T, t, K', M'))
        \/
        (K' = ((HR, b, HF), pc, npc) /\ M' = M /\ idx' ⩹ idx)
      )
      /\ curTRel (Mc', (LR', F')) (t, K') /\ wfIndex C (Mc' ⊎ Mr ⊎ M', (LR', F'), D') pc' idx'
      /\ get_Hs_pcont (T, t, K', M') = (pc', npc') /\ D' = [].
Proof.
  intros.
  inv H1.
  {
    (* i *)
    admit.
  }
  {
    (* Jumpl aexp rd *)
    exists Mc M.
    eexists.
    exists (5%nat, 6%nat).
    split; eauto.
    split; eauto.
    split; eauto.
    split.
    {
      left.
      eapply Htau_step.
      eapply HJumpl; eauto.
      eapply Rinj_eval_impl_Heval_addrexp; eauto.
      inv H6; eauto.
      eapply Rinj_indom_GenReg_LH; eauto.
      inv H6; eauto.
    }
    split.
    {
      inv H6. 
      econstructor; eauto.
      clear - H19.
      unfolds ctxfm.
      simpljoin1.
      exists x x0 x1.
      repeat (split; eauto).
      eapply get_R_set_neq_stable; eauto; intro; tryfalse.
      eapply get_R_set_neq_stable; eauto; intro; tryfalse.
      eapply Rinj_set_sameLH_stable; eauto.
    }
    split.
    {
      econstructor; intros; econstructor; eauto.
      unfold Nat.lt; omega.
      unfold Nat.lt; omega.
    }
    simpl; split; eauto.
  }
  {
    (* Call f *)
    exists Mc M.
    eexists.
    exists (5%nat, 6%nat).
    repeat (split; eauto).
    {
      left.
      econstructor; eauto.
      eapply HCall; eauto.
      eapply Rinj_indom_GenReg_LH; eauto.
      inv H6; eauto.
    }
    
  }
  Admitted.

(* WfCth and WfRdy Preservation *)
Lemma wfCth_wfRdy_tau_step_preservation_clt :
  forall idx C Cas S pc npc S' pc' npc' PrimSet T t K M Spec,
    indom pc C ->
    simImpsPrimSet Spec Cas PrimSet -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy (C, Cas) (C, PrimSet) t' K' 
    ) ->
    LP__ (C ⊎ Cas, (S, pc, npc)) tau (C ⊎ Cas, (S', pc', npc')) ->
    exists T' t0 K0 M' idx1,
      ((idx1 ⩹ idx /\ (T, t, K, M) = (T', t0, K0, M')) \/
       (exists HP', star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\
                    HP__ HP' tau (C, PrimSet, (T', t0, K0, M'))))
      /\
      wfCth idx1 (C, Cas) (C ⊎ Cas, (S', pc', npc')) (C, PrimSet, (T', t0, K0, M')) /\
      (
        forall t1 K1, (ThrdMap.set t0 None T') t1 = Some K1 ->
                      wfRdy (C, Cas) (C, PrimSet) t1 K1 
      ).
Proof.   
  introv Ht; intros.
  inv H2.
  Focus 2.
  inv H15. 
  clear - H0 Ht H20.
  unfold indom in *.
  simpljoin1.
  unfold disjoint in *.
  specialize (H0 pc).
  rewrite H in H0; simpls.
  clear - H1 H0.
  unfolds legal_com.
  destruct (Cas pc) eqn:Heqe; simpls; tryfalse.
 
  eapply LP__local1 in H4; eauto.
  lets HLP__ : H4.
  inv H4.
  assert (D = nil).
  {
    inv H12; eauto.
  }
  subst D.
  simpl in H9.
  inv H9.
  lets Hwp_stateRel : H12.
  inv H12.
  destruct K.
  destruct p.
  destruct h.
  destruct p.
  renames h0 to HR, z to b, h to HF.
  simpl in H15; inv H15.
  unfolds Tid.

  assert ((Mc ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM =
          Mc ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)).
  {
    rewrite <- lemmas.merge_assoc; eauto.
  }
  
  assert (((Mc ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M =
          Mc ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M).
  {
    rewrite H2; eauto.
  }

  assert (Mc ⊥ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)).
  { 
    eapply lemmas.disj_sep_merge_still; eauto.
    clear - H11.
    eapply lemmas.disj_sym in H11.
    eapply lemmas_ins.disj_merge_disj_sep in H11.
    destruct H11.
    eapply lemmas.disj_sym; eauto.
  }

  assert ((Mc ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)) ⊥ M).
  { 
    rewrite <- H2; eauto.
  }
  
  rewrite H4 in H17.
  eapply LH__progress_HH_progress in H17; eauto.
  2 : rewrite <- H2; eauto.

  destruct H17 as (Mc' & M'' & K' & idx' & HLM' & Hdisj1 & Hdisj2 & Hstep
                   & HcurTRel' & HwfIndex' & Hpcont' & HD''); subst.

  destruct Hstep as [Hstep | Hstep].
  {
    assert (exists idx1, wfCth idx1 (C, Cas)
                          (C ⊎ Cas, (((Mc' ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)) ⊎ M'',
                                      (LR'', F'), []), pc', npc')) (C, PrimSet, (T, t, K', M''))).
    { 
      eapply inital_wfCth_holds; eauto. 
      eapply Wp_stateRel with (Mc := Mc') (MT := MT); eauto.
      assert ((Mc' ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM =
              Mc' ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)).
      {
        rewrite merge_assoc; eauto.
      }
      rewrite H7; eauto.
      eapply disj_merge_disj_sep1; eauto.
      eapply disj_sym.
      eapply disj_sep_merge_still; eauto.
      eapply disj_sym.
      eapply disj_merge_disj_sep2; eauto.
      eapply disj_sym in H11.
      eapply disj_merge_disj_sep2 in H11; eauto.
      rewrite <- merge_assoc; eauto.
      clear - H1 Hstep.
      eapply HProgSafe_progress_and_preservation in H1; eauto.
      simpljoin1.
      eauto.
    }
    destruct H7 as [idx1 H7].
    exists T t K' M'' idx1.
    split.
    right.
    eexists.
    split.
    econstructor; eauto.
    eauto.
    split; eauto.
  }
  { 
    simpljoin1.
    do 5 eexists.
    split.
    left.
    split; eauto.
    simpl in Hpcont'; inv Hpcont'.
    split; eauto.
    eapply clt_wfCth; eauto.
    eapply Wp_stateRel with (Mc := Mc') (MT := MT); eauto.
    assert ((Mc' ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM =
            Mc' ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)).
    {
      rewrite merge_assoc; eauto.
    }
    rewrite H7; eauto.
    eapply disj_merge_disj_sep1; eauto.
    eapply disj_sym.
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym.
    eapply disj_merge_disj_sep2; eauto.
    eapply disj_sym in H11.
    eapply disj_merge_disj_sep2 in H11; eauto.
    rewrite <- merge_assoc; eauto.
  }
Qed.

Lemma wfCth_wfRdy_event_step_preservation :
  forall idx C Cas S pc npc S' pc' npc' PrimSet T t K M Spec v,
    simImpsPrimSet Spec Cas PrimSet -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy (C, Cas) (C, PrimSet) t' K' 
    ) ->
    LP__ (C ⊎ Cas, (S, pc, npc)) (out v) (C ⊎ Cas, (S', pc', npc')) ->
    exists T' t0 K0 M' HP',
      (
        star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\
                    HP__ HP' (out v) (C, PrimSet, (T', t0, K0, M'))
      )
      /\
      (exists idx1, wfCth idx1 (C, Cas) (C ⊎ Cas, (S', pc', npc')) (C, PrimSet, (T', t0, K0, M'))) /\
      (
        forall t1 K1, (ThrdMap.set t0 None T') t1 = Some K1 ->
                      wfRdy (C, Cas) (C, PrimSet) t1 K1 
      ).
Proof.
  intros.
  inv H2.
  {
    (* clt code *)
    lets HLP : H4.
    inv H4.
    inv H17.
    lets Hwp_stateRel : H12.
    inv H12.
    lets HcurTRel : H20.
    inv H20. 
    simpl in H9. 
    inv H9.
    lets HRinj : H22.
    inv H22.
    destruct H10 as [H10 Hdisj_ctx_k]. 
    simpljoin1.
    lets Ho0 : H2.
    specialize (Ho0 r8).
    simpljoin1.
    assert (x2 = v).
    { 
      clear - H24 H10.
      unfolds get_R.
      rewrite H10 in H24; simpls; tryfalse.
      inv H24; eauto.
    } 
    subst x2.
 
    do 5 eexists.
    split.
    split.
    econstructor; eauto.
 
    eapply He_step.
    eapply HPrint; eauto. 
    clear - H15 H16 H0 H6.
    simpls.
    inv H15.
    eapply indom_get_left in H6; eauto.
    clear - H22.
    unfold get_HR.
    rewrite H22; eauto.

    split.
    eapply inital_wfCth_holds; eauto.
    {
      econstructor; eauto.
      econstructor; eauto.
    }
    {
      unfolds HProgSafe.
      intros.
      assert (star_step HP__ (C, PrimSet, (T, t, (HR, b, HF, pc0, npc), M))
                        (C, PrimSet, (T, t, (HR, b, HF, npc, npc +ᵢ ($ 4)), M))).
      {
        simpl in H15.
        inv H15.
        eapply indom_get_left in H6; eauto.
        econstructor.
        econstructor; eauto.
        instantiate (1 := out v).
        eapply He_step; eauto.
        eapply HPrint; eauto.
        unfold get_HR; rewrite H22; eauto.
      }
      eapply multi_step_cons in H23; eauto.
    }
    {
      simpls.
     inv H15; eauto.
    }
    {
      clear - H3.
      intros; eauto.
    }
  }
  {
    clear - H15 H0 H4.
    inv H4.
    inv H10.
    inv H15.
    clear - H3 H11 H0.
    simpljoin1.
    clear H1.
    unfold disjoint in *.
    specialize (H0 pc).
    destruct (C pc) eqn:Heqe.
    destruct (Cas pc) eqn:Heqe1; tryfalse.
    destruct (Cas pc) eqn:Heqe2; tryfalse.
    unfold merge in *.
    rewrite Heqe in H3; simpls.
    destruct c; simpls; tryfalse.
  }
Qed.
 
Lemma wfCth_wfRdy_abort_preservation :
  forall idx C Cas S pc npc PrimSet T t K M Spec,
    simImpsPrimSet Spec Cas PrimSet -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy (C, Cas) (C, PrimSet) t' K' 
    ) ->
    ~ (exists (LP': LProg) m, LP__ (C ⊎ Cas, (S, pc, npc)) m LP') ->
    exists HP' : HProg, star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\ ~ (exists (HP'': HProg) m', HP__ HP' m' HP'').
Proof.
  intros.
  inv H2.

  (* object *)
  Focus 2.
  clear H17 H18 H19.
  inv H15.
  destruct H17 as [Hlegal_pc Hlegal_npc].
  lets Hlegal_pc' : Hlegal_pc.
  eapply legel_pc_ in Hlegal_pc; eauto.
  destruct Hlegal_pc as (i & aexp & rd & f & Hlegal_pc).
  destruct Hlegal_pc as [Hntrans | Hlegal_pc].
  eapply H18 in Hntrans; eauto.
  simpljoin1.
  eapply legal_com_safety_property in H2; eauto.
  simpljoin1.
  eapply LP_CdhpInc with (C2 := C) in H2; eauto.
  rewrite disj_merge_reverse_eq in H2; eauto.
  clear - H4 H2.
  contradiction H4; eauto.
  eapply disj_sym; eauto.

  destruct Hlegal_pc as [Hcall | Hretl].
  eapply H19 in Hcall; eauto; clear H18 H19 H20.
  simpljoin1.
  eapply legal_com_safety_property in H2; eauto.
  simpljoin1.
  eapply LP_CdhpInc with (C2 := C) in H2; eauto.
  rewrite disj_merge_reverse_eq in H2; eauto.
  clear - H4 H2.
  contradiction H4; eauto.
  eapply disj_sym; eauto.

  eapply H20 in Hretl; eauto; clear H18 H19 H20.
  simpljoin1.
  eapply legal_com_safety_property in H2; eauto.
  simpljoin1.
  eapply LP_CdhpInc with (C2 := C) in H2; eauto.
  rewrite disj_merge_reverse_eq in H2; eauto.
  clear - H4 H2.
  contradiction H4; eauto.
  eapply disj_sym; eauto.

  (* client *)
  eexists.
  split.
  econstructor; eauto.
  intro.
  contradiction H4.
  clear H4.
  destruct K.
  destruct p.
  simpls.
  inv H15.

  simpljoin1.
  inv H2.
  {
    inv H12.
    inv H13.
    { 
      inv H19; destruct Q as [R F].
      {
        (* ld aexp ri *)
        do 2 eexists; econstructor; eauto; simpl; eauto.
        eapply LNTrans.
        eapply get_vl_merge_still; eauto.
        eapply NormalIns.
        eapply Ld_step; eauto.
        inv H15.
        eapply Rinj_Heval_impl_eval_addrexp; eauto.
        rewrite disj_merge_reverse_eq; eauto.
        eapply get_vl_merge_still; eauto.
        clear - H15 H20.
        inv H15.
        inv H12.
        simpljoin1.
        unfold indom in *.
        simpljoin1.
        specialize (H ri).
        simpljoin1.
        eauto.
      }
      {
        (* st ri aexp *)
        do 2 eexists; econstructor; eauto; simpl; eauto.
        eapply LNTrans.
        eapply get_vl_merge_still; eauto.
        eapply NormalIns.
        eapply ST_step; eauto.
        eapply Rinj_Heval_impl_eval_addrexp; eauto.
        inv H15; eauto.
        eapply Rinj_getGenregHL_eq; eauto.
        inv H15; eauto.
        rewrite disj_merge_reverse_eq; eauto.
        eapply indom_merge_still; eauto.
      }
      {
        (* nop *) 
        do 2 eexists; econstructor; eauto; simpl; eauto.
        econstructor; eauto.
        eapply get_vl_merge_still; eauto.
        eapply NormalIns.
        eapply Nop_step.
      }
      {
        (* add rs oexp rd *)
        do 2 eexists.
        econstructor; eauto; simpl; eauto.
        eapply LNTrans; eauto.
        eapply get_vl_merge_still; eauto.
        eapply NormalIns.
        eapply Add_step; eauto.
        eapply Rinj_getGenregHL_eq; eauto.
        inv H15; eauto.
        eapply Rinj_Heval_impl_eval_oexp; eauto.
        inv H15; eauto.
        inv H15.
        clear - H28.
        inv H28.
        specialize (H rd).
        simpljoin1.
        unfold indom; eauto.
      }
      {
        (* sub rs oexp rd *)
        do 2 eexists. 
        econstructor; eauto; simpl; eauto.
        eapply LNTrans; eauto.
        eapply get_vl_merge_still; eauto.
        eapply NormalIns.
        eapply Sub_step; eauto.
        eapply Rinj_getGenregHL_eq; eauto.
        inv H15; eauto.
        eapply Rinj_Heval_impl_eval_oexp; eauto.
        inv H15; eauto.
        eapply Rinj_indom_GenReg_HL; eauto.
        inv H15; eauto.
      }
      {
        (* subcc rs oexp rd *)
        do 2 eexists; econstructor; simpl; eauto.
        eapply LNTrans.
        eapply get_vl_merge_still; eauto.
        eapply NormalIns.
        eapply Subcc_step; eauto.
        eapply Rinj_getGenregHL_eq; eauto.
        inv H15; eauto.
        eapply Rinj_Heval_impl_eval_oexp; eauto.
        inv H15; eauto.
        eapply Rinj_indom_GenReg_HL; eauto.
        inv H15; eauto.
        clear - H15.
        inv H15.
        inv H12.
        simpljoin1.
        unfold indom; eauto.
        inv H15.
        inv H29.
        simpljoin1.
        unfold indom; eauto.
      }
      {
        (* Psave sz *)
        inv H15.
        inv H26.
        destruct H19 as [H19 Hdisj_ctx_k].
        simpljoin1.
        lets Hwim : H4.
        specialize (Hwim Rwim).
        simpljoin1.
        renames x to k, x2 to v.
        inv H24.
        destruct H20 as (n & F2 & H20).
        simpljoin1.
        remember (F' ++ F2) as F.
        do 14 (destruct F as [ | ?fm F]; [simpls; tryfalse | idtac]); simpls; try omega.
        clear H29.
        unfold get_R in H20; rewrite H5 in H20; simpl in H20; inv H20.
        unfold get_R in H21; rewrite H19 in H21; simpl in H21; inv H21.
        destruct (win_masked (pre_cwp x) ($ 1) <<ᵢ n) eqn:Heqe.
        {
          assert (length F' = 12%nat).
          {
            clear - H22 H26 H27 H28 Heqe.
            unfolds win_masked, pre_cwp. 
            destruct ((($ 1) <<ᵢ (((x +ᵢ N) -ᵢ ($ 1)) modu N)) &ᵢ (($ 1) <<ᵢ n)) !=ᵢ ($ 0) eqn:Heqe1; simpls; tryfalse.
            eapply nth_bit_and in Heqe1; eauto.
            subst. 
            rewrite fmlst_underflow_len_6 in H28; eauto.
            eapply int_inrange_0_7_sub_one_still; eauto.
          }
          do 13 (destruct F' as [ | ?fm F']; [simpls; tryfalse | idtac]); simpls; try omega.
          clear H20.
          inv HeqF. 
          assert (exists b', get_frame_nth fm23 6 = Some (Ptr (b', $ 0))).
          {
            clear - H25.
            do 6
               (
                 match goal with
                 | H : stkRel _ _ |- _ => inv H
                 end
               ).
            eauto.
          }
          destruct H20 as [b0' Hget_frame_b].
          
          do 2 eexists.
          econstructor; eauto.
          simpl; eauto.
          eapply LPsave_trap.
          eapply get_vl_merge_still; eauto.
          unfold get_R; rewrite H5; eauto.
          unfold get_R; rewrite H19; eauto.
          eauto.
          econstructor; eauto.
          instantiate (4 := [fm14; fm15; fm16; fm17; fm18; fm19; fm20; fm21; fm22]).
          simpls; eauto.
          unfold get_R; rewrite H19; eauto.
        }
        {
          assert (exists b M', Malloc ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)
                                 b $ 0 sz M').
          {
            lets Ht : (finite_memory ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)).
            destruct Ht as (b0 & Ht).
            remember (fun l : Address => match l with
                                       | (b', o') => if Z.eq_dec b0 b' then
                                                      if int_le ($ 0) o' && Int.lt o' sz then
                                                        Some (W ($ 2))
                                                      else
                                                        None
                                                    else None
                                       end) as m. 
            exists b0 (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) ⊎ m).
            econstructor; eauto; intros. 
            destruct (Z.eq_dec b0 b'1) eqn:Heqeb; subst.
            {
              right.
              split; eauto.
              destruct (int_le $ 0 o') eqn:Heqe_intle; destruct (sz >ᵢ o') eqn:Heqe_sz; simpl.
              exists (W $ 2).
              rewrite disj_merge_reverse_eq; eauto.
              eapply get_vl_merge_still; eauto.
              destruct (Z.eq_dec b'1 b'1); tryfalse.
              rewrite Heqe_intle, Heqe_sz.
              simpl; eauto.

              clear - Ht.
              unfold disjoint.
              intros.
              destruct x.
              destruct (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (z, i))
                       eqn:Heqe'.
              {
                destruct (Z.eq_dec b'1 z); eauto.
                subst.
                unfolds Mfresh.
                specialize (Ht i).
                contradiction Ht.
                unfold indom; eauto.
              }
              {
                destruct (Z.eq_dec b'1 z); destruct (int_le $ 0 i); destruct (sz >ᵢ i); simpl; eauto.
              }

              unfold merge at 1.
              destruct (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (b'1, o'))
                       eqn : Heqeb'; eauto.
              destruct (Z.eq_dec b'1 b'1); simpl; tryfalse; eauto.
              rewrite Heqe_intle, Heqe_sz.
              eauto.

              unfold merge at 1.
              destruct (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (b'1, o'))
                       eqn : Heqeb'; eauto.
              destruct (Z.eq_dec b'1 b'1); simpl; tryfalse; eauto.
              rewrite Heqe_intle, Heqe_sz; simpl; eauto.

              unfold merge at 1.
              destruct (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (b'1, o'))
                       eqn : Heqeb'; eauto.
              destruct (Z.eq_dec b'1 b'1); simpl; tryfalse; eauto.
              rewrite Heqe_intle, Heqe_sz; simpl; eauto.
            }
            {
              left.
              split; eauto.
              destruct (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (b'1, o'))
                       eqn : Heqeb'.
              unfold merge at 1.
              rewrite Heqeb'; eauto.
              unfold merge at 1.
              rewrite Heqeb'; eauto.
              destruct (Z.eq_dec b0 b'1); tryfalse; eauto.
            }
          }
          destruct H20 as (b0 & M'' & Hmalloc).
          
          do 2 eexists.
          econstructor; eauto.
          simpl; eauto.
          eapply LPsave_no_trap; eauto.
          eapply get_vl_merge_still; eauto.
          econstructor.
          unfold get_R; rewrite H5; eauto.
          unfold get_R; rewrite H19; eauto.
          eauto.
          eauto.
          eapply fetch_window_HL; eauto.
          instantiate (3 := [fm; fm0; fm3; fm4; fm5; fm6; fm7; fm8; fm9; fm10; fm11]); simpl; eauto.
          eauto.
          eauto.
        }
      }
      {
        (* Prestore *)  
        inv H15.
        inv H24.
        destruct H19 as [H19 Hdisj_ctx_k].
        destruct H2 as (n0 & F2 & H2). 
        simpljoin1.
        remember (F' ++ F2) as F.
        do 14 (destruct F as [ | ?fm F]; [simpls; tryfalse | idtac]); simpls; try omega.
        clear H20.
        inv H26. 
        simpljoin1.
        lets Hwim : (H13 Rwim).
        simpljoin1.

        assert (x = x0).
        { 
          clear - H2 H19.
          unfolds get_R.
          rewrite H19 in H2.
          inv H2; eauto.
        }
        subst x.
        assert (x3 = ($ 1) <<ᵢ n0).
        { 
          clear - H4 H27.
          unfolds get_R.
          rewrite H27 in H4; simpls; eauto.
          inv H4; eauto.
        }
        subst x3.
        
        destruct (win_masked (post_cwp x0) (($ 1) <<ᵢ n0)) eqn:Heqe.
        {
          assert (F' = nil).
          {  
            clear - H15 Heqe H9 H5 H18.
            unfolds win_masked.
            destruct (((($ 1) <<ᵢ (post_cwp x0)) &ᵢ (($ 1) <<ᵢ n0)) !=ᵢ ($ 0)) eqn:Heqe'; tryfalse.
            unfolds post_cwp.
            assert ((x0 +ᵢ ($ 1)) modu N = n0).
            {
              eapply nth_bit_and; eauto.
              eapply int_inrange_0_7_add_one_still; eauto.
            }
            subst. 
            rewrite fmlst_underflow_len_0 in H18; eauto.
            rewrite Int_unsigned_0 in H18; simpls.
            destruct F'; simpls; eauto; tryfalse.
          }
          subst F'.
          simpl in HeqF; subst F2.
          assert (b'0 = b').
          {
            inv H25; eauto.
          }
          subst b'0.
          assert (exists fm1, fetch_frame ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)
                                     (b', $ 0) 
                                     (b', $ 4) (b', $ 8) (b', $ 12) (b', $ 16)
                                     (b', $ 20) (b', $ 24) (b', $ 28) = Some fm1).
          {
            clear - H25 H11 H10 H8 Hdisj_ctx_k.
            inv H25.
            exists fm1. 
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable2; eauto.
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable1; eauto.
            eapply fetch_frame_set_Mframe_same1; eauto.
          }
          destruct H28 as [fm1' Hfetch_Mframe1].
          assert (exists fm2, fetch_frame ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)
                                     (b', $ 32) (b', $ 36) (b', $ 40) (b', $ 44)
                                     (b', $ 48) (b', $ 52) (b', $ 56) (b', $ 60) = Some fm2).
          {
            clear - H25 H11 H10 H8 Hdisj_ctx_k.
            inv H25.
            exists fm2. 
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable2; eauto.
            erewrite fetch_frame_disj_merge_stable1; eauto.
            erewrite fetch_frame_disj_merge_stable2; eauto.
            eapply fetch_frame_set_Mframe_same2; eauto.
          }
          destruct H28 as [fm2' Hfetch_Mframe2].
          
          do 2 eexists.
          econstructor; eauto.
          simpl; eauto.
          eapply LPrestore_trap.
          eapply get_vl_merge_still; eauto.
          instantiate (1 := x0).
          unfold get_R; rewrite H19; eauto.
          instantiate (1 := ($ 1) <<ᵢ n0).
          unfold get_R; rewrite H27; eauto.
          eauto.
          
          econstructor; eauto.
          clear - H21 H7.
          specialize (H7 r30).
          simpljoin1.
          rewrite H21 in H0; inv H0.
          unfold get_R; rewrite H; eauto.
        }
        {
          do 2 eexists.
          econstructor; eauto.
          simpl; eauto.
          eapply LPrestore_no_trap.
          eapply get_vl_merge_still; eauto.
          instantiate (2 := b).
          eauto.
          econstructor.
          unfold get_R; rewrite H19; eauto.
          unfold get_R; rewrite H27; eauto.
          eauto.
          eauto.
          eapply fetch_window_HL; eauto.
          eauto.
          eauto.
          eauto.
        }
      }
    }
    {
      (* cjumpl aexp rd *)
      destruct Q as [R F].
      do 2 eexists; econstructor; eauto.
      simpl; eauto.
      eapply LJumpl; eauto.
      eapply get_vl_merge_still; eauto.
      eapply Rinj_Heval_impl_eval_addrexp; eauto.
      inv H15; eauto.
      eapply Rinj_indom_GenReg_HL; eauto.
      inv H15; eauto.
    }
    {
      (* call f *)
      destruct Q as [R F].
      do 2 eexists; econstructor; eauto.
      simpl; eauto.
      eapply LCall; eauto.
      eapply get_vl_merge_still; eauto.
      eapply Rinj_indom_GenReg_HL; eauto.
      inv H15; eauto.
    }
    {
      (* Retl *)
      destruct Q as [R F].
      do 2 eexists; econstructor; eauto.
      simpl; eauto.
      eapply LRetl; eauto.
      eapply get_vl_merge_still; eauto. 
      eapply Rinj_getGenregHL_eq; eauto.
      inv H15; eauto.
    }
    {
      (* cbe f : true *)
      destruct Q as [R F].
      do 2 eexists; econstructor; eauto.
      simpl; eauto.
      eapply LBe_true; eauto.
      eapply get_vl_merge_still; eauto.
      clear - H15 H19.
      inv H15.
      inv H12.
      simpljoin1.
      unfolds get_HR.
      rewrite H4 in H19; simpls; eauto.
      inv H19.
      unfold get_R.
      rewrite H3; eauto.
    }
    {
      (* cbe f : false *)
      destruct Q as [R F].
      do 2 eexists; econstructor; eauto.
      simpl; eauto.
      eapply LBe_false; eauto.
      eapply get_vl_merge_still; eauto.
      clear - H15 H19.
      inv H15.
      inv H12.
      simpljoin1.
      unfolds get_HR.
      rewrite H4 in H19; simpls; eauto.
      inv H19.
      unfold get_R.
      rewrite H3; eauto.
    }
  }
  {
    inv H13.
    destruct_state S.
    inv H12.
    inv H19.
    inv H25.
    simpljoin1.
    do 2 eexists.
    econstructor.
    simpl; eauto.
    eapply LPrint.
    eapply get_vl_merge_still; eauto.
    instantiate (1 := v).
    clear - H11 H2.
    specialize (H2 r8).
    simpljoin1.
    unfolds get_HR, get_R.
    rewrite H0 in H11.
    inv H11.
    rewrite H; eauto.
  }
  { 
    inv H13.
    unfolds simImpsPrimSet.
    lets Hprim : H15.
    assert (HwdSpec : exists Fp Fq, Spec f = Some (Fp, Fq) /\ wdSpec Fp Fq prim).
    {
      eapply H with (L := nil) in Hprim; eauto.
      simpljoin1.
      do 2 eexists; split; eauto.
    }
    destruct HwdSpec as (Fp & Fq & HSpec & HwdSpec).
    inv HwdSpec.
    specialize (H4 lv).
    destruct H4 as (num & Pr & L & Hpre & Hpost & HSta).

    eapply H with (L := L) in Hprim; eauto.
    simpljoin1.
    rewrite H4 in HSpec; inv HSpec.
    unfold simImpPrim in H9.
    assert (Hinv : INV (Pm prim lv) num lv (S, (T, t, (h, f, f +ᵢ ($ 4)), M), Pm prim lv, num)).
    {
      unfold INV.
      split; eauto.
      split; simpl; eauto.
      left.
      eexists.
      split; eauto.
      econstructor; eauto.
    }

    eapply Hpre in Hinv.
    eapply rel_sep_star_split in Hinv.
    simpljoin1.
    lets Hrel_safety : H13.
    assert (x = lv).
    {
      lets Hlv : H13.
      eapply H6 in Hlv.
      simpl in Hlv.
      simpljoin1.
      inv H23; eauto.
    }
    subst x.
    
    eapply H9 in Hrel_safety; eauto.
    destruct Hrel_safety as (i & Hrel_safety).
    inv Hrel_safety.
    assert (Hcom : exists i aexp rd f',
               (Cas f = Some (c (cntrans i)) \/ Cas f = Some (c (cjumpl aexp rd)) \/ Cas f = Some (c (cbe f')))
               \/ Cas f = Some (c (ccall f')) \/ Cas f = Some (c cretl)).
    {
      eapply legel_pc_; eauto.
    }
    destruct Hcom as (i' & aexp & rd & f' & Hcom).
    destruct Hcom as [Hcom | Hcom].
    {
      eapply H31 in Hcom.
      simpljoin1.
      eapply legal_com_safety_property in H20; eauto.
      simpljoin1.
      eapply LP_CdhpInc with (C2 := C) in H20; eauto.
      rewrite disj_merge_reverse_eq in H20; eauto.
      eapply disj_sym; eauto.
    }
    destruct Hcom as [Hcom | Hcom].
    {
      eapply H32 in Hcom.
      simpljoin1.
      eapply legal_com_safety_property in H20; eauto.
      simpljoin1.
      eapply LP_CdhpInc with (C2 := C) in H20; eauto.
      rewrite disj_merge_reverse_eq in H20; eauto.
      eapply disj_sym; eauto.
    }
    {
      eapply H33 in Hcom; eauto.
      simpljoin1.
      eapply legal_com_safety_property in H20; eauto.
      simpljoin1.
      eapply LP_CdhpInc with (C2 := C) in H20; eauto.
      rewrite disj_merge_reverse_eq in H20; eauto.
      eapply disj_sym; eauto.
    }
  }
Qed.
  
(* Compositionality Proof *)
Lemma wfCth_wfRdy_imply_wpsim :
  forall idx C Cas S pc npc PrimSet T t K M Spec,
    simImpsPrimSet Spec Cas PrimSet -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy (C, Cas) (C, PrimSet) t' K' 
    ) ->
    wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)).
Proof.
  cofix Hp; intros.
  econstructor; intros.
  {
    (* tau *) 
    lets Hpreserve : H2.
    lets HLP : H4.
    lets Hcase : (classic (indom pc C)).
    destruct Hcase as [Hcase | Hcase].
    {
      inv H4.
      eapply wfCth_wfRdy_tau_step_preservation_clt in Hpreserve; eauto.
      destruct Hpreserve as (T' & t0 & K0 & M' & idx1 & Hpreserve).
      destruct Hpreserve as (Hstep & HwfCth & HwfRdy).
      destruct Hstep as [ (Hlt & Hno_step) | (HP' & HHstar_step & HHstep) ].
      {
        left.
        exists idx1.
        split; eauto.
        inv Hno_step.
        eapply Hp; eauto.
      }
      {
        right.
        exists idx1 HP' (C, PrimSet, (T', t0, K0, M')).
        split; eauto.
        split; eauto.
        eapply Hp; eauto.
        clear - H1 HHstar_step HHstep.
        unfolds HProgSafe.
        intros.
        assert (star_tau_step HP__ (C, PrimSet, (T, t, K, M)) (C, PrimSet, (T', t0, K0, M'))).
        econstructor; eauto.
        eapply star_tau_step_impl_star_step in H0.
        assert (Hstar : star_step HP__ (C, PrimSet, (T, t, K, M)) hp').
        eapply multi_step_cons; eauto.
        eapply H1 in Hstar; eauto.
      }
    }
    {
      inv H2; tryfalse. 
      inv H15. 
      assert (exists i aexp rd f,
          (Cas pc = Some (c (cntrans i)) \/ Cas pc = Some (c (cjumpl aexp rd)) \/ Cas pc = Some (c (cbe f)))
              \/ Cas pc = Some (c (ccall f)) \/ Cas pc = Some (c cretl)).
      { 
        clear - H20.
        simpljoin1.
        clear - H.
        unfolds legal_com.
        destruct (Cas pc) eqn:Heqe; simpls; tryfalse.
        destruct c; simpls; eauto; try solve [do 4 eexists; eauto]; tryfalse.
        destruct c; simpls; eauto; try solve [do 4 eexists; eauto]; tryfalse.
      }
      assert (Hnpc : exists i aexp rd f,
          (Cas npc = Some (c (cntrans i)) \/ Cas npc = Some (c (cjumpl aexp rd)) \/ Cas npc = Some (c (cbe f)))
              \/ Cas npc = Some (c (ccall f)) \/ Cas npc = Some (c cretl)).
      { 
        clear - H20.
        simpljoin1.
        clear - H0.
        unfolds legal_com.
        destruct (Cas npc) eqn:Heqe; simpls; tryfalse.
        destruct c; simpls; eauto; try solve [do 4 eexists; eauto]; tryfalse.
        destruct c; simpls; eauto; try solve [do 4 eexists; eauto]; tryfalse.
      } 
      renames H20 to Hlegal_pc_npc.
      destruct H2 as (i & aexp & rd & f & H2).
      destruct Hnpc as (i0 & aexp0 & rd0 & f0 & Hnpc).
  
      destruct H2 as [Hcom | Hcom].
      {
        lets Hcom' : Hcom. 
        eapply H21 in Hcom; clear H21 H22 H23.
        destruct Hcom as [Hprogress' Hpreserve'].
        left.
        inv H4.
        assert (HLP' : LP__ (Cas, (LM, (LR, F), D, pc, npc)) tau (Cas, (LM', (LR'', F'), D'', pc', npc'))).
        {
          clear - H0 HLP Hcom'.
          rewrite disj_merge_reverse_eq with (m1 := C) in HLP; eauto.
          eapply LP__local1; eauto.
          unfold indom.
          repeat (destruct Hcom' as [Hcom' | Hcom']; eauto).
        }
 
        destruct Hprogress' as (Sc' & pc0 & npc0 & Hprogress').
        lets Hpreserve'' : Hprogress'.
        eapply Hpreserve' in Hpreserve''; eauto.
        simpljoin1.
        exists x.
        split; eauto.
        eapply Hp; eauto.

        eapply legal_com_safety_property in Hprogress'; eauto.
        simpljoin1.
        assert ((Cas, (LM', (LR'', F'), D'', pc', npc')) = (Cas, (x0, pc0, npc0))).
        {
          destruct Hcom' as [Hcom' | Hcom'].
          eapply LP_deterministic; eauto. simpl; eauto.
          destruct Hcom' as [Hcom' | Hcom']; eapply LP_deterministic; eauto.
          simpl; eauto.
          simpl; eauto.
        }
        inv H12.
        eapply prim_wfCth; eauto.
      }
      destruct Hcom as [Hcom | Hcom].
      { 
        lets Hcom' : Hcom.
        eapply H22 in Hcom'; clear H21 H22 H23.
        simpljoin1.
        left.
        renames x to Sc1, x1 to pc1, x3 to npc1.
        renames x0 to Sc2, x2 to pc2, x4 to npc2.
        lets Hpreserve' : H2.
        eapply H5 with (S1 := Sc1) in Hpreserve'; eauto.
        simpljoin1.

        inv H4.
        lets H2' : H2.
        eapply legal_com_safety_property in H2'; eauto.
        simpljoin1.
        assert ((Cas, (x1, pc1, npc1)) = (Cas, ((LM', (LR'', F'), D''), pc', npc'))).
        {
          rewrite disj_merge_reverse_eq with (m1 := C) in HLP; eauto.
          eapply LP__local1 in HLP; eauto.
          eapply LP_deterministic; eauto.
          simpl; eauto.
          clear - Hcom.
          unfold indom; eauto.
        }
        inv H20.

        exists x0.
        split; eauto.
        econstructor.
        {
          intros.
          lets Hcom2 : H20.
          inv H20.
          left.
          lets Hpreserve2 : H6.
          eapply legal_com_safety_property in H6; eauto.
          simpljoin1.
          assert (pc' = npc).
          {
            clear - H4 Hcom.
            inv H4.
            inv H15; CElim Cas.
            eauto.
          }
          subst npc.
          assert ((Cas, (x1, pc2, npc2)) = (Cas, ((LM'0, (LR''0, F'0), D''0), pc'0, npc'0))).
          {
            rewrite disj_merge_reverse_eq with (m1 := C) in Hcom2; eauto.
            eapply LP__local1 in Hcom2; eauto.
            clear - H6 Hcom2 Hnpc.
            destruct Hnpc as [Hnpc | Hnpc].
            repeat (destruct Hnpc as [Hnpc | Hnpc]; [eapply LP_deterministic; simpls; eauto | idtac]).
            simpls; eauto.
            simpls; eauto.
            eapply LP_deterministic; eauto.
            simpl; eauto.
            repeat (destruct Hnpc as [Hnpc | Hnpc]; [eapply LP_deterministic; simpls; eauto | idtac]).
            simpls; eauto.
            eapply LP_deterministic; eauto.
            simpl; eauto.
            clear - Hnpc.
            unfold indom.
            repeat (destruct Hnpc as [Hnpc | Hnpc]; [eauto | idtac]).
            eauto.
            eauto.
          }
          inv H22.
          exists x.
          split; eauto.
          eapply Hp; eauto.
          eapply prim_wfCth; eauto.

          assert (pc' = npc).
          {
            clear - H4 Hcom.
            inv H4.
            inv H15; CElim Cas.
            eauto.
          }
          subst; eauto.
        }
        {
          intros.
          lets Hcom2 : H20.
          inv H20.
          lets Hpreserve2 : H6.
          eapply legal_com_safety_property in H6; eauto.
          simpljoin1.
          assert (pc' = npc).
          {
            clear - H4 Hcom.
            inv H4.
            inv H15; CElim Cas.
            eauto.
          }
          subst npc. 
          clear - Hcom2 H6 Hnpc H0.
          rewrite disj_merge_reverse_eq in Hcom2; eauto.
          eapply LP__local1 in Hcom2; eauto.
          inv Hcom2.
          inv H16.
          inv H6.
          inv H15; CElim Cas.
          unfold indom.
          repeat (destruct Hnpc as [Hnpc | Hnpc]; [eauto | idtac]).
          eauto.
          eauto.

          assert (pc' = npc).
          {
            clear - H4 Hcom.
            inv H4.
            inv H15; CElim Cas.
            eauto.
          }
          subst; eauto.
        }
        {
          intros.
          eapply legal_com_safety_property in H6; eauto.
          simpljoin1.
          clear - H6 H20 H0.
          contradiction H20.
          eapply LP_CdhpInc with (C2 := C) in H6; eauto.
          rewrite disj_merge_reverse_eq in H6; eauto.
          eapply disj_sym; eauto.

          assert (pc' = npc).
          {
            clear - H4 Hcom.
            inv H4.
            inv H15; CElim Cas.
            eauto.
          }
          subst; eauto.
        }
      }
      {
        lets Hcom' : Hcom.
        eapply H23 in Hcom'; clear H21 H22 H23.
        simpljoin1.
        renames x to Sc1, x1 to pc1, x3 to npc1.
        renames x0 to Sc2, x2 to pc2, x4 to npc2.
 
        lets Hpreserve' : H2.
        eapply H5 with (S1 := Sc1) in Hpreserve'; eauto.
        simpljoin1.
        inv H4.
        clear H22 H23.
        eapply legal_com_safety_property in H2; eauto.
        simpljoin1.
        assert ((Cas, (LM', (LR'', F'), D'', pc', npc')) = (Cas, (x4, pc1, npc1))).
        {
          clear - H0 HLP H2 Hcom. 
          rewrite disj_merge_reverse_eq in HLP; eauto.
          eapply LP__local1 in HLP; eauto.
          eapply LP_deterministic; eauto.
          simpl; eauto.
          unfold indom; eauto.
        }
        inv H11.
        assert (pc1 = npc).
        {
          clear - H2 Hcom.
          inv H2.
          inv H15; CElim Cas.
          eauto.
        }
        subst pc1.
        destruct H9.
        {
          simpljoin1.
          clear H5.
          left.
          exists (0%nat, 0%nat).
          split; eauto.
          econstructor.
          {
            intros.
            right.
            lets HLP2 : H5.
            inv H5.
            clear H30 H31.
            eapply legal_com_safety_property in H6; eauto.
            simpljoin1.
            assert ((Cas, (LM'0, (LR''0, F'0), D''0, pc', npc')) = (Cas, (x6, x4 +ᵢ ($ 8), x4 +ᵢ ($ 12)))).
            {   
              clear - H0 H5 HLP2 Hnpc.
              rewrite disj_merge_reverse_eq in HLP2; eauto.
              eapply LP__local1 in HLP2; eauto.
              destruct Hnpc as [Hnpc | Hnpc].
              repeat (destruct Hnpc as [Hnpc | Hnpc]; [eapply LP_deterministic; eauto; simpl; eauto | idtac]).
              eapply LP_deterministic; eauto; simpl; eauto.
              destruct Hnpc as [Hnpc | Hnpc]; eapply LP_deterministic; eauto; simpl; eauto.
              unfold indom.
              repeat (destruct Hnpc as [Hnpc | Hnpc]; eauto).
            }
            inv H22.

            assert (Hexec_prim : exists HS' HSr' w', exec_prim (A, (T, t, K, M)) (Pdone, HS')
                                                /\ hstate_union x2 HSr' HS' /\ (x7, HSr', Pdone, w') ||= Pr).
            {
              clear - H11 H14 H18 H21.
              inv H18.
              lets Ht : H11.
              inv Ht.
              destruct H.
              2 : tryfalse.
              assert (Pm prim lv = Pm prim lv); eauto.
            }
            destruct Hexec_prim as (HS' & HSr' & w' & Hexec_prim & Hhstate_union & HPr).

            assert (x1  = Pdone).
            {
              clear - H11.
              inv H11.
              eauto.
            }
            subst x1.
            
            assert (((LM'0, (LR''0, F'0), D''0), HS', Pdone, (x3 + w')%nat) ||= Q ⋆ Pr).
            {
              
              clear - H12 H6 HPr Hhstate_union.
              simpl.
              do 6 eexists. 
              repeat (split; eauto).
            }
            assert (HProgSafe' : HProgSafe (C, PrimSet, HS')).
            {
              clear - H1 Hexec_prim H17.
              inv H17.
              lets Ht : Hexec_prim.
              inv Ht.
              assert (Pm prim lv = Pm prim lv); eauto.
              destruct K.
              destruct p.
              eapply H in H0; eauto.
              simpljoin1.
              unfolds HProgSafe.
              intros.
              assert (star_step HP__ (C, PrimSet, (T, t, (h, w0, w), M)) hp').
              {
                eapply multi_step_cons.
                2 : eauto. 
                eapply multi_step.
                econstructor; eauto.
                instantiate (1 := tau). 
                destruct_hstate HS'.
                eapply Hp_step; eauto.
              }
              eauto.
            }
            assert (Hwp_state' : wp_stateRel (LM'0, (LR''0, F'0), D''0) HS' /\
                                 get_Hs_pcont HS' = (x4 +ᵢ ($ 8), x4 +ᵢ ($ 12))).
            {
              eapply H19; eauto.
              clear - H20 H6.
              simpls.
              destruct_state Sc2.
              destruct_state x7.
              simpls.
              simpljoin1.
              eapply get_vl_merge_still; eauto.
            }
            destruct Hwp_state' as [Hwp_state' Hget_Hs_pcont'].
            lets HwfCth' : Hwp_state'.
            eapply inital_wfCth_holds in HwfCth'; eauto.
            destruct HwfCth' as (idx' & HwfCth').
            exists idx' (C, PrimSet, (T, t, K, M)) (C, PrimSet, HS').
            split.
            econstructor; eauto.
            split.
            clear - Hexec_prim H17.
            inv H17.
            lets Ht : Hexec_prim.
            inv Ht.
            destruct K.
            destruct p.
            assert (Pm prim lv = Pm prim lv); eauto.
            eapply H in H0; eauto.
            simpljoin1.
            destruct_hstate HS'.
            eapply Hp_step; eauto.

            destruct_hstate HS'.
            eapply Hp; eauto.
            intros.
            econstructor; intros.
            eapply inital_wfCth_holds; eauto.
          }
          {
            intros.
            lets HLP2 : H5.
            inv H5.
            clear H30 H31.
            rewrite disj_merge_reverse_eq in HLP2; eauto.
            eapply LP__local1 in HLP2; eauto.
            eapply legal_com_safety_property in H6; eauto.
            simpljoin1.
            clear - HLP2 H5.
            inv HLP2.
            inv H5.
            inv H15.
            inv H13; CElim Cas.
            clear - Hnpc.
            unfold indom.
            repeat (destruct Hnpc as [Hnpc | Hnpc]; eauto).
          }
          {
            intros.
            eapply legal_com_safety_property in H6; eauto.
            simpljoin1.
            contradiction H5.
            clear - H6 H0.
            eapply LP_CdhpInc with (C2 := C) in H6; eauto.
            rewrite disj_merge_reverse_eq in H6; eauto.
            eapply disj_sym; eauto.
          }
        }
        {
          simpljoin1.
          clear H5.
          left.
          exists x0.
          split; eauto.
          econstructor.
          {
            intros.
            lets HLP2 : H5.
            inv H5.
            left.
            exists x.
            split; eauto.
            eapply legal_com_safety_property in H6; eauto.
            simpljoin1.
            assert ((Cas, (x1, pc2, npc2)) = (Cas, (LM'0, (LR''0, F'0), D''0, pc', npc'))).
            {
              clear - HLP2 H5 H0 Hnpc.
              rewrite disj_merge_reverse_eq in HLP2; eauto.
              eapply LP__local1 in HLP2; eauto.
              destruct Hnpc as [Hnpc | Hnpc].
              repeat (destruct Hnpc as [Hnpc | Hnpc]; [eapply LP_deterministic; eauto; simpl; eauto | idtac]).
              eapply LP_deterministic; eauto; simpl; eauto.
              destruct Hnpc as [Hnpc | Hnpc]; eapply LP_deterministic; eauto; simpl; eauto.
              unfold indom.
              repeat (destruct Hnpc as [Hnpc | Hnpc]; [eauto | idtac]).
              eauto.
              eauto.
            }
            inv H20.
            eapply Hp; eauto.
            eapply prim_wfCth; eauto.
          }
          {
            eapply legal_com_safety_property in H6; eauto.
            simpljoin1.
            intros.
            clear - H5 H20 H0 Hnpc.
            lets HLP2 : H20.
            inv H20.
            clear H10 H11.
            rewrite disj_merge_reverse_eq in HLP2; eauto.
            eapply LP__local1 in HLP2; eauto.
            inv HLP2.
            inv H16.
            inv H5.
            inv H15; CElim Cas.
            unfold indom.
            repeat (destruct Hnpc as [Hnpc | Hnpc]; eauto).
          }
          {
            eapply legal_com_safety_property in H6; eauto.
            simpljoin1.
            clear - Hnpc H5 H0.
            eapply LP_CdhpInc with (C2 := C) in H5; eauto.
            rewrite disj_merge_reverse_eq in H5; eauto.
            intro; tryfalse.
            contradiction H; eauto.
            eapply disj_sym; eauto.
          }
        }
      }
    }
  }
  {
    (* event *) 
    lets Hpreserve : H2.
    lets HLP : H4.
    inv H4.     
    eapply wfCth_wfRdy_event_step_preservation in Hpreserve; eauto.
    destruct Hpreserve as (T' & t0 & K0 & M' & HP' & HHP' & Hpreserve).
    destruct Hpreserve as (HwfCth & Hwfrdy).
    destruct HHP' as [HH_star_steps HHstep].
    destruct HwfCth as [idx1 HwfCth].
 
    do 3 eexists.
    split; eauto.
    split; eauto.
    instantiate (1 := idx1).
    eapply Hp; eauto.
    clear - H1 HH_star_steps HHstep.
    unfolds HProgSafe; intros.
    eapply star_tau_step_impl_star_step in HH_star_steps.
    assert (star_step HP__ (C, PrimSet, (T, t, K, M)) (C, PrimSet, (T', t0, K0, M'))).
    eapply multi_step; eauto.
    assert (Hstar : star_step HP__ (C, PrimSet, (T, t, K, M)) hp').
    eapply multi_step_cons; eauto.
    eapply H1 in Hstar; eauto.
  }
  {
    (* abort *)
    eapply wfCth_wfRdy_abort_preservation in H4; eauto.
  }
  Unshelve.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact ($ 2).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact nop.
  exact ($ 3).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact ($ 3).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact ($ 5).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact nop.
  exact ($ 4).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact ($ 5).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
Qed.
