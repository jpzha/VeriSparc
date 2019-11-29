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
Require Import lemmas_comp2.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

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
       exists (Nat.succ (Nat.succ n), p).
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
       instantiate (3 := (Nat.succ n, p)).
       instantiate (3 := (n, p)).
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
  exact (4%nat, (4%nat, 4%nat)).
  exact (4%nat, (4%nat, 4%nat)).
  exact 4%nat.
Qed.

Lemma Lsafety_imp_rel_safety_aux :
  forall n k C S pc npc S' pc' npc' HS HS' k' idx Q A,
    Lsafety n (k, (C, (S, pc, npc))) (k', (C, (S', pc', npc'))) ->
    exec_prim (A, HS) (Pdone, HS') -> rel_safety k' idx (C, S', pc', npc') (Pdone, HS') Q ->
    A <> Pdone ->
    (Nat.eqb k 0 = true -> C pc = Some (c cretl) -> (n = 0)%nat) ->
    rel_safety_aux k (idx_sum (0%nat, (0%nat, n)) idx) (C, S, pc, npc) (A, HS) Q.
Proof.
  cofix Hp; intros. 
  renames H3 to Hstrong.
  inv H.
  {
    destruct idx; simpl.
    destruct p.
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
        exists (idx_sum (0%nat, (0%nat, x2)) idx).
        split.
        eapply idx_sum_pre_lt.
        do 2 eapply lex_ord_right.
        unfold Nat.lt, Nat.succ; omega.
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

      exists (idx_sum (0%nat, (0%nat, x5)) idx) (idx_sum (0%nat, (0%nat, Nat.succ x5)) idx).
      split.
      eapply idx_sum_pre_lt.
      do 2 eapply lex_ord_right.
      unfold Nat.lt, Nat.succ; omega.
      split.
      eapply idx_sum_pre_lt.
      do 2 eapply lex_ord_right.
      unfold Nat.lt, Nat.succ; omega.

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
        exists (idx_sum (0%nat, (0%nat, x5)) idx) (idx_sum (0%nat, (0%nat, Nat.succ x5)) idx).
        do 3 eexists.
        right; eauto.
        split; eauto.
        split; eauto.
        eapply idx_sum_pre_lt; eauto.
        do 2 eapply lex_ord_right.
        unfold Nat.lt, Nat.succ; omega.
        split; eauto.
        eapply idx_sum_pre_lt; eauto.
        do 2 eapply lex_ord_right.
        unfold Nat.lt, Nat.succ; omega.

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
  exists (idx_sum (0%nat, (0%nat, x5)) x3).
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
        (0%nat, (0%nat, 0%nat)) ⩹ idx
    ) ->
    (
      forall k v, 
        C pc = Some Prestore ->
        get_R R cwp = Some (W k) -> get_R R Rwim = Some (W v) ->
        win_masked (post_cwp k) v = true ->
        (0%nat, (0%nat, 0%nat)) ⩹ idx
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
Inductive wfCth (restoreQ : Memory -> RState -> Prop) : Index -> XCodeHeap * XCodeHeap -> LProg -> HProg -> Prop :=
| clt_wfCth : forall C Cas S HS pc npc PrimSet idx,
    wp_stateRel restoreQ S HS -> wfIndex C S pc idx -> 
    get_Hs_pcont HS = (pc, npc) -> indom pc C ->
    wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS)

| prim_wfCth : forall C Cas Sc HSc S HS Sr HSr w Q Pr A pc npc PrimSet idx k,
    state_union Sc Sr S -> hstate_union HSc HSr HS ->
    rel_safety_aux k idx (Cas, Sc, pc, npc) (A, HSc) Q ->
    (Sr, HSr, A, w) ||= Pr -> 
    wfHPrimExec C A HS PrimSet -> Sta A Pr ->
    (
      forall S' HS' w' f, (S', HS', Pdone, w') ||= Q ⋆ Pr -> getregs S' r15 = Some (W f) ->
                     HProgSafe (C, PrimSet, HS') -> (exec_prim (A, HS) (Pdone, HS')) -> 
                     wp_stateRel restoreQ S' HS' /\ get_Hs_pcont HS' = (f +ᵢ ($ 8), f +ᵢ ($ 12)) 
    ) ->
    wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).

(* Well-formed Ready Thread *)
Inductive wfRdy (restoreQ : Memory -> RState -> Prop) :
  XCodeHeap * XCodeHeap -> XCodeHeap * apSet -> Tid -> tlocst -> Prop :=
| cons_wfRdy : forall t K PrimSet C Cas,
    (
      forall S HS f T HM pc npc, 
        wp_stateRel restoreQ S HS -> HS = (T, t, K, HM) -> HProgSafe (C, PrimSet, HS) ->
        getregs S r15 = Some (W f) -> pc = f +ᵢ ($ 8) -> npc = f +ᵢ ($ 12) ->
        get_Hs_pcont HS = (pc, npc) ->
        exists idx, wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS)
    ) ->
    wfRdy restoreQ (C, Cas) (C, PrimSet) t K.

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
  forall Spec C Cas PrimSet S HS pc npc restoreQ,
    simImpsPrimSet Spec Cas PrimSet restoreQ ->
    wp_stateRel restoreQ S HS -> HProgSafe (C, PrimSet, HS) ->
    get_Hs_pcont HS = (pc, npc) -> C ⊥ Cas ->
    exists idx, wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).
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
    exists (5%nat, (6%nat, 6%nat)).
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
    assert (HwdSpec : exists Fp Fq, Spec pc = Some (Fp, Fq) /\ wdSpec restoreQ Fp Fq hprim).
    { 
      clear - H HSpec.
      eapply H with (L := nil) in HSpec.
      destruct HSpec as (lv & Fp & Fq & HSpec & HPrimSet & HAprim & HwdSpec & HsimImpPrim).
      do 2 eexists.
      split; eauto.
    } 
    destruct HwdSpec as (Fp & Fq & HSpec_pc & HwdSpec).
    inv HwdSpec. 
    renames H4 to Hret, H5 to Hprim_exec.
    destruct Hret as [Hret HGoodPrim].
    specialize (H6 lv). 
    destruct H6 as (num & Pr & L & Hwf_pre & Hwf_post & HSta).
    assert (Hinv : INV (Pm hprim lv) num lv (S, (T, t, K, m), (Pm hprim lv), num) restoreQ).
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
    assert (wp_stateRel restoreQ S' HS').
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
  forall C Cas Spec Mc Mr LR F pc npc LM' LR' F' D' pc' npc' T t HR b HF M PrimSet idx restoreQ,
    Mfresh b Mr ->
    simImpsPrimSet Spec Cas PrimSet restoreQ -> C ⊥ Cas -> 
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
  introv HMfresh_sp.
  intros.
  inv H1.
  {
    (* i *)
    inv H16.
    {
      inv H8.
      {
        (* ld aexp ri *)
        assert (HindomM : indom addr M).
        {
          eapply HProgSafe_progress_and_preservation in H2.
          simpljoin1.
          clear H2.
          inv H1.
          inv H19; CElim C.
          inv H20; CElim C.
          inv H6.
          eapply Rinj_eval_impl_Heval_addrexp in H12; eauto.
          rewrite H18 in H12; inv H12.
          unfold indom; eauto.
          inv H19; CElim C.
          inv H19.
          contradiction H10; unfold indom; eauto.
        }

        exists Mc M.
        eexists.
        exists (5%nat, (6%nat, 6%nat)).
        split; eauto.
        split; eauto.
        split; eauto.
        split.
        {
          left.
          econstructor; eauto.
          eapply HNTrans; eauto.
          econstructor; eauto.
          eapply Rinj_eval_impl_Heval_addrexp; eauto.
          inv H6; eauto.
          rewrite disj_merge_reverse_eq in H16; eauto.
          eapply indom_get_left; eauto.
          eapply Rinj_indom_GenReg_LH; eauto.
          inv H6; eauto.
        }
        split; eauto.
        {
          inv H6.
          econstructor; eauto.
          clear - H23.
          unfolds ctxfm.
          simpljoin1.
          do 3 eexists.
          repeat (split; eauto).
          eapply get_R_set_neq_stable; eauto; try intro; tryfalse.
          eapply get_R_set_neq_stable; eauto; try intro; tryfalse.
          eapply Rinj_set_sameLH_stable; eauto.
        }
        split; eauto.
        {
          econstructor; eauto; intros; econstructor; eauto; unfold Nat.lt; try omega.
        }
      }
      {
        (* st ri aexp *)
        assert (Hindom : indom addr M).
        {
          eapply HProgSafe_progress_and_preservation in H2.
          simpljoin1.
          clear H2.
          inv H1.
          inv H19; CElim C.
          inv H20; CElim C.
          inv H6.
          eapply Rinj_eval_impl_Heval_addrexp in H12; eauto.
          rewrite H18 in H12; inv H12; eauto.
          inv H19; CElim C.
          inv H19.
          contradiction H10; eauto.
        }

        exists Mc (MemMap.set addr (Some v) M).
        eexists.
        exists (5%nat, (6%nat, 6%nat)).
        split.
        rewrite disj_merge_reverse_eq; eauto.
        rewrite indom_memset_merge_eq; eauto.
        rewrite disj_merge_reverse_eq; eauto.
        eapply disj_sym in H5.
        eapply disj_indom_memset_still; eauto.

        split; eauto.
        split; eauto.
        eapply disj_sym in H5.
        eapply disj_sym.
        eapply disj_indom_memset_still; eauto.

        split.
        left.
        econstructor; eauto.
        eapply HNTrans; eauto.
        econstructor; eauto.
        eapply Rinj_eval_impl_Heval_addrexp; eauto.
        inv H6; eauto.
        eapply Rinj_GenReg_LH; eauto.
        inv H6; eauto.

        split; eauto.
        inv H6; econstructor; eauto.

        split; eauto.
        econstructor; intros; econstructor; eauto; unfold Nat.lt; try omega.
      }
      {
        (* nop *)
        exists Mc M.
        eexists.
        exists (5%nat, (6%nat, 6%nat)).
        split; eauto.
        split; eauto.
        split; eauto.
        split.

        left.
        econstructor; eauto.
        eapply HNTrans; eauto.
        econstructor; eauto.

        split.
        inv H6; econstructor; eauto.

        split; eauto.
        econstructor; intros; econstructor; eauto; unfold Nat.lt; try omega.
      }
      {
        (* add rs oexp rd *)
        exists Mc M.
        eexists.
        exists (5%nat, (6%nat, 6%nat)).
        split; eauto.
        split; eauto.
        split; eauto.

        split.
        left.
        econstructor; eauto.
        eapply HNTrans; eauto.
        econstructor; eauto.
        eapply Rinj_GenReg_LH; eauto.
        inv H6; eauto.
        eapply Rinj_eval_impl_Heval_opexp; eauto.
        inv H6; eauto.
        eapply Rinj_indom_GenReg_LH; eauto.
        inv H6; eauto.
        split; eauto.

        inv H6.
        econstructor; eauto.
        clear - H23.
        unfolds ctxfm.
        simpljoin1.
        do 3 eexists.
        repeat (split; eauto).
        eapply get_R_set_neq_stable; eauto; intro; tryfalse.
        eapply get_R_set_neq_stable; eauto; intro; tryfalse.
        eapply Rinj_set_sameLH_stable; eauto.

        split; eauto.
        econstructor; intros; econstructor; eauto; unfold Nat.lt; try omega.
      }
      {
        (* sub rs oexp rd *)
        exists Mc M.
        eexists.
        exists (5%nat, (6%nat, 6%nat)).
        split; eauto.
        split; eauto.
        split; eauto.

        split.
        left.
        econstructor; eauto.
        eapply HNTrans; eauto.
        econstructor; eauto.
        eapply Rinj_GenReg_LH; eauto.
        inv H6; eauto.
        eapply Rinj_eval_impl_Heval_opexp; eauto.
        inv H6; eauto.
        eapply Rinj_indom_GenReg_LH; eauto.
        inv H6; eauto.

        split; eauto.
        inv H6; econstructor; eauto.

        clear - H23.
        unfolds ctxfm.
        simpljoin1.
        do 3 eexists.
        repeat (split; eauto).
        eapply get_R_set_neq_stable; eauto; intro; tryfalse.
        eapply get_R_set_neq_stable; eauto; intro; tryfalse.
        eapply Rinj_set_sameLH_stable; eauto.

        split; eauto.
        econstructor; intros; econstructor; eauto; unfold Nat.lt; try omega.
      }
      {
        (* subcc rs oexp rd *)
        exists Mc M.
        eexists.
        exists (5%nat, (6%nat, 6%nat)).
        split; eauto.
        split; eauto.
        split; eauto.

        split.
        left.
        inv H6.
        econstructor; eauto.
        eapply HNTrans; eauto.
        econstructor; eauto.
        eapply Rinj_GenReg_LH; eauto.
        eapply Rinj_eval_impl_Heval_opexp; eauto.
        eapply Rinj_indom_GenReg_LH; eauto.
        inv H26; simpljoin1; unfold indom; eauto.
        inv H26; simpljoin1; unfold indom; eauto.

        split; eauto.
        inv H6.
        econstructor; eauto.
        clear - H24.
        simpls.
        unfolds ctxfm.
        simpljoin1.
        do 3 eexists.
        repeat (split; eauto).        
        repeat (erewrite get_R_set_neq_stable; eauto; try (intro; tryfalse)).
        repeat (erewrite get_R_set_neq_stable; eauto; try (intro; tryfalse)).
        simpl.
        eapply Rinj_set_z_fz_stable; eauto.
        eapply Rinj_set_n_fn_stable; eauto.
        eapply Rinj_set_sameLH_stable; eauto.

        split; eauto.
        econstructor; intros; econstructor; unfold Nat.lt; omega.
      }
      {
        (* and rs oexp rd : high-level doesn't have this instruction *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H18; CElim C.
        inv H19; CElim C.
        inv H18; CElim C.
        inv H18.
        contradiction H10; unfold indom; eauto.
      }
      {
        (* andcc rs oexp rd : high-level doesn't have *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H20; CElim C.
        inv H21; CElim C.
        inv H20; CElim C.
        inv H20.
        contradiction H10; unfold indom; eauto.
      }
      {
        (* or rs oexp rd *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H18; CElim C.
        inv H19; CElim C.
        inv H18; CElim C.
        inv H18.
        contradiction H10; unfold indom; eauto.
      }
      {
        (* sll rs oexp rd *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H18; CElim C.
        inv H19; CElim C.
        inv H18; CElim C.
        inv H18.
        contradiction H10; unfold indom; eauto.
      }
      {
        (* srl rs oexp rd *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H18; CElim C.
        inv H19; CElim C.
        inv H18; CElim C.
        inv H18.
        contradiction H10; unfold indom; eauto.
      }
      {
        (* sett v rd *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H16; CElim C.
        inv H17; CElim C.
        inv H16; CElim C.
        inv H16.
        contradiction H10; unfold indom; eauto.
      }
      {
        (* rd rsp ri *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H17; CElim C.
        inv H18; CElim C.
        inv H17; CElim C.
        inv H17.
        contradiction H10; unfold indom; eauto.
      }
      {
        (* getcwp ri *)
        eapply HProgSafe_progress_and_preservation in H2.
        simpljoin1.
        clear H2.
        inv H1.
        inv H17; CElim C.
        inv H18; CElim C.
        inv H17; CElim C.
        inv H17.
        contradiction H10; unfold indom; eauto.
      }
    }
    {
      (* save rs oexp rd *)
      eapply HProgSafe_progress_and_preservation in H2.
      simpljoin1.
      clear H2.
      inv H1.
      inv H15; CElim C.
      inv H16; CElim C.
      inv H15; CElim C.
      inv H15.
      contradiction H10; unfold indom; eauto.
    }
    {
      (* restore rs oexp rd *)
      eapply HProgSafe_progress_and_preservation in H2.
      simpljoin1.
      clear H2.
      inv H1.
      inv H15; CElim C.
      inv H16; CElim C.
      inv H15; CElim C.
      inv H15.
      contradiction H10; unfold indom; eauto.
    }
    {
      (* wr rs oexp rsp *)
      eapply HProgSafe_progress_and_preservation in H2.
      simpljoin1.
      clear H2.
      inv H1.
      inv H16; CElim C.
      inv H17; CElim C.
      inv H16; CElim C.
      inv H16.
      contradiction H10; unfold indom; eauto.
    }
  }
  {
    (* Jumpl aexp rd *)
    exists Mc M.
    eexists.
    exists (5%nat, (6%nat, 6%nat)).
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
    exists (5%nat, (6%nat, 6%nat)).
    repeat (split; eauto).
    {
      left.
      econstructor; eauto.
      eapply HCall; eauto.
      eapply Rinj_indom_GenReg_LH; eauto.
      inv H6; eauto.
    }
    {
      inv H6.
      econstructor; eauto.
      clear - H19.
      inv H19.
      simpljoin1.
      econstructor; eauto.
      do 2 eexists.
      repeat (split; eauto).
      erewrite get_R_set_neq_stable; eauto; try intro; tryfalse.
      erewrite get_R_set_neq_stable; eauto; try intro; tryfalse.
      eapply Rinj_set_sameLH_stable; eauto.
    }
    {
      intros.
      econstructor; eauto; unfold Nat.lt; try omega.
    }
    {
      intros.
      econstructor; eauto; unfold Nat.lt; try omega.
    }
    simpl; eauto.
  }
  {
    (* Retl *)
    exists Mc M.
    eexists.
    exists (5%nat, (6%nat, 6%nat)).
    split; eauto.
    split; eauto.
    split; eauto.
    split.
    {
      left.
      econstructor; eauto.
      eapply HRetl; eauto.
      instantiate (1 := f).
      inv H6.
      eapply Rinj_GenReg_LH; eauto.
    }
    split.
    {
      inv H6.
      econstructor; eauto.
    }
    split; eauto.
    econstructor; eauto.
    intros; econstructor; eauto; unfold Nat.lt; try omega.
    intros; econstructor; eauto; unfold Nat.lt; try omega.
  }
  {
    (* Be f : true *)
    exists Mc M.
    eexists.
    exists (5%nat, (6%nat, 6%nat)).
    split; eauto.
    split; eauto.
    split; eauto.
    split.
    {
      left.
      econstructor; eauto.
      eapply HBe_true; eauto.
      inv H6.
      clear - H22 H21.
      unfolds get_R, get_HR.
      inv H21.
      simpljoin1.
      rewrite H3 in H22; simpls; tryfalse.
      inv H22.
      rewrite H4; eauto.
    }
    split.
    {
      inv H6.
      econstructor; eauto.
    }
    split; eauto.
    {
      econstructor; eauto.
      intros; econstructor; eauto; unfold Nat.lt; try omega.
      intros; econstructor; eauto; unfold Nat.lt; try omega.
    }
  }
  {
    (* Be f : false *)
    exists Mc M.
    eexists.
    exists (5%nat, (6%nat, 6%nat)).
    split; eauto.
    split; eauto.
    split; eauto.
    split.
    {
      left.
      econstructor; eauto.
      eapply HBe_false; eauto.
      inv H6.
      clear - H22 H21.
      unfolds get_R, get_HR.
      inv H21.
      simpljoin1.
      rewrite H3 in H22; simpls; tryfalse.
      inv H22.
      rewrite H4; eauto.
    }
    split.
    {
      inv H6; econstructor; eauto.
    }
    split; eauto.
    {
      econstructor; eauto.
      intros; econstructor; eauto; unfold Nat.lt; try omega.
      intros; econstructor; eauto; unfold Nat.lt; try omega.
    }
  }
  { 
    (* Psave w : no trap *) 
    exists (fun l : Address => match l with
                        | (b', o') => if Z.eq_dec b' b0 then
                                       if int_leu ($ 0) o' && Int.ltu o' ($ 64) && Int.eq (o' modu $ 4) ($ 0) then
                                         LM' (b', o') else None
                                     else Mc (b', o')
                        end)
      (fun l : Address => match l with
                        | (b', o') => if Z.eq_dec b' b0 then
                                       if int_leu ($ 64) o' && Int.ltu o' w && Int.eq (o' modu $ 4) ($ 0) then
                                         LM' (b', o') else None
                                     else M (b', o')
                        end).
    assert (Hw_range : $ 64 <ᵤᵢ w).
    {
      eapply HProgSafe_progress_and_preservation in H2; eauto.
      simpljoin1.
      inv H1.
      inv H16; CElim C.
      inv H17; CElim C.
      unfolds Malloc.
      simpljoin1; eauto.
      inv H16; CElim C.
      inv H16.
      contradiction H11; eauto.
    } 
    assert (HHsp : HR r14 = Some (Ptr (b, $ 0)) /\ wdFp HR HF).
    {
      eapply HProgSafe_progress_and_preservation in H2; eauto.
      simpljoin1.
      inv H1.
      inv H16; CElim C.
      inv H17; CElim C.
      simpljoin1; eauto.
      inv H16; CElim C.
      inv H16.
      contradiction H11; unfold indom; eauto.
    }
    inv H23.
    renames H11 to HL_cwp, H13 to HL_wim, H15 to Hmask_false, H18 to HL_fetch.
    destruct HHsp as [HHsp HHfp].
      
    do 2 eexists.
    split. 
    {
      clear - H22 H4 H5 Hw_range.
      unfolds Malloc.
      simpljoin1.
      eapply FunctionalExtensionality.functional_extensionality; intros.
      destruct x.
      destruct (Z.eq_dec b0 z); subst.
      {
        specialize (H1 z i).
        destruct H1; simpljoin1; tryfalse.
        unfold merge.
        destruct (Z.eq_dec z z); tryfalse.
        destruct (int_leu $ 0 i) eqn:Heqe1; destruct (Int.ltu i w) eqn:Heqe2;
          destruct (Int.eq (i modu ($ 4)) $ 0) eqn:Heqe'; simpls; eauto.
        {
          simpljoin1. 
          destruct (Int.ltu i $ 64) eqn:Heqe3; eauto.
          rewrite H1; eauto.
          destruct (Mr (z, i)) eqn:Heqe4.
          clear - H Heqe4.
          unfolds Mfresh.
          specialize (H i).
          contradiction H.
          eapply indom_merge_still.
          eapply indom_merge_still2; eauto.
          unfold indom; eauto.
          eapply not_lt_impl_ge in Heqe3.
          rewrite Heqe3; eauto.
        }
        { 
          destruct (Int.ltu i $ 64) eqn:Heqe3; eauto.
          destruct (LM' (z, i)) eqn:Heqe4; eauto.
          destruct (Mr (z, i)) eqn:Heqe5; eauto. 
          unfolds Mfresh; specialize (H i). 
          contradiction H.
          unfold indom; eauto.
          simpl.
          destruct (int_leu $ 64 i); simpl; eauto.
          unfolds Mfresh.
          specialize (H i).
          contradiction H.
          unfold indom; eauto.
          unfolds Mfresh.
          specialize (H i).
          contradiction H.
          unfold indom; eauto.
          simpl; eauto.
          destruct (Mr (z, i)) eqn:Heqe5; eauto; tryfalse.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1; tryfalse.
          destruct (int_leu $ 64 i); simpl; eauto.
          simpl.
          unfolds Mfresh.
          specialize (H i).
          destruct (LM' (z, i)) eqn:Heqe4; tryfalse.
          contradiction H; unfold indom; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3; eauto.
          destruct (int_leu $ 64 i); simpl; eauto.
        }
        {
          destruct (Int.ltu i $ 64) eqn:Heqe3; simpl.
          unfolds Mfresh.
          destruct (LM' (z, i)) eqn:Heqe4; tryfalse; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3; eauto.
          destruct (int_leu $ 64 i); simpl; eauto.
          unfolds Mfresh.
          specialize (H i).
          destruct (LM' (z, i)) eqn:Heqe4; eauto; tryfalse.
          contradiction H; unfold indom; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3; eauto.
          destruct (int_leu $ 64 i); eauto.
        }
        {
          unfolds Mfresh.
          specialize (H i).
          destruct (LM' (z, i)) eqn:Heqe3; eauto.
          contradiction H; unfold indom; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3. 
          destruct (Int.ltu i $ 64) eqn:Heqe4; destruct (int_leu $ 64 i); eauto.
        } 
        {
          unfolds Mfresh.
          specialize (H i).
          destruct (LM' (z, i)) eqn:Heqe3; eauto.
          contradiction H; unfold indom; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3; eauto.
          destruct (int_leu $ 64 i); eauto.
        }
        {
          unfolds Mfresh.
          specialize (H i).
          destruct (LM' (z, i)) eqn:Heqe3; eauto.
          contradiction H; unfold indom; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3; eauto.
          destruct (int_leu $ 64 i); eauto.
        }
        {
          unfolds Mfresh.
          specialize (H i).
          destruct (LM' (z, i)) eqn:Heqe3; eauto.
          contradiction H; unfold indom; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3; eauto.
          destruct (int_leu $ 64 i); eauto.
        }
        {
          unfolds Mfresh.
          specialize (H i).
          destruct (LM' (z, i)) eqn:Heqe3; eauto.
          contradiction H; unfold indom; eauto.
          symmetry in H2.
          eapply merge_none_sep_none in H2; simpljoin1.
          eapply merge_none_sep_none in H1; simpljoin1.
          rewrite H3; eauto.
          destruct (int_leu $ 64 i); eauto.
        }
      }
      {
        specialize (H1 z i).
        destruct H1; simpljoin1; tryfalse.
        unfold merge.
        destruct (Z.eq_dec z b0); subst; tryfalse.
        destruct (Mc (z, i)) eqn:Heqe4.
        eapply get_vl_merge_still with (m := Mr) in Heqe4; eauto.
        eapply get_vl_merge_still with (m := M) in Heqe4; eauto.
        rewrite Heqe4 in H2; eauto.
        destruct (Mr (z, i)) eqn:Heqe5; eauto.
        eapply get_vl_merge_still with (m := Mc) in Heqe5; eauto.
        rewrite disj_merge_reverse_eq in Heqe5; eauto.
        eapply get_vl_merge_still with (m := M) in Heqe5; eauto.
        rewrite Heqe5 in H2; eauto.
        eapply disj_sym; eauto.
        destruct (M (z, i)) eqn:Heqe6; eauto.
        eapply get_vl_merge_still with (m := (Mc ⊎ Mr)) in Heqe6; eauto.
        rewrite disj_merge_reverse_eq in Heqe6; eauto.
        rewrite H2 in Heqe6; eauto.
        eapply disj_sym; eauto.
        clear - H2 Heqe4 Heqe5 Heqe6.
        unfold merge in *.
        rewrite Heqe4, Heqe5, Heqe6 in H2; eauto.
      }
    }
    split.
    { 
      inv H22.
      simpljoin1.
      unfold disjoint; intros.
      destruct x.
      specialize (H9 z i).
      destruct (Z.eq_dec z b0); subst.
      {
        destruct H9; simpljoin1; tryfalse. 
        destruct (int_leu $ 0 i) eqn:Heqe1; destruct (Int.ltu i w) eqn:Heqe2;
          destruct ((i modu ($ 4)) =ᵢ ($ 0)) eqn:Heqe'; simpls; tryfalse; simpljoin1;
            destruct (Mr (b0, i)) eqn:Heqe''; destruct (Int.ltu i $ 64) eqn:Heqe3; simpl; eauto.
        {
          destruct (LM' (b0, i)) eqn:Heqe4; eauto; tryfalse.
          destruct (Mr (b0, i)) eqn:Heqe5; eauto; tryfalse.
          eapply get_vl_merge_still with (m := Mc) in Heqe5; eauto.
          rewrite disj_merge_reverse_eq in Heqe5; eauto. 
          eapply get_vl_merge_still with (m := M) in Heqe5; eauto.
          unfolds Mfresh.
          specialize (H1 i).
          contradiction H1; unfold indom; eauto.
          eapply disj_sym; eauto.
        }
        {
          destruct (LM' (b0, i)) eqn:Heqe4; eauto.
        }
        {
          destruct (LM' (b0, i)) eqn:Heqe4; eauto.
          clear - H1 H10.
          unfolds Mfresh.
          specialize (H1 i).
          contradiction H1; unfold indom; eauto.
        }
        {
          destruct (LM' (b0, i)) eqn:Heqe4; eauto.
        }
      }
      {
        destruct H9; simpljoin1; tryfalse.
        destruct (Mc (z, i)) eqn:Heqe; eauto.
        destruct (Mr (z, i)) eqn:Heqe1; eauto.
        clear - H4 Heqe Heqe1.
        unfold disjoint in *.
        specialize (H4 (z, i)).
        rewrite Heqe, Heqe1 in H4; tryfalse.
        destruct (Mr (z, i)); eauto.
      }
    }
    split.
    {
      unfold disjoint; intros.
      destruct x; simpl.
      unfold merge.
      destruct (Z.eq_dec z b0); subst.
      { 
        destruct (int_leu $ 0 i) eqn:Heqe1; destruct (Int.ltu i $ 64) eqn:Heqe2;
          destruct (i modu ($ 4)) =ᵢ ($ 0) eqn:Heqe'; simpl; eauto; tryfalse.
        {
          destruct (LM' (b0, i)) eqn:Heqe.
          destruct (int_leu $ 64 i) eqn:Heqe3; destruct (Int.ltu i w) eqn:Heqe4; simpl; eauto.
          eapply lt_impl_not_ge in Heqe2; tryfalse.
          destruct (Mr (b0, i)) eqn:Heqe3; eauto.
          destruct (int_leu $ 64 i); destruct (Int.ltu i w); simpl; eauto.
          destruct (int_leu $ 64 i); destruct (Int.ltu i w); simpl; eauto.
        }
        {
          destruct (Mr (b0, i)) eqn:Heqe3; eauto.
          destruct (int_leu $ 64 i) eqn:Heqe4; destruct (Int.ltu i w) eqn:Heqe5; simpl; eauto.
          destruct (int_leu $ 64 i); destruct (Int.ltu i w); simpl; eauto.
        }
        {
          destruct (Mr (b0, i)) eqn:Heqe3; 
            destruct (int_leu $ 64 i) eqn:Heqe4; destruct (Int.ltu i w) eqn:Heqe5; 
              destruct (LM' (b0, i)) eqn:Heqe6; simpl; eauto.
          unfolds Malloc, Mfresh.
          simpljoin1.
          specialize (H1 i).
          contradiction H1; unfold indom.
          exists v0.
          eapply get_vl_merge_still; eauto.
          rewrite disj_merge_reverse_eq; eauto.
          eapply get_vl_merge_still; eauto.
        } 
        {
          destruct (Mr (b0, i)) eqn:Heqe3; eauto;
            destruct (int_leu $ 64 i) eqn:Heqe4; destruct (Int.ltu i w) eqn:Heqe5; simpl; eauto.
        }
        {
          destruct (Mr (b0, i)) eqn:Heqe3; eauto;
            destruct (int_leu $ 64 i) eqn:Heqe4; destruct (Int.ltu i w) eqn:Heqe5;
              destruct (LM' (b0, i)) eqn:Heqe6; simpl; eauto.
          unfolds Malloc, Mfresh; simpljoin1.
          specialize (H1 i).
          contradiction H1; unfold indom.
          exists v0.
          eapply get_vl_merge_still; eauto.
          rewrite disj_merge_reverse_eq; eauto.
          eapply get_vl_merge_still; eauto.
        }
        {
          destruct (Mr (b0, i)) eqn:Heqe3; eauto;
            destruct (int_leu $ 64 i) eqn:Heqe4; destruct (Int.ltu i w) eqn:Heqe5;
              destruct (LM' (b0, i)) eqn:Heqe6; simpl; eauto.
        }
        {
          destruct (Mr (b0, i)) eqn:Heqe3; eauto;
            destruct (int_leu $ 64 i) eqn:Heqe4; destruct (Int.ltu i w) eqn:Heqe5;
              destruct (LM' (b0, i)) eqn:Heqe6; simpl; eauto.
          unfolds Malloc, Mfresh; simpljoin1.
          specialize (H1 i).
          contradiction H1; unfold indom.
          exists v0.
          eapply get_vl_merge_still; eauto.
          rewrite disj_merge_reverse_eq; eauto.
          eapply get_vl_merge_still; eauto.
        }
        {
          destruct (Mr (b0, i)) eqn:Heqe3; eauto;
            destruct (int_leu $ 64 i) eqn:Heqe4; destruct (Int.ltu i w) eqn:Heqe5;
              destruct (LM' (b0, i)) eqn:Heqe6; simpl; eauto.
        }
      }
      {
        unfolds Malloc.
        simpljoin1.
        specialize (H9 z i).
        destruct H9; simpljoin1; tryfalse.
        destruct (Mc (z, i)) eqn:Heqe; eauto.
        destruct (M (z, i)) eqn:Heqe1; eauto.
        eapply disj_sym in H5.
        eapply disj_merge_disj_sep in H5; eauto.
        simpljoin1.
        clear - H5 Heqe Heqe1.
        unfold disjoint in *.
        specialize (H5 (z, i)).
        rewrite Heqe1, Heqe in H5; eauto.
        destruct (Mr (z, i)) eqn:Heqe1; eauto.
        destruct (M (z, i)) eqn:Heqe2; eauto.
        eapply disj_sym in H5.
        eapply disj_merge_disj_sep in H5; eauto.
        simpljoin1.
        clear - H11 Heqe1 Heqe2.
        unfold disjoint in *.
        specialize (H11 (z, i)).
        rewrite Heqe1, Heqe2 in H11; tryfalse.
        destruct (M (z, i)); eauto.
      }
    }
    split.
    {
      left.
      econstructor; eauto.
      eapply HNTrans; eauto.  
      econstructor.
      eapply fetch_window_LH; eauto.
      inv H6; eauto.
      inv H21; eauto.

      split.
      instantiate (1 := fm2).
      instantiate (1 := fm1).
      eauto.
      split; eauto.

      instantiate (1 := b0).
      unfold Malloc.
      inv H22.
      split.
      eapply block_fresh_merge_sep in H1.
      simpljoin1; eauto.
      split; eauto.
      simpljoin1.
      intros.
      specialize (H9 b' o').
      destruct H9; simpljoin1.
      {
        left.
        split; eauto.
        destruct (Z.eq_dec b' b0); tryfalse; eauto.
      }
      { 
        right. 
        split; eauto.
        destruct (Z.eq_dec b' b'); tryfalse; subst.
        assert (Hnone : M (b', o') = None).
        {
          clear - H1 H4 H5.
          destruct (M (b', o')) eqn:Heqe; eauto.
          unfolds Mfresh.
          specialize (H1 o').
          contradiction H1; unfold indom; eauto.
          rewrite disj_merge_reverse_eq; eauto.
          exists v.
          eapply get_vl_merge_still; eauto.
        } 
        destruct (int_leu $ 0 o') eqn:Heqe1; destruct (Int.ltu o' w) eqn:Heqe2; simpls; simpljoin1;
          try solve [destruct (int_leu $ 64 o') eqn:Heqe3;
                     destruct (o' modu ($ 4)) =ᵢ ($ 0) eqn:Heqe4; simpls; eauto].
        destruct (int_leu $ 64 o') eqn:Heqe3; destruct ((o' modu ($ 4)) =ᵢ ($ 0)) eqn:Heqe4; simpls; eauto.
        clear - Heqe1 Heqe3.
        destruct o'; unfolds int_leu, Int.ltu, Int.eq; simpls.
        try rewrite Int_unsigned_0, Int_unsigned_64 in *.
        destruct (zlt 0 intval); destruct (zeq 0 intval); destruct (zlt 64 intval); destruct (zeq 64 intval);
          simpls; tryfalse; try omega.
      }
    }
    split.
    { 
      inv H6.
      simpljoin1.
      assert (b <> b0).
      {
        clear - H22 H18.
        unfolds Malloc; simpljoin1.
        intro; subst.
        unfolds Mfresh.
        specialize (H ($ 0)).
        contradiction H.
        specialize (H18 (b0, $ 0)). 
        do 3 try eapply indom_merge_still.
        simpljoin1.
        eapply H2.
        unfold DomCtx.
        destruct (Z.eq_dec t b0); tryfalse.
        destruct (Z.eq_dec b0 b0); tryfalse; eauto.
      }
      assert (forall ofs, Mk (b0, ofs) = None).
      {
        intros; clear - H22.
        unfolds Malloc; simpljoin1.
        do 3 (eapply block_fresh_merge_sep in H; simpljoin1).
        clear - H4.
        unfolds Mfresh.
        specialize (H4 ofs).
        unfold indom in *.
        destruct (Mk (b0, ofs)) eqn:Heqe; eauto.
        contradiction H4; eauto.
      }
      assert (forall ofs, Mk (b, ofs) = None).
      {  
        clear - H18 H20 H6; intros.
        specialize (H18 (b, ofs)); simpljoin1.
        destruct (classic (indom (b, ofs) Mk)); unfold indom in *; simpljoin1; eauto.
        eapply indom_stk_ofs_in_restrict_range with (ofs' := ofs) in H20; eauto.
        2 : unfold indom; eauto.
        Focus 2.
        destruct (Mk (b, ofs)) eqn:Heqe; eauto.
        contradiction H1; eauto. 
        assert (DomCtx (b, ofs) t b).
        {
          unfold DomCtx.
          destruct (Z.eq_dec t b); eauto; tryfalse.
          destruct (Z.eq_dec b b); subst; tryfalse; eauto.
        }
        eapply H in H2; simpljoin1.
        unfold disjoint in *.
        specialize (H6 (b, ofs)).
        rewrite H2, H1 in H6; tryfalse.
      }
      assert (Ht_neq_b0 : t <> b0).
      {
        clear - H22 H18.
        intro; subst.
        unfolds Malloc; simpljoin1.
        specialize (H18 (b0, $ 0)); simpljoin1.
        do 3 (eapply block_fresh_merge_sep in H; simpljoin1).
        clear - H H2 H3.
        assert (DomCtx (b0, $ 0) b0 b).
        unfold DomCtx.
        destruct (Z.eq_dec b0 b0); subst; tryfalse; eauto.
        eapply H2 in H0.
        unfolds Mfresh.
        specialize (H $ 0); contradiction H; eauto.
      }
      assert (HMk_t_none : forall ofs, Mk (t, ofs) = None).
      { 
        clear - H18 H20 H6; intros.
        destruct (Mk (t, ofs)) eqn:Heqe; eauto.
        eapply indom_stk_ofs_in_0_inrange with (b' := t) in H20; eauto.
        2 : unfold indom; eauto.
        specialize (H18 (t, $ 0)).
        simpljoin1.
        assert (DomCtx (t, $ 0) t b).
        {
          unfold DomCtx.
          destruct (Z.eq_dec t t); subst; tryfalse.
          eauto.
        }
        eapply H in H1; eauto.
        clear - H6 H20 H1.
        unfold indom in *; simpljoin1.
        unfold disjoint in *.
        specialize (H6 (t, $ 0)).
        unfolds Tid.
        rewrite H0, H in H6; tryfalse.
      } 
      econstructor. 
      instantiate (2 :=
                     fun l : Address => match l with
                                      | (b'0, o'0) => if Z.eq_dec b'0 b0 then
                                                       if int_leu $ 0 o'0 && Int.ltu o'0 $ 64
                                                                 &&  (o'0 modu ($ 4)) =ᵢ ($ 0)then
                                                         LM' (b'0, o'0)
                                                       else
                                                         None
                                                     else
                                                       if Z.eq_dec b'0 t then
                                                         Mctx (b'0, o'0)
                                                       else
                                                         None
                                      end
                  ).
      instantiate (1 :=
                     fun l : Address => match l with
                                      | (b'0, o'0) => if Z.eq_dec b'0 b then
                                                       if int_leu $ 0 o'0 && Int.ltu o'0 $ 64
                                                                  && (o'0 modu ($ 4)) =ᵢ ($ 0)then
                                                         Mctx (b'0, o'0)
                                                       else
                                                         None
                                                     else Mk (b'0, o'0)
                                      end
                  ).
      split; simpljoin1.
      {
        eapply FunctionalExtensionality.functional_extensionality; eauto; intros.
        destruct x.
        unfold merge.
        destruct (Z.eq_dec z b0); subst.
        { 
          destruct (int_leu $ 0 i); destruct (Int.ltu i $ 64);
            destruct (Z.eq_dec b0 b); destruct ( (i modu ($ 4)) =ᵢ ($ 0)); simpl; eauto; tryfalse.
          destruct (LM' (b0, i)) eqn:Heqe; eauto.
        } 
        {
          destruct (Mctx (z, i)) eqn:Heqe1.
          destruct (Z.eq_dec z t); subst; eauto.
          destruct (Z.eq_dec z b); subst; eauto.

          specialize (H18 (b, i)). 
          assert (indom (b, i) Mctx); unfold indom; eauto.
          simpljoin1.
          eapply H11 in H10; eauto.
          unfold DomCtx in H10.
          destruct (Z.eq_dec t b); tryfalse.
          destruct (Z.eq_dec b b); tryfalse.
          simpljoin1. 
          rewrite H10, H14.
          simpl; eauto.
          rewrite H15; eauto.
          
          assert (indom (z, i) Mctx); unfold indom; eauto.
          specialize (H18 (z, i)); simpljoin1.
          eapply H11 in H10.
          unfold DomCtx in H10.
          destruct (Z.eq_dec t z); tryfalse.
          destruct (Z.eq_dec b z); tryfalse.

          destruct (Z.eq_dec z t); subst; tryfalse.
          destruct (Z.eq_dec t b); subst; tryfalse; eauto.
          destruct (int_leu $ 0 i); destruct (Int.ltu i $ 64); destruct (i modu ($ 4)) =ᵢ ($ 0); eauto.
          destruct (Z.eq_dec z b); subst; tryfalse; eauto.
          rewrite H9.
          destruct (int_leu $ 0 i); destruct (Int.ltu i $ 64); destruct (i modu ($ 4)) =ᵢ ($ 0); eauto.
        }
      }
      {
        unfold disjoint; intros.
        destruct x.
        destruct (Z.eq_dec z b0); subst.
        destruct (int_leu $ 0 i) eqn:Heqe1; destruct (Int.ltu i $ 64) eqn:Heqe2;
          destruct (i modu ($ 4)) =ᵢ ($ 0) eqn:Heqe'; destruct (Z.eq_dec b0 b);
            try rewrite H8; simpl; subst; eauto; tryfalse.
        {
          destruct (LM' (b0, i)) eqn:Heqe3; eauto.
        }
        
        destruct (Z.eq_dec z t); subst; tryfalse; eauto.
        destruct (Mctx (t, i)) eqn:Heqe; subst; eauto; unfolds Tid.
        rewrite Heqe.
        destruct (Z.eq_dec t b); subst; simpl; tryfalse.
        specialize (H18 (b, i)).
        simpljoin1.
        assert (indom (b, i) Mctx); unfold indom; eauto.
        eapply H10 in H13.
        unfold DomCtx in H13.
        destruct (Z.eq_dec b b); subst; tryfalse.
        rewrite HMk_t_none; eauto.
        rewrite Heqe.
        rewrite HMk_t_none.
        destruct (Z.eq_dec t b); destruct (int_leu $ 0 i); destruct (Int.ltu i $ 64);
          destruct ((i modu ($ 4)) =ᵢ ($ 0)); simpl; eauto.
        destruct (Mctx (z, i)); destruct (Mk (z, i));
          destruct (Z.eq_dec z b); destruct (int_leu $ 0 i); destruct (Int.ltu i $ 64);
            destruct ((i modu ($ 4)) =ᵢ ($ 0)); simpl; eauto.
      }
      {
        intros.
        split; eauto.
        destruct l.
        split; intros.
        {
          unfold indom in H10.
          simpljoin1.
          destruct (Z.eq_dec z b0); subst; eauto.
          destruct (int_leu $ 0 i) eqn:Heqe1; destruct (Int.ltu i $ 64) eqn:Heqe2;
            destruct ((i modu ($ 4)) =ᵢ ($ 0)) eqn:Heqe3; simpl in H10; tryfalse.
          
          unfold DomCtx.
          destruct (Z.eq_dec t b0); eauto; tryfalse.
          destruct (Z.eq_dec b0 b0); eauto; tryfalse.
          
          destruct (Z.eq_dec z t); subst; tryfalse.
          specialize (H18 (t, i)).
          simpljoin1.
          assert (indom (t, i) Mctx); unfold indom; eauto.
          eapply H11 in H14.
          unfold DomCtx in H14.
          destruct (Z.eq_dec t t); subst; tryfalse.
          unfold DomCtx.
          destruct (Z.eq_dec t t); subst; tryfalse; eauto.
        }
        { 
          unfold DomCtx in H10.
          destruct (Z.eq_dec t z); subst; eauto.
          unfold indom.
          destruct (Z.eq_dec z b0); subst; tryfalse.
          destruct (Z.eq_dec z z); subst; eauto; tryfalse.
          assert (DomCtx (z, i) z b).
          {
            unfold DomCtx.
            destruct (Z.eq_dec z z); tryfalse; eauto.
          }
          specialize (H18 (z, i)); simpljoin1.
          eapply H13 in H11; eauto.
  
          destruct (Z.eq_dec b0 z); subst; tryfalse; eauto.
          unfold indom.
          destruct (Z.eq_dec z z); tryfalse; eauto.
          simpljoin1.
          rewrite H10, H11; simpl; eauto.
          rewrite H13.
          clear - H22 H10 H11 Hw_range H13. 
          unfolds Malloc; simpljoin1.
          specialize (H1 z i).
          destruct H1; simpljoin1; tryfalse.
          assert (i <ᵤᵢ w).
          eapply int_ltu_trans; eauto.
          rewrite H10, H1, H13 in H2; simpls; eauto.
        }
      }
      {
        instantiate (1 := fml :: fmi :: F').
        inv H19.
        simpljoin1.
        rewrite HL_cwp in H10; inv H10.
        rewrite HL_wim in H11; inv H11.
        repeat (destruct F'0 as [_ | ?fm F'0]; simpl in H19; tryfalse); clear H19.
        unfold win_masked in Hmask_false.
        destruct (((($ 1) <<ᵢ (pre_cwp x)) &ᵢ (($ 1) <<ᵢ x0)) !=ᵢ ($ 0)) eqn:Heqe; tryfalse.
        assert (Hmask_false' : pre_cwp x <> x0).
        {
          intro; subst.
          clear - Heqe H15.
          destruct (classic (((($ 1) <<ᵢ (pre_cwp x)) &ᵢ (($ 1) <<ᵢ (pre_cwp x))) = $ 0)).
          rewrite H in Heqe; tryfalse.
          eapply and_zero_not_eq in H; eauto; tryfalse.
          eapply in_range_0_7_pre_cwp_still; eauto.
          eapply in_range_0_7_pre_cwp_still; eauto.
          eapply negb_false_iff in Heqe.
          eapply int_eq_true_eq in Heqe; tryfalse.
        }
        lets Hrange : H15.
        eapply not_overflow with (x0 := x0) in Hrange; eauto.
        eapply valid_frame_list_length in Hrange.
        rewrite <- H17 in Hrange.
        assert (exists fm1' fm2' x', x1 = x' ++ [fm1'; fm2']).
        {
          clear - H14 Hrange.
          destruct x1; subst; simpls.
          repeat (destruct F' as [_ | ?fm F']; simpls; tryfalse; try omega).
          destruct x1; subst; simpls.
          repeat (destruct F' as [_ | ?fm F']; simpls; tryfalse; try omega).
          eapply list_get_tail_two; eauto.
          destruct x1; simpl; omega.
        }
        destruct H10 as (fm1' & fm2' & x' & H10); subst.
        rewrite <- app_assoc_reverse in H14.
        eapply list_tail_two in H14; eauto; simpljoin1.
        econstructor.
        instantiate (1 := pre_cwp x).
        exists x0 x'.
        split.
        { 
          simpl.
          eapply get_R_set_neq_stable; eauto.
          2 : intro; tryfalse.
          eapply get_R_set_R_same_reg; eauto.
          intro; tryfalse.
          eapply indom_setwin_still.
          clear - HL_cwp.
          unfold get_R, indom in *.
          destruct (LR cwp); eauto.
        }
        split.
        { 
          simpl. 
          eapply get_R_set_neq_stable; eauto.
          2 : intro; tryfalse.
          eapply get_R_set_neq_stable; eauto.
          2 : intro; tryfalse.
          eapply get_R_spreg_set_window_still; eauto.
        }
        split; eauto.
        split; eauto.
        {
          simpl.
          rewrite <- H14; eauto.
        }
        split; eauto.
        {
          eapply in_range_0_7_pre_cwp_still; eauto.
        }
        split; eauto.
        split; eauto.
        {
          rewrite <- valid_rotate_add_1; eauto.
          rewrite <- H17.
          simpl; eauto.
        }
      }
      {
        instantiate (1 := b).
        assert (Hfetch_frame1 : exists fm1, fetch_frame Mctx (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12)
                                                  (b, $ 16) (b, $ 20) (b, $ 24) (b, $ 28) = Some fm1).
        {
          eapply DomCtx_fetch_frame_0; eauto.
        }
        destruct Hfetch_frame1 as [fm1' Hfetch_frame1].
        assert (Hfetch_frame2 : exists fm2, fetch_frame Mctx (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44)
                                                   (b, $ 48) (b, $ 52) (b, $ 56) (b, $ 60) = Some fm2).
        {
          eapply DomCtx_fetch_frame_32; eauto.
        }
        destruct Hfetch_frame2 as [fm2' Hfetch_frame2].
        assert (Hmem : 
            (fun l : Address => match l with
                             |  (b'0, o'0) => if Z.eq_dec b'0 b then
                                               if int_leu $ 0 o'0 && Int.ltu o'0 $ 64 &&
                                                          (o'0 modu ($ 4)) =ᵢ ($ 0) then
                                                 Mctx (b'0, o'0)
                                               else None
                                             else Mk (b'0, o'0)
                              end) = set_Mframe' b $ 0 fm1' ⊎ set_Mframe' b $ 32 fm2' ⊎ Mk).
        {
          unfold merge.
          eapply FunctionalExtensionality.functional_extensionality; intros.
          destruct x. 
          destruct (set_Mframe' b $ 0 fm1' (z, i)) eqn:Heqe1.
          {
            lets Hset_addr1 : Heqe1.
            eapply set_Mframe'_get_some_address_0 in Hset_addr1; simpljoin1.
            destruct (Z.eq_dec b b); tryfalse.
            rewrite H11.
            eapply int_ltu_trans with (p := $ 64) in H13; eauto.
            rewrite H13, H14; simpl.
            eapply fetch_frame_set_Mframe_get0; eauto.
          }
          { 
            destruct (set_Mframe' b $ 32 fm2' (z, i)) eqn:Heqe2.
            lets Hset_addr2 : Heqe2.
            eapply set_Mframe'_get_some_address_32 in Hset_addr2; simpljoin1.
            destruct (Z.eq_dec b b); tryfalse.
            eapply int_leu_trans with (n := $ 0) in H11; eauto.
            rewrite H11, H13, H14; simpl.
            eapply fetch_frame_set_Mframe_get32; eauto.

            destruct (Z.eq_dec z b); subst; eauto.
            rewrite H9. 
            destruct (int_leu $ 0 i) eqn:Hrange1; destruct (Int.ltu i $ 64) eqn:Hrange2;
              destruct (i modu ($ 4)) =ᵢ ($ 0) eqn:Heqe3; simpl; eauto.
            assert (Hrange_sp : $ 0 <=ᵤᵢ i <ᵤᵢ $ 64).
            rewrite Hrange1, Hrange2; eauto.
            eapply range_split with (c := $ 32) in Hrange_sp; eauto.
            destruct Hrange_sp as [Hrange_sp | Hrange_sp].
            {
              eapply range_legal_set_Mframe_ok0 in Hrange_sp; simpljoin1; eauto.
              rewrite H10 in Heqe1; tryfalse.
            }
            {
              eapply range_legal_set_Mframe_ok32 in Hrange_sp; simpljoin1; eauto.
              rewrite H10 in Heqe2; tryfalse.
            }
          }
        }
        rewrite Hmem.
        eapply LFconsHFcons; eauto.
        eapply set_frame_0_32_disj; eauto.
        clear - H9.
        eapply disj_sym.
        eapply disj_sep_merge_still; eauto.
        unfold disjoint; intros.
        destruct (Mk x) eqn:Heqe1; eauto.
        destruct (set_Mframe' b $ 0 fm1' x) eqn:Heqe2; eauto.
        eapply set_Mframe'_get_some_address_0 in Heqe2; eauto; simpljoin1.
        rewrite H9 in Heqe1; tryfalse.
        destruct (set_Mframe' b $ 0 fm1' x) eqn:Heqe2; eauto.
        unfold disjoint; intros.
        destruct (Mk x) eqn:Heqe1; eauto.
        destruct (set_Mframe' b $ 32 fm2' x) eqn:Heqe2; eauto.
        eapply set_Mframe'_get_some_address_32 in Heqe2; eauto; simpljoin1.
        rewrite H9 in Heqe1; tryfalse.
        destruct (set_Mframe' b $ 32 fm2' x) eqn:Heqe2; eauto.

        clear -  H21 HL_fetch HHfp H20.
        assert (HRfp : HR r30 = Some (Ptr (b', $ 0))).
        {
          unfolds wdFp; simpljoin1.
          inv H20; eauto.
        }
        inv H21; simpljoin1.
        specialize (H r30).
        simpljoin1.
        rewrite HRfp in H6; inv H6.
        clear - HL_fetch H.
        unfolds fetch.
        destruct (fetch_frame LR r8 r9 r10 r11 r12 r13 r14 r15); tryfalse.
        destruct (fetch_frame LR r16 r17 r18 r19 r20 r21 r22 r23); tryfalse.
        destruct (fetch_frame LR r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe; tryfalse.
        inv HL_fetch.
        unfold fetch_frame in Heqe.

        do 8 (match goal with
              | H : context [LR ?A] |- _ => destruct (LR A) eqn:?Heqe; simpls; tryfalse
              end).
        inv Heqe; simpl; eauto.
      }
      {
        simpl. 
        eapply Rinj_set_sameLH_stable'; eauto.
        eapply Rinj_set_cwp_stable.
        eapply Rinj_set_window_HL; eauto.
      }
    }
    split; eauto.
    {
      instantiate (1 := (5%nat, (6%nat, 6%nat))).
      econstructor; eauto; intros; econstructor; eauto; unfold Nat.lt; omega.
    }
  }
  {
    (* Psave w : trap *)
    inv H25. 
    assert (HlenF1 : length F1 = 9%nat).
    {
      inv H6.
      inv H21.
      simpljoin1.
      repeat (destruct F1 as [_ | ?fm F1]; simpls; tryfalse).
      eauto.
    } 
    
    repeat (destruct F1 as [_ | ?fm F1]; simpl in HlenF1; tryfalse); clear HlenF1.
    inv H6.
    inv H21.
    simpljoin1.
    clear H15.
    rewrite H22 in H1; inv H1.
    rewrite H23 in H18; inv H18. 
    rewrite H23 in H6. 
    eapply shr_same_bit_eq in H6; eauto; subst w0.
    unfolds win_masked. 
    destruct (((($ 1) <<ᵢ (pre_cwp x)) &ᵢ (($ 1) <<ᵢ x0)) !=ᵢ ($ 0)) eqn:Heqe; tryfalse.
    lets Hwin_mask : Heqe.
    eapply nth_bit_and in Heqe; eauto; subst.
    2 : eapply in_range_0_7_pre_cwp_still; eauto.
    unfold pre_cwp in H12. 
    rewrite fmlst_underflow_len_6 in H12; eauto.
    rewrite Int_unsigned_6 in H12; simpl in H12.
    repeat (destruct F' as [_ | ?fm F']; simpl in H12; tryfalse); clear H12.
    repeat (destruct x1; simpl in H9; tryfalse).
    inv H9.

    lets HstkRel : H25.
    eapply stkRel_sep with (F1 := [fm12; fm13; fm14; fm15; fm16; fm17; fm18; fm19; fm20; fm21])
                           (F2 := [fm22; fm23]) (n := 5%nat) in HstkRel; eauto.
    destruct HstkRel as (M1 & M2 & HF1 & HF2 & b'0 & HstkRel).
    simpljoin1.
    specialize (H18 fm20 fm21 [fm12; fm13; fm14; fm15; fm16; fm17; fm18; fm19]).
    simpl in H18.
    lets Hget_frame_b : H14.
    rewrite H18 in Hget_frame_b; eauto.
    inv Hget_frame_b; clear H18.

    rewrite fetch_some_set_Mframe_still.
    rewrite fetch_some_set_Mframe_still.
    rewrite fetch_some_set_Mframe_still.
    rewrite fetch_some_set_Mframe_still.
    rewrite fetch_some_set_Mframe_still2.
    rewrite fetch_some_set_Mframe_still2.
    rewrite fetch_some_set_Mframe_still2.
    rewrite fetch_some_set_Mframe_still2.

    do 3 eexists.
    exists (0%nat, (0%nat, 0%nat)).
    split; eauto.

    split.
    {
      eapply disj_sym in H4.
      eapply disj_merge_disj_sep in H4.
      simpljoin1.
      eapply disj_sym.
      eapply disj_sep_merge_still; eauto.
      eapply disj_merge_disj_sep in H4.
      simpljoin1.
      eapply disj_sep_merge_still; eauto.
      eapply disj_sym in H9.
      eapply disj_sym.
      eapply disjoint_setMfrm_still; eauto.
      eapply indoms_setMframe_still; eauto. 
      inv H13.
      eapply indoms_merge_left.
      eapply indoms_merge_right.
      eapply indoms_set_Mframe'_32; eauto.
      eapply disjoint_setMfrm_still; eauto.
      inv H13; eauto. 
      eapply indoms_merge_left.
      eapply indoms_merge_left.
      eapply indoms_set_Mframe'_0.
    }
    split.
    {
      eapply disj_sym in H5.
      eapply disj_merge_disj_sep in H5.
      simpljoin1.
      eapply disj_merge_disj_sep in H1.
      simpljoin1.
      eapply disj_merge_disj_sep in H9.
      simpljoin1.

      eapply disj_sym.
      eapply disj_sep_merge_still; eauto.
      eapply disj_sep_merge_still; eauto.
      eapply disj_sep_merge_still; eauto.
      eapply disj_sym. 
      eapply disjoint_setMfrm_still; eauto.
      eapply indoms_setMframe_still; eauto.
      clear - H13.
      inv H13.
      eapply indoms_merge_left.
      eapply indoms_merge_right.
      eapply indoms_set_Mframe'_32; eauto.

      eapply disjoint_setMfrm_still; eauto.
      2 : eapply disj_sym; eauto.
      clear - H13.
      inv H13.
      eapply indoms_merge_left.
      eapply indoms_merge_left.
      eapply indoms_set_Mframe'_0; eauto.
    }
    split.
    {
      right.
      split; eauto.
      split; eauto.
      inv H7.
      eapply H30; eauto.
      unfold win_masked; eauto.
      rewrite Hwin_mask; eauto.
    } 
    split.
    {
      econstructor.
      split; eauto.
      eapply disj_merge_disj_sep in H17; simpljoin1.
      eapply disj_sep_merge_still; eauto.
      eapply disj_sym.
      eapply disjoint_setMfrm_still; eauto.
      eapply indoms_setMframe_still; eauto.
      clear - H13.
      inv H13.
      eapply indoms_merge_left.
      eapply indoms_merge_right. 
      eapply indoms_set_Mframe'_32.
      eapply disjoint_setMfrm_still; eauto.
      clear - H13.
      inv H13.
      eapply indoms_merge_left.
      eapply indoms_merge_left.
      eapply indoms_set_Mframe'_0; eauto.
      eapply disj_sym; eauto.

      eauto.

      simpl.
      instantiate (1 := [fm12; fm13; fm14; fm15; fm16; fm17; fm18; fm19; fm20; fm21]).
      econstructor.
      do 2 eexists.
      split.
      {
        erewrite get_R_set_neq_stable; eauto.
        intro; tryfalse.
      }
      split.
      {
        rewrite get_R_set_R_same_reg; eauto.
        intro; tryfalse.
        clear - H23.
        unfold get_R, indom in *.
        destruct (LR Rwim) eqn:Heqe; eauto.
      }
      split.
      {
        eapply pre_2_neq; eauto.
      }
      split.
      {
        instantiate (1 := [fm22; fm23; f]); simpl; eauto.
      }
      split; eauto.
      split.
      {
        eapply in_range_0_7_pre_cwp_still; eauto.
      }
      split; simpl; eauto.
      {
        unfold pre_cwp.
        rewrite caculate_5; eauto.
      }
      { 
        inv H13.
        
        instantiate (1 := b').
        assert ([fm12; fm13; fm14; fm15; fm16; fm17; fm18; fm19; fm20; fm21] =
                [fm12; fm13; fm14; fm15; fm16; fm17; fm18; fm19; fm20; fm21] ++ nil); eauto.
        rewrite H1; clear H1. 
        eapply stkRel_merge with (b2 := b0); simpl; eauto. 
        rewrite fetch_some_set_Mframe_still.
        rewrite fetch_some_set_Mframe_still.
        rewrite fetch_some_set_Mframe_still. 
        rewrite fetch_some_set_Mframe_still2.
        eapply LFnilHFcons.
        rewrite set_Mframe_set_Mframe'_same_0.
        rewrite  set_Mframe_set_Mframe'_same_32.
        unfold set_Mframe'; eauto.

        eapply disj_dom_eq_still with (m1 := set_Mframe' b0 $ 0 fm1')
                                      (m2 := set_Mframe' b0 $ 32 fm2'); eauto.
        unfold set_Mframe'.
        eapply dom_eq_set_same_Mframe; eauto.
        unfold set_Mframe'.
        eapply dom_eq_set_same_Mframe; eauto.

        eapply disj_dom_eq_still; eauto.
        eapply dom_eq_merge_still.
        unfold set_Mframe'.
        eapply dom_eq_set_same_Mframe; eauto.
        unfold set_Mframe'.
        eapply dom_eq_set_same_Mframe; eauto.
        eapply same_m_dom_eq.

        eauto.

        eauto.

        rewrite set_Mframe_set_Mframe'_same_0.
        clear - H30.
        unfolds set_Mframe'.
        eapply disj_dom_eq_still; eauto.
        eapply dom_eq_set_same_Mframe; eauto.
        eapply same_m_dom_eq; eauto.

        eapply indoms_set_Mframe'_32; eauto.
        eapply indoms_set_Mframe'_0; eauto.
 
        eapply indoms_setMframe_still.
        eapply indoms_merge_right.
        eapply indoms_set_Mframe'_32; eauto.
        eapply indoms_merge_left.
        eapply indoms_set_Mframe'_0; eauto.

        simpl; eauto.

        eapply disj_sym.
        eapply disjoint_setMfrm_still.
        eapply indoms_setMframe_still.
        eapply indoms_merge_left.
        eapply indoms_merge_right.
        eapply indoms_set_Mframe'_32; eauto.

        eapply disjoint_setMfrm_still.
        eapply indoms_merge_left.
        eapply indoms_merge_left.
        eapply indoms_set_Mframe'_0; eauto.
        eapply disj_sym; eauto.

        intros.
        repeat (destruct F' as [_ | ?fm F']; simpls; tryfalse).
        inv H1; eauto.
      }
      {
        clear - H26.
        inv H26; simpljoin1.
        econstructor; eauto.
        intros.
        specialize (H rr).
        simpljoin1.
        erewrite getR_setR_neq_stable; eauto.
        intro; tryfalse.

        split; intros.
        lets Hwim : H0 Rwim.
        specialize (H0 sr).
        simpljoin1.
        unfold set_R.
        unfold is_indom.
        rewrite H6.
        destruct (RegName_eq Rwim sr); subst; eauto.
        inv e.
        rewrite RegMap.gss; eauto.
        rewrite RegMap.gso; eauto.

        split; do 3 (try split; try (erewrite getR_setR_neq_stable; eauto; try intro; tryfalse)).
      }
    }
    split; eauto.
    {
      econstructor; eauto.
      2 : intros; CElim C.
      intros.
      erewrite get_R_set_same_stable in H18; eauto; try intro; tryfalse.
      inv H18.
      erewrite get_R_set_neq_stable in H9; eauto; try intro; tryfalse.
      inv H9.
      clear - H19 H24.
      unfolds win_masked.
      destruct (((($ 1) <<ᵢ (pre_cwp k)) &ᵢ (($ 1) <<ᵢ (pre_cwp (pre_cwp k)))) !=ᵢ ($ 0)) eqn:Heqe; tryfalse.
      eapply nth_bit_and in Heqe; eauto.
      eapply pre_1_neq in H19.
      contradiction H19; eauto.
      eapply in_range_0_7_pre_cwp_still; eauto.
    }

    eapply disj_sym.
    eapply disjoint_setMfrm_still; eauto.
    2 : eapply disj_sym; eauto.
    clear - H13; inv H13.
    eapply indoms_merge_left.
    eapply indoms_merge_left.
    eapply indoms_set_Mframe'_0; eauto.
 
    eapply indoms_setMframe_still; eauto.
    2 : eapply disj_sym; eauto.
    2 : eapply disj_sym; eauto.
    clear - H13; inv H13.
    eapply indoms_merge_left.
    eapply indoms_merge_right.
    eapply indoms_set_Mframe'_32; eauto.

    clear - H13; inv H13.
    eapply indoms_merge_left.
    eapply indoms_merge_left.
    eapply indoms_set_Mframe'_0; eauto.
    
    eapply disj_sym.
    eapply disjoint_setMfrm_still; eauto.
    2 : eapply disj_sym; eauto.
    eapply indoms_merge_right.
    clear - H13; inv H13.
    do 2 eapply indoms_merge_left.
    eapply indoms_set_Mframe'_0; eauto.
    2 : eapply disj_sym; eauto.
    2 : eapply disj_sym; eauto.

    eapply indoms_setMframe_still.
    eapply indoms_merge_right.
    clear - H13; inv H13.
    eapply indoms_merge_left.
    eapply indoms_merge_right.
    eapply indoms_set_Mframe'_32.
    eapply indoms_merge_right.
    clear - H13; inv H13.
    do 2 eapply indoms_merge_left.
    eapply indoms_set_Mframe'_0.

    eapply indoms_setMframe_still; eauto.
    do 2 eapply indoms_merge_right.
    clear - H13; inv H13.
    eapply indoms_merge_left.
    eapply indoms_merge_right.
    eapply indoms_set_Mframe'_32.

    do 2 eapply indoms_merge_right.
    clear - H13; inv H13.
    do 2 eapply indoms_merge_left.
    eapply indoms_set_Mframe'_0.

    eapply indoms_setMframe_still; eauto.
    eapply indoms_merge_left.
    do 2 eapply indoms_merge_right.
    clear - H13; inv H13.
    eapply indoms_merge_left.
    eapply indoms_merge_right.
    eapply indoms_set_Mframe'_32.

    eapply indoms_merge_left.
    do 2 eapply indoms_merge_right.
    clear - H13; inv H13.
    do 2 eapply indoms_merge_left.
    eapply indoms_set_Mframe'_0.
  }
  {
    (* Prestore : no trap *)
    assert (HHprop : exists b' fm1 fm2 HF', HR r14 = Some (Ptr (b, $ 0)) /\ HR r30 = Some (Ptr (b', $ 0))
                                       /\ HF = (b', fm1, fm2) :: HF').
    {
      clear - H13 H2.
      eapply HProgSafe_progress_and_preservation in H2; eauto; simpljoin1.
      inv H; CElim C.
      inv H8; CElim C.
      inv H9; CElim C.
      simpljoin1; eauto.
      do 4 eexists.
      repeat (split; eauto).
      inv H8; CElim C.
      inv H8.
      contradiction H4; unfold indom; eauto.
    }
    destruct HHprop as (b' & fm1 & fm2 & HF' & HHR_sp & HHR_fp & HHF); subst.    
    inv H24.
    assert (b0 = b).
    {
      clear - HHR_sp H23 H6.
      inv H6.
      inv H13.
      simpljoin1.
      specialize (H r14); simpljoin1.
      rewrite H23 in H; inv H; eauto.
      rewrite HHR_sp in H5; inv H5; eauto.
    }
    subst b0.
    
    exists (Mfree Mc b) (Mfree M b).
    eexists.
    exists (5%nat, (6%nat, 6%nat)).

    split.
    rewrite Mfree_merge_sep.
    rewrite Mfree_merge_sep_fresh_right; eauto.

    split.
    eapply Mfree_left_disjoint_stable; eauto.

    split.
    eapply Mfree_both_sides_disjoint_stable with (b := b) in H5; eauto.
    rewrite Mfree_merge_sep_fresh_right in H5; eauto.

    split.
    {
      left.
      econstructor.
      eapply HNTrans; eauto.
      econstructor; eauto.
      eapply fetch_window_LH; eauto.
      inv H6.
      inv H26; eauto.
    }

    split; eauto.
    {
      inv H6.
      inv H24; simpljoin1.
      rewrite H11 in H1; inv H1.
      rewrite H12 in H6; inv H6.
      unfold win_masked in H15.
      destruct (((($ 1) <<ᵢ (post_cwp x)) &ᵢ (($ 1) <<ᵢ x0)) !=ᵢ ($ 0)) eqn:Heqe; tryfalse.
      unfold post_cwp in Heqe.

      lets Hin : H10.
      eapply post_valid_head_two with (x0 := x0) in Hin; eauto.
      Focus 2.
      clear - Heqe H10 H14.
      intro; subst. 
      destruct (classic (((($ 1) <<ᵢ ((x +ᵢ ($ 1)) modu N)) &ᵢ (($ 1) <<ᵢ ((x +ᵢ ($ 1)) modu N))) = $ 0)).
      rewrite H in Heqe.
      unfolds Int.eq.
      rewrite Int_unsigned_0 in Heqe; eauto.
      destruct (zeq 0 0); simpls; tryfalse.
      eapply and_zero_not_eq in H; eauto; tryfalse.
      eapply negb_false_iff in Heqe.
      eapply int_eq_true_eq in Heqe; tryfalse.
      eapply range_1_6_lenF_ge_2 in Hin; eauto.
      rewrite <- H17 in Hin.
      assert (exists fm1' fm2' F'', F' = fm1' :: fm2' :: F'').
      {
        destruct F'; simpls; tryfalse; try omega.
        destruct F'; simpls; tryfalse; try omega.
        eauto.
      }
      destruct H1 as (fm1' & fm2' & F'' & HLF''); subst.
      simpl in H9.
      inv H9.
      assert (b'0 = b').
      {
        inv H25; subst; eauto.
      }
      subst b'0.
      assert (Hblock_neq : b <> b').
      {
        clear - H22 H25 H20. 
        intro; subst.
        eapply indom_stkRel_HF_b_0_in with (b' := b') in H25; simpl; eauto.
        specialize (H22 (b', $ 0)); simpljoin1.

        assert (indom (b', $ 0) Mctx).
        {
          eapply H.
          unfold DomCtx.
          destruct (Z.eq_dec t b'); subst; tryfalse.
          destruct (Z.eq_dec b' b'); subst; tryfalse.
          split; eauto.
        }
        unfold indom in *; simpljoin1.
        unfold disjoint in *.
        specialize (H20 (b', $ 0)).
        rewrite H1, H2 in H20; tryfalse.
      }
      assert (Hblock_neq_t : b' <> t).
      {
        intro; subst.
        eapply indom_stkRel_HF_b_0_in with (b' := t) in H25; simpl; eauto.
        clear - H20 H25 H22.
        specialize (H22 (t, $ 0)).
        simpljoin1.

        assert (indom (t, $ 0) Mctx).
        {
          eapply H.
          unfold DomCtx.
          destruct (Z.eq_dec t t); subst; tryfalse; eauto.
        }
        unfold indom, disjoint in *; simpljoin1.
        specialize (H20 (t, $ 0)).
        unfolds Tid; rewrite H1, H2 in H20; tryfalse.
      }

      assert (HMk_b_none : forall ofs, Mk (b, ofs) = None).
      {
        clear - H22 H20 H25; intros.
        specialize (H22 (b, ofs)); simpljoin1.
        destruct (classic (indom (b, ofs) Mk)); unfold indom in *; simpljoin1; eauto.
        eapply indom_stk_ofs_in_restrict_range with (ofs' := ofs) in H25; eauto.
        2 : unfold indom; eauto.
        Focus 2.
        destruct (Mk (b, ofs)) eqn:Heqe; eauto.
        contradiction H1; eauto. 
        assert (DomCtx (b, ofs) t b).
        {
          unfold DomCtx.
          destruct (Z.eq_dec t b); eauto; tryfalse.
          destruct (Z.eq_dec b b); subst; tryfalse; eauto.
        }
        eapply H in H2; simpljoin1.
        unfold disjoint in *.
        specialize (H20 (b, ofs)).
        rewrite H2, H1 in H20; tryfalse.
      }
      
      inv H25.

      econstructor.
      { 
        instantiate
          (2 := fun l : Address => match l with
                                 | (b'0, o'0) => if Z.eq_dec b'0 b' then
                                                    (set_Mframe' b' $ 0 fm1'0 ⊎ set_Mframe' b' $ 32 fm2'0) (b'0, o'0)
                                                else
                                                  if Z.eq_dec b'0 t then
                                                    Mctx (b'0, o'0)
                                                  else
                                                    None
                                 end).
        instantiate (1 := Mfree M' b).
        split. 
        { 
          unfold Mfree, disjoint.
          eapply FunctionalExtensionality.functional_extensionality; intros.
          destruct x2; simpl. 
          destruct (Z.eq_dec b z); subst; tryfalse.
 
          unfold merge.
          destruct (Z.eq_dec z b'); tryfalse; eauto.
          specialize (H22 (z, i)); simpljoin1.
          destruct (Z.eq_dec z t); tryfalse.
          destruct (Z.eq_dec z z); tryfalse; eauto.

          unfold merge. 
          destruct (Mctx (z, i)) eqn:Heqe'; destruct (Z.eq_dec z b'); subst; tryfalse; eauto.
          {
            specialize (H22 (b', i)).
            simpljoin1.
            assert (indom (b', i) Mctx).
            unfold indom; eauto.

            eapply H9 in H15.
            clear - n H15 Hblock_neq_t.
            unfolds DomCtx.
            destruct (Z.eq_dec t b'); tryfalse; eauto.
            destruct (Z.eq_dec b b'); tryfalse.
          }
          {
            destruct (Z.eq_dec z t); subst; eauto.
            destruct (Z.eq_dec b z); subst; tryfalse.
            assert (indom (z, i) Mctx).
            unfold indom; eauto.
            specialize (H22 (z, i)); simpljoin1.
            eapply H18 in H1.
            unfold DomCtx in H1.
            destruct (Z.eq_dec t z); tryfalse.
            destruct (Z.eq_dec b z); tryfalse.
          }
          {
            destruct (Z.eq_dec b b'); eauto; tryfalse.
          }
          {
            destruct (set_Mframe' b' $ 0 fm1'0 (z, i)) eqn:Heqe1; tryfalse.
            eapply set_Mframe'_get_some_address_0 in Heqe1; eauto; simpljoin1; tryfalse.
            destruct (set_Mframe' b' $ 32 fm2'0 (z, i)) eqn:Heqe2; tryfalse.
            eapply set_Mframe'_get_some_address_32 in Heqe2; eauto; simpljoin1; tryfalse.
            destruct (Z.eq_dec z t); subst; eauto; tryfalse.
            destruct (Z.eq_dec b t); subst; eauto; tryfalse.
            destruct (Z.eq_dec b z); subst; eauto; tryfalse.
          }
        }
        {
          eapply Mfree_right_disjoint_stable; eauto.
          unfold disjoint; intros.
          destruct x2.
          destruct (Z.eq_dec z b'); subst; eauto.

          destruct ((set_Mframe' b' $ 0 fm1'0 ⊎ set_Mframe' b' $ 32 fm2'0) (b', i)) eqn:Heqe1;
            destruct (M' (b', i)) eqn:Heqe2; eauto; tryfalse.
          clear - H31 Heqe1 Heqe2.
          unfold disjoint in *.
          specialize (H31 (b', i)).
          rewrite Heqe1, Heqe2 in H31; tryfalse.
 
          destruct (Z.eq_dec z t); destruct (M' (z, i)) eqn:Heqe1;
            destruct (Mctx (z, i)) eqn:Heqe2; subst; tryfalse; eauto.
          clear - H20 Heqe1 Heqe2.
          eapply disj_merge_disj_sep in H20; simpljoin1.
          eapply disj_merge_disj_sep in H; simpljoin1.
          unfold disjoint in H0.
          specialize (H0 (t, i)).
          unfolds Tid.
          rewrite Heqe2, Heqe1 in H0; tryfalse.
        }
      }
      {
        intros.
        split; eauto.

        split; intros.
        {
          unfold indom in H1; simpljoin1.
          destruct l; simpls.
          destruct (Z.eq_dec z b'); subst; tryfalse.
          destruct (Z.eq_dec t b'); subst; tryfalse.
          destruct (Z.eq_dec b' b'); subst; tryfalse.
          eapply indom_merge_indom_one_of in H1; eauto; simpljoin1.
          destruct H1.
          eapply set_Mframe'_get_some_address_0 in H1; eauto.
          simpljoin1.
          split; eauto.
          split; eauto.
          eapply int_ltu_trans with (m := $ 32); eauto.
          eapply set_Mframe'_get_some_address_32 in H1; eauto.
          simpljoin1.
          split; eauto.
          eapply int_leu_trans with (m := $ 32); eauto.

          destruct (Z.eq_dec z t); subst; tryfalse; eauto.
          specialize (H22 (t, i)); simpljoin1.
          assert (indom (t, i) Mctx).
          unfold indom; eauto.
          eapply H15 in H21; eauto.
          unfold DomCtx in H21.
          destruct (Z.eq_dec t t); tryfalse; eauto.
        }
        {
          unfold indom; destruct l.
          destruct (Z.eq_dec z b'); subst; eauto.

          unfold DomCtx in H1.
          destruct (Z.eq_dec t b'); subst; tryfalse.
          destruct (Z.eq_dec b' b'); subst; tryfalse.
          simpljoin1.
          assert (Hrange : $ 0 <=ᵤᵢ i <ᵤᵢ $ 64); eauto.
          rewrite H1, H6; eauto.
          eapply range_split with (c := $ 32) in Hrange; eauto.
          destruct Hrange as [Hrange | Hrange].
          eapply range_legal_set_Mframe_ok0 with (b := b') (fm := fm1'0) in Hrange; eauto.
          simpljoin1.
          exists x2.
          eapply get_vl_merge_still; eauto.
          eapply range_legal_set_Mframe_ok32 with (b := b') (fm := fm2'0) in Hrange; eauto.
          simpljoin1.
          exists x2.
          rewrite disj_merge_reverse_eq; eauto.
          eapply get_vl_merge_still; eauto.

          destruct (Z.eq_dec z t); subst; tryfalse.
          unfold DomCtx in H1.
          destruct (Z.eq_dec t t); tryfalse; subst.
          assert (indom (t, i) Mctx).
          {
            specialize (H22 (t, i)); simpljoin1.
            eapply H18; unfold DomCtx.
            destruct (Z.eq_dec t t); tryfalse; eauto.
          }
          unfold indom in H6; simpljoin1; eauto.

          clear - H1 n n0.
          unfolds DomCtx.
          destruct (Z.eq_dec t z); subst; tryfalse.
          destruct (Z.eq_dec b' z); subst; tryfalse.
        }
      }
      {
        instantiate (1 := F'').
        econstructor. 
        exists x0 (x1 ++ [fmo; fml]).
        split.
        simpl; rewrite get_R_set_R_same_reg; eauto.
        intro; tryfalse.
        eapply indom_setwin_still; eauto.
        clear - H26.
        inv H26; simpljoin1.
        unfold indom; eauto. 

        split.
        eapply get_R_set_neq_stable; eauto.
        2 : intro; tryfalse.
        eapply get_R_spreg_set_window_still; eauto.

        split.
        eapply negb_false_iff in Heqe.
        unfold post_cwp.
        eapply int_eq_true_eq in Heqe; eauto.
        eapply and_zero_not_eq in Heqe; eauto.
        eapply in_range_0_7_post_cwp_still; eauto.

        split; eauto.
        rewrite app_assoc_reverse; eauto.

        split.
        eapply in_range_0_7_post_cwp_still; eauto.

        split; eauto.

        split; eauto.
        unfold post_cwp.
        rewrite <- valid_rotate_sub_1; eauto.
        clear - H17; simpls.
        rewrite <- H17; simpl.
        rewrite Nat.sub_0_r; eauto.
        eapply negb_false_iff in Heqe.
        eapply int_eq_true_eq in Heqe; eauto.
        eapply and_zero_not_eq in Heqe; eauto.
        eapply in_range_0_7_post_cwp_still; eauto.

        rewrite app_length; simpl; eauto.
        simpl in H19.
        rewrite Nat.add_comm; eauto.
      }
      {
        instantiate (1 := b'0).
        rewrite Mfresh_Mfree_stable; eauto.
        clear - HMk_b_none.
        unfold Mfresh; intros.
        unfold indom; intro; subst; simpljoin1.
        specialize (HMk_b_none o).
        eapply merge_none_sep_none in HMk_b_none; simpljoin1; tryfalse.
      }
      {
        simpl.
        eapply Rinj_set_cwp_stable, Rinj_set_window_HL; eauto.
      }
    }

    split; eauto.
    econstructor; intros; econstructor; eauto; unfold Nat.lt; try omega.
  }
  {
    (* Prestore : trap *)
    assert (exists HF' fm1' fm2' b0, HF = (b0, fm1', fm2') :: HF' /\ get_HR HR r30 = Some (Ptr (b0, $ 0))).
    {
      eapply HProgSafe_progress_and_preservation in H2; eauto; simpljoin1.
      inv H1.
      inv H15; CElim C.
      inv H17; CElim C.
      simpljoin1.
      do 4 eexists.
      split; eauto.
      unfold get_HR; rewrite H8; eauto.
      inv H15; CElim C.
      inv H15.
      contradiction H11; unfold indom; eauto.
    }
    destruct H1 as (HF' & fm1' & fm2' & b0 & H_HF & H_Hr30); subst.
     
    inv H25.
    simpljoin1.
    rewrite H23 in H1.
    inv H1. 
    do 3 eexists.
    exists (0%nat, (0%nat, 0%nat)).

    split; eauto.
    split; eauto.
    split; eauto.
    split.
    {
      right.
      split; eauto.
      split; eauto.
      inv H7.
      eapply H20; eauto.
    }
    split.
    { 
      inv H6.
      inv H26.
      simpljoin1.
      rewrite H22 in H1; inv H1.
      rewrite H23 in H6. 
      eapply shr_same_bit_eq in H6; eauto; subst w.
      lets Hwin_mask : H24.
      unfold win_masked in H24.
      destruct (((($ 1) <<ᵢ (post_cwp x)) &ᵢ (($ 1) <<ᵢ x0)) !=ᵢ ($ 0)) eqn:Heqe; tryfalse.
      eapply nth_bit_and in Heqe; eauto; subst.
      unfold post_cwp in H13.
      rewrite fmlst_underflow_len_0 in H13; eauto.
      2 : eapply in_range_0_7_post_cwp_still; eauto.
 
      rewrite Int_unsigned_0 in H13; simpl in H13.
      destruct F'; simpls; tryfalse.
      econstructor.
      eauto.
      eauto.

      instantiate (1 := fm1'0 :: fm2'0 :: nil).
      econstructor; eauto.
      do 2 eexists.
      split.
      erewrite get_R_set_neq_stable; eauto; intro; tryfalse.
      split.
      erewrite get_R_set_same_stable; eauto; intro; tryfalse.
      split.
      intro.
      eapply post_2_neq in H11.
      contradiction H11; eauto.
      split.
      instantiate (1 := F1); simpl; eauto.
      split; eauto.
      split.
      eapply in_range_0_7_post_cwp_still; eauto.
      split; eauto.
      simpl.
      clear - H11.
      unfold post_cwp.
      eapply in_range_0_7_num in H11.
      repeat (destruct H11 as [H11 | H11]; subst; eauto).
 
      instantiate (1 := b0).
      inv H27.
      assert (b1 = b0).
      {
        clear - H14 H_Hr30 H28.
        inv H28.
        specialize (H r30).
        simpljoin1.
        unfolds get_R, get_HR.
        rewrite H in H14.
        rewrite H6 in H_Hr30.
        inv H_Hr30.
        inv H14.
        eauto.
      }
      subst b1.
      rewrite <- merge_assoc in H17, H15.
      rewrite disj_merge_reverse_eq with (m1 := Mctx) in H17, H15; eauto.
      do 2 rewrite <- merge_assoc in H17, H15; eauto.
      rewrite fetch_frame_merge_elim in H17, H15; eauto.
      rewrite disj_merge_reverse_eq in H17; eauto.
      rewrite fetch_frame_merge_elim in H17, H15; eauto.
      rewrite fetch_frame_set_Mframe_same1 in H15.
      rewrite fetch_frame_set_Mframe_same2 in H17.
      inv H15.
      inv H17.
      econstructor; eauto.

      eapply indoms_set_Mframe'_0; eauto.
      eapply indoms_set_Mframe'_32; eauto.
      eapply indoms_merge_left.
      eapply indoms_set_Mframe'_0; eauto.
      eapply indoms_merge_right.
      eapply indoms_set_Mframe'_32; eauto.

      clear - H28.
      inv H28.
      simpljoin1.
      econstructor; eauto; intros.
      specialize (H rr); simpljoin1.
      erewrite getR_setR_neq_stable; eauto.
      intro; tryfalse.
      split; intros.
      unfold set_R, is_indom.
      lets Hwim : H0 Rwim.
      simpljoin1.
      rewrite H6; eauto.
      destruct (RegName_eq Rwim sr).
      inv e.
      rewrite RegMap.gss; eauto.
      rewrite RegMap.gso; eauto.
      do 3 (erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
      split; eauto.
      split; eauto.
    }
    split; eauto.
    {
      econstructor; intros; CElim C.
      erewrite get_R_set_neq_stable in H9; eauto; try intro; tryfalse.
      inv H9.
      erewrite get_R_set_R_same_reg in H10; eauto; try intro; tryfalse.
      inv H10. 
      unfolds win_masked.
      destruct (((($ 1) <<ᵢ (post_cwp k0)) &ᵢ (($ 1) <<ᵢ w)) !=ᵢ ($ 0)) eqn:Heqe; simpls; tryfalse.
      eapply nth_bit_and in Heqe; eauto; subst.
      destruct (((($ 1) <<ᵢ (post_cwp k0)) &ᵢ (($ 1) <<ᵢ (post_cwp (post_cwp k0)))) !=ᵢ ($ 0)) eqn:Heqe1; tryfalse.
      eapply nth_bit_and in Heqe1; eauto.
      eapply post_1_neq in H8; tryfalse.
      eapply in_range_0_7_post_cwp_still; eauto.
      eapply in_range_0_7_post_cwp_still; eauto.
      inv H6.
      inv H27.
      simpljoin1.
      rewrite H22 in H1; inv H1; eauto.
      clear - H23.
      unfold get_R, indom in *.
      destruct (LR Rwim); eauto.
    }
  }
Qed.

Lemma block_fresh_sep_merge :
  forall b M m,
    Mfresh b M -> Mfresh b m -> Mfresh b (M ⊎ m).
Proof.
  intros.
  unfolds Mfresh; intros.
  specialize (H o).
  specialize (H0 o).
  intro.
  unfold indom in *.
  simpljoin1.
  unfold merge in *. 
  destruct (M (b, o)) eqn:Heqe; contradiction H; eauto.
  contradiction H0; eauto.
Qed.

Lemma indom_rdythrd_b_0_valid :
  forall M T b ofs restoreQ,
    rdyTsRel restoreQ M T -> indom (b, ofs) M ->
    indom (b, $ 0) M.
Proof.
  intros.
  generalize dependent b.
  generalize dependent ofs.
  induction H; simpl; intros.
  {
    inv H0.
    simpljoin1; subst.
    eapply indom_merge_indom_oneof in H1.
    destruct H1.
    {
      lets HDomCtx : H7.
      specialize (H7 (b, ofs)); simpljoin1.
      eapply H1 in H0.
      unfold DomCtx in H0.
      destruct (Z.eq_dec t b); subst; tryfalse.
      eapply indom_merge_still.
      specialize (HDomCtx (b, $ 0)); simpljoin1.
      eapply H4.
      unfold DomCtx.
      destruct (Z.eq_dec b b); tryfalse; eauto.

      destruct (Z.eq_dec b0 b); subst; tryfalse.
      eapply indom_merge_still.
      specialize (HDomCtx (b, $ 0)); simpljoin1.
      eapply H4; eauto.
      unfold DomCtx.
      destruct (Z.eq_dec t b); subst; tryfalse.
      destruct (Z.eq_dec b b); subst; tryfalse.
      eauto.
    }
    {
      eapply indom_merge_still2.
      eapply indom_stk_ofs_in_0_inrange; eauto.
    }
  }
  {
    subst.
    eapply indom_merge_indom_oneof in H5; eauto.
    destruct H5.
    eapply indom_merge_still; eauto.
    eapply indom_merge_still2; eauto.
  }
Qed.

(* WfCth and WfRdy Preservation *)
Lemma wfCth_wfRdy_tau_step_preservation_clt :
  forall idx C Cas S pc npc S' pc' npc' PrimSet T t K M Spec restoreQ,
    indom pc C ->
    simImpsPrimSet Spec Cas PrimSet restoreQ -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy restoreQ (C, Cas) (C, PrimSet) t' K' 
    ) ->
    LP__ (C ⊎ Cas, (S, pc, npc)) tau (C ⊎ Cas, (S', pc', npc')) ->
    exists T' t0 K0 M' idx1,
      ((idx1 ⩹ idx /\ (T, t, K, M) = (T', t0, K0, M')) \/
       (exists HP', star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\
                    HP__ HP' tau (C, PrimSet, (T', t0, K0, M'))))
      /\
      wfCth restoreQ idx1 (C, Cas) (C ⊎ Cas, (S', pc', npc')) (C, PrimSet, (T', t0, K0, M')) /\
      (
        forall t1 K1, (ThrdMap.set t0 None T') t1 = Some K1 ->
                      wfRdy restoreQ (C, Cas) (C, PrimSet) t1 K1 
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
  3 : rewrite <- H2; eauto.

  destruct H17 as (Mc' & M'' & K' & idx' & HLM' & Hdisj1 & Hdisj2 & Hstep
                   & HcurTRel' & HwfIndex' & Hpcont' & HD''); subst.

  destruct Hstep as [Hstep | Hstep].
  {
    assert (exists idx1, wfCth restoreQ idx1 (C, Cas)
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

  assert (indom (b, $ 0) Mc).
  {
    clear - H18.
    inv H18.
    specialize (H9 (b, $ 0)); simpljoin1.
    eapply indom_merge_still.
    eapply H.
    unfold DomCtx.
    destruct (Z.eq_dec t b); subst; eauto.
    destruct (Z.eq_dec b b); eauto.
  }
  eapply block_fresh_sep_merge; eauto.
  unfold Mfresh; intros; intro.
  eapply indom_rdythrd_b_0_valid in H8; eauto.
  clear - H10 H7 H8.
  unfold disjoint in *.
  specialize (H10 (b, $ 0)).
  unfold indom in *; simpljoin1.
  rewrite H0, H in H10; tryfalse.
 
  unfold Mfresh; intros; intro.
  clear - H7 H8 H11.
  unfold indom in *; simpljoin1.
  eapply disj_sym in H11.
  eapply disj_merge_disj_sep1 in H11; eauto.
  unfold disjoint in *.
  specialize (H11 (b, $ 0)).
  lets Hofs : H.
  unfold TaskCur in Hofs.
  destruct (Address_eq (0, $ 0) (b, o)); subst; eauto.
  inv e.
  rewrite H, H0 in H11; tryfalse.
  rewrite MemMap.gso in Hofs; eauto.
  unfolds empM; tryfalse.
Qed.

Lemma wfCth_wfRdy_event_step_preservation :
  forall idx C Cas S pc npc S' pc' npc' PrimSet T t K M Spec v restoreQ,
    simImpsPrimSet Spec Cas PrimSet restoreQ -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy restoreQ (C, Cas) (C, PrimSet) t' K' 
    ) ->
    LP__ (C ⊎ Cas, (S, pc, npc)) (out v) (C ⊎ Cas, (S', pc', npc')) ->
    exists T' t0 K0 M' HP',
      (
        star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\
                    HP__ HP' (out v) (C, PrimSet, (T', t0, K0, M'))
      )
      /\
      (exists idx1, wfCth restoreQ idx1 (C, Cas) (C ⊎ Cas, (S', pc', npc')) (C, PrimSet, (T', t0, K0, M'))) /\
      (
        forall t1 K1, (ThrdMap.set t0 None T') t1 = Some K1 ->
                      wfRdy restoreQ (C, Cas) (C, PrimSet) t1 K1 
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
  forall idx C Cas S pc npc PrimSet T t K M Spec restoreQ,
    simImpsPrimSet Spec Cas PrimSet restoreQ -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy restoreQ (C, Cas) (C, PrimSet) t' K' 
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
        inv H27.
        destruct H20 as [H20 Hdisj_ctx_k]. 
        destruct H13 as [H13 [HwdFp [Hwd_sp HHR''] ] ].
        simpljoin1.
        lets Hwim : H4.
        specialize (Hwim Rwim).
        simpljoin1.
        renames x to k, x2 to v.
        inv H25.
        destruct H20 as (n & F2 & H20).
        simpljoin1.
        remember (F' ++ F2) as F.
        do 14 (destruct F as [ | ?fm F]; [simpls; tryfalse | idtac]); simpls; try omega.
        clear H29.
        unfold get_R in H20; rewrite H5 in H20; simpl in H20; inv H20.
        unfold get_R in H21; rewrite H13 in H21; simpl in H21; inv H21.
        destruct (win_masked (pre_cwp x) ($ 1) <<ᵢ n) eqn:Heqe.
        {
          assert (length F' = 12%nat).
          {  
            clear - H22 H25 H27 H28 Heqe.
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
            clear - H26.
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
          unfold get_R; rewrite H13; eauto.
          eauto. 
          econstructor; eauto.
          instantiate (4 := [fm14; fm15; fm16; fm17; fm18; fm19; fm20; fm21; fm22]).
          simpls; eauto.
          unfold get_R; rewrite H13; eauto.
        }
        {
          assert (exists b M', Malloc ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)
                                 b $ 0 sz M').
          {
            lets Ht : (finite_memory ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)).
            destruct Ht as (b0 & Ht). 
            remember (fun l : Address => match l with
                                       | (b', o') => if Z.eq_dec b0 b' then
                                                       if int_leu ($ 0) o' && Int.ltu o' sz
                                                                  && (o' modu ($ 4)) =ᵢ ($ 0) then
                                                        Some (W ($ 2))
                                                      else
                                                        None
                                                    else None
                                       end) as m. 
            exists b0 (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) ⊎ m).
            econstructor; eauto; intros.
            split.
            {
              clear - H18.
              inv H18; simpljoin1.
              eapply int_ltu_trans; eauto.
              unfold Int.ltu; eauto.
            }
            intros.
            destruct (Z.eq_dec b0 b'1) eqn:Heqeb; subst.
            {
              right.
              split; eauto.
              assert (Hnone : ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (b'1, o') = None).
              {
                clear - Ht.
                destruct (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (b'1, o'))
                         eqn : Heqe; eauto.
                unfolds Mfresh.
                specialize (Ht o').
                contradiction Ht; unfold indom; eauto.
              }
              
              destruct (int_leu $ 0 o') eqn:Heqe_intle;
                destruct (Int.ltu o' sz) eqn:Heqe_sz; simpl.

              destruct (o' modu ($ 4)) =ᵢ ($ 0) eqn:Heqe_mod4.
              exists (W $ 2).
              rewrite disj_merge_reverse_eq; eauto.
              eapply get_vl_merge_still; eauto.
              destruct (Z.eq_dec b'1 b'1); tryfalse.
              rewrite Heqe_intle, Heqe_sz.
              simpl; eauto.
              rewrite Heqe_mod4; eauto.

              clear - Ht Hnone.
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
                destruct (Z.eq_dec b'1 z); destruct (int_leu $ 0 i); destruct (Int.ltu i sz);
                  destruct ((i modu ($ 4)) =ᵢ ($ 0)); simpl; eauto.
              }

              unfold merge at 1.
              destruct (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) (b'1, o'))
                       eqn : Heqeb'; eauto.
              destruct (Z.eq_dec b'1 b'1); simpl; tryfalse; eauto.
              rewrite Heqe_intle, Heqe_sz, Heqe_mod4; simpl; eauto.

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

              unfold merge at 1.
              rewrite Hnone.
              destruct (Z.eq_dec b'1 b'1); subst; tryfalse.
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
          unfold get_R; rewrite H13; eauto.
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
          clear - H4 H28.
          unfolds get_R.
          rewrite H28 in H4; simpls; eauto.
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
          destruct H29 as [fm1' Hfetch_Mframe1].
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
          destruct H29 as [fm2' Hfetch_Mframe2].
           
          do 2 eexists.
          econstructor; eauto.
          simpl; eauto.
          eapply LPrestore_trap.
          eapply get_vl_merge_still; eauto.
          instantiate (1 := x0).
          unfold get_R; rewrite H19; eauto.
          instantiate (1 := ($ 1) <<ᵢ n0).
          unfold get_R; rewrite H28; eauto.
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
          specialize (H7 r14); simpljoin1.
          rewrite H22 in H29; inv H29; eauto.
          
          econstructor.
          unfold get_R; rewrite H19; eauto.
          unfold get_R; rewrite H28; eauto.
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
    assert (HwdSpec : exists Fp Fq, Spec f = Some (Fp, Fq) /\ wdSpec restoreQ Fp Fq prim).
    {
      eapply H with (L := nil) in Hprim; eauto.
      simpljoin1.
      do 2 eexists; split; eauto.
    } 
    destruct HwdSpec as (Fp & Fq & HSpec & HwdSpec).
    inv HwdSpec.
    specialize (H5 lv).
    destruct H5 as (num & Pr & L & Hpre & Hpost & HSta).
    destruct H2 as [H2 Hwdprim].
 
    eapply H with (L := L) in Hprim; eauto.
    simpljoin1.
    rewrite H5 in HSpec; inv HSpec.
    unfold simImpPrim in H10.
    assert (Hinv : INV (Pm prim lv) num lv (S, (T, t, (h, f, f +ᵢ ($ 4)), M), Pm prim lv, num) restoreQ).
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
    lets Hrel_safety : H19.
    assert (x = lv).
    { 
      lets Hlv : H19.
      eapply H8 in Hlv.
      simpl in Hlv.
      simpljoin1.
      inv H24; eauto.
    }
    subst x.
    
    eapply H10 in Hrel_safety; eauto.
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
      eapply H32 in Hcom.
      simpljoin1.
      eapply legal_com_safety_property in H21; eauto.
      simpljoin1.
      eapply LP_CdhpInc with (C2 := C) in H21; eauto.
      rewrite disj_merge_reverse_eq in H21; eauto.
      eapply disj_sym; eauto.
    }
    destruct Hcom as [Hcom | Hcom].
    {
      eapply H33 in Hcom.
      simpljoin1.
      eapply legal_com_safety_property in H21; eauto.
      simpljoin1.
      eapply LP_CdhpInc with (C2 := C) in H21; eauto.
      rewrite disj_merge_reverse_eq in H21; eauto.
      eapply disj_sym; eauto.
    }
    {
      eapply H34 in Hcom; eauto.
      simpljoin1.
      eapply legal_com_safety_property in H21; eauto.
      simpljoin1.
      eapply LP_CdhpInc with (C2 := C) in H21; eauto.
      rewrite disj_merge_reverse_eq in H21; eauto.
      eapply disj_sym; eauto.
    }
  }
Qed.
  
(* Compositionality Proof *)
Lemma wfCth_wfRdy_imply_wpsim :
  forall idx C Cas S pc npc PrimSet T t K M Spec restoreQ,
    simImpsPrimSet Spec Cas PrimSet restoreQ -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth restoreQ idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy restoreQ (C, Cas) (C, PrimSet) t' K' 
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
          exists (0%nat, (0%nat, 0%nat)).
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

            assert (Hexec_prim : exists HS' HSr', exec_prim (A, (T, t, K, M)) (Pdone, HS')
                                                /\ hstate_union x2 HSr' HS' /\ (x7, HSr', Pdone, w) ||= Pr).
            {
              clear - H11 H14 H18 H21.
              inv H18.
              lets Ht : H11.
              inv Ht.
              destruct H.
              2 : tryfalse.
              assert (Pm prim lv = Pm prim lv); eauto.
            }
            destruct Hexec_prim as (HS' & HSr' & Hexec_prim & Hhstate_union & HPr).

            assert (x1  = Pdone).
            {
              clear - H11.
              inv H11.
              eauto.
            }
            subst x1.
            
            assert (((LM'0, (LR''0, F'0), D''0), HS', Pdone, (x3 + w)%nat) ||= Q ⋆ Pr).
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
            assert (Hwp_state' : wp_stateRel restoreQ (LM'0, (LR''0, F'0), D''0) HS' /\
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
