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
Require Import highlang.
Require Import lowlang.
Require Import logic.
Require Import reg_lemma.
Require Import soundness.
Require Import refinement.
Require Import rellogic.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope. 

(** Auxiliary Lemmas about Steps *)
Lemma star_tau_step_impl_star_step :
  forall A P P' (step : A -> msg -> A -> Prop),
    star_tau_step step P P' ->
    star_step step P P'.
Proof.
  intros.
  induction H.
  econstructor; eauto.
  eapply multi_step; eauto.
Qed.

Lemma multi_step_cons :
  forall A P P' P'' (step : A -> msg -> A -> Prop),
    star_step step P P' -> star_step step P' P'' ->
    star_step step P P''.
Proof.
  intros.
  generalize dependent P.
  induction H0; intros; eauto.
  eapply IHstar_step in H1; eauto.
  eapply multi_step; eauto.
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

Inductive wfHPrimExec : XCodeHeap -> primcom -> HState -> Prop :=
| cons_wfHPrimExec : forall C A HS,
    (
      forall hprim lv T t HQ pc npc HM,
        A = Pm hprim lv -> HS = (T, t, (HQ, pc, npc), HM) ->
        HH__ C (HQ, pc, npc, HM) (Callevt pc lv) (HQ, pc, npc, HM)
    ) ->
    wfHPrimExec C A HS.

(** Well-formed Current Thread *)
Inductive wfCth : Index -> XCodeHeap * XCodeHeap -> LProg -> HProg -> Prop :=
| clt_wfCth : forall C Cas S HS pc npc PrimSet idx,
    wp_stateRel S HS -> wfIndex C S pc idx -> 
    get_Hs_pcont HS = (pc, npc) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS)

| prim_wfCth : forall C Cas Sc HSc S HS Sr HSr w Q Pr A pc npc PrimSet idx k,
    state_union Sc Sr S -> hstate_union HSc HSr HS ->
    rel_safety k idx (Cas, Sc, pc, npc) (A, HSc) Q -> (Sr, HSr, A, w) ||= Pr -> wfHPrimExec C A HS ->
    (
      forall S' HS' w' f, (S', HS', Pdone, w') ||= Q ⋆ Pr -> getregs S' r15 = Some (W f) ->
                          HProgSafe (C, PrimSet, HS') ->
                        exists idx_j, wfCth idx_j (C, Cas) (C ⊎ Cas, (S', f +ᵢ ($ 8), f +ᵢ ($ 12))) (C, PrimSet, HS')
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

Lemma LH__progress_HH__progress :
  forall C Mc Mr LR F pc npc LM' LR' F' D' pc' npc' T t HR b HF M PrimSet,
    LH__ C ((Mc ⊎ Mr ⊎ M, (LR, F), []), pc, npc) tau
         ((LM', (LR', F'), D'), pc', npc') ->
    HProgSafe (C, PrimSet, (T, t, ((HR, b, HF), pc, npc), M)) ->
    indom pc C -> Mc ⊥ Mr -> (Mc ⊎ Mr) ⊥ M ->
    curTRel (Mc, (LR, F)) (t, ((HR, b, HF), pc, npc)) ->
    exists Mc' M' K',
      LM' = Mc' ⊎ Mr ⊎ M' /\ Mc' ⊥ Mr -> (Mc' ⊎ Mr) ⊥ M'
      /\ HP__ (C, PrimSet, (T, t, ((HR, b, HF), pc, npc), M)) tau (C, PrimSet, (T, t, K', M'))
      /\ curTRel (Mc', (LR', F')) (t, K') /\ D' = nil.
Proof.
Admitted.

(* WfCth and WfRdy Preservation *)
Lemma wfCth_wfRdy_tau_step_preservation :
  forall idx C Cas S pc npc S' pc' npc' PrimSet T t K M Spec,
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
  intros.
  lets Ht : classic (indom pc C).
  destruct Ht as [Ht | Ht].
  {  
    inv H2.
    {
      inv H10.
      eapply LP__local1 in H4; eauto.
      inv H4.
      simpl in H18.
      destruct K.
      destruct p.
      destruct h.
      destruct p.
      renames h0 to HR, z to b, h to HF.
      simpl in H15.
      inv H15.
      inv H18.

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
      }
      
      unfold Tid in H4.
      rewrite H4 in H22.
      eapply LH__progress_HH__progress in H22; eauto.
    }
  }
Admitted.

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
    exists T' t0 K0 M' idx1 HP',
      (
        star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\
                    HP__ HP' (out v) (C, PrimSet, (T', t0, K0, M'))
      )
      /\
      wfCth idx1 (C, Cas) (C ⊎ Cas, (S', pc', npc')) (C, PrimSet, (T', t0, K0, M')) /\
      (
        forall t1 K1, (ThrdMap.set t0 None T') t1 = Some K1 ->
                      wfRdy (C, Cas) (C, PrimSet) t1 K1 
      ).
Proof.
Admitted.

Lemma wfCth_wfRdy_abort_preservation :
  forall idx C Cas S pc npc PrimSet T t K M Spec m,
    simImpsPrimSet Spec Cas PrimSet -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy (C, Cas) (C, PrimSet) t' K' 
    ) ->
    ~ (exists LP' : LProg, LP__ (C ⊎ Cas, (S, pc, npc)) m LP') ->
    exists HP' : HProg, star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\ ~ (exists (HP'': HProg) m', HP__ HP' m' HP'').
Proof.
Admitted.

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
    inv H4.
    eapply wfCth_wfRdy_tau_step_preservation in Hpreserve; eauto.
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
    (* event *)
    lets Hpreserve : H2.
    lets HLP : H4.
    inv H4.    
    eapply wfCth_wfRdy_event_step_preservation in Hpreserve; eauto. 
    destruct Hpreserve as (T' & t0 & K0 & M' & idx1 & HP' & (HH_star_steps & HHstep)
                           & HwfCth & Hwfrdy).
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
    destruct H4 as (HP' & HHstar_steps & HHstep).
    clear - H1 HHstar_steps HHstep.
    unfolds HProgSafe.
    eapply star_tau_step_impl_star_step in HHstar_steps.
    eapply H1 in HHstar_steps.
    tryfalse.
  }
Qed.
