(*+ Final Theorem Proof +*)  
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
Require Import compositionality.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(** Auxiliary Lemmas about multi-steps *)
Inductive n_tau_step {prog : Type} (step : prog -> msg -> prog -> Prop) :
  nat -> prog -> prog -> Prop :=
| tau_step0 : forall p, n_tau_step step 0%nat p p
| tau_step_Sn : forall (p p' p'' : prog) n, n_tau_step step n p p' -> step p' tau p'' ->
                                             n_tau_step step (S n) p p''.

Lemma Hstar_step_code_unchange :
  forall C PrimSet HS HP',
    star_tau_step HP__ (C, PrimSet, HS) HP' ->
    exists HS', HP' = (C, PrimSet, HS').
Proof. 
  intros.
  remember (C, PrimSet, HS) as HP.
  generalize dependent C.
  generalize dependent PrimSet.
  generalize dependent HS.
  induction H; intros; eauto; subst.
  assert ((C, PrimSet, HS) = (C, PrimSet, HS)).
  eauto.
  eapply IHstar_tau_step in H1; eauto.
  destruct H1; subst.
  inv H0; eauto.
Qed.

Lemma Lstar_step_code_unchange :
  forall C S LP',
    star_tau_step LP__ (C, S) LP' ->
    exists S', LP' = (C, S').
Proof.
  intros.
  remember (C, S) as LP.
  generalize dependent C.
  generalize dependent S.
  induction H; intros; eauto; subst.
  assert ((C, S) = (C, S)); eauto.
  eapply IHstar_tau_step in H1; eauto.
  destruct H1; subst.
  inv H0.
  eauto.
Qed.

Lemma n_tau_step_front_back :
  forall n A P P' P'' (step : A -> msg -> A -> Prop),
    n_tau_step step n P P' -> step P' tau P'' ->
    exists P0, step P tau P0 /\ n_tau_step step n P0 P''.
Proof.
  induction n; intros.
  inv H.
  exists P''; split; eauto.
  econstructor; eauto.
  inv H.
  eapply IHn with (step := step) in H2; eauto.
  destruct H2 as [P0 [Hstep H2] ].
  exists P0; split; eauto.
  econstructor; eauto.
Qed.

Lemma star_step_impl_n_step :
  forall A P P' (step : A -> msg -> A -> Prop),
    star_tau_step step P P' -> exists n, n_tau_step step n P P'.
Proof.
  intros.
  induction H.
  exists 0%nat; econstructor; eauto.
  destruct IHstar_tau_step as [n IHstar_tau_step].
  exists (S n); econstructor; eauto.
Qed.

Lemma n_step_impl_star_step :
  forall n A P P' (step : A -> msg -> A -> Prop),
    n_tau_step step n P P' -> star_tau_step step P P'.
Proof.
  induction n; intros.
  inv H.
  econstructor; eauto.
  inv H.
  eapply multi_tau_step; eauto.
Qed.

Lemma multi_tau_step_front_back :
  forall A P P' P'' (step : A -> msg -> A -> Prop),
    star_tau_step step P P' -> step P' tau P'' ->
    exists P0, step P tau P0 /\ star_tau_step step P0 P''.
Proof.
  intros.
  eapply star_step_impl_n_step in H.
  destruct H as [n H].
  eapply n_tau_step_front_back with (step := step) in H; eauto.
  destruct H as (P0 & Hstep & Hn_tau_step).
  exists P0; split; eauto.
  eapply n_step_impl_star_step; eauto.
Qed.

Lemma n_tau_step_cons :
  forall m n A P P' P'' (step : A -> msg -> A -> Prop),
    n_tau_step step n P P' -> n_tau_step step m P' P'' ->
    n_tau_step step (Nat.add n m) P P''.
Proof.
  induction m; intros.
  inv H0.
  rewrite Nat.add_0_r; eauto.
  inv H0.
  eapply IHm in H; eauto.
  rewrite <- plus_n_Sm.
  econstructor; eauto.
Qed.

Lemma multi_tau_step_cons :
  forall A P P' P'' (step : A -> msg -> A -> Prop),
    star_tau_step step P P' -> star_tau_step step P' P'' ->
    star_tau_step step P P''.
Proof.
  intros.
  generalize dependent P.
  induction H0; intros; eauto.
  eapply IHstar_tau_step in H1; eauto.
  eapply multi_tau_step; eauto.
Qed.

(** final theorem proof *)
CoInductive IdxEtrace {tprog} (step : tprog -> msg -> tprog -> Prop): Index -> tprog -> Etr -> Prop :=
| IdxEtr_tau1 : forall P P' P'' idx idx',
    star_tau_step step P P' -> step P' tau P'' ->
    IdxEtrace step idx' P'' empEtr -> IdxEtrace step idx P empEtr
| IdxEtr_tau2 : forall P P' idx idx',
    star_tau_step step P P' -> idx' ⩹ idx ->
    IdxEtrace step idx' P' empEtr -> IdxEtrace step idx P empEtr
| IdxEtr_abort : forall P P' m idx,
    star_tau_step step P P' -> (~ (exists P'', step P' m P'')) -> IdxEtrace step idx P abortEtr
| Etr_event : forall P P' P'' v etr idx idx',
    star_tau_step step P P' -> step P' (out v) P'' ->
    IdxEtrace step idx' P'' etr -> IdxEtrace step idx P (outEtr v etr).

Lemma n_tau_step_wp_preserve :
  forall n LP LP' HP idx,
    n_tau_step LP__ n LP LP' -> wp_sim idx LP HP ->
    exists idx_j HP' m, n_tau_step HP__ m HP HP' /\ wp_sim idx_j LP' HP'.
Proof.
  induction n; intros.
  inv H.
  exists idx HP 0%nat.
  split; eauto.
  econstructor; eauto.
  inv H.
  lets Hn_tau_step : H2.
  eapply n_tau_step_front_back with (step := LP__) in Hn_tau_step; eauto.
  destruct Hn_tau_step as (P0 & HLP__ & Hn_tau_step).
  inv H0.
  clear H1 H4.
  lets Hwp_sim_prop : HLP__.
  eapply H in Hwp_sim_prop; eauto.
  clear H.
  destruct Hwp_sim_prop as [(idx1 & Hlt & Hwp_sim) | (idx1 & HP' & HP'' & HHstar_step & HHstep & Hwp_sim)].
  {
    eapply IHn in Hwp_sim; eauto.
  }
  {
    eapply IHn in Hwp_sim; eauto.
    destruct Hwp_sim as (idx_j & HP0 & m & HH_n_steps & Hwp_sim).
    eapply star_step_impl_n_step in HHstar_step.
    destruct HHstar_step as (n' & HHstar_step).
    exists idx_j HP0 (Nat.add (S n') m).
    split; eauto.
    eapply n_tau_step_cons; eauto.
    econstructor; eauto.
  }
Qed.

Lemma star_tau_step_wp_preserve :
  forall LP LP' HP idx,
    star_tau_step LP__ LP LP' -> wp_sim idx LP HP ->
    exists idx_j HP', star_tau_step HP__ HP HP' /\ wp_sim idx_j LP' HP'.
Proof.
  intros.
  eapply star_step_impl_n_step in H.
  destruct H.
  eapply n_tau_step_wp_preserve in H; eauto.
  destruct H as (idx_j & HP' & m & Hn_tau_step & Hwp_sim).
  eapply n_step_impl_star_step in Hn_tau_step; eauto.
Qed.

Lemma wp_sim_ensures_refinement_empEtr :
  forall C Cas S pc npc PrimSet HS idx,
    C ⊥ Cas -> wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS) ->
    Etrace LP__ (C ⊎ Cas, (S, pc, npc)) empEtr ->
    IdxEtrace HP__ idx (C, PrimSet, HS) empEtr.
Proof.
  cofix Hp; intros.
  inv H1.
  lets Hstar_step : H2.
  eapply multi_tau_step_front_back with (step := LP__) in Hstar_step; eauto.
  destruct Hstar_step as (P0 & Hstep & Hstar).
  inv H0.
  clear H5 H6.
  lets Hwp_prop : Hstep.
  eapply H1 in Hwp_prop; eauto.
  clear H1; destruct Hwp_prop as [(idx1 & Hlt & Hwp_sim) | (idx1 & HP' & HP'' & Hstar_step & HHstep & Hwp_sim)].
  {
    inv Hstep.
    eapply IdxEtr_tau2; eauto.
    instantiate (1 := (C, PrimSet, HS)); econstructor; eauto.
    eapply Hp; eauto.
    clear - H4 Hstar.
    inv H4.
    eapply multi_tau_step_cons in H; eauto.
    eapply Etr_tau; eauto.
  }
  {
    inv Hstep.
    eapply IdxEtr_tau1; eauto.
    instantiate (1 := idx1).
    eapply Hstar_step_code_unchange in Hstar_step; eauto.
    destruct Hstar_step as [HS' Hstar_step]; subst.
    inv HHstep.
    eapply Hp; eauto.
    clear - Hstar H4.
    inv H4.
    eapply multi_tau_step_cons in H; eauto.
    eapply Etr_tau; eauto.
    eapply Hp; eauto.    
    clear - Hstar H4.
    inv H4.
    eapply multi_tau_step_cons in H; eauto.
    eapply Etr_tau; eauto.
  }
Qed.

Lemma wp_sim_ensures_refinement_abort :
  forall  C Cas S pc npc PrimSet HS idx,
    C ⊥ Cas -> wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS) ->
    Etrace LP__ (C ⊎ Cas, (S, pc, npc)) abortEtr ->
    IdxEtrace HP__ idx (C, PrimSet, HS) abortEtr.
Proof.
  intros.
  inv H1.
  eapply star_tau_step_wp_preserve in H2; eauto.
  destruct H2 as (idx_j & HP' & HHstar_step & Hwp_sim).
  clear H0.
  inv Hwp_sim.
  clear H0 H1.
  eapply H2 in H3.
  clear H2.
  destruct H3 as (HP'0 & Hstar & Habort). 
  assert (Ht : star_tau_step HP__ (C, PrimSet, HS) HP'0).
  eapply multi_tau_step_cons with (P' := HP'); eauto.
  clear HHstar_step Hstar.
  econstructor; eauto.
  Unshelve.
  exact tau.
Qed.

Lemma wp_sim_ensures_idx_refinement :
  forall C Cas S pc npc PrimSet HS B idx,
    C ⊥ Cas -> wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS) ->
    Etrace LP__ (C ⊎ Cas, (S, pc, npc)) B ->
    IdxEtrace HP__ idx (C, PrimSet, HS) B.
Proof.
  cofix Hp; intros.
  destruct B.
  {
    eapply wp_sim_ensures_refinement_empEtr; eauto.
  }
  {
    eapply wp_sim_ensures_refinement_abort; eauto.
  }
  {
    inv H1. 
    eapply star_tau_step_wp_preserve in H0; eauto.
    destruct H0 as (idx_j & HP' & HHstar & Hwp_sim).
    inv Hwp_sim.
    clear H0 H2.
    lets Hwp_sim_prop : H6.
    eapply H1 in Hwp_sim_prop; eauto.
    clear H1.
    destruct Hwp_sim_prop as (idx1 & HP'0 & HP'' & HHstar_step & HHstep & Hwp_sim).
    econstructor.
    instantiate (1 := HP'0).
    eapply multi_tau_step_cons; eauto.
    eauto.
    instantiate (1 := idx1).
    eapply Hstar_step_code_unchange in HHstar; eauto.
    destruct HHstar as (HS' & HHstar); subst.
    eapply Hstar_step_code_unchange in HHstar_step; eauto.
    destruct HHstar_step as (HS'' & HHstar_step); subst.
    inv HHstep.
    eapply Lstar_step_code_unchange in H4.
    destruct H4 as [S' LP']; subst.
    inv H6.
    eapply Hp; eauto.
  }
Qed.

Lemma IdxEtrace_impl_progress :
  forall A idx (step : A -> msg -> A -> Prop) P,
    IdxEtrace step idx P empEtr -> well_founded LtIndex ->
    exists P' P'' idx', star_tau_step step P P' /\ step P' tau P'' /\ IdxEtrace step idx' P'' empEtr.
Proof.
  intros.
  unfold well_founded in H0.
  specialize (H0 idx).
  generalize dependent P.
  induction H0; intros.
  inv H1.
  {
    exists P' P'' idx'.
    repeat (split; eauto).
  }
  {
    inv H2.
    {
      eapply H0; eauto.
    }
    {
      exists p' P' idx'; eauto.
    }
  }
Qed.

Lemma IdxEtrace_imply_Etrace :
  forall A (step : A -> msg -> A -> Prop) idx P B,
    IdxEtrace step idx P B ->
    Etrace step P B.
Proof.
  cofix Hp; intros.
  destruct B.
  {
    (* tau *)
    eapply IdxEtrace_impl_progress in H; eauto.
    destruct H as (P' & P'' & idx' & Hstar_step & Hstep & HIdxEtrace).
    econstructor; eauto.
    eapply well_founded_LtIndex; eauto.
  }
  {
    inv H.
    econstructor; eauto.
  }
  {
    inv H.
    econstructor; eauto.
  }
Qed.

Lemma wp_sim_ensures_refinement' :
  forall C Cas S pc npc PrimSet HS B idx,
    C ⊥ Cas -> wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS) ->
    Etrace LP__ (C ⊎ Cas, (S, pc, npc)) B ->
    Etrace HP__ (C, PrimSet, HS) B.
Proof.
  intros.
  eapply wp_sim_ensures_idx_refinement in H1; eauto.
  eapply IdxEtrace_imply_Etrace; eauto.
Qed.
  
(* Whole program simulation ensures refinement *)
Lemma wp_sim_ensures_refinement :
  forall C S pc npc Cas PrimSet HS idx,
    C ⊥ Cas -> wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS) ->
    Etr_Refinement (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).
Proof.
  intros.
  unfold Etr_Refinement; intros.
  eapply wp_sim_ensures_refinement'; eauto.
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
    clear H5.
    rename H4 into Hret.
    specialize (H6 lv).
    destruct H6 as (num & Pr & L & Hwf_pre & Hwf_post).
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
    destruct H2.
    inv H0.
    split; eauto.
    eexists.
    econstructor; eauto.
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
    destruct idx. 
    exists (Nat.succ (Nat.succ n), n0).
    eapply prim_wfCth; eauto.
    instantiate (1 := Fq0 L).
    instantiate (1 := 0%nat). 
    eapply rel_safety_idx_inc_still; eauto.
    econstructor; eauto.

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
    simpljoin1.
    simpl in H5.
    simpl.
    inv H7.
    eapply Hret in H18; eauto.
    simpl.
    rewrite H5 in H.
    inv H; eauto.
  }
Qed.

(* Compositionality1 *)
Lemma compositionality1 :
  forall Spec C Cas PrimSet S HS pc npc,
    simImpsPrimSet Spec Cas PrimSet ->
    wp_stateRel S HS -> HProgSafe (C, PrimSet, HS) ->
    get_Hs_pcont HS = (pc, npc) -> C ⊥ Cas -> 
    exists idx, wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).
Proof.
  intros.
  lets HwfCth : H.
  eapply inital_wfCth_holds in HwfCth; eauto.
  destruct HwfCth as (idx & HwfCth).
  exists idx.
  destruct HS.
  destruct p.
  renames t to K.
  destruct p.
  renames t to T, t0 to t.
  eapply wfCth_wfRdy_imply_wpsim; eauto.
  intros.
  econstructor; intros; subst.
  eapply inital_wfCth_holds; eauto.
Qed.

(** Logic ensures simulation *)
Lemma logic_ensures_simulation :
  forall Spec Cas PrimSet,
    rel_wf_prim Spec Cas PrimSet ->
    simImpsPrimSet Spec Cas PrimSet.
Proof.
Admitted.

(** Simulation Implies Contexttual Refinement *)
Lemma sim_imp_ctx_refinement :
  forall Spec Cas PrimSet,
    simImpsPrimSet Spec Cas PrimSet ->
    correct Cas PrimSet.
Proof.
  intros.
  unfold correct; intros.
  lets Ht : compositionality1 __; eauto.
  eapply Ht in H; eauto.
  destruct H as [idx H].
  eapply wp_sim_ensures_refinement; eauto.
Qed.  

(** Final Theorem *)
Theorem FinalTheorem : forall Spec Cas PrimSet,
    rel_wf_prim Spec Cas PrimSet -> correct Cas PrimSet.
Proof.
  intros.
  eapply sim_imp_ctx_refinement.
  eapply logic_ensures_simulation; eauto.
Qed.
