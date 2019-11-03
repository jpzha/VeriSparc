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
Require Import reg_lemma.
Require Import soundness.
Require Import refinement.
Require Import rellogic.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

Inductive n_tau_step {prog : Type} (step : prog -> msg -> prog -> Prop) :
  Index -> prog -> prog -> Prop :=
| Zero_tau_step : forall p idx, n_tau_step step idx p p
| Multi_tau_step : forall (p p' p'' : prog) idx_i idx_j,
    step p tau p' -> idx_j ⩹ idx_i -> n_tau_step step idx_j p' p'' -> 
    n_tau_step step idx_i p p''.

Lemma LEtr_emp_n_step_H_progress :
  forall LP LP' HP ndx idx,
    n_tau_step LP__ ndx LP LP' -> wp_sim idx LP HP -> idx ⩹ ndx ->
    (exists HP' HP'', star_step HP__ HP HP' /\ HP__ HP' tau HP'').
Proof.
  intros.
  generalize dependent LP.
  generalize dependent LP'.
  generalize dependent HP.

Lemma wp_sim_ensures_refinement' :
  forall C Cas S pc npc PrimSet HS B idx,
    C ⊥ Cas -> wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS) ->
    Etrace LP__ (C ⊎ Cas, (S, pc, npc)) B ->
    Etrace HP__ (C, PrimSet, HS) B.
Proof.
  cofix Hp.
  intros.
  destruct B.
  {
  }
  
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

(* Compositionality1 *)
Lemma compositionality1 :
  forall Spec C Cas PrimSet S HS pc npc,
    simImpsPrimSet Spec Cas PrimSet ->
    wp_stateRel S HS -> HProgSafe (C, PrimSet, HS) ->
    get_Hs_pcont HS = (pc, npc) -> C ⊥ Cas ->
    exists idx, wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).
Proof.
Admitted.

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
