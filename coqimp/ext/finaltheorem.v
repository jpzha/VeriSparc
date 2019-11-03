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

(*
Inductive n_tau_step {prog : Type} (step : prog -> msg -> prog -> Prop) :
  Index -> prog -> prog -> Prop :=
| Zero_tau_step : forall p idx, ~ (exists idx', idx' ⩹ idx) -> n_tau_step step idx p p
| Multi_tau_step : forall (p p' p'' p''': prog) idx_i idx_j,
    star_tau_step step p p' -> step p' tau p'' -> idx_j ⩹ idx_i ->
    n_tau_step step idx_j p'' p''' -> 
    n_tau_step step idx_i p p'''.

Lemma Etr_emp_n_step :
  forall A (P : A) ndx (step : A -> msg -> A -> Prop),
    Etrace step P empEtr -> well_founded LtIndex ->
    exists P', n_tau_step step ndx P P'.
Proof.
  intros.
  generalize dependent P.
  generalize dependent step.
  unfold well_founded in H0.
  specialize (H0 ndx).
  induction H0; intros.
  inv H1.
  destruct x.
  destruct n, n0.
  {
    exists P.
    eapply Zero_tau_step.
    intro.
    destruct H1.
    inv H1; try omega.
  }
  {
    eapply H0 in H4; eauto.
    Focus 2.
    instantiate (1 := (0%nat, n0)); econstructor; eauto.
    destruct H4 as [P''' H4].
    exists P'''.
    eapply Multi_tau_step; eauto.
    econstructor; eauto.
  }
  {
    eapply H0 in H4; eauto.
    Focus 2.
    instantiate (1 := (n, 0%nat)); econstructor; eauto.
    destruct H4 as [P''' H4].
    exists P'''.
    eapply Multi_tau_step; eauto.
    econstructor; eauto.
  }
  {
    eapply H0 in H4; eauto.
    Focus 2.
    instantiate (1 := (S n, n0)).
    econstructor; eauto.
    destruct H4 as [P''' H4].
    exists P'''.
    eapply Multi_tau_step; eauto.
    econstructor; eauto.
  }
Qed.

Lemma LEtr_emp_n_step_H_progress :
  forall LP LP' HP ndx idx,
    well_founded LtIndex ->
    n_tau_step LP__ ndx LP LP' -> wp_sim idx LP HP -> idx ⩹ ndx ->
    (exists HP' HP'', star_step HP__ HP HP' /\ HP__ HP' tau HP'').
Proof.
  intros.
  generalize dependent LP.
  generalize dependent LP'.
  generalize dependent HP.
  generalize dependent idx.
  unfold well_founded in H. 
  specialize (H ndx).
  induction H; intros.
  inv H1.
  contradiction H4; eauto.
  inv H3.
  clear H8 H9.
  inv H4.
  {
    eapply H1 in H5.
    clear H1.
    destruct H5.
    {
      destruct H1 as [idx1 [Hlt Hwp_sim] ].
      eapply H0 in Hwp_sim.
      eauto.
      instantiate(1 := idx); eauto.
      eauto.
      
    }
  }
  
  generalize dependent HP.
  generalize dependent idx.
  induction H; intros.
  contradiction H; eauto.
  inv H4. 
  clear H6 H7.
  
  
  induction H1; intros.
  {
    inv H0.
    false.
    contradiction H2.
    exists (n, m').
    econstructor; eauto.
    Print Index.
  }
 *)

Lemma wp_sim_ensures_refinement' :
  forall C Cas S pc npc PrimSet HS B idx,
    C ⊥ Cas -> wp_sim idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS) ->
    Etrace LP__ (C ⊎ Cas, (S, pc, npc)) B ->
    IdxEtrace HP__ idx (C, PrimSet, HS) B.
Proof.
  cofix Hp; intros.
  destruct B.
  {
    inv H1.
    inv H2.
    {
      inv H0. 
      clear H2 H5.
      lets Hlp_step : H3.
      eapply H1 in H3; eauto.
      clear H1.
      destruct H3 as [ [idx1 [Hlt H3] ] | [idx1 [ HP' [HP'' [Hstar [HPstep Hwpsim] ] ] ] ] ].
      {
        eapply IdxEtr_tau2.
        instantiate (1 := (C, PrimSet, HS)).
        eapply zero_tau_step; eauto.
        eauto.
        eapply Hp; eauto.
      }
    }
  }

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
