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
  Admitted.

(** Final Theorem *)
Theorem FinalTheorem : forall Spec Cas PrimSet,
    rel_wf_prim Spec Cas PrimSet -> correct Cas PrimSet.
Proof.
  intros.
  eapply sim_imp_ctx_refinement.
  eapply logic_ensures_simulation; eauto.
Qed.
