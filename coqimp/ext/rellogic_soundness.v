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
 
Definition insSeq_rel_sound Spec P f I Q :=
  forall C S HS A w,
    LookupXC C f I -> (S, HS, A, w) ||= P ->
    rel_safety_insSeq Spec (w, (1 + get_insSeqLen I)%nat) (C, S, f, f +ᵢ ($ 4)) (A, HS) Q.

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

Lemma function_correctness :
  forall P Q Spec S HS A w pc I C,
    insSeq_rel_sound Spec P pc I Q -> LookupXC C pc I ->
    cdhp_rel_sound Spec C -> (S, HS, A, w) ||= P ->
    rel_safety 0%nat (w, (1 + get_insSeqLen I)%nat) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q.
Proof.
Admitted.
