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
                                   rel_safety_insSeq Spec (w, (1 + get_insSeqLen I)%nat)
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
                (Kq = nil /\ A' = Pdone /\ (0%nat, 0%nat) ⩹ idx1 /\
                 (exists f', getregs S2 r15 = Some (W f') /\ pc2 = f' +ᵢ ($ 8) /\ npc2 = f' +ᵢ ($ 12))) \/
                (exists Q' Kq', Kq = Q' :: Kq' /\ rel_safety_WFST idx1 (C, S2, pc2, npc2) (A', HS') Q' Kq' Spec)
              )
      )
    ) ->
    rel_safety_WFST idx (C, S, pc, npc) (A, HS) Q Kq Spec.

Lemma function_correctness_aux' :
    forall P Q Spec S HS A w pc I C Kq,
      rel_safety_insSeq Spec (w, (1 + get_insSeqLen I)%nat) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q -> 
      LookupXC C pc I ->
      (S, HS, A, w) ||= P -> WFST Q Kq Spec C ->
      rel_safety_WFST (w, (1 + get_insSeqLen I)%nat) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q Kq Spec.
Proof.
Admitted.

Lemma function_correctness_aux :
  forall P Q Spec S HS A w pc I C Kq,
    insSeq_rel_sound Spec P pc I Q -> LookupXC C pc I ->
    cdhp_rel_sound Spec C -> (S, HS, A, w) ||= P -> WFST Q Kq Spec C ->
    rel_safety_WFST (w, (1 + get_insSeqLen I)%nat) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q Kq Spec.
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
  }
   
Theorem function_correctness :
  forall P Q Spec S HS A w pc I C,
    insSeq_rel_sound Spec P pc I Q -> LookupXC C pc I ->
    cdhp_rel_sound Spec C -> (S, HS, A, w) ||= P -> Q ⇒ RAprim Pdone ⋆ RAtrue ->
    rel_safety 0%nat (w, (1 + get_insSeqLen I)%nat) (C, S, pc, pc +ᵢ ($ 4)) (A, HS) Q.
Proof.
Admitted.
