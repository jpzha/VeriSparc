Require Import Coqlib.        
Require Import Maps.      
Require Import LibTactics.  
       
Require Import Integers.  
Open Scope Z_scope.    
Import ListNotations.
  
Set Asymmetric Patterns. 
       
Require Import state.    
Require Import language. 

Set Implicit Arguments.  
Unset Strict Implicit. 
             
Require Import logic. 
Require Import soundness.
   
Require Import lemmas.
Require Import lemmas_ins.
Require Import inssound.

Require Import wf_seq_sound.

Require Import Coq.Logic.FunctionalExtensionality.
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.
    

(*+ Well-formed CodeHeap Proof +*)

Theorem cdhp_rule_sound :
  forall C Spec Spec',
    wf_cdhp Spec C Spec' ->
    cdhp_sound Spec C Spec'.
Proof.
  intros.
  unfolds wf_cdhp, cdhp_sound.
  intros.
  eapply H with (L := L) in H0.
  simpljoin1.
  renames x to I.
  exists I.
  split; eauto.
  eapply wf_seq_sound in H3; eauto.
Qed.

Definition ins_sound_partial (p q : asrt) (i : ins) :=
  forall s s', s |= p -> (Q__ s (cntrans i) s') -> s' |= q.

Lemma total_to_partial :
  forall p q i,
    ins_sound p q i -> ins_sound_partial p q i.
Proof.
  intros.
  unfolds ins_sound, ins_sound_partial.
  intros.
  eapply H in H0; eauto.
  simpljoin1.
  eapply ins_exec_deterministic in H0; eauto.
  subst.
  eauto.
Qed.
  
(*+ Well-formed function proof +*)
Lemma safety_Sn_safety_n :
  forall n C S pc npc q k,
    safety (Nat.succ n) C S pc npc q k ->
    safety n C S pc npc q k.
Proof.
  intro n.
  induction n; intros.

  -
    econstructor; eauto.

  -
    econstructor; intros.

    + (** i *)
      inversion H; subst.
      clear H3 H4 H5 H6 H7 H8.
      eapply H2 in H0.
      clear H2.
      simpljoin1.
      split; eauto.

    + (** jumpl aexp rd *)
      inversion H; subst.
      clear H2 H4 H5 H6 H7 H8.
      eapply H3 in H0.
      clear H3.
      simpljoin1.
      split; eauto.
      exists x x0 x1 x2 x3 x4.
      split; eauto.

    + (** cbe f *)
      inversion H; subst.
      clear H2 H3 H5 H6 H7 H8.
      eapply H4 in H0.
      clear H4.
      simpljoin1; eauto.
      split; eauto.
      exists x x0 x1 x2 x3 x4.
      split; eauto.

    + (** cnbe *)
      inversion H; subst.
      clear H2 H3 H4 H6 H7 H8.
      eapply H5 in H0; eauto.
      simpljoin1.
      split; eauto.
      exists x x0 x1 x2 x3 x4.
      eauto.

    + (** call f *)
      inversion H; subst.
      clear H2 H3 H4 H5 H7 H8.
      eapply H6 in H0.
      simpljoin1.
      split; eauto.
      exists x x0 x1 x2 x3 x4.
      eauto.

    + (** retl *)
      inversion H; subst.
      clear H2 H3 H4 H5 H6 H8.
      eapply H7 in H0.
      simpljoin1.
      split; eauto.
      exists x x0 x1 x2 x3 x4.
      eauto.
      clear H7.
      intros.
      eapply H1 in H4; eauto.
      destruct H4; eauto.
      right.
      simpljoin1.
      split; eauto.

    + (** ret *)
      inversion H; subst.
      clear H2 H3 H4 H5 H6 H7.
      eapply H8 in H0.
      simpljoin1.
      split; eauto.
      exists x x0 x1 x2 x3 x4.
      eauto.
      clear H8.
      intros.
      eapply H1 in H4; eauto.
      destruct H4; eauto.
      right.
      simpljoin1.
      split; eauto.
Qed.

Lemma safety_call_ret :
  forall n C S pc npc q q' Spec Spec' f k,
    safety_insSeq C S pc npc q Spec ->
    cdhp_subst Spec Spec' -> cdhp_sound Spec C Spec' -> q ==> (Or r15 ==ₑ f) ->
    (forall S', S' |= q -> safety n C S' (f +ᵢ ($ 8)) (f +ᵢ ($ 12)) q' k) ->
    safety n C S pc npc q' (Nat.succ k).
Proof.
  intro n.
  induction n; intros.

  -
    econstructor; eauto.

  - 
    inversion H; subst.

    + (** i *)
      econstructor; intros; get_ins_diff_false.
      clear H7.
      split; eauto.
      intros.
      eapply IHn; eauto.
      intros.
      eapply H3 in H8.
      clear - H8.
      eapply safety_Sn_safety_n; eauto.
 
    + (** call f *)
      econstructor; intros; get_ins_diff_false.
      clear H7.
      split; eauto.
      clear H5.
      intros.
      eapply H6 in H7; eauto.
      simpljoin1.
      renames x to fp, x0 to fq, x1 to L, x2 to r.
      lets Hfp : H10.
      eapply sep_star_split in Hfp.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      simpl in H13.
      simpljoin1.
      lets Hcdhp_subst : H0. 
      lets Hcdhp_sound : H1.
      unfold cdhp_subst in Hcdhp_subst.
      unfold cdhp_sound in Hcdhp_sound.
      eapply Hcdhp_subst in H9.
      eapply Hcdhp_sound in H9; eauto.
      simpljoin1.
      rename x into I.
      eapply wf_seq_frame_rule in H15; eauto.
      eapply IHn with (q := fq L ** r) (f := pc); eauto.
      clear - H7 H12.  
      intros.
      sep_star_split_tac.
      simpls.
      simpljoin1.
      simpls.
      eapply H12 in H; eauto.
      simpls.
      simpljoin1.
      rewrite get_R_rn_neq_r0; eauto.
      2 : intro; tryfalse.
      rewrite get_R_rn_neq_r0 in H; eauto.
      2 : intro; tryfalse.
      eapply disj_in_m1_merge_still; eauto.
      intros.
      eapply IHn; eauto.
      intros.
      eapply H3 in H17.
      eapply safety_Sn_safety_n; eauto.
 
    + (** jumpl aexp rd *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      eapply H6 in H9; eauto.
      simpljoin1. 
      renames x to fp, x0 to fq, x1 to L, x2 to r.
      lets Hcdhp_subst : H0.
      lets Hcdhp_sound : H1.
      unfold cdhp_subst in Hcdhp_subst.
      unfold cdhp_sound in Hcdhp_sound. 
      eapply Hcdhp_subst in H9.
      lets Ht : H10.
      eapply sep_star_split in Ht.
      simpljoin1.
      destruct_state x.
      destruct_state x0.
      simpl in H14.
      simpljoin1.
      eapply Hcdhp_sound with (L := L) in H9; eauto.
      simpljoin1.
      renames x to I.
      eapply wf_seq_frame_rule in H16; eauto.
      eapply wf_seq_conseq_rule in H16; eauto.
      unfold insSeq_sound in H16. 
      eapply H16 in H9; eauto.
      eapply IHn; eauto.
      clear - H3.
      intros.
      eapply H3 in H.
      eapply safety_Sn_safety_n; eauto.

    + (** be f *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      clear H5 H7.
      eapply H6 in H9; eauto.
      simpljoin1.
      destruct (Int.eq x ($ 0)) eqn : Heqe.
      {
        eapply int_eq_true_eq in Heqe.
        eapply H9 in Heqe.
        eapply IHn; eauto.
        intros.
        eapply safety_Sn_safety_n; eauto.
      }
      {
        eapply int_eq_false_neq in Heqe.
        eapply H7 in Heqe.
        simpljoin1.
        renames x0 to fp, x1 to fq, x2 to L, x3 to r.
        lets Hcdhp_subst : H0.
        lets Hcdhp_sound : H1.
        unfold cdhp_subst in Hcdhp_subst.
        unfold cdhp_sound in Hcdhp_sound.
        eapply Hcdhp_subst in H10. 
        sep_star_split_tac.
        simpl in H16.
        simpljoin1.
        eapply Hcdhp_sound in H10; eauto.
        simpljoin1.
        renames x0 to I.
        eapply wf_seq_frame_rule in H16; eauto.
        eapply wf_seq_conseq_rule in H16; eauto.
        unfold insSeq_sound in H16.
        eapply H16 with (S := (merge m m0, (merge r0 r1, f2), d0)) in H10; eauto.
        eapply IHn; eauto.
        intros.
        eapply H3 in H17.
        eapply safety_Sn_safety_n; eauto.
        simpl.
        exists (m, (r0, f2), d0) (m0, (r1, f2), d0).
        simpl.
        repeat (split; eauto).
      }

    + (** bne f *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      clear H5 H7.
      eapply H6 in H9; eauto.
      simpljoin1.
      destruct (Int.eq x ($ 0)) eqn : Heqe.
      {
        eapply int_eq_true_eq in Heqe.
        eapply H7 in Heqe.
        simpljoin1.
        renames x0 to fp, x1 to fq, x2 to L, x3 to r.
        sep_star_split_tac.
        simpl in H16.
        simpljoin1.
        lets Hcdhp_subst : H0.
        lets Hcdhp_sound : H1.
        unfold cdhp_subst in Hcdhp_subst.
        unfold cdhp_sound in Hcdhp_sound.
        eapply Hcdhp_subst in H10.
        eapply Hcdhp_sound with (L := L) in H10; eauto.
        simpljoin1.
        renames x0 to I.
        eapply wf_seq_frame_rule in H16; eauto.
        eapply wf_seq_conseq_rule in H16; eauto.
        eapply IHn; eauto.
        unfold insSeq_sound in H16.
        eapply H16; eauto.
        simpl.
        exists (m, (r0, f2), d0) (m0, (r1, f2), d0).
        simpl.
        repeat (split; eauto).
        intros.
        eapply H3 in H17.
        eapply safety_Sn_safety_n; eauto.
      }
      {
        eapply int_eq_false_neq in Heqe.
        eapply H9 in Heqe.
        eapply IHn; eauto.
        intros.
        eapply safety_Sn_safety_n; eauto.
      }

    + (** retl *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      right.
      clear H5 H7.
      eapply H6 in H9; eauto.
      split.
      eauto.
      simpl.
      simpljoin1.
      lets Hret : H5.
      eapply H3 in H5.
      eapply H2 in Hret.
      destruct_state S2.
      simpls.
      rewrite H7 in Hret.
      inversion Hret; subst.
      eapply safety_Sn_safety_n; eauto.

    + (** ret *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      right.
      clear H5 H7.
      eapply H6 in H9; eauto.
      split.
      eauto.
      simpl.
      simpljoin1.
      lets Hret : H5.
      eapply H3 in H5.
      eapply H2 in Hret.
      destruct_state S2.
      simpls.
      rewrite H7 in Hret.
      inversion Hret; subst.
      eapply safety_Sn_safety_n; eauto.
Qed.  

Lemma safety_function :
  forall n C S pc npc q Spec Spec',
    safety_insSeq C S pc npc q Spec ->
    cdhp_subst Spec Spec' -> cdhp_sound Spec C Spec' ->
    safety n C S pc npc q 0.
Proof.
  intro n.
  induction n; intros.
  
  -
    econstructor; eauto.

  -
    inversion H; subst.

    + (** i *)
      econstructor; intros; get_ins_diff_false.
      clear H5.
      split; eauto.
 
    + (** call f *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      clear H5. 
      unfold Nat.succ.
      intros.
      eapply H4 in H6; eauto. simpljoin1.
      renames x to fp, x0 to fq, x1 to L, x2 to r.
      eapply safety_call_ret with (q := fq L ** r) (f := pc); eauto.
      clear - H8 H9 H10 H0 H1.
      unfolds cdhp_subst.
      unfolds cdhp_sound.
      eapply H0 in H8.
      sep_star_split_tac.
      simpls.
      simpljoin1.
      eapply H1 in H8; eauto.
      simpljoin1.
      renames x to I.
      eapply wf_seq_frame_rule in H6; eauto.
      unfolds insSeq_sound.
      eapply H6; eauto.
      simpl. 
      exists (m, (r0, f1), d0) (m0, (r1, f1), d0).
      repeat (split; eauto). 
      intros.  
      clear - H6 H11.
      sep_star_split_tac.
      simpls.
      simpljoin1.
      simpls.
      eapply H11 in H1; eauto.
      simpls.
      eapply get_R_merge_still; eauto.

    + (** jumpl aexp rd *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      clear H5 H3.
      eapply H4 in H7; eauto.
      simpljoin1. 
      renames x to fp, x0 to fq, x1 to L, x2 to r.
      clear - IHn H3 H5 H6 H7 H0 H1.
      lets Hcdhp_subst : H0.
      lets Hcdhp_sound : H1.
      unfold cdhp_subst in Hcdhp_subst.
      unfold cdhp_sound in Hcdhp_sound.
      eapply Hcdhp_subst in H3.
      sep_star_split_tac.
      simpl in H8.
      simpljoin1.
      eapply Hcdhp_sound in H3; eauto.
      simpljoin1.
      renames x to I.
      eapply wf_seq_frame_rule in H8; eauto.
      eapply wf_seq_conseq_rule in H8; eauto.
      unfolds insSeq_sound.
      eapply H8 in H3; eauto.
      simpl.
      exists (m, (r0, f0), d0) (m0, (r1, f0), d0).
      simpl.
      repeat (split; eauto).

    + (** be f *) 
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      clear H5 H3.
      eapply H4 in H7; eauto.
      simpljoin1.
      destruct (Int.eq x ($ 0)) eqn:Hx.
      {
        assert (Hx0 : x = $ 0).
        {
          clear - Hx.
          unfolds Int.eq.
          destruct (zeq (Int.unsigned x) (Int.unsigned $ 0)) eqn:Heqe; tryfalse.
          clear Heqe.
          eapply z_eq_to_int_eq in e.
          do 2 rewrite Int.repr_unsigned in e; eauto.
        }

        eapply H7 in Hx0.
        eauto.
      }
      {
        assert (Hx_neq0 : x <> $ 0).
        {
          clear - Hx.
          unfolds Int.eq.
          destruct (zeq (Int.unsigned x) (Int.unsigned $ 0)) eqn:Heqe; tryfalse.
          clear Heqe.
          intro.
          subst.
          eauto.
        }

        eapply H5 in Hx_neq0.
        simpljoin1.
        renames x0 to fp, x1 to fq, x2 to L, x3 to r.
        sep_star_split_tac.
        simpl in H14.
        simpljoin1.
        lets Hcdhp_subst : H0.
        lets Hcdhp_sound : H1.
        unfold cdhp_subst in Hcdhp_subst.
        unfold cdhp_sound in Hcdhp_sound.
        eapply Hcdhp_subst in H8.
        eapply Hcdhp_sound in H8; eauto.
        simpljoin1.
        renames x0 to I.
        eapply wf_seq_frame_rule in H14; eauto.
        eapply wf_seq_conseq_rule in H14; eauto.
        unfold insSeq_sound in H14.
        eapply H14 in H8; eauto.
        simpl.
        exists (m, (r0, f1), d0) (m0, (r1, f1), d0).
        simpl.
        repeat (split; eauto).
      }

    + (** bne f *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      clear H5 H3.
      eapply H4 in H7; eauto.
      simpljoin1.
      destruct (Int.eq x ($ 0)) eqn:Hx.
      {
        assert (Hx0 : x = $ 0).
        {
          clear - Hx.
          unfolds Int.eq.
          destruct (zeq (Int.unsigned x) (Int.unsigned $ 0)) eqn:Heqe; tryfalse.
          clear Heqe.
          eapply z_eq_to_int_eq in e.
          do 2 rewrite Int.repr_unsigned in e; eauto.
        }

        eapply H5 in Hx0.
        simpljoin1.
        renames x0 to fp, x1 to fq, x2 to L, x3 to r.
        sep_star_split_tac.
        simpl in H14.
        simpljoin1.
        lets Hcdhp_subst : H0.
        lets Hcdhp_sound : H1.
        unfold cdhp_subst in Hcdhp_subst.
        unfold cdhp_sound in Hcdhp_sound.
        eapply Hcdhp_subst in H8.
        eapply Hcdhp_sound in H8; eauto.
        simpljoin1.
        renames x0 to I.
        eapply wf_seq_frame_rule in H14; eauto.
        eapply wf_seq_conseq_rule in H14; eauto.
        unfold insSeq_sound in H14.
        eapply H14 in H8; eauto.
        simpl.
        exists (m, (r0, f1), d0) (m0, (r1, f1), d0).
        simpl.
        repeat (split; eauto).
      }
      {
        assert (Hx_neq0 : x <> $ 0).
        {
          clear - Hx.
          unfolds Int.eq.
          destruct (zeq (Int.unsigned x) (Int.unsigned $ 0)) eqn:Heqe; tryfalse.
          clear Heqe.
          intro.
          subst.
          eauto.
        }

        eapply H7 in Hx_neq0.
        eauto.
      }

    + (** retl *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      eapply H4 in H7; eauto.
      left.
      simpljoin1.
      eauto.

    + (** ret *)
      econstructor; intros; get_ins_diff_false.
      split; eauto.
      intros.
      eapply H4 in H7; eauto.
      left.
      simpljoin1.
      eauto.
Qed.

(** wf_function means if the current instruction sequence is well-formed and the code heap is well-formed, then we get the execution of the current function is safe for any steps n *)
Theorem wf_function :
  forall p q Spec Spec' S C pc I,
    insSeq_sound Spec p pc I q -> LookupC C pc I ->
    cdhp_subst Spec Spec' -> cdhp_sound Spec C Spec' -> S |= p ->
    forall n, safety n C S pc (pc +ᵢ ($ 4)) q 0.
Proof.
  intros.
  unfolds insSeq_sound.
  lets Hsafety_insSeq : H0.
  eapply H in Hsafety_insSeq; eauto.
  eapply safety_function; eauto.
Qed.

  