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

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(** Auxiliary Lemmas about Int *)
Lemma Int_unsigned_0 :
  Int.unsigned $ 0 = 0%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_1 :
  Int.unsigned $ 1 = 1%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_2 :
  Int.unsigned $ 2 = 2%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_3 :
  Int.unsigned $ 3 = 3%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_4 :
  Int.unsigned $ 4 = 4%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_5 :
  Int.unsigned $ 5 = 5%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_6 :
  Int.unsigned $ 6 = 6%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_7 :
  Int.unsigned $ 7 = 7%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_8 :
  Int.unsigned $ 8 = 8%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_9 :
  Int.unsigned $ 9 = 9%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_10 :
  Int.unsigned $ 10 = 10%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_11 :
  Int.unsigned $ 11 = 11%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_12 :
  Int.unsigned $ 12 = 12%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_13 :
  Int.unsigned $ 13 = 13%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_14 :
  Int.unsigned $ 14 = 14%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma Int_unsigned_15 :
  Int.unsigned $ 15 = 15%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma nth_bit_and :
  forall n1 n2,
    $ 0 <=ᵤᵢ n1 <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ n2 <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ n1) &ᵢ (($ 1) <<ᵢ n2) !=ᵢ ($ 0) = true ->
    n1 = n2.
Proof.
  intros.
  eapply and_not_zero_eq; eauto.
  intro.
  unfolds Int.eq.
  rewrite H2 in H1.
  try rewrite Int_unsigned_0 in *.
  simpls; tryfalse.
Qed.

Lemma int_inrange_0_7_add_one_still :
  forall n,
    $ 0 <=ᵤᵢ n <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ (n +ᵢ ($ 1)) modu N <=ᵤᵢ $ 7.
Proof.
  intros.
  destruct n; simpls.
  unfolds int_leu.
  unfolds Int.ltu.
  try rewrite Int_unsigned_0 in *.
  try rewrite Int_unsigned_7 in *.
  simpls.
  unfolds Int.eq; simpls.
  unfolds Int.add; simpls.
  try rewrite Int_unsigned_0 in *.
  try rewrite Int_unsigned_7 in *.
  try rewrite Int_unsigned_1 in *.
  unfold Int.modu.
  unfold N.
  try rewrite Int_unsigned_8 in *.
  
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); simpls; tryfalse; try omega.
  {
    destruct intval; simpls; tryfalse.
    destruct p; simpls; try omega.
    destruct p; simpls; try omega.
    destruct p; simpls; try omega.
    destruct p; simpls; try omega.
    tryfalse.
    destruct p; simpls; tryfalse.
    destruct p; simpls; tryfalse.
    destruct p; simpls; tryfalse.
    rewrite Int_unsigned_6; simpls; eauto.
    rewrite Int_unsigned_4; simpls; eauto.
    destruct p; simpls; tryfalse; try omega.
    destruct p; simpls; tryfalse; try omega.
    rewrite Int_unsigned_7; simpls; eauto.
    destruct p; simpls; tryfalse; try omega.
    rewrite Int_unsigned_5; simpls; eauto.
    rewrite Int_unsigned_3; simpls; eauto.
    rewrite Int_unsigned_2; simpls; eauto.
  }
  {
    subst; simpls.
    rewrite Int_unsigned_8; eauto.
  }
  {
    subst; simpls.
    rewrite Int_unsigned_1; eauto.
  }
Qed.

Lemma int_inrange_0_7_sub_one_still :
  forall n,
    $ 0 <=ᵤᵢ n <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ ((n +ᵢ N) -ᵢ ($ 1)) modu N <=ᵤᵢ $ 7.
Proof.
  intros.
  destruct n; simpls.
  unfolds int_leu.
  unfolds Int.ltu.
  try rewrite Int_unsigned_0 in *.
  try rewrite Int_unsigned_7 in *.
  simpls.
  unfolds Int.eq; simpls.
  unfolds Int.add; simpls.
  unfolds Int.sub; simpls.
  try rewrite Int_unsigned_0 in *.
  try rewrite Int_unsigned_7 in *.
  try rewrite Int_unsigned_1 in *.
  try rewrite Int_unsigned_8 in *. 
  unfold Int.modu.
  unfold N.
  try rewrite Int_unsigned_8 in *.
  
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); simpls; tryfalse; try omega.
  {
    destruct intval; simpls; tryfalse.
    destruct p; simpls; try omega.
    destruct p; simpls; try omega.
    destruct p; simpls; try omega.
    destruct p; simpls; try omega.
    tryfalse.
    destruct p; simpls; tryfalse.
    destruct p; simpls; tryfalse.
    destruct p; simpls; tryfalse.
    rewrite Int_unsigned_13; simpls; eauto.
    rewrite Int_unsigned_11; simpls; eauto.
    destruct p; simpls; tryfalse; try omega.
    destruct p; simpls; tryfalse; try omega.
    rewrite Int_unsigned_14; simpls; eauto.
    destruct p; simpls; tryfalse; try omega.
    rewrite Int_unsigned_12; simpls; eauto.
    rewrite Int_unsigned_10; simpls; eauto.
    rewrite Int_unsigned_9; simpls; eauto.
  }
  {
    subst; simpls.
    rewrite Int_unsigned_15; eauto.
  }
  {
    subst; simpls.
    rewrite Int_unsigned_8; eauto.
  }
Qed.

Lemma fmlst_underflow_len_0 :
  forall x0,
    $ 0 <=ᵤᵢ x0 <=ᵤᵢ $ 7 ->
    ((N +ᵢ ((x0 +ᵢ ($ 1)) modu N)) -ᵢ x0) -ᵢ ($ 1) modu N = $ 0.
Proof.
  intros.
  eapply in_range_0_7_num in H.
  unfold N, Int.add, Int.sub, Int.modu; simpls.
  destruct H; subst.
  {
    rewrite Int_unsigned_0, Int_unsigned_1, Int_unsigned_8; simpls.
    rewrite Int_unsigned_1; simpls.
    assert (1 mod 8 = 1); simpl; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_8, Int_unsigned_1; simpls.
    rewrite Int_unsigned_2; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_8, Int_unsigned_2, Int_unsigned_1; simpls.
    rewrite Int_unsigned_3; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_8, Int_unsigned_3, Int_unsigned_1; simpls.
    rewrite Int_unsigned_4; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_8, Int_unsigned_4, Int_unsigned_1; simpls.
    rewrite Int_unsigned_5; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_8, Int_unsigned_5, Int_unsigned_1; simpls.
    rewrite Int_unsigned_6; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_8, Int_unsigned_6, Int_unsigned_1; simpls.
    rewrite Int_unsigned_7; eauto.
  }
  {
    rewrite Int_unsigned_8, Int_unsigned_7, Int_unsigned_1; simpls.
    rewrite Int_unsigned_8; eauto.
  }
Qed.

Lemma fmlst_underflow_len_6 :
  forall x0,
    $ 0 <=ᵤᵢ x0 <=ᵤᵢ $ 7 ->
    (((N +ᵢ (((x0 +ᵢ N) -ᵢ ($ 1)) modu N)) -ᵢ x0) -ᵢ ($ 1)) modu N = $ 6.
Proof.
  intros.
  eapply in_range_0_7_num in H.
  unfold N, Int.add, Int.sub, Int.modu; simpls.
  destruct H; subst.
  {
    rewrite Int_unsigned_0, Int_unsigned_1, Int_unsigned_8; simpls.
    rewrite Int_unsigned_8; simpls.
    assert (7 mod 8 = 7); simpl; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_1, Int_unsigned_8; simpls.
    rewrite Int_unsigned_9; simpls; rewrite Int_unsigned_8; simpls.
    assert (8 mod 8 = 0); simpl; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_2, Int_unsigned_8, Int_unsigned_1; simpls.
    rewrite Int_unsigned_10; simpls; rewrite Int_unsigned_9; simpls.
    assert (9 mod 8 = 1); simpl; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_3, Int_unsigned_8, Int_unsigned_1; simpls.
    rewrite Int_unsigned_11; simpls; rewrite Int_unsigned_10; simpls.
    assert (10 mod 8 = 2); simpl; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_4, Int_unsigned_8, Int_unsigned_1; simpls.
    rewrite Int_unsigned_12; simpls; rewrite Int_unsigned_11; simpls.
    assert (11 mod 8 = 3); simpl; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_5, Int_unsigned_8, Int_unsigned_1; simpls.
    rewrite Int_unsigned_13; simpls; rewrite Int_unsigned_12; simpls.
    assert (12 mod 8 = 4); simpl; eauto.
  }
  destruct H; subst.
  {
    rewrite Int_unsigned_6, Int_unsigned_8, Int_unsigned_1; simpls.
    rewrite Int_unsigned_14; simpls; rewrite Int_unsigned_13; simpls.
    assert (13 mod 8 = 5); simpl; eauto.
  }
  {
    rewrite Int_unsigned_7, Int_unsigned_8, Int_unsigned_1; simpls.
    rewrite Int_unsigned_15; simpls; rewrite Int_unsigned_14; simpls.
    assert (14 mod 8 = 6); simpl; eauto.
  }
Qed.

(** Auxiliary Lemmas about Register *)
Lemma get_R_set_R_same_reg :
  forall R rr w,
    rr <> Rr r0 -> indom rr R ->
    get_R (set_R R rr w) rr = Some w.
Proof.
  intros.
  unfold set_R.
  unfold is_indom.
  unfold indom in *.
  simpljoin1.
  rewrite H0; simpl; eauto.
  unfold get_R.
  rewrite RegMap.gss; eauto.
  destruct rr; simpls; tryfalse; eauto.
  destruct g; simpls; tryfalse; eauto.
Qed.

Lemma getR_setR_neq_stable :
  forall R rr v rr' w,
    R rr = Some v -> rr <> rr' -> set_R R rr' w rr = Some v.
Proof.
  intros.
  unfold set_R.
  unfold is_indom.
  destruct (R rr') eqn:Heqe.
  rewrite RegMap.gso; eauto.
  eauto.
Qed.

Lemma fetch_frame_set_R_psr_stable :
  forall (R : RegFile) (psr : PsrReg) w fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    fetch_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (set_R R psr w) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfold fetch_frame in *.

  destruct (R rr0) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  2 : intro; tryfalse.
  clear Heqe0.

  destruct (R rr1) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  2 : intro; tryfalse.
  clear Heqe0.

  destruct (R rr2) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  2 : intro; tryfalse.
  clear Heqe0.

  destruct (R rr3) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  2 : intro; tryfalse.
  clear Heqe0.

  destruct (R rr4) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  2 : intro; tryfalse.
  clear Heqe0.

  destruct (R rr5) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  2 : intro; tryfalse.
  clear Heqe0.

  destruct (R rr6) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  2 : intro; tryfalse.
  clear Heqe0.

  destruct (R rr7) eqn:Heqe0; tryfalse.
  erewrite getR_setR_neq_stable; eauto.
  intro; tryfalse.
Qed. 

Lemma fetch_set_R_psr_stable :
  forall R (psr : PsrReg) w fmo fml fmi,
    fetch R = Some [fmo; fml; fmi] ->
    fetch (set_R R (Rpsr psr) w) = Some [fmo; fml; fmi].
Proof.
  intros.
  unfolds fetch.
  destruct (fetch_frame R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe0; tryfalse.
  eapply fetch_frame_set_R_psr_stable in Heqe0.
  rewrite Heqe0; clear Heqe0.
  destruct (fetch_frame R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe0; tryfalse.
  eapply fetch_frame_set_R_psr_stable in Heqe0.
  rewrite Heqe0; clear Heqe0.
  destruct (fetch_frame R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe0; tryfalse.
  eapply fetch_frame_set_R_psr_stable in Heqe0; eauto.
  rewrite Heqe0; eauto.
Qed.

Lemma fetch_frame_set_window_out :
  forall (R : RegFile) fm1 fm2 fm3,
    (forall (rr : GenReg), indom rr R) ->
    fetch_frame (set_window R fm1 fm2 fm3) r8 r9 r10 r11 r12 r13 r14 r15 = Some fm1.
Proof.
  intros.
  unfold fetch_frame.
  destruct fm1.

  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r8 = Some v).
  {
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls.
    do 23 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r8).
    eauto.
  }
  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r9 = Some v0).
  {
    clear H0.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls. 
    do 22 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r9).
    eapply indom_setR_still; eauto.
  }
  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r10 = Some v1).
  {
    clear H0 H1.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls. 
    do 21 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r10).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r11 = Some v2).
  {
    clear H0 H1 H2.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls. 
    do 20 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r11).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r12 = Some v3).
  {
    clear H0 H1 H2 H3.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls. 
    do 19 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r12).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r13 = Some v4).
  {
    clear H0 H1 H2 H3 H4.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls. 
    do 18 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r13).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r14 = Some v5).
  {
    clear H0 H1 H2 H3 H4 H5.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls. 
    do 17 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r14).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm2 fm3 r15 = Some v6).
  {
    clear H0 H1 H2 H3 H4 H5 H6.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm2.
    simpls. 
    do 16 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r15).
    repeat (eapply indom_setR_still; eauto).
  }
  rewrite H0, H1, H2, H3, H4, H5, H6, H7.
  eauto.
Qed.

Lemma fetch_frame_set_window_local :
  forall (R : RegFile) fm1 fm2 fm3,
    (forall (rr : GenReg), indom rr R) ->
    fetch_frame (set_window R fm1 fm2 fm3) r16 r17 r18 r19 r20 r21 r22 r23 = Some fm2.
Proof.
  intros.
  unfold fetch_frame.
  destruct fm2.

  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r16 = Some v).
  {
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 15 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r16).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r17 = Some v0).
  {
    clear H0.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 14 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r17).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r18 = Some v1).
  {
    clear H0 H1.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 13 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r18).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r19 = Some v2).
  {
    clear H0 H1 H2.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 12 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r19).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r20 = Some v3).
  {
    clear H0 H1 H2 H3.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 11 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r20).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r21 = Some v4).
  {
    clear H0 H1 H2 H3 H4.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 10 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r21).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r22 = Some v5).
  {
    clear H0 H1 H2 H3 H4 H5.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 9 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r22).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 ([[v, v0, v1, v2, v3, v4, v5, v6]]) fm3 r23 = Some v6).
  {
    clear H0 H1 H2 H3 H4 H5.
    unfold set_window.
    unfold set_frame.
    destruct fm3, fm1.
    simpls.
    do 8 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r23).
    repeat (eapply indom_setR_still; eauto).
  }
  rewrite H0, H1, H2, H3, H4, H5, H6, H7.
  eauto.
Qed.

Lemma fetch_frame_set_window_in :
  forall (R : RegFile) fm1 fm2 fm3,
    (forall (rr : GenReg), indom rr R) ->
    fetch_frame (set_window R fm1 fm2 fm3) r24 r25 r26 r27 r28 r29 r30 r31 = Some fm3.
Proof.
  intros.
  unfold fetch_frame.
  destruct fm3.
  
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r24 = Some v).
  {
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    do 7 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r24).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r25 = Some v0).
  {
    clear H0.
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    do 6 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r25).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r26 = Some v1).
  {
    clear H0 H1.
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    do 5 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r26).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r27 = Some v2).
  {
    clear H0 H1 H2.
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    do 4 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r27).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r28 = Some v3).
  {
    clear H0 H1 H2 H3.
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    do 3 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r28).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r29 = Some v4).
  {
    clear H0 H1 H2 H3 H4.
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    do 2 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r29).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r30 = Some v5).
  {
    clear H0 H1 H2 H3 H4 H5.
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    do 1 (try erewrite getR_setR_neq_stable; eauto; try intro; tryfalse).
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r30).
    repeat (eapply indom_setR_still; eauto).
  }
  assert (set_window R fm1 fm2 ([[v, v0, v1, v2, v3, v4, v5, v6]]) r31 = Some v6).
  {
    clear H0 H1.
    unfold set_window.
    unfold set_frame.
    destruct fm2, fm1.
    simpls.
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite RegMap.gss; eauto.
    specialize (H r31).
    repeat (eapply indom_setR_still; eauto).
  }
  rewrite H0, H1, H2, H3.
  rewrite H4, H5, H6, H7.
  eauto.
Qed.

Lemma set_window_OK :
  forall (R : RegFile) fm1 fm2 fm3,
    (forall (rr : GenReg), indom rr R) ->
    fetch (set_window R fm1 fm2 fm3) = Some [fm1; fm2; fm3].
Proof.
  intros.
  unfold fetch.
  rewrite fetch_frame_set_window_out; eauto.
  rewrite fetch_frame_set_window_local; eauto.
  rewrite fetch_frame_set_window_in; eauto.
Qed.

Lemma fetch_frame_set_Mframe_same1 :
  forall b fm,
    fetch_frame (set_Mframe b ($ 0) fm) (b, $ 0) (b, $ 4) (b, $ 8)
                (b, $ 12) (b, $ 16) (b, $ 20) (b, $ 24) (b, $ 28) = Some fm.
Proof.
  intros.
  destruct fm.
  simpls.
  unfold fetch_frame; simpls.

  do 7 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 6 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 5 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 4 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 3 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 2 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 1 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gss; eauto.
Qed.

Lemma fetch_frame_set_Mframe_same2 :
  forall b fm,
    fetch_frame (set_Mframe b ($ 32) fm) (b, $ 32) (b, $ 36) (b, $ 40)
                (b, $ 44) (b, $ 48) (b, $ 52) (b, $ 56) (b, $ 60) = Some fm.
Proof.
  intros.
  destruct fm.
  simpls.
  unfold fetch_frame; simpls.

  do 7 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 6 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 5 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 4 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 3 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 2 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  do 1 (rewrite MemMap.gso; [ | intro; tryfalse]).
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gss; eauto.
Qed.

(** Auxiliary Lemmas about Sep Star *)
Lemma rel_sep_star_split :
  forall S HS A w P1 P2,
    (S, HS, A, w) ||= P1 ⋆ P2 ->
    exists S1 S2 HS1 HS2 w1 w2, state_union S1 S2 S /\ hstate_union HS1 HS2 HS /\
                     (S1, HS1, A, w1) ||= P1 /\ (S2, HS2, A, w2) ||= P2 /\ w = (w1 + w2)%nat.
Proof.
  intros.
  simpls. 
  destruct H as (hs1 & hs2 & s1 & s2 & w1 & w2 & Hhstate_union & Hstate_union & Hw & HP1 & HP2).
  do 6 eexists. 
  repeat (split; eauto).
Qed.

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

(** Auxiliary Lemmas about multi-steps *)
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

Definition get_Pc (P : LProg) :=
  match P with
  | (C, LS) => match LS with
              | (S', pc, npc) => C pc
              end
  end.

Lemma LP_deterministic :
  forall P P' P'' m com,
    get_Pc P = Some (c com) ->
    LP__ P m P' -> LP__ P m P'' -> P' = P''.
Proof.
  intros.
  inv H0.
  inv H1.
  rewrite <- H2 in H12.
  inv H12.
 
  inv H3; simpls;
    match goal with
    | H1 : C ?pc = Some ?A, H2 : C ?pc = Some ?B |- _ =>
      rewrite H1 in H2; inv H2
    | _ => idtac
    end.

  Ltac CElim C :=
    match goal with
    | H1 : C ?pc = Some ?A, H2 : C ?pc = Some ?B |- _ =>
      rewrite H1 in H2; inv H2
    | _ => idtac
    end.

  inv H13; CElim C.
  eapply ins_exec_deterministic in H11; eauto.
  inv H11; eauto.

  inv H13; CElim C.
  rewrite H18 in H16; inv H16; eauto.

  inv H13; CElim C; eauto.

  inv H13; CElim C; eauto.
  rewrite H18 in H16; inv H16; eauto.

  inv H13; CElim C; eauto.
  rewrite H18 in H16; inv H16; tryfalse.

  inv H13; CElim C; eauto.
  rewrite H18 in H16; inv H16; tryfalse.
Qed.

Lemma LP_CdhpInc :
  forall C1 C2 S S' m pc npc pc' npc',
    LP__ (C1, (S, pc, npc)) m (C1, (S', pc', npc')) ->
    LP__ (C1 ⊎ C2, (S, pc, npc)) m (C1 ⊎ C2, (S', pc', npc')).
Proof.
  intros.
  inv H.
  econstructor; eauto.
  inv H9; try solve [econstructor; eauto; try eapply get_vl_merge_still; eauto].
Qed.  
  
(** Auxiliary Lemmas about rel_safety *)
Lemma LtIndex_Trans :
  forall idx1 idx2 idx3,
    idx1 ⩹ idx2 -> idx2 ⩹ idx3 ->
    idx1 ⩹ idx3.
Proof.
  intros.
  unfolds LtIndex.
  destruct idx1, idx2, idx3.  
  inv H.
  inv H0.
  eapply lex_ord_left.
  eapply Nat.lt_trans; eauto.
  eapply lex_ord_left; eauto.
  inv H0.
  eapply lex_ord_left; eauto.
  eapply lex_ord_right; eauto.
  eapply Nat.lt_trans; eauto.
Qed.

Lemma rel_safety_idx_inc_still :
  forall k idx idx1 C S pc npc A HS Q,
    rel_safety k idx (C, S, pc, npc) (A, HS) Q -> idx ⩹ idx1 ->
    rel_safety k idx1 (C, S, pc, npc) (A, HS) Q.
Proof.
  cofix Hp; intros.
  inv H.
  econstructor; eauto; intros.
  {   
    clear H13 H14.
    eapply H12 in H.
    destruct H.
    split; eauto.
    intros.
    eapply H1 in H2.
    destruct H2.
    left.
    simpljoin1.
    exists idx.
    split; eauto.
    right.
    simpljoin1.
    destruct x0.
    eexists.
    exists (Nat.succ (Nat.succ n), n0).
    split; eauto.
    eapply Hp; eauto.
    econstructor; eauto.
  }
  {
    clear H12 H14.
    eapply H13 in H; eauto.
    destruct H.
    split; eauto.
    intros.
    eapply H1 with (S2 := S2) in H2; eauto.
    simpljoin1.
    destruct H2.
    exists x0 idx A HS.
    split; eauto. 
    simpljoin1; eauto.
    simpljoin1; eauto.    
    destruct x.
    do 4 eexists.
    split.
    eauto.
    instantiate (1 := (Nat.succ (Nat.succ n), n0)).
    eapply Hp; eauto.
    econstructor; eauto.
  }
  {
    clear H12 H13. 
    eapply H14 in H; eauto; clear H14.
    destruct H.
    split; eauto.
    intros.
    eapply H1 with (S2 := S2) in H2; eauto.
    simpljoin1.
    destruct H2. 
    exists x0 idx A HS x3.
    split; eauto.
    simpljoin1; eauto.
    destruct H4.
    left; eauto.
    simpljoin1; subst; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    eapply LtIndex_Trans; eauto.
 
    right; eauto.
    simpljoin1.
    split; eauto.
    destruct H4.
    simpljoin1.
    do 5 eexists.
    split; eauto.
    left.
    split; eauto.
    split; eauto.
    split; eauto.
    simpljoin1.
    do 5 eexists.
    split; eauto.
  }
  Unshelve.
  exact (5%nat, 6%nat).
  exact (5%nat, 6%nat).
  exact (5%nat, 6%nat).
  exact 5%nat.
Qed.

Ltac destruct_hstate hs :=
  destruct hs as [ [ [?T ?t] ?K] ?M].

(** Lemmas about eval expression *)
Lemma Rinj_getGenregHL_eq' :
  forall (ri : GenReg) R (HR : HRegFile) v,
    (forall rr : GenReg, exists v : Val, R rr = Some v /\ HR rr = Some v) -> HR ri = Some v ->
    R ri = Some v.
Proof.
  intros.
  specialize (H ri).
  simpljoin1.
  rewrite H0 in H1.
  inv H1; eauto.
Qed.

Lemma Rinj_getGenregHL_eq :
  forall (ri : GenReg) R HR v,
    Rinj R HR -> get_HR HR ri = Some v ->
    get_R R ri = Some v.
Proof.
  intros.
  inv H.
  specialize (H1 ri).
  simpljoin1.
  unfolds get_HR, get_R.
  rewrite H7 in H0.
  rewrite H; simpl; eauto.
Qed.

Lemma Rinj_Heval_impl_eval_oexp :
  forall HR R oexp v,
    Rinj R HR ->
    Heval_opexp HR oexp = Some v ->
    eval_opexp R oexp = Some v.
Proof.
  intros.
  destruct oexp; simpls; eauto.
  inv H.
  simpljoin1.
  specialize (H1 g).
  simpljoin1.
  unfolds get_HR.
  rewrite H7 in H0.
  unfold get_R.
  rewrite H1.
  destruct g; simpls; eauto.
Qed.

Lemma Rinj_Heval_impl_eval_addrexp :
  forall HR R aexp v,
    Rinj R HR ->
    Heval_addrexp HR aexp = Some v ->
    eval_addrexp R aexp = Some v.
Proof. 
  intros.
  destruct aexp; simpls.
  eapply Rinj_Heval_impl_eval_oexp; eauto.
  destruct (get_HR HR g) eqn:Heqe; simpls; eauto; tryfalse.
  assert (get_R R g = Some v0).
  {
    clear - H Heqe.
    inv H.
    simpljoin1.
    specialize (H0 g).
    simpljoin1.
    unfolds get_HR, get_R.
    rewrite H6 in Heqe.
    rewrite H0.
    eauto.
  }
  rewrite H1.
  destruct (Heval_opexp HR o) eqn:Heqe1; simpls; tryfalse.
  eapply Rinj_Heval_impl_eval_oexp in Heqe1; eauto.
  rewrite Heqe1; eauto.
Qed.
Lemma Rinj_indom_GenReg_HL :
  forall HR R (rd : GenReg),
    Rinj R HR -> indom rd HR -> indom rd R.
Proof.
  intros.
  inv H.
  simpljoin1.
  specialize (H1 rd).
  simpljoin1.
  unfold indom in *.
  simpljoin1.
  eauto.
Qed. 
      

(** Lemmas about exe_delay *)
Lemma exe_delay_empR_still :
  forall D R' D', 
    exe_delay empR D = (R', D') -> R' = empR.
Proof.
  induction D; intros; simpls.
  inv H; eauto.
  destruct a.
  destruct p.
  destruct d.
  {
    destruct (exe_delay empR D) eqn:Heqe.
    inv H.
    specialize (IHD r D').
    assert ((r, D') = (r, D')); eauto.
    eapply IHD in H; eauto.
    subst.
    unfold set_R.
    unfold is_indom.
    simpls; eauto.
  }
  {
    destruct (exe_delay empR D) eqn:Heqe.
    inv H.
    assert ((R', d0) = (R', d0)); eauto.
  }
Qed.

Lemma dly_frm_free_exe_delay_stable_relast :
  forall P D M R R' D' F hs A w,
    ((M, (R, F), D), hs, A, w) ||= P ->
    exe_delay R D = (R', D') ->
    ((M, (R', F), D'), hs, A, w) ||= P.
Proof.
  induction P; intros;
    try solve [destruct_state hs;
               simpls;
               simpljoin1;
               destruct m;
               simpljoin1;
               do 2 eexists;
               repeat (split; eauto);
               eapply exe_delay_empR_still; eauto].
  {
    (* RAlst a *)
    simpls.
    simpljoin1.
    repeat (split; eauto).
    eapply dly_frm_free_exe_delay_stable; eauto.
  }
  {
    (* RAtoken n *)
    simpls.
    destruct_state hs.
    destruct m.
    simpljoin1.
    repeat (split; eauto).
    eapply exe_delay_empR_still; eauto.
  }
  {
    (* RAfalse *)
    simpls; tryfalse.
  }
  {
    (* P1 /\ P2 *)
    simpls.
    simpljoin1.
    eapply IHP1 in H; eauto.
  }
  {
    (* P1 \/ P2 *)
    simpls.
    destruct H; eauto.
  }
  {
    (* P1 * P2 *)
    simpls.
    simpljoin1.
    destruct_state x1.
    destruct_state x2.
    simpls.
    simpljoin1.
    destruct_hstate x.
    destruct_hstate x0.
    simpls.
    simpljoin1.
    eapply exe_dly_sep_split in H0; eauto.
    simpljoin1.
    eapply IHP1 in H3; eauto.
    eapply IHP2 in H4; eauto.
    do 6 eexists.
    repeat (split; eauto).
    simpls.
    repeat (split; eauto).
  }
  {
    (* forall P *)
    simpls.
    intros.
    specialize (H0 x).
    eauto.
  }
  {
    (* exists P *)
    simpls.
    simpljoin1.
    eauto.
  }
Qed.

Lemma exe_delay_safety_property_relast :
  forall D (R R' R1 : RegFile) M D' F Pr hs A w,
    (R', D') = exe_delay R D -> disjoint R R1 ->
    ((M, (R1, F), D), hs, A, w) ||= Pr ->
    exists R1', disjoint R' R1' /\ (merge R' R1', D') = exe_delay (merge R R1) D /\
           (R1', D') = exe_delay R1 D /\ ((M, (R1', F), D'), hs, A, w) ||= Pr.
Proof.
  intros.
  assert (exists R1', (R1', D') = exe_delay R1 D).
  {
    eapply exe_delay_dlyls_deterministic; eauto.
  }
  destruct H2 as [R1' H2].
  lets Hdom_eq : H2.
  eapply exe_delay_dom_eq in Hdom_eq; eauto.
  exists R1'.
  lets Hmerge : H.
  eapply exe_delay_disj_merge with (R1 := R) (R2 := R1) in Hmerge; eauto.
  simpljoin1.
  repeat (split; eauto).
  eapply dly_frm_free_exe_delay_stable_relast; eauto.
Qed.

Lemma dlyfrmfree_changeFrm_stable_relasrt :
  forall P M (R : RegFile) F F' D hs A w,
    ~ indom cwp R ->
    ((M, (R, F), D), hs, A, w) ||= P ->
    ((M, (R, F'), D), hs, A, w) ||= P.
Proof.
  induction P; intros; destruct_hstate hs; simpls; simpljoin1;
    try solve [do 2 eexists; repeat (split; eauto)]; tryfalse.

  repeat (split; eauto).
  eapply dlyfrmfree_changeFrm_stable; eauto.

  repeat (split; eauto).

  do 2 eexists.
  split; eauto.
  eapply IHP; eauto.
  eapply notindom_after_exedly_pre_still; eauto.

  eapply IHP1 in H0; eauto.

  destruct H0.
  eapply IHP1 in H0; eauto.
  eapply IHP2 in H0; eauto.

  destruct_hstate x.
  destruct_hstate x0.
  destruct_state x1.
  destruct_state x2.
  simpls.
  simpljoin1. 
  eapply IHP1 in H3; eauto.
  eapply IHP2 in H4; eauto.
  do 6 eexists.
  repeat (split; eauto).
  simpl.
  repeat (split; eauto).
  intro.
  contradiction H.
  eapply indom_merge_still2; eauto.
  intro.
  contradiction H.
  eapply indom_merge_still; eauto.

  intros.
  specialize (H1 x).
  eauto.

  exists x.
  eauto.
Qed.

Lemma dlyfrmfree_notin_changeDly_still_relasrt :
  forall P M R F D (rsp : SpReg) v n hs A w,
    ((M, (R, F), D), hs, A, w) ||= P ->
    ~ indom rsp R ->
    ((M, (R, F), (n, rsp, v) :: D), hs, A, w) ||= P.
Proof.
  induction P; intros; tryfalse;
    try solve [destruct_hstate hs;
               simpls; simpljoin1; do 2 eexists; repeat (split; eauto)];
    destruct_hstate hs; simpls; simpljoin1; repeat (split; eauto).

  eapply dlyfrmfree_notin_changeDly_still; eauto.

  exists x ((Nat.succ n, rsp, v) :: x0).
  simpls.
  rewrite H; simpl.
  split; eauto.
  eapply IHP; eauto.
  eapply notindom_after_exedly_pre_still; eauto.

  destruct H; eauto.

  destruct_hstate x.
  destruct_hstate x0.
  destruct_state x1.
  destruct_state x2.
  simpls.
  simpljoin1. 
  do 6 eexists.
  instantiate (3 := (m0, (r0, f0), (n, rsp, v) :: d0)).
  instantiate (5 := (m, (r, f0), (n, rsp, v) :: d0)).
  repeat (split; eauto).
  Focus 2.
  eapply IHP1; eauto.
  intro.
  contradiction H0.
  eapply indom_merge_still; eauto.
  Focus 2.
  eapply IHP2; eauto.
  intro.
  contradiction H0.
  eapply indom_merge_still2; eauto.
  simpl.
  repeat (split; eauto).

  intros.
  specialize (H0 x).
  eapply H; eauto.

  exists x.
  eauto.
Qed.

(** Auxiliary rel_safety *)
CoInductive rel_safety_aux :
  nat -> Index -> (XCodeHeap * State * Word * Word) -> (primcom * HState) -> relasrt -> Prop :=
| aux_cons_safety : forall k idx C S pc npc A HS Q,
    (legal_com (C pc) /\ legal_com (C npc)) ->
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
              exists idx1, (idx1 ⩹ idx) /\ rel_safety_aux k idx1 (C, S', pc', npc') (A, HS) Q 
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
            exists idx1 idx2,
              idx1 ⩹ idx2 /\ idx2 ⩹ idx /\ rel_safety_aux (Nat.succ k) idx1 (C, S2, pc2, npc2) (A, HS) Q
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
            exists idx1 idx2 A' HS' w,
              (Nat.eqb k 0 = true /\ exec_prim (A, HS) (A', HS') /\ (S2, HS', A', w) ||= Q /\ (0%nat, 0%nat) ⩹ idx
              /\ (exists f', getregs S2 r15 = Some (W f') /\ pc2 = f' +ᵢ ($ 8) /\ npc2 = f' +ᵢ ($ 12))) \/
              (Nat.eqb k 0 = false /\ idx1 ⩹ idx2 /\ idx2 ⩹ idx /\ A' = A /\ HS = HS' /\
               rel_safety_aux (Nat.pred k) idx1 (C, S2, pc2, npc2) (A', HS') Q))
    ) ->
    rel_safety_aux k idx (C, S, pc, npc) (A, HS) Q.

Definition idx_sum (idx1 idx2 : Index) :=
  match idx1, idx2 with
  | (a1, b1), (a2, b2) => ((a1 + a2)%nat, (b1 + b2)%nat)
  end.

Lemma idx_lt_sum_still :
  forall idx idx' idx'',
    idx ⩹ idx' -> idx ⩹ idx_sum idx' idx''.
Proof.
  intros.
  destruct idx, idx', idx''.
  simpls.
  inv H.
  destruct n3.
  econstructor; eauto.
  rewrite Nat.add_0_r; eauto.
  econstructor.
  eapply Nat.lt_trans; eauto.
  eapply Nat.lt_add_pos_r; eauto.
  omega.
  destruct n3.
  rewrite Nat.add_0_r; eauto.
  unfold LtIndex.
  eapply lex_ord_right.
  destruct n4.
  rewrite Nat.add_0_r; eauto.
  eapply Nat.lt_trans; eauto.
  eapply Nat.lt_add_pos_r; eauto.
  omega.
  econstructor.
  eapply Nat.lt_add_pos_r; eauto.
  omega.
Qed.

Lemma idx_sum_pre_lt :
  forall idx1 idx2 idx',
    idx1 ⩹ idx2 ->
    idx_sum idx1 idx' ⩹ idx_sum idx2 idx'.
Proof.
  intros.
  destruct idx1, idx2, idx'.
  simpls.
  destruct n3.
  repeat (rewrite Nat.add_0_r; eauto).
  destruct n4.
  repeat (rewrite Nat.add_0_r; eauto).
  unfolds LtIndex.
  inv H.
  {
    econstructor; eauto.
  }
  eapply lex_ord_right.
  assert ((n0 + S n4 = S n4 + n0)%nat).
  rewrite Nat.add_comm; eauto.
  assert ((n2 + S n4 = S n4 + n2)%nat).
  rewrite Nat.add_comm; eauto.
  rewrite H, H0.  
  eapply plus_lt_compat_l; eauto.

  unfolds LtIndex.
  inv H.
  econstructor.
  assert ((n + S n3 = S n3 + n)%nat).
  rewrite Nat.add_comm; eauto.
  assert ((n1 + S n3 = S n3 + n1)%nat).
  rewrite Nat.add_comm; eauto.
  rewrite H, H0.
  eapply plus_lt_compat_l; eauto.

  eapply lex_ord_right.
  rewrite Nat.add_comm with (n := n0).
  rewrite Nat.add_comm with (n := n2).
  eapply plus_lt_compat_l; eauto.
Qed.

Inductive Lsafety : nat -> nat * LProg -> nat * LProg -> Prop :=
| bas_Lsafety : forall k C S pc npc,  Lsafety 0%nat (k, (C, (S, pc, npc))) (k, (C, (S, pc, npc)))  
| cons_Lsafety : forall k k' C S S' pc npc pc' npc' n,
    legal_com (C pc) -> legal_com (C npc) ->
    (
        forall f aexp rd i,
          (C pc = Some (c (cntrans i)) \/ C pc = Some (c (cjumpl aexp rd)) \/ C pc = Some (c (cbe f))) ->
          (
            (* progress *)
            exists S1 pc1 npc1 n',
              LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
              Lsafety n' (k, (C, (S1, pc1, npc1))) (k', (C, (S', pc', npc'))) /\
              (n = Nat.succ n')
          )
    ) ->
    (
        forall f,
          C pc = Some (c (ccall f)) ->
          (
            (* progress *)
            exists S1 pc1 npc1 S2 pc2 npc2 n',
              LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
              LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2)) /\ 
              Lsafety n' (Nat.succ k, (C, (S2, pc2, npc2))) (k', (C, (S', pc', npc'))) /\
              (n = Nat.succ (Nat.succ n'))
          )
    ) ->
    (
          C pc = Some (c (cretl)) ->
          (
            (* progress *)
            exists S1 pc1 npc1 S2 pc2 npc2 n',
              LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
              LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2)) /\ 
              (Nat.eqb k 0 = false /\
               Lsafety n' (Nat.pred k, (C, (S2, pc2, npc2))) (k', (C, (S', pc', npc'))) /\
               n = Nat.succ (Nat.succ n'))
          )
    ) ->
    Lsafety n (k, (C, (S, pc, npc))) (k', (C, (S', pc', npc'))).

Lemma legel_pc_ : forall (C : XCodeHeap) pc,
    legal_com (C pc) ->
    exists i aexp rd f,
      (C pc = Some (c (cntrans i)) \/ C pc = Some (c (cjumpl aexp rd)) \/ C pc = Some (c (cbe f)))
      \/ C pc = Some (c (ccall f)) \/ C pc = Some (c cretl).
Proof.
  intros.
  destruct (C pc) eqn:Heqe; simpls; tryfalse. 
  destruct c; simpls; try solve [do 4 eexists; right; eauto]; tryfalse.
  destruct c; simpls; try solve [do 4 eexists; eauto]; tryfalse.
  Unshelve.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact ($ 1).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact nop.
  exact ($ 1).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact ($ 1).
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
Qed.

Lemma fetch_frame_HL :
  forall HR (R : RegFile) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame HR rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    (forall (rr : GenReg), exists v, R rr = Some v /\ HR rr = Some v) ->
    fetch_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfold fetch_frame in *.
  
  destruct (HR rr0) eqn:Heqe0; simpls; tryfalse.
  lets Hrr0 : H0.
  specialize (Hrr0 rr0).
  simpljoin1.
  rewrite Heqe0 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe0.

  destruct (HR rr1) eqn:Heqe1; simpls; tryfalse.
  lets Hrr1 : H0.
  specialize (Hrr1 rr1).
  simpljoin1.
  rewrite Heqe1 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe1.

  destruct (HR rr2) eqn:Heqe2; simpls; tryfalse.
  lets Hrr2 : H0.
  specialize (Hrr2 rr2).
  simpljoin1.
  rewrite Heqe2 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe2.

  destruct (HR rr3) eqn:Heqe2; simpls; tryfalse.
  lets Hrr3 : H0.
  specialize (Hrr3 rr3).
  simpljoin1.
  rewrite Heqe2 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe2.

  destruct (HR rr4) eqn:Heqe2; simpls; tryfalse.
  lets Hrr4 : H0.
  specialize (Hrr4 rr4).
  simpljoin1.
  rewrite Heqe2 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe2.

  destruct (HR rr5) eqn:Heqe2; simpls; tryfalse.
  lets Hrr5 : H0.
  specialize (Hrr5 rr5).
  simpljoin1.
  rewrite Heqe2 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe2.

  destruct (HR rr6) eqn:Heqe2; simpls; tryfalse.
  lets Hrr6 : H0.
  specialize (Hrr6 rr6).
  simpljoin1.
  rewrite Heqe2 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe2.

  destruct (HR rr7) eqn:Heqe2; simpls; tryfalse.
  lets Hrr7 : H0.
  specialize (Hrr7 rr7).
  simpljoin1.
  rewrite Heqe2 in H2.
  inv H2.
  rewrite H1; clear H1 Heqe2.

  inv H; eauto.
Qed.

Lemma fetch_window_HL :
  forall HR (R : RegFile) fmo fml fmi,
    Hfetch HR = Some [fmo; fml; fmi] ->
    (forall (rr : GenReg), exists v, R rr = Some v /\ HR rr = Some v) ->
    fetch R = Some [fmo; fml; fmi].
Proof.
  intros.
  unfolds Hfetch.
  unfold fetch.
  destruct (fetch_frame HR r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe; tryfalse.
  eapply fetch_frame_HL with (R := R) in Heqe; eauto.
  rewrite Heqe; eauto.
  destruct (fetch_frame HR r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe1; tryfalse.
  eapply fetch_frame_HL with (R := R) in Heqe1; eauto.
  rewrite Heqe1; eauto.
  destruct (fetch_frame HR r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe2; tryfalse.
  eapply fetch_frame_HL with (R := R) in Heqe2; eauto.
  rewrite Heqe2; eauto.
Qed.
  
Lemma legal_com_ins_safety_property_relasrt :
  forall s s1 s1' s2 hs A w Pr C pc npc pc' npc',
    legal_com (C pc) ->
    LH__ C (s1, pc, npc) tau (s1', pc', npc') ->
    state_union s1 s2 s -> (s2, hs, A, w) ||= Pr ->
    exists s' s2', LH__ C (s, pc, npc) tau (s', pc', npc') /\ state_union s1' s2' s' /\
              (s2', hs, A, w) ||= Pr.
Proof.
  intros.
  destruct_state s1.
  destruct_state s2.
  simpls.
  simpljoin1.
  unfolds legal_com.
  inv H0; try solve
              [
                match goal with
                | H0 : C ?pc = Some _ |- _ => rewrite H0 in H; simpl in H; tryfalse
                end
              ].
  {
    (* i *)
    lets Hfrm : H12.
    eapply ins_frm_property in Hfrm; eauto.
    Focus 2.
    instantiate (2 := (m0, (r0, f0), d0)).
    simpl; repeat (split; eauto).
    simpljoin1.
    destruct_state s1'.
    destruct_state x0.
    simpls; simpljoin1.

    inv H12.
    {
      inv H5.
      {
        (* ld aexp ri *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Ld_step; eauto.
        eapply eval_addrexp_merge_still; eauto.
        eapply get_vl_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* st ri aexp *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply ST_step; eauto.
        eapply eval_addrexp_merge_still; eauto.
        eapply get_R_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_memset_merge_eq; eauto.
      }
      {
        (* nop *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Nop_step; eauto.
      }
      {
        (* add rs oexp rd *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Add_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* sub rs oexp rd *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Sub_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* subcc rs oexp rd *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Subcc_step; try eapply indom_merge_still; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        simpl. 
        erewrite indom_setR_merge_eq1; eauto.
        erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
        erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
        eauto.
        eauto.
        eauto.
      }
      {
        (* and *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply And_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* andcc *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Andcc_step; try eapply indom_merge_still; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        simpl.
        erewrite indom_setR_merge_eq1; eauto.
        erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
        erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
        eauto.
        eauto.
        eauto.
      }
      {
        (* or rs oexp rd *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Or_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* sll rs oexp rd *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Sll_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* srl rs oexp rd *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Srl_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply eval_opexp_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* sett v rd *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Set_step; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* rd rsp ri *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply Rd_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
      {
        (* getcwp ri *)
        eexists.
        exists (m2, (r2, f1), d1).
        split.
        Focus 2.
        repeat (split; eauto).
        eapply LNTrans; eauto.
        eapply NormalIns; eauto.
        eapply GetCwp_step; eauto.
        eapply get_R_merge_still; eauto.
        eapply indom_merge_still; eauto.
        rewrite indom_setR_merge_eq1; eauto.
      }
    }
    {
      (* save rs oexp rd *)
      eexists. 
      exists (m2, (r2, fml :: fmi :: F'), d1).
      split.
      Focus 2.
      repeat (split; eauto).
      eapply dlyfrmfree_changeFrm_stable_relasrt; eauto.
      clear - H3 H17.
      intro.  
      eapply indom_m2_disj_notin_m1 with (l := cwp) in H3; eauto.
      contradiction H3.
      unfold indom.
      unfolds get_R.
      destruct (r cwp) eqn:Heqe; eauto.
      eapply LNTrans; eauto.
      eapply SSave; try eapply get_R_merge_still; eauto.
      eapply fetch_disj_merge_still1; eauto.
      eapply indom_merge_still; eauto.
      eapply eval_opexp_merge_still; eauto.
      simpl. 
      rewrite <- indom_setR_merge_eq1; eauto.
      rewrite <- indom_setR_merge_eq1; eauto.
      erewrite fetch_some_set_win_merge_eq; eauto.
      eapply indom_setwin_still; eauto.
      unfold indom.
      clear - H17.
      unfolds get_R.
      destruct (r cwp); eauto.
      eapply indom_setR_still; eauto.
      eapply indom_setwin_still; eauto.
    }
    {
      (* restore rs oexp rd *)
      eexists. 
      exists (m2, (r2, F' ++ [fmo; fml]), d1).
      split.
      Focus 2.
      repeat (split; eauto).
      eapply dlyfrmfree_changeFrm_stable_relasrt; eauto.
      clear - H3 H17.
      intro.  
      eapply indom_m2_disj_notin_m1 with (l := cwp) in H3; eauto.
      contradiction H3.
      unfold indom.
      unfolds get_R.
      destruct (r cwp) eqn:Heqe; eauto.
      eapply LNTrans; eauto.
      eapply RRestore; try eapply get_R_merge_still; eauto.
      eapply fetch_disj_merge_still1; eauto.
      eapply indom_merge_still; eauto.
      eapply eval_opexp_merge_still; eauto.
      simpl.
      rewrite <- indom_setR_merge_eq1; eauto.
      rewrite <- indom_setR_merge_eq1; eauto. 
      erewrite fetch_some_set_win_merge_eq; eauto.
      eapply indom_setwin_still; eauto.
      unfold indom. 
      clear - H17.
      unfolds get_R.
      destruct (r cwp); eauto.
      eapply indom_setR_still; eauto.
      eapply indom_setwin_still; eauto.
    }
    {
      eexists.
      exists (m2, (r2, f1), set_delay rsp (set_spec_reg rsp v1 xor v2) d0).
      split.
      Focus 2.
      repeat (split; eauto).
      eapply dlyfrmfree_notin_changeDly_still_relasrt; eauto.
      clear - H3 H19.
      intro.
      eapply indom_m1_disj_notin_m2 in H3; eauto; tryfalse.
      eapply H3 in H; tryfalse.
      eauto.
      eapply LNTrans; eauto.
      eapply Wr; eauto.
      eapply get_R_merge_still; eauto.
      eapply eval_opexp_merge_still; eauto.
      eapply indom_merge_still; eauto.
    }
  }
  {
    (* jumpl aexp rd *)
    exists (m ⊎ m0, (set_R r rd (W pc) ⊎ r0, f0), d0) (m0, (r0, f0), d0).
    split.
    Focus 2.
    simpls.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.
    eapply LJumpl; eauto.
    eapply eval_addrexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setR_merge_eq1; eauto.
  }
  {
    (* call f *)
    exists (m ⊎ m0, (set_R r r15 (W pc) ⊎ r0, f0), d0) (m0, (r0, f0), d0).
    split.
    Focus 2.
    simpls.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.
    eapply LCall; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setR_merge_eq1; eauto.
  }
  {
    (* retl *)
    exists (m ⊎ m0, (r ⊎ r0, f0), d0) (m0, (r0, f0), d0).
    split.
    Focus 2.
    simpl.
    repeat (split; eauto).
    eapply LRetl; eauto.
    eapply get_R_merge_still; eauto.
  }
  {
    (* cbe f : true *)
    exists (m ⊎ m0, (r ⊎ r0, f0), d0) (m0, (r0, f0), d0).
    split.
    Focus 2.
    simpl.
    repeat (split; eauto).
    eapply LBe_true; eauto.
    eapply get_R_merge_still; eauto.
  }
  {
    (* cbe f : false *)
    exists (m ⊎ m0, (r ⊎ r0, f0), d0) (m0, (r0, f0), d0).
    split.
    Focus 2.
    simpl.
    repeat (split; eauto).
    eapply LBe_false; eauto.
    eapply get_R_merge_still; eauto.
  }
Qed.

Lemma legal_com_safety_property :
  forall s1 s1' s2 s Pr (C : XCodeHeap) pc npc pc' npc' hs A w,
    legal_com (C pc) -> state_union s1 s2 s ->
    LP__ (C, (s1, pc, npc)) tau (C, (s1', pc', npc')) -> (s2, hs, A, w) ||= Pr ->
    exists s' s2', LP__ (C, (s, pc, npc)) tau (C, (s', pc', npc')) /\ state_union s1' s2' s' /\
              (s2', hs, A, w) ||= Pr.
Proof.
  intros.
  inv H1.
  destruct_state s2.
  simpl in H0.
  simpljoin1.
  lets Hexe_delay : H8.
  eapply exe_delay_safety_property_relast in H8; eauto.
  simpljoin1.
  eapply legal_com_ins_safety_property_relasrt in H12; eauto.
  Focus 2.
  simpl.
  repeat (split; eauto).
  simpljoin1.
  do 2 eexists.
  repeat (split; eauto).
  destruct_state x0.
  eapply LCstep; eauto.
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
    eapply Hret in H19; eauto.
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
    curTRel (Mc, (LR, F)) (t, ((HR, b, HF), pc, npc)) ->
    wfIndex C (Mc ⊎ Mr ⊎ M, (LR, F), []) pc idx ->
    exists Mc' M' K' idx',
      LM' = Mc' ⊎ Mr ⊎ M' /\ Mc' ⊥ Mr /\ (Mc' ⊎ Mr) ⊥ M'
      /\
      (
        HP__ (C, PrimSet, (T, t, ((HR, b, HF), pc, npc), M)) tau (C, PrimSet, (T, t, K', M'))
        \/
        (K' = ((HR, b, HF), pc, npc) /\ M' = M /\ idx' ⩹ idx)
      )
      /\ wfCth idx' (C, Cas) (C ⊎ Cas, ((LM', (LR', F'), D'), pc', npc')) (C, PrimSet, (T, t, K', M')).
Proof.
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
  inv H4.
  inv H12.
  simpl in H9; symmetry in H9; inv H9. 
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
    clear - H18.
    eapply lemmas.disj_sym in H18.
    eapply lemmas_ins.disj_merge_disj_sep in H18.
    destruct H18.
    eapply lemmas.disj_sym; eauto.
  }

  assert ((Mc ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)) ⊥ M).
  { 
    rewrite <- H2; eauto.
  }

  rewrite H4 in H17.
  eapply LH__progress_HH_progress in H17; eauto.
  Focus 2.
  rewrite <- H2; eauto.

  destruct H17 as (Mc' & M'' & K' & idx' & HLM' & Hdisj1 & Hdisj2 & Hstep
                   & HwfCth); subst.
  exists T t K' M'' idx'.
  split.
  destruct Hstep as [Hstep | Hstep].
  {
    right.
    eexists.
    split.
    econstructor; eauto.
    eauto.
  }
  {
    left.
    simpljoin1.
    split; eauto.
  }

  split; eauto.
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
    destruct H13 as [H13 Hfp].
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
  {
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
          destruct H25 as [H25 Hfp].
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
            assert (length F' = 12).
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
                                         | (b', o') => if Z.eq_dec b b' then
                                                        if int_le ($ 0) o' && Int.lt o' sz then
                                                          Some (W ($ 2))
                                                        else
                                                          None
                                                        else None
                                         end) as m.
              exists b0 (((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M) ⊎ m).
            }
            do 2 eexists.
            econstructor; eauto.
            simpl; eauto.
            eapply LPsave_no_trap; eauto.
            eapply get_vl_merge_still; eauto. Print Mfresh.
          }
        }
        {
          (* Prestore *)  
          inv H15.
          inv H23.
          destruct H24 as [H24 Hfp].
          destruct H18 as [H18 Hdisj_ctx_k].
          destruct H2 as (n0 & F2 & H2). 
          simpljoin1.
          remember (F' ++ F2) as F.
          do 14 (destruct F as [ | ?fm F]; [simpls; tryfalse | idtac]); simpls; try omega.
          clear H19.
          inv H25. 
          simpljoin1.
          lets Hwim : (H18 Rwim).
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
            clear - H4 H26.
            unfolds get_R.
            rewrite H26 in H4; simpls; eauto.
            inv H4; eauto.
          }
          subst x3.
          
          destruct (win_masked (post_cwp x0) (($ 1) <<ᵢ n0)) eqn:Heqe.
          {
            assert (F' = nil).
            {
              clear - H15 Heqe H9 H5 H13.
              unfolds win_masked.
              destruct (((($ 1) <<ᵢ (post_cwp x0)) &ᵢ (($ 1) <<ᵢ n0)) !=ᵢ ($ 0)) eqn:Heqe'; tryfalse.
              unfolds post_cwp.
              assert ((x0 +ᵢ ($ 1)) modu N = n0).
              {
                eapply nth_bit_and; eauto.
                eapply int_inrange_0_7_add_one_still; eauto.
              }
              subst.
              rewrite fmlst_underflow_len_0 in H15; eauto.
              rewrite Int_unsigned_0 in H15; simpls.
              destruct F'; simpls; eauto; tryfalse.
            }
            subst F'.
            simpl in HeqF; subst F2.
            assert (b'0 = b').
            {
              inv H24; eauto.
            }
            subst b'0.
            assert (exists fm1, fetch_frame ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)
                                        (b', $ 0) 
                                        (b', $ 4) (b', $ 8) (b', $ 12) (b', $ 16)
                                        (b', $ 20) (b', $ 24) (b', $ 28) = Some fm1).
            {
              clear - H24 H11 H10 H8 Hdisj_ctx_k.
              inv H24.
              exists fm1. 
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable2; eauto.
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable1; eauto.
              eapply fetch_frame_set_Mframe_same1; eauto.
            }
            destruct H27 as [fm1' Hfetch_Mframe1].
            assert (exists fm2, fetch_frame ((((Mctx ⊎ Mk) ⊎ MT) ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM) ⊎ M)
                                       (b', $ 32) (b', $ 36) (b', $ 40) (b', $ 44)
                                       (b', $ 48) (b', $ 52) (b', $ 56) (b', $ 60) = Some fm2).
            {
              clear - H24 H11 H10 H8 Hdisj_ctx_k.
              inv H24.
              exists fm2. 
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable2; eauto.
              erewrite fetch_frame_disj_merge_stable1; eauto.
              erewrite fetch_frame_disj_merge_stable2; eauto.
              eapply fetch_frame_set_Mframe_same2; eauto.
            }
            destruct H27 as [fm2' Hfetch_Mframe2].
            
            do 2 eexists.
            econstructor; eauto.
            simpl; eauto.
            eapply LPrestore_trap.
            eapply get_vl_merge_still; eauto.
            instantiate (1 := x0).
            unfold get_R; rewrite H19; eauto.
            instantiate (1 := ($ 1) <<ᵢ n0).
            unfold get_R; rewrite H26; eauto.
            eauto.
            
            econstructor; eauto.
            unfold get_R; rewrite Hfp; eauto.
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
            unfold get_R; rewrite H26; eauto.
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
  }
  
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
