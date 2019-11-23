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
    fetch_frame (set_Mframe' b ($ 0) fm) (b, $ 0) (b, $ 4) (b, $ 8)
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
    fetch_frame (set_Mframe' b ($ 32) fm) (b, $ 32) (b, $ 36) (b, $ 40)
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
  inv H1.
  inv H2.
  eapply lex_ord_right; eauto.
  econstructor; eauto.
  eapply Nat.lt_trans; eauto.
  eapply lex_ord_right; eauto.
  econstructor; eauto.
  inv H2.
  eapply lex_ord_right; eauto.
  econstructor; eauto.
  eapply lex_ord_right; eauto.
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
    exists (Nat.succ (Nat.succ n), p).
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
    instantiate (1 := (Nat.succ (Nat.succ n), p)).
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
  exact (5%nat, (6%nat, 6%nat)).
  exact (5%nat, (6%nat, 6%nat)).
  exact (5%nat, (6%nat, 6%nat)).
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
              (Nat.eqb k 0 = true /\ exec_prim (A, HS) (A', HS') /\ (S2, HS', A', w) ||= Q
               /\ (0%nat, (0%nat, 0%nat)) ⩹ idx
              /\ (exists f', getregs S2 r15 = Some (W f') /\ pc2 = f' +ᵢ ($ 8) /\ npc2 = f' +ᵢ ($ 12))) \/
              (Nat.eqb k 0 = false /\ idx1 ⩹ idx2 /\ idx2 ⩹ idx /\ A' = A /\ HS = HS' /\
               rel_safety_aux (Nat.pred k) idx1 (C, S2, pc2, npc2) (A', HS') Q))
    ) ->
    rel_safety_aux k idx (C, S, pc, npc) (A, HS) Q.

Definition idx_sum (idx1 idx2 : Index) :=
  match idx1, idx2 with
  | (a1, (b1, c1)), (a2, (b2, c2)) => ((a1 + a2)%nat, ((b1 + b2)%nat, (c1 + c2)%nat))
  end.

Lemma idx_lt_sum_still :
  forall idx idx' idx'',
    idx ⩹ idx' -> idx ⩹ idx_sum idx' idx''.
Proof. 
  intros.
  destruct idx, idx', idx''.
  simpls.
  inv H.
  destruct p0, p1.
  destruct n1.
  econstructor; eauto.
  rewrite Nat.add_0_r; eauto.
  econstructor.
  eapply Nat.lt_trans; eauto.
  eapply Nat.lt_add_pos_r; eauto.
  omega. 
  destruct p0, p1.
  inv H1. 
  destruct n1.
  rewrite Nat.add_0_r; eauto.  
  eapply lex_ord_right.
  destruct n3.
  rewrite Nat.add_0_r; eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply Nat.lt_trans; eauto.
  eapply Nat.lt_add_pos_r; eauto.
  omega.
  econstructor.
  eapply Nat.lt_add_pos_r; eauto.
  omega.
  destruct n1.
  rewrite Nat.add_0_r; eauto.
  eapply lex_ord_right.
  destruct n3.
  rewrite Nat.add_0_r; eauto.
  eapply lex_ord_right.
  destruct n4; simpls.
  rewrite Nat.add_0_r; eauto.
  unfolds Nat.lt; omega.
  econstructor; eauto.
  unfold Nat.lt; omega.
  econstructor.
  unfold Nat.lt; omega.
Qed.

Lemma idx_sum_pre_lt :
  forall idx1 idx2 idx',
    idx1 ⩹ idx2 ->
    idx_sum idx1 idx' ⩹ idx_sum idx2 idx'.
Proof.
  intros.
  destruct idx1, idx2, idx'.
  destruct p, p0, p1.
  simpls.
  destruct n1.
  repeat (rewrite Nat.add_0_r; eauto).
  destruct n6.
  repeat (rewrite Nat.add_0_r; eauto).
  destruct n7.
  repeat (rewrite Nat.add_0_r; eauto).
  
  unfolds LtIndex.
  inv H.
  {
    econstructor; eauto.
  }
  inv H1.
  eapply lex_ord_right.
  econstructor; eauto.
  do 2 eapply lex_ord_right.
  unfolds Nat.lt; omega.

  inv H.
  econstructor; eauto.
  inv H1.
  eapply lex_ord_right.
  econstructor.
  unfolds Nat.lt; omega.

  do 2 eapply lex_ord_right.
  unfolds Nat.lt; omega.

  inv H.
  econstructor; eauto.
  unfolds Nat.lt; omega.
  inv H1.
  eapply lex_ord_right.
  econstructor; eauto.
  unfolds Nat.lt; omega.
  do 2 eapply lex_ord_right.
  unfolds Nat.lt; omega.
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
