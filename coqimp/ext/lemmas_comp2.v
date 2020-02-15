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
Require Import lemmas_comp.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(** Auxiliary Lemmas about list *)
Lemma list_get_tail_two :
  forall A (l : list A),
    (length l >= 2) % nat -> exists a b l', l = l' ++ [a; b].
Proof.
  induction l; intros; simpls; try omega.
  destruct l; simpls; try omega.
  destruct l; simpls; eauto.
  exists a a0 (@nil A); simpl; eauto.
  assert ((S (S (length l)) >= 2)%nat).
  destruct l; omega.
  eapply IHl in H0; eauto.
  simpljoin1.
  exists x x0 (a :: x1).
  simpl.
  rewrite H0; eauto.
Qed.

Lemma list_tail_two :
  forall A (l1 l2 : list A) a1 b1 a2 b2,
    l1 ++ [a1; b1] = l2 ++ [a2; b2] ->
    l1 = l2 /\ a1 = a2 /\ b1 = b2.
Proof.
  induction l1; intros; simpls.
  destruct l2; simpls; tryfalse.
  inv H; eauto.
  destruct l2; simpls; tryfalse.
  destruct l2; simpls; tryfalse.
  destruct l2; simpls; tryfalse.
  assert (length (a :: l1 ++ [a1; b1]) = length [a2; b2]).
  rewrite H; eauto.
  simpls.
  rewrite app_length in H0; simpls.
  inv H0.
  omega.
  inv H.
  eapply IHl1 in H2; eauto; simpljoin1.
  split; eauto.
Qed.

(** Auxiliary Lemmas about Integer *)
Lemma Int_unsigned_64 :
  Int.unsigned $ 64 = 64%Z.
Proof.
  eapply Int.unsigned_repr_eq; eauto.
Qed.

Lemma int_ltu_trans :
  forall n m p,
    n <ᵤᵢ m -> m <ᵤᵢ p -> n <ᵤᵢ p.
Proof.
  intros.
  destruct n, m, p.
  unfolds Int.ltu; simpls.
  destruct (zlt intval intval0); destruct (zlt intval0 intval1); simpls; tryfalse.
  destruct (zlt intval intval1); eauto; try omega.
Qed.

Lemma int_leu_trans :
  forall n m p,
    n <=ᵤᵢ m -> m <=ᵤᵢ p -> n <=ᵤᵢ p.
Proof.
  intros.
  destruct n, m, p.
  unfolds int_leu, Int.ltu, Int.eq; simpls.
  destruct (zlt intval intval0); destruct (zeq intval intval0);
    destruct (zlt intval0 intval1); destruct (zeq intval0 intval1); simpls; tryfalse; try omega.
  destruct (zlt intval intval1); eauto; try omega.
  destruct (zlt intval intval1); eauto; try omega.
  destruct (zlt intval intval1); eauto; try omega.
  destruct (zlt intval intval1); eauto; try omega.
  simpl; eauto.
  destruct (zeq intval intval1); eauto; try omega.
Qed.

Lemma not_lt_impl_ge :
  forall a b,
    Int.ltu a b = false -> int_leu b a = true.
Proof.
  intros.
  destruct a, b.
  unfolds int_leu; simpls.
  unfolds Int.ltu; simpls.
  unfolds Int.eq; simpls.
  destruct (zlt intval intval0); simpls; tryfalse.
  destruct (zlt intval0 intval); destruct (zeq intval0 intval); tryfalse; try omega; eauto.
Qed.

Lemma lt_impl_not_ge :
  forall a b,
    Int.ltu a b = true -> int_leu b a = false.
Proof.
  intros.
  destruct a, b.
  unfolds int_leu; simpls.
  unfolds Int.ltu; simpls.
  unfolds Int.eq; simpls.
  destruct (zlt intval intval0); simpls; tryfalse.
  destruct (zlt intval0 intval); destruct (zeq intval0 intval); tryfalse; try omega; eauto.
Qed.

Ltac auto_solve :=
    match goal with
    | H : ?A \/ ?B |- _ => destruct H; subst; tryfalse; eauto; try omega; auto_solve
    | _ => subst; eauto
    end.

Lemma shr_same_bit_eq :
  forall x y,
    $ 0 <=ᵤᵢ x <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ y <=ᵤᵢ $ 7 ->
    Some (W ($ 1) <<ᵢ x) = Some (W ($ 1) <<ᵢ y) ->
    x = y.
Proof.
  intros.
  inv H1.
  destruct (($ 1) <<ᵢ x) eqn:Heqe1; destruct (($ 1) <<ᵢ y) eqn:Heqe2.
  inv H3.
  assert (Int.eq ($ 1) <<ᵢ x ($ 1) <<ᵢ y = true).
  rewrite Heqe1, Heqe2; simpls.
  unfold Int.eq; simpls.
  destruct (zeq intval0 intval0); eauto.
  clear Heqe1 Heqe2.

  eapply int_eq_true_eq in H1.
  assert ((($ 1) <<ᵢ x) &ᵢ (($ 1) <<ᵢ y) !=ᵢ ($ 0) = true).
  {
    rewrite H1.
    clear - H0.
    rewrite Int.and_idem.
    eapply in_range_0_7_num in H0.
    unfolds int_leu, Int.shl, Int.and, Int.ltu, Int.eq; simpls.

    destruct H0; subst.
    do 5 (try rewrite Int_unsigned_1, Int_unsigned_0; simpl).
    rewrite Int_unsigned_1; simpl; eauto.
  
    destruct H; subst.
    do 5 (try rewrite Int_unsigned_1, Int_unsigned_0; simpl).
    rewrite Int_unsigned_2; simpl; eauto.

    destruct H; subst.
    do 5 (try rewrite Int_unsigned_1, Int_unsigned_2, Int_unsigned_0; simpl).
    rewrite Int_unsigned_4; simpl; eauto.

    destruct H; subst.
    do 5 (try rewrite Int_unsigned_1, Int_unsigned_3, Int_unsigned_0; simpl).
    rewrite Int_unsigned_8; simpl; eauto.

    destruct H; subst.
    do 5 (try rewrite Int_unsigned_1, Int_unsigned_4, Int_unsigned_0; simpl).
    rewrite Int.unsigned_repr; eauto.
    unfold Int.max_unsigned; simpl; omega.

    destruct H; subst.
    do 5 (try rewrite Int_unsigned_1, Int_unsigned_5, Int_unsigned_0; simpl).
    rewrite Int.unsigned_repr; eauto.
    unfold Int.max_unsigned; simpl; omega.

    destruct H; subst.
    do 5 (try rewrite Int_unsigned_1, Int_unsigned_6, Int_unsigned_0; simpl).
    rewrite Int.unsigned_repr; eauto.
    unfold Int.max_unsigned; simpl; omega.

    do 5 (try rewrite Int_unsigned_1, Int_unsigned_7, Int_unsigned_0; simpl).
    rewrite Int.unsigned_repr; eauto.
    unfold Int.max_unsigned; simpl; omega.
  }

  eapply nth_bit_and; eauto.
Qed.

Lemma caculate_5 :
  forall x,
    $ 0 <=ᵤᵢ x <=ᵤᵢ $ 7 ->
    (((N +ᵢ ((((((x +ᵢ N) -ᵢ ($ 1)) modu N) +ᵢ N) -ᵢ ($ 1)) modu N)) -ᵢ x) -ᵢ ($ 1)) modu N = $ 5.
Proof.
  intros.
  unfold Int.add, N, Int.sub, Int.modu.
  rewrite Int_unsigned_8, Int_unsigned_1.
  eapply in_range_0_7_num in H.
  repeat (destruct H; subst; eauto).
Qed.

Lemma not_overflow :
  forall x x0,
    $ 0 <=ᵤᵢ x <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ x0 <=ᵤᵢ $ 7 -> pre_cwp x <> x0 -> x <> x0 ->
    $ 0 <=ᵤᵢ (((N +ᵢ x0) -ᵢ x) -ᵢ ($ 1)) modu N <=ᵤᵢ $ 5.
Proof.
  intros.
  unfolds pre_cwp, N.
  eapply in_range_0_7_num in H.

  repeat (destruct H; subst; [eapply in_range_0_7_num in H0; subst; auto_solve | idtac]).
  eapply in_range_0_7_num in H0; subst; auto_solve.
Qed.

Lemma valid_frame_list_length :
  forall x,
    $ 0 <=ᵤᵢ x <=ᵤᵢ $ 5 ->
    (0 <= 2 * Z.to_nat (Int.unsigned x) <= 10)%nat.
Proof.
  intros.
  eapply in_range_0_5_num in H; eauto.
  destruct H; subst.
  rewrite Int_unsigned_0; simpl; omega.
  destruct H; subst.
  rewrite Int_unsigned_1; simpl; omega.
  destruct H; subst.
  rewrite Int_unsigned_2; simpl; omega.
  destruct H; subst.
  rewrite Int_unsigned_3; simpl; omega.
  destruct H; subst.
  rewrite Int_unsigned_4; simpl; omega.
  rewrite Int_unsigned_5; simpl; omega.
Qed.

Lemma valid_rotate_add_1 :
  forall x x0,
    $ 0 <=ᵤᵢ x <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ x0 <=ᵤᵢ $ 7 -> pre_cwp x <> x0 -> x <> x0 ->
    (2 + 2 * Z.to_nat (Int.unsigned (((N +ᵢ x0) -ᵢ x) -ᵢ ($ 1)) modu N))%nat =
    (2 * Z.to_nat (Int.unsigned (((N +ᵢ x0) -ᵢ (pre_cwp x)) -ᵢ ($ 1)) modu N))%nat.
Proof.
  intros.
  eapply in_range_0_7_num in H.
  repeat (destruct H; subst; [eapply in_range_0_7_num in H0; subst; auto_solve | idtac]).
  eapply in_range_0_7_num in H0; subst; auto_solve.
Qed.

Lemma valid_rotate_sub_1 :
  forall x0 x,
    $ 0 <=ᵤᵢ x <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ x0 <=ᵤᵢ $ 7 -> x <> x0 -> post_cwp x <> x0 ->
    (2 * Z.to_nat (Int.unsigned (((N +ᵢ x0) -ᵢ x) -ᵢ ($ 1)) modu N) - 2)%nat =
    (2 * Z.to_nat (Int.unsigned (((N +ᵢ x0) -ᵢ ((x +ᵢ ($ 1)) modu N)) -ᵢ ($ 1)) modu N))%nat.
Proof.
  intros. 
  eapply in_range_0_7_num in H.
  unfolds post_cwp.
  repeat (destruct H; subst; [eapply in_range_0_7_num in H0; subst; auto_solve | idtac]);
    try solve [contradiction H2; eauto].
  eapply in_range_0_7_num in H0; subst; auto_solve.
  contradiction H2; eauto.
Qed.

Lemma post_valid_head_two :
  forall x x0,
    $ 0 <=ᵤᵢ x <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ x0 <=ᵤᵢ $ 7 -> x <> x0 ->
    ((x +ᵢ ($ 1)) modu N) <> x0 ->
    $ 1 <=ᵤᵢ (((N +ᵢ x0) -ᵢ x) -ᵢ ($ 1)) modu N <=ᵤᵢ $ 6.
Proof.
  intros.
  unfold N.
  eapply in_range_0_7_num in H.
  repeat (destruct H; subst; [eapply in_range_0_7_num in H0; subst; auto_solve | idtac]).
  eapply in_range_0_7_num in H0; subst; auto_solve.
Qed.

Lemma range_split :
  forall a b c i,
    a <=ᵤᵢ i <ᵤᵢ b -> a <=ᵤᵢ c <ᵤᵢ b ->
    a <=ᵤᵢ i <ᵤᵢ c \/ c <=ᵤᵢ i <ᵤᵢ b.
Proof.
  intros.
  destruct a, b, i, c.
  unfolds int_leu, Int.ltu, Int.eq; simpls.
  destruct (zlt intval intval1); destruct (zeq intval intval1); destruct (zlt intval1 intval0);
    destruct (zlt intval intval2); destruct (zeq intval intval2); destruct (zlt intval2 intval0);
      destruct (zlt intval1 intval2); try destruct (zlt intval2 intval1); destruct (zeq intval2 intval1);
        eauto; try omega; simpls; tryfalse.
Qed.

Lemma legal_frame_range0 :
  forall v,
    $ 0 <=ᵤᵢ v <ᵤᵢ $ 32 -> Int.eq (v modu $ 4) ($ 0) = true ->
    v = ($ 0) \/ v = ($ 4) \/ v = ($ 8) \/ v = ($ 12) \/
    v = ($ 16) \/ v = ($ 20) \/ v = ($ 24) \/ v = ($ 28).
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := v).
  unfolds int_leu.
  unfolds Int.ltu, Int.eq, Int.modu.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 32 = 32%Z); eauto. 
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite Int_unsigned_4 in *.
  destruct v.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 32); subst; eauto; tryfalse; try omega.
  destruct intval; tryfalse; eauto 20.
  do 8 (try destruct p; eauto 10; tryfalse).
Qed.

Lemma legal_frame_range32 :
  forall v,
    $ 32 <=ᵤᵢ v <ᵤᵢ $ 64 -> Int.eq (v modu $ 4) ($ 0) = true ->
    v = ($ 32) \/ v = ($ 36) \/ v = ($ 40) \/ v = ($ 44) \/
    v = ($ 48) \/ v = ($ 52) \/ v = ($ 56) \/ v = ($ 60).
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := v).
  unfolds int_leu.
  unfolds Int.ltu, Int.eq, Int.modu.
  assert (Int.unsigned $ 32 = 32%Z); eauto.
  assert (Int.unsigned $ 64 = 64%Z); eauto. 
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite Int_unsigned_4, Int_unsigned_0 in *.
  destruct v.
  simpl Int.unsigned in *.
  destruct (zlt 32 intval); destruct (zeq 32 intval);
    destruct (zlt intval 64); subst; eauto; tryfalse; try omega.
  destruct intval; tryfalse; eauto 20.
  do 8 (try destruct p; eauto 10; tryfalse).
Qed.

Lemma range_1_6_lenF_ge_2 :
  forall x,
    $ 1 <=ᵤᵢ x <=ᵤᵢ $ 6 -> (2 <= 2 * Z.to_nat (Int.unsigned x) <= 12)%nat.
Proof.
  intros.
  destruct x; simpls.
  unfolds int_leu, Int.ltu, Int.eq; simpls.
  rewrite Int_unsigned_1, Int_unsigned_6 in *.
  destruct (zlt 1 intval); destruct (zeq 1 intval);
    destruct (zlt intval 6); destruct (zeq intval 6); eauto; simpls; try omega; tryfalse.
  destruct intval; simpl; try omega; tryfalse.
  repeat (destruct p; simpls; try omega; tryfalse; eauto).
  subst; simpl; omega.
  subst; simpl; omega.
Qed.

(** Auxiliary Lemmas about Memory *)
Lemma merge_none_sep_none :
  forall A B (M m : A -> option B) l,
    (M ⊎ m) l = None -> M l = None /\ m l = None.
Proof.
  intros.
  unfold merge in *.
  destruct (M l) eqn:Heqe; subst; tryfalse.
  split; eauto.
Qed.

(** Auxiliary Lemmas about windows *)
Lemma indom_memset_still :
  forall l l0 v0 (M : Memory),
    indom l M -> indom l (MemMap.set l0 (Some v0) M).
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  destruct (Address_eq l0 l); subst; eauto.
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gso; eauto.
Qed.

Lemma indom_merge_elim :
  forall A B (M m : A -> option B) l,
    indom l M -> (M ⊎ m) l = M l.
Proof.
  intros.
  unfold merge.
  unfold indom in *.
  simpljoin1.
  rewrite H; eauto.
Qed.

Lemma indom_merge_indom_oneof :
  forall A B (M m : A -> option B) l,
    indom l (M ⊎ m) -> indom l M \/ indom l m.
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  unfold merge in *.
  destruct (M l); eauto.
Qed.

Lemma indom_merge_indom_one_of :
  forall A B (M m : A -> option B) l v,
    (M ⊎ m) l = Some v -> M ⊥ m ->
    M l = Some v \/ m l = Some v.
Proof.
  intros.
  unfold disjoint, merge in *.
  destruct (M l) eqn:Heqe; tryfalse.
  inv H.
  eauto.
  specialize (H0 l).
  rewrite Heqe in H0.
  eauto.
Qed.

Lemma get_R_set_same_stable :
  forall rn R v v1,
    get_R R rn = Some v -> rn <> r0 -> get_R (set_R R rn v1) rn = Some v1.
Proof.
  intros.
  unfolds get_R.
  destruct (R rn) eqn:Heqe; tryfalse.
  unfold set_R.
  unfold is_indom.
  rewrite Heqe.
  rewrite RegMap.gss; eauto.
  destruct rn; simpls; tryfalse; eauto.
  destruct g; simpls; tryfalse; eauto.
Qed.

Lemma fetch_frame_merge_elim :
  forall A (M m : A -> option Val) l0 l1 l2 l3 l4 l5 l6 l7,
    indoms [l0; l1; l2; l3; l4; l5; l6; l7] M ->
    fetch_frame (M ⊎ m) l0 l1 l2 l3 l4 l5 l6 l7 = fetch_frame M l0 l1 l2 l3 l4 l5 l6 l7.
Proof.
  intros.
  unfold fetch_frame.
  simpls.
  simpljoin1.
  repeat (rewrite indom_merge_elim; eauto).
Qed.

Lemma fetch_frame_LH :
  forall HR (R : RegFile) (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) fm,
    fetch_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    (forall (rr : GenReg), exists v, R rr = Some v /\ HR rr = Some v) ->
    fetch_frame HR rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfold fetch_frame in *.
  
  destruct (R rr0) eqn:Heqe0; simpls; tryfalse.
  lets Hrr0 : H0.
  specialize (Hrr0 rr0).
  simpljoin1.
  rewrite Heqe0 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe0.

  destruct (R rr1) eqn:Heqe1; simpls; tryfalse.
  lets Hrr1 : H0.
  specialize (Hrr1 rr1).
  simpljoin1.
  rewrite Heqe1 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe1.

  destruct (R rr2) eqn:Heqe2; simpls; tryfalse.
  lets Hrr2 : H0.
  specialize (Hrr2 rr2).
  simpljoin1.
  rewrite Heqe2 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe2.

  destruct (R rr3) eqn:Heqe2; simpls; tryfalse.
  lets Hrr3 : H0.
  specialize (Hrr3 rr3).
  simpljoin1.
  rewrite Heqe2 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe2.

  destruct (R rr4) eqn:Heqe2; simpls; tryfalse.
  lets Hrr4 : H0.
  specialize (Hrr4 rr4).
  simpljoin1.
  rewrite Heqe2 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe2.

  destruct (R rr5) eqn:Heqe2; simpls; tryfalse.
  lets Hrr5 : H0.
  specialize (Hrr5 rr5).
  simpljoin1.
  rewrite Heqe2 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe2.

  destruct (R rr6) eqn:Heqe2; simpls; tryfalse.
  lets Hrr6 : H0.
  specialize (Hrr6 rr6).
  simpljoin1.
  rewrite Heqe2 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe2.

  destruct (R rr7) eqn:Heqe2; simpls; tryfalse.
  lets Hrr7 : H0.
  specialize (Hrr7 rr7).
  simpljoin1.
  rewrite Heqe2 in H1.
  inv H1.
  rewrite H2; clear H2 Heqe2.

  inv H; eauto.
Qed.

Lemma fetch_window_LH :
  forall HR R fmo fml fmi,
    fetch R = Some [fmo; fml; fmi] ->
    (forall rr : GenReg, exists v : Val, R rr = Some v /\ HR rr = Some v) ->
    Hfetch HR = Some [fmo; fml; fmi].
Proof.
  intros.
  unfolds fetch, Hfetch.
  destruct (fetch_frame R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe; tryfalse.
  eapply fetch_frame_LH with (HR := HR) in Heqe; eauto.
  rewrite Heqe; eauto.
  destruct (fetch_frame R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe1; tryfalse.
  eapply fetch_frame_LH with (HR := HR) in Heqe1; eauto.
  rewrite Heqe1; eauto.
  destruct (fetch_frame R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe2; tryfalse.
  eapply fetch_frame_LH with (HR := HR) in Heqe2; eauto.
  rewrite Heqe2; eauto.
Qed.

Lemma indom_memset_merge_eq2:
  forall (A : Type) (M m : AddrEq.t -> option A) (l : AddrEq.t) (v : A),
    indom l m -> M ⊥ m ->
    MemMap.set l (Some v) (M ⊎ m) = M ⊎ MemMap.set l (Some v) m.
Proof.
  intros.
  unfold merge.
  eapply FunctionalExtensionality.functional_extensionality; intros.
  destruct (Address_eq l x); subst; eauto.
  rewrite MemMap.gss; eauto.
  destruct (M x) eqn:Heqe; eauto.
  unfold disjoint in *.
  specialize (H0 x).
  unfold indom in *.
  simpljoin1.
  rewrite Heqe, H in H0; tryfalse.
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gso; eauto.
  destruct (M x) eqn:Heqe; eauto.
  rewrite MemMap.gso; eauto.
Qed.

Fixpoint getMs (vl : list (Address * Val)) :=
  match vl with
  | nil => nil
  | (l, w) :: vl' => l :: getMs vl'
  end.

Lemma indoms_setM_still :
  forall vl (M : Memory) a v, 
    indoms (getMs vl) M ->
    indoms (getMs vl) (MemMap.set a (Some v) M).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpls.
    eauto.
  -
    destruct a.
    simpls.
    simpljoin1.
    split.
    clear - H.
    unfold indom in *.
    simpljoin1.
    destruct (Address_eq a0 a); subst; eauto.
    rewrite MemMap.gss; eauto.
    rewrite MemMap.gso; eauto.
    eapply IHvl; eauto.
Qed.

Lemma indoms_setMs_merge_eq :
  forall vl M m,
    indoms (getMs vl) M ->
    set_Ms (merge M m) vl = merge (set_Ms M vl) m.
Proof.
  intros vl.
  induction vl; intros.
  -
    simpls.
    eauto.
  -
    destruct a.
    simpl in H.
    simpl. 
    simpljoin1.
    rewrite indom_memset_merge_eq; eauto.
    eapply IHvl.
    eapply indoms_setM_still; eauto.
Qed.

Lemma indoms_setMs_merge_eq2 :
  forall vl M m,
    indoms (getMs vl) m -> M ⊥ m ->
    set_Ms (merge M m) vl = merge M (set_Ms m vl).
Proof.
  intros vl.
  induction vl; intros.
  -
    simpls.
    eauto.
  -
    destruct a.
    simpl in H.
    simpl. 
    simpljoin1.
    rewrite indom_memset_merge_eq2; eauto.
    eapply IHvl.
    eapply indoms_setM_still; eauto.
    eapply disj_sym.
    eapply disj_indom_memset_still; eauto.
    eapply disj_sym; eauto.
Qed.

Lemma fetch_some_set_Mframe_still :
  forall (M m : Memory) fm l0 l1 l2 l3 l4 l5 l6 l7,
    indoms [l0; l1; l2; l3; l4; l5; l6; l7] M ->
    set_Mframe (M ⊎ m) l0 l1 l2 l3 l4 l5 l6 l7 fm =
    set_Mframe M l0 l1 l2 l3 l4 l5 l6 l7 fm ⊎ m.
Proof.
  intros.
  unfolds set_Mframe.
  destruct fm.
  eapply indoms_setMs_merge_eq; eauto.
Qed.

Lemma fetch_some_set_Mframe_still2 :
  forall (M m : Memory) fm l0 l1 l2 l3 l4 l5 l6 l7,
    M ⊥ m -> indoms [l0; l1; l2; l3; l4; l5; l6; l7] m ->
    set_Mframe (M ⊎ m) l0 l1 l2 l3 l4 l5 l6 l7 fm =
    M ⊎ set_Mframe m l0 l1 l2 l3 l4 l5 l6 l7 fm.
Proof.
  intros.
  unfolds set_Mframe.
  destruct fm.
  eapply indoms_setMs_merge_eq2; eauto.
Qed.

Lemma disjoint_setMfrm_still :
  forall M m l0 l1 l2 l3 l4 l5 l6 l7 fm,
    indoms [l0; l1; l2; l3; l4; l5; l6; l7] M -> M ⊥ m ->
    set_Mframe M l0 l1 l2 l3 l4 l5 l6 l7 fm ⊥ m.
Proof.
  intros.
  unfold set_Mframe.
  destruct fm; simpls.
  simpljoin1.
  do 8 (try eapply disj_indom_memset_still; eauto).

  eapply indom_memset_still; eauto.
  repeat (eapply indom_memset_still; eauto).
  repeat (eapply indom_memset_still; eauto).
  repeat (eapply indom_memset_still; eauto).
  repeat (eapply indom_memset_still; eauto).
  repeat (eapply indom_memset_still; eauto).
  repeat (eapply indom_memset_still; eauto).
Qed.

Lemma indom_setMframe_still :
  forall a M l0 l1 l2 l3 l4 l5 l6 l7 fm,
    indom a M -> indom a (set_Mframe M l0 l1 l2 l3 l4 l5 l6 l7 fm).
Proof.
  intros.
  unfold set_Mframe.
  destruct fm; simpl.
  repeat (eapply indom_memset_still; eauto).
Qed.

Lemma indoms_setMframe_still :
  forall vl M l0 l1 l2 l3 l4 l5 l6 l7 fm,
    indoms vl M ->
    indoms vl (set_Mframe M l0 l1 l2 l3 l4 l5 l6 l7 fm).
Proof.
  induction vl; intros; simpls; eauto.
  simpljoin1.
  split.
  eapply indom_setMframe_still; eauto.
  eapply IHvl; eauto.
Qed.

Lemma indoms_merge_right :
  forall A B vl (M m : A -> option B),
    indoms vl m ->
    indoms vl (M ⊎ m).
Proof.
  induction vl; simpls; eauto; intros.
  simpljoin1.
  split.
  eapply indom_merge_still2; eauto.
  eapply IHvl; eauto.
Qed.

Lemma indoms_merge_left :
  forall A B vl (M m : A -> option B),
    indoms vl M ->
    indoms vl (M ⊎ m).
Proof.
  induction vl; simpls; eauto; intros.
  simpljoin1.
  split.
  eapply indom_merge_still; eauto.
  eapply IHvl; eauto.
Qed.

Lemma indoms_set_Mframe'_0 :
  forall b fm,
    indoms [(b, $ 0); (b, $ 4); (b, $ 8); (b, $ 12);
              (b, $ 16); (b, $ 20); (b, $ 24); (b, $ 28)] (set_Mframe' b $ 0 fm).
Proof.
  intros.
  simpls.
  unfold set_Mframe'; destruct fm; simpls.
  split.
  {
    do 7 eapply indom_memset_still.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 6 eapply indom_memset_still.
    assert (($ 0) +ᵢ ($ 4) = $ 4); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 5 eapply indom_memset_still.
    assert (($ 0) +ᵢ ($ 8) = $ 8); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 4 eapply indom_memset_still.
    assert (($ 0) +ᵢ ($ 12) = $ 12); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 3 eapply indom_memset_still.
    assert (($ 0) +ᵢ ($ 16) = $ 16); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 2 eapply indom_memset_still.
    assert (($ 0) +ᵢ ($ 20) = $ 20); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    eapply indom_memset_still.
    assert (($ 0) +ᵢ ($ 24) = $ 24); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    assert (($ 0) +ᵢ ($ 28) = $ 28); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  eauto.
Qed.

Lemma indoms_set_Mframe'_32 :
  forall b fm,
    indoms [(b, $ 32); (b, $ 36); (b, $ 40); (b, $ 44);
              (b, $ 48); (b, $ 52); (b, $ 56); (b, $ 60)] (set_Mframe' b $ 32 fm).
Proof.
  intros.
  simpls.
  unfold set_Mframe'; destruct fm; simpls.
  split.
  {
    do 7 eapply indom_memset_still.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 6 eapply indom_memset_still.
    assert (($ 32) +ᵢ ($ 4) = $ 36); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 5 eapply indom_memset_still.
    assert (($ 32) +ᵢ ($ 8) = $ 40); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 4 eapply indom_memset_still.
    assert (($ 32) +ᵢ ($ 12) = $ 44); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 3 eapply indom_memset_still.
    assert (($ 32) +ᵢ ($ 16) = $ 48); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    do 2 eapply indom_memset_still.
    assert (($ 32) +ᵢ ($ 20) = $ 52); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    eapply indom_memset_still.
    assert (($ 32) +ᵢ ($ 24) = $ 56); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  split.
  {
    assert (($ 32) +ᵢ ($ 28) = $ 60); eauto.
    rewrite H.
    eapply memset_l_l_indom; eauto.
  }
  eauto.
Qed.
  
(** Auxiliary Lemmas about Rinj *)
Lemma MemMap_set_neq_reorder :
  forall l1 l2 (v1 v2 : Val) M,
    l1 <> l2 ->
    MemMap.set l1 (Some v1) (MemMap.set l2 (Some v2) M) =
    MemMap.set l2 (Some v2) (MemMap.set l1 (Some v1) M).
Proof.
  intros.
  eapply FunctionalExtensionality.functional_extensionality; eauto.
  intros.
  destruct (Address_eq l1 x); subst.
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gso; eauto.
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gso; eauto.
  destruct (Address_eq l2 x); subst.
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gss; eauto.
  rewrite MemMap.gso; eauto.
  rewrite MemMap.gso; eauto.
  rewrite MemMap.gso; eauto.
Qed.

Lemma Rinj_GenReg_LH' :
  forall (HR : HRegFile) (R : RegFile) (rr : GenReg) (v : Val),
    Rinj R HR -> R rr = Some v -> HR rr = Some v.
Proof.
  intros.
  inv H.
  specialize (H1 rr).
  simpljoin1.
  rewrite H0 in H; inv H.
  eauto.
Qed.

Lemma Rinj_GenReg_LH :
  forall (HR : HRegFile) (R : RegFile) (rr : GenReg) (v : Val),
    Rinj R HR -> get_R R rr = Some v -> get_HR HR rr = Some v.
Proof.
  intros.
  unfolds get_R.
  unfold get_HR.
  destruct (R rr) eqn:Heqe; tryfalse.
  eapply Rinj_GenReg_LH' in Heqe; eauto.
  rewrite Heqe.
  destruct rr; simpls; eauto.
Qed.

Lemma Rinj_eval_impl_Heval_opexp :
  forall (HR : HRegFile) (R : RegFile) (oexp : OpExp) (v : Val),
    Rinj R HR -> eval_opexp R oexp = Some v -> Heval_opexp HR oexp = Some v.
Proof.
  intros.
  unfolds eval_opexp.
  unfold Heval_opexp.
  destruct oexp.
  eapply Rinj_GenReg_LH; eauto.
  destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
Qed.

Lemma Rinj_eval_impl_Heval_addrexp :
  forall (HR : HRegFile) (R : RegFile) (aexp : AddrExp) (v : Val),
    Rinj R HR -> eval_addrexp R aexp = Some v -> Heval_addrexp HR aexp = Some v.
Proof.
  intros.
  unfolds eval_addrexp.
  unfold Heval_addrexp.
  destruct aexp.
  eapply Rinj_eval_impl_Heval_opexp; eauto.
  destruct (get_R R g) eqn:Heqe; tryfalse.
  eapply Rinj_GenReg_LH in Heqe; eauto.
  rewrite Heqe; eauto.
  destruct (eval_opexp R o) eqn:Heqe1; tryfalse.
  eapply Rinj_eval_impl_Heval_opexp in Heqe1; eauto.
  rewrite Heqe1; eauto.
Qed.

Lemma Rinj_indom_GenReg_LH:
  forall (HR : HRegFile) (R : RegFile) (rd : GenReg),
    Rinj R HR -> indom rd R -> indom rd HR.
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  inv H.
  simpljoin1; eauto.
  specialize (H1 rd); simpljoin1; eauto.
Qed.

Lemma Rinj_set_sameLH_stable :
  forall R HR (rd : GenReg) v,
    Rinj R HR -> Rinj (set_R R rd v) (set_HR HR rd v).
Proof.
  intros.
  inv H.
  econstructor; eauto.
  intros.
  lets Ht1 : H0 rd.
  lets Ht2 : H0 rr.
  simpljoin1.
  unfold set_R.
  unfold set_HR.
  unfold is_indom.
  destruct (RegName_eq rr rd); destruct (HRegName_eq rr rd).
  {
    inv e.
    exists v.
    rewrite H, H3.
    rewrite RegMap.gss.
    rewrite HRegMap.gss.
    eauto.
  }
  {
    inv e; tryfalse.
  }
  {
    inv e; tryfalse.
  }
  {
    rewrite H2, H4.
    rewrite RegMap.gso; eauto.
    rewrite HRegMap.gso; eauto.
  }
  simpljoin1.
  split.
  intros.
  specialize (H sr).
  simpljoin1.
  exists x2.
  unfold set_R.
  unfold is_indom.
  specialize (H0 rd).
  simpljoin1.
  rewrite H0; eauto.
  rewrite RegMap.gso; eauto.
  intro; tryfalse.
  split.
  unfold set_R.
  unfold is_indom.
  specialize (H0 rd).
  simpljoin1.
  rewrite H0; eauto.
  exists x.
  rewrite RegMap.gso; eauto.
  intro; tryfalse.
  split.
  exists x1.
  unfold set_R, set_HR.
  unfold is_indom.
  lets Ht1 : H0 rd.
  simpljoin1.
  rewrite H6, H7.
  rewrite RegMap.gso; eauto; try intro; tryfalse.
  rewrite HRegMap.gso; eauto; try intro; tryfalse.
  exists x0.
  unfold set_R, set_HR.
  unfold is_indom.
  lets Ht1 : H0 rd.
  simpljoin1.
  rewrite H6, H7.
  rewrite RegMap.gso; eauto; try intro; tryfalse.
  rewrite HRegMap.gso; eauto; try intro; tryfalse.
Qed.

Lemma Rinj_set_sameLH_stable' :
  forall R HR (rd : GenReg) v,
    Rinj R HR -> Rinj (set_R R rd v) (HRegMap.set rd (Some v) HR).
Proof.
  intros.
  lets Ht : H.
  eapply Rinj_set_sameLH_stable with (rd := rd) (v := v) in H.
  unfold set_HR in H.
  unfold is_indom in *.
  inv Ht.
  specialize (H0 rd); simpljoin1.
  rewrite H7 in H; eauto.
Qed.

Lemma Rinj_set_Lsp_stable :
  forall R HR (sr : SpReg) w,
    Rinj R HR -> Rinj (set_R R sr (W w)) HR.
Proof.
  intros.
  inv H; simpljoin1.
  econstructor; eauto.
  intros.
  specialize (H sr).
  simpljoin1.
  specialize (H0 rr); simpljoin1.
  erewrite getR_setR_neq_stable; eauto.
  intro; tryfalse.
  split.
  unfold set_R.
  unfold is_indom.
  intros.
  lets Ht : H sr.
  simpljoin1.
  rewrite H6; eauto.
  destruct (RegName_eq sr sr0); subst; eauto.
  inv e. 
  rewrite RegMap.gss; eauto.
  eauto.
  rewrite RegMap.gso; eauto.

  specialize (H sr).
  simpljoin1.
  unfold set_R, is_indom; rewrite H.
  do 3 (rewrite RegMap.gso; eauto; try intro; tryfalse).
  split; eauto.
  split; eauto.
Qed.

Lemma Rinj_set_cwp_stable :
  forall R HR w,
    Rinj R HR -> Rinj (set_R R cwp (W w)) HR.
Proof.
  intros.
  inv H; simpljoin1.
  econstructor; eauto.
  intros.
  specialize (H0 rr); simpljoin1.
  erewrite getR_setR_neq_stable; eauto.
  intro; tryfalse.
  split.
  unfold set_R.
  unfold is_indom.
  rewrite H1; eauto.
  intros.
  specialize (H sr).
  simpljoin1.
  rewrite RegMap.gso; eauto.
  intro; tryfalse.
  split.
  unfold set_R, is_indom.
  rewrite H1; eauto.
  rewrite RegMap.gss; eauto.
  unfold set_R, is_indom; rewrite H1.
  do 2 (rewrite RegMap.gso; eauto; try intro; tryfalse).
  split; eauto.
Qed.

Lemma Rinj_set_n_fn_stable :
  forall R HR (rd : GenReg) v,
    Rinj R HR -> Rinj (set_R R n v) (set_HR HR fn v).
Proof.
  intros.
  inv H.
  econstructor; eauto.
  intros.
  specialize (H0 rr).
  simpljoin1.
  exists x.
  unfold set_R, set_HR.
  unfold is_indom.
  rewrite H2, H5.
  rewrite RegMap.gso; eauto; try (intro; tryfalse).
  rewrite HRegMap.gso; eauto; try (intro; tryfalse).
  split; eauto.

  simpljoin1.
  intros.
  specialize (H sr).
  unfold set_R, is_indom.
  rewrite H2.
  rewrite RegMap.gso; eauto.
  intro; tryfalse.

  simpljoin1.
  split.
  unfold set_R, is_indom.
  rewrite H2; eauto.
  rewrite RegMap.gso; eauto; intro; tryfalse.

  split.
  exists v.
  unfold set_R, set_HR, is_indom.
  rewrite H2, H5.
  rewrite RegMap.gss; eauto.
  rewrite HRegMap.gss; eauto.

  unfold set_R, set_HR, is_indom.
  rewrite H2, H5.
  rewrite RegMap.gso, HRegMap.gso; eauto; try (intro; tryfalse).
Qed.

Lemma Rinj_set_z_fz_stable :
  forall R HR (rd : GenReg) v,
    Rinj R HR -> Rinj (set_R R z v) (set_HR HR fz v).
Proof.
  intros.
  inv H.
  econstructor; eauto.
  intros.
  specialize (H0 rr).
  simpljoin1.
  exists x.
  unfold set_R, set_HR.
  unfold is_indom.
  rewrite H3, H4.
  rewrite RegMap.gso; eauto; try (intro; tryfalse).
  rewrite HRegMap.gso; eauto; try (intro; tryfalse).
  split; eauto.

  simpljoin1.
  intros.
  specialize (H sr).
  unfold set_R, is_indom.
  rewrite H3.
  rewrite RegMap.gso; eauto.
  intro; tryfalse.

  simpljoin1.
  split.
  unfold set_R, is_indom.
  rewrite H3; eauto.
  rewrite RegMap.gso; eauto; intro; tryfalse.

  split.
  unfold set_R, set_HR, is_indom.
  rewrite H3, H4.
  rewrite RegMap.gso, HRegMap.gso; eauto; try (intro; tryfalse).
  
  exists v.
  unfold set_R, set_HR, is_indom.
  rewrite H3, H4.
  rewrite RegMap.gss; eauto.
  rewrite HRegMap.gss; eauto.
Qed.

Lemma Rinj_set_window_HL :
  forall R HR fm1 fm2 fm3,
    Rinj R HR ->
    Rinj (set_window R fm1 fm2 fm3) (set_Hwindow HR fm1 fm2 fm3).
Proof.
  intros.
  unfold set_window, set_Hwindow.
  unfold set_frame, set_Hframe.
  destruct fm1, fm2, fm3; simpl.
  repeat (eapply Rinj_set_sameLH_stable); eauto.
Qed.

Lemma set_Mframe_set_Mframe'_same_0:
  forall b fm fm',
    set_Mframe (set_Mframe' b $ 0 fm) (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12) (b, $ 16) 
               (b, $ 20) (b, $ 24) (b, $ 28) fm' =
    set_Mframe empM (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12) (b, $ 16) 
               (b, $ 20) (b, $ 24) (b, $ 28) fm'.
Proof.
  intros.
  unfold set_Mframe.
  destruct fm'; simpls.
  unfold set_Mframe'.
  destruct fm; simpls.
  assert (($ 0) +ᵢ ($ 28) = $ 28); eauto.
  assert (($ 0) +ᵢ ($ 24) = $ 24); eauto.
  assert (($ 0) +ᵢ ($ 20) = $ 20); eauto.
  assert (($ 0) +ᵢ ($ 16) = $ 16); eauto.
  assert (($ 0) +ᵢ ($ 12) = $ 12); eauto.
  assert (($ 0) +ᵢ ($ 8) = $ 8); eauto.
  assert (($ 0) +ᵢ ($ 4) = $ 4); eauto.
  rewrite H, H0, H1, H2, H3, H4, H5; clear H H0 H1 H2 H3 H4 H5.

  do 7 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 0)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 6 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 4)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 5 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 8)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 4 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 12)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 3 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 16)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 2 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 20)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 1 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 24)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  rewrite memset_twice; eauto.
Qed.

Lemma set_Mframe_set_Mframe'_same_32:
  forall b fm fm',
    set_Mframe (set_Mframe' b $ 32 fm) (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44) (b, $ 48) 
               (b, $ 52) (b, $ 56) (b, $ 60) fm' =
    set_Mframe empM (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44) (b, $ 48) 
               (b, $ 52) (b, $ 56) (b, $ 60) fm'.
Proof.
  intros.
  unfold set_Mframe.
  destruct fm'; simpls.
  unfold set_Mframe'.
  destruct fm; simpls.
  assert (($ 32) +ᵢ ($ 28) = $ 60); eauto.
  assert (($ 32) +ᵢ ($ 24) = $ 56); eauto.
  assert (($ 32) +ᵢ ($ 20) = $ 52); eauto.
  assert (($ 32) +ᵢ ($ 16) = $ 48); eauto.
  assert (($ 32) +ᵢ ($ 12) = $ 44); eauto.
  assert (($ 32) +ᵢ ($ 8) = $ 40); eauto.
  assert (($ 32) +ᵢ ($ 4) = $ 36); eauto.
  rewrite H, H0, H1, H2, H3, H4, H5; clear H H0 H1 H2 H3 H4 H5.

  do 7 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 32)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 6 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 36)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 5 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 40)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 4 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 44)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 3 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 48)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 2 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 52)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  do 1 (try rewrite MemMap_set_neq_reorder with (l1 := (b, $ 56)); try intro; tryfalse).
  rewrite memset_twice; eauto.

  rewrite memset_twice; eauto.
Qed.

Lemma dom_eq_set_same_Mframe :
  forall M l0 l1 l2 l3 l4 l5 l6 l7 fm fm',
    dom_eq (set_Mframe M l0 l1 l2 l3 l4 l5 l6 l7 fm) (set_Mframe M l0 l1 l2 l3 l4 l5 l6 l7 fm').
Proof.
  intros.
  unfold dom_eq.
  split; intros; unfold indom in *.
  {
    simpljoin1.
    unfolds set_Mframe.
    destruct fm, fm'; simpls.
    destruct (Address_eq l l7); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l6); subst.
    rewrite MemMap.gss; eauto.
 
    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l5); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l4); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l3); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l2); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l1); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l0); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    eauto.
  }
  {
    simpljoin1.
    unfolds set_Mframe.
    destruct fm, fm'; simpls.
    destruct (Address_eq l l7); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l6); subst.
    rewrite MemMap.gss; eauto.
 
    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l5); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l4); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l3); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l2); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l1); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    destruct (Address_eq l l0); subst.
    rewrite MemMap.gss; eauto.

    try rewrite MemMap.gso in *; try (intro; tryfalse).
    eauto.
  }
Qed.

Lemma get_R_set_frame_genreg_spreg_still :
  forall R (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) fm v (sr : SpReg),
    get_R R sr = Some v ->
    get_R (set_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm) sr = Some v.
Proof.
  intros.
  unfold set_frame.
  destruct fm; simpl.
  do 8 (eapply get_R_set_neq_stable; [idtac | intro; tryfalse]); eauto.
Qed.

Lemma get_R_spreg_set_window_still :
  forall R fm1 fm2 fm3 (sr : SpReg) v,
    get_R R sr = Some v ->
    get_R (set_window R fm1 fm2 fm3) sr = Some v.
Proof.
  intros.
  unfold set_window.
  do 3 (eapply get_R_set_frame_genreg_spreg_still; eauto).
Qed.

Lemma set_Mframe'_get_some_address_0 :
  forall b fm x v,
    set_Mframe' b $ 0 fm x = Some v ->
    exists ofs, x = (b, ofs) /\ int_leu $ 0 ofs = true /\ Int.ltu ofs $ 32 = true /\ (ofs modu ($ 4)) =ᵢ ($ 0) = true.
Proof.
  intros.
  unfolds set_Mframe', set_Mframe.
  destruct fm; simpls.

  destruct (Address_eq (b, $ 28) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 24) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 20) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 16) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 12) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 8) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 4) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 0) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  unfolds empM; tryfalse.
Qed.

Lemma set_Mframe'_get_some_address_32 :
  forall b fm x v,
    set_Mframe' b $ 32 fm x = Some v ->
    exists ofs, x = (b, ofs) /\ int_leu $ 32 ofs = true /\ Int.ltu ofs $ 64 = true /\ (ofs modu ($ 4)) =ᵢ ($ 0) = true.
Proof.
  intros.
  unfolds set_Mframe', set_Mframe.
  destruct fm; simpls.

  destruct (Address_eq (b, $ 60) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 56) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 52) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 48) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 44) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 40) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 36) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  destruct (Address_eq (b, $ 32) x); subst; eauto.
  rewrite MemMap.gso in H; eauto.
  unfolds empM; tryfalse.
Qed.

Lemma set_frame_0_32_disj :
  forall b fm1 fm2,
    set_Mframe' b $ 0 fm1 ⊥ set_Mframe' b $ 32 fm2.
Proof.
  intros.
  unfold disjoint; intros.
  destruct (set_Mframe' b $ 0 fm1 x) eqn:Heqe1; eauto.
  { 
    destruct (set_Mframe' b $ 32 fm2 x) eqn:Heqe2; eauto.
    eapply set_Mframe'_get_some_address_0 in Heqe1; simpljoin1.
    eapply set_Mframe'_get_some_address_32 in Heqe2; simpljoin1; eauto.
    destruct x; unfolds int_leu, Int.ltu, Int.eq; simpls.
    assert (Int.unsigned $ 64 = 64); eauto.
    assert (Int.unsigned $ 32 = 32); eauto.
    try rewrite H, H6, Int_unsigned_0 in *; clear H H4.
    
    destruct (zlt intval 32); destruct (zlt 0 intval); destruct (zeq 0 intval);
      destruct (zlt 32 intval); destruct (zeq 32 intval); destruct (zlt intval 64);
        eauto; try omega; simpls; tryfalse.
  }
  {
    destruct (set_Mframe' b $ 32 fm2 x); eauto.
  }
Qed.

Lemma DomCtx_fetch_frame_0 :
  forall t b M,
    (forall l, (indom l M <-> DomCtx l t b) /\ t <> b) ->
    exists fm, fetch_frame M (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12) (b, $ 16) (b, $ 20) (b, $ 24) (b, $ 28) =
          Some fm.
Proof.
  intros.
  unfold fetch_frame. 
  assert (forall ofs, int_leu $ 0 ofs && Int.ltu ofs $ 64 && Int.eq (ofs modu ($ 4)) ($ 0) = true
                 -> M (b, ofs) <> None).
  {
    intros.
    specialize (H (b, ofs)).
    simpljoin1.
    assert (DomCtx (b, ofs) t b).
    {
      unfold DomCtx.
      destruct (Z.eq_dec t b); tryfalse.
      destruct (Z.eq_dec b b); tryfalse; eauto.
      destruct (int_leu $ 0 ofs); destruct (Int.ltu ofs $ 64); simpls; tryfalse; eauto.
    }
    eapply H in H2.
    unfold indom in *; simpljoin1.
    intro; tryfalse.
  }

  repeat
  match goal with
  | |- context [M ?A] =>
    let H := fresh in
    destruct (M A) eqn:H; [idtac | eapply H0 in H; eauto; tryfalse]
  end.
  eauto.
Qed.

Lemma DomCtx_fetch_frame_32 :
  forall t b M,
    (forall l, (indom l M <-> DomCtx l t b) /\ t <> b) ->
    exists fm, fetch_frame M (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44) (b, $ 48) (b, $ 52) (b, $ 56) (b, $ 60) =
          Some fm.
Proof.
  intros.
  unfold fetch_frame.
  assert (forall ofs, int_leu $ 0 ofs && Int.ltu ofs $ 64 && Int.eq (ofs modu ($ 4)) ($ 0) = true
                 -> M (b, ofs) <> None).
  {
    intros.
    specialize (H (b, ofs)).
    simpljoin1.
    assert (DomCtx (b, ofs) t b).
    {
      unfold DomCtx.
      destruct (Z.eq_dec t b); tryfalse.
      destruct (Z.eq_dec b b); tryfalse; eauto.
      destruct (int_leu $ 0 ofs); destruct (Int.ltu ofs $ 64); simpls; tryfalse; eauto.
    }
    eapply H in H2.
    unfold indom in *; simpljoin1.
    intro; tryfalse.
  }

  repeat
  match goal with
  | |- context [M ?A] =>
    let H := fresh in
    destruct (M A) eqn:H; [idtac | eapply H0 in H; eauto; tryfalse]
  end.
  eauto.
Qed.

Lemma fetch_frame_set_Mframe_get0 :
  forall M b fm l v,
    fetch_frame M (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12)
                (b, $ 16) (b, $ 20) (b, $ 24) (b, $ 28) = Some fm ->
    set_Mframe' b $ 0 fm l = Some v ->
    M l = Some v.
Proof.
  intros.
  unfold fetch_frame in *.
  do 8
  match goal with
  | H : context [M ?A] |- _ =>
    let H' := fresh in
    destruct (M A) eqn:H'; simpls; tryfalse
  end.
  inv H.
  unfolds set_Mframe', set_Mframe; simpls.

  destruct (Address_eq (b, $ 28) l); simpls; subst; eauto.
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 24) l); simpls; subst; eauto.
  rewrite MemMap.gso in H0; try intro; tryfalse.
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 20) l); simpls; subst; eauto.
  do 2 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 16) l); simpls; subst; eauto.
  do 3 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 12) l); simpls; subst; eauto.
  do 4 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 8) l); simpls; subst; eauto.
  do 5 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 4) l); simpls; subst; eauto.
  do 6 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 0) l); simpls; subst; eauto.
  do 7 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  do 8 (rewrite MemMap.gso in H0; eauto).
  unfolds empM; tryfalse.
Qed.

Lemma fetch_frame_set_Mframe_get32 :
  forall M b fm l v,
    fetch_frame M (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44)
                (b, $ 48) (b, $ 52) (b, $ 56) (b, $ 60) = Some fm ->
    set_Mframe' b $ 32 fm l = Some v ->
    M l = Some v.
Proof.
  intros.
  unfold fetch_frame in *.
  do 8
  match goal with
  | H : context [M ?A] |- _ =>
    let H' := fresh in
    destruct (M A) eqn:H'; simpls; tryfalse
  end.
  inv H.
  unfolds set_Mframe', set_Mframe; simpls.

  destruct (Address_eq (b, $ 60) l); simpls; subst; eauto.
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 56) l); simpls; subst; eauto.
  rewrite MemMap.gso in H0; try intro; tryfalse.
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 52) l); simpls; subst; eauto.
  do 2 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 48) l); simpls; subst; eauto.
  do 3 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 44) l); simpls; subst; eauto.
  do 4 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 40) l); simpls; subst; eauto.
  do 5 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 36) l); simpls; subst; eauto.
  do 6 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  destruct (Address_eq (b, $ 32) l); simpls; subst; eauto.
  do 7 (rewrite MemMap.gso in H0; try intro; tryfalse).
  rewrite MemMap.gss in H0; inv H0; eauto.

  do 8 (rewrite MemMap.gso in H0; eauto).
  unfolds empM; tryfalse.
Qed.

Ltac auto_solve1 :=
  match goal with
  | |- context [MemMap.set ?A _ _ ?B] =>
    rewrite MemMap.gso; [idtac | try intro; tryfalse]
  end.


Lemma range_legal_set_Mframe_ok0 :
  forall i b fm,
    $ 0 <=ᵤᵢ i <ᵤᵢ $ 32 -> (i modu ($ 4)) =ᵢ ($ 0) = true ->
    exists v, set_Mframe' b $ 0 fm (b, i) = Some v.
Proof.
  intros.
  unfold set_Mframe', set_Mframe.
  destruct fm; simpl.
  eapply legal_frame_range0 in H; eauto.
  
  destruct H; subst; simpl.
  do 7 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 6 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 5 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 4 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 3 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 2 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 1 auto_solve1; rewrite MemMap.gss; eauto.
  rewrite MemMap.gss; eauto.
Qed.

Lemma range_legal_set_Mframe_ok32 :
  forall i b fm,
    $ 32 <=ᵤᵢ i <ᵤᵢ $ 64 -> (i modu ($ 4)) =ᵢ ($ 0) = true ->
    exists v, set_Mframe' b $ 32 fm (b, i) = Some v.
Proof.
  intros.
  unfold set_Mframe', set_Mframe.
  destruct fm; simpl.
  eapply legal_frame_range32 in H; eauto.
  
  destruct H; subst; simpl.
  do 7 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 6 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 5 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 4 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 3 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 2 auto_solve1; rewrite MemMap.gss; eauto.
  destruct H; subst; simpl.
  do 1 auto_solve1; rewrite MemMap.gss; eauto.
  rewrite MemMap.gss; eauto.
Qed.

(** Auxiliary Lemmas about Malloc and Mfree *)
Lemma block_fresh_merge_sep :
  forall b M1 M2,
    Mfresh b (M1 ⊎ M2) -> Mfresh b M1 /\ Mfresh b M2.
Proof.
  intros.
  unfolds Mfresh.
  split; intros.
  specialize (H o).
  intro; contradiction H.
  eapply indom_merge_still; eauto.
  specialize (H o).
  intro; contradiction H.
  eapply indom_merge_still2; eauto.
Qed.

Lemma Mfree_merge_sep :
  forall m1 m2 b,
    Mfree (m1 ⊎ m2) b = Mfree m1 b ⊎ Mfree m2 b.
Proof.
  intros.
  unfold Mfree.
  eapply FunctionalExtensionality.functional_extensionality; intros.
  destruct x.
  unfold merge.
  destruct (Z.eq_dec b z); subst; eauto.
Qed.

Lemma Mfree_merge_sep_fresh_left :
  forall m1 m2 b,
    Mfresh b m1 ->
    Mfree (m1 ⊎ m2) b = m1 ⊎ Mfree m2 b.
Proof.
  intros.
  unfold Mfree.
  eapply FunctionalExtensionality.functional_extensionality; intros.
  destruct x.
  unfold merge.
  destruct (Z.eq_dec b z); subst; eauto.
  destruct (m1 (z, i)) eqn:Heqe; eauto.
  unfolds Mfresh.
  specialize (H i).
  contradiction H; unfold indom; eauto.
Qed.

Lemma Mfree_merge_sep_fresh_right :
  forall m1 m2 b,
    Mfresh b m2 ->
    Mfree (m1 ⊎ m2) b = Mfree m1 b ⊎ m2.
Proof.
  intros.
  unfold Mfree.
  eapply FunctionalExtensionality.functional_extensionality; intros.
  destruct x.
  unfold merge.
  destruct (Z.eq_dec b z); subst; eauto.
  destruct (m2 (z, i)) eqn:Heqe; eauto.
  unfolds Mfresh.
  specialize (H i).
  contradiction H; unfold indom; eauto.
Qed.

Lemma Mfree_left_disjoint_stable :
  forall M m b,
    M ⊥ m -> Mfree M b ⊥ m.
Proof.
  intros.
  unfold disjoint in *; intros.
  specialize (H x).
  unfold Mfree; destruct x.
  destruct (Z.eq_dec b z); subst.
  destruct (m (z, i)); eauto.
  eauto.
Qed.

Lemma Mfree_right_disjoint_stable :
  forall M m b,
    M ⊥ m -> M ⊥ Mfree m b.
Proof.
  intros.
  unfold disjoint in *; intros.
  specialize (H x).
  unfold Mfree; destruct x.
  destruct (M (z, i)); destruct (Z.eq_dec b z); eauto.
Qed.

Lemma Mfree_both_sides_disjoint_stable :
  forall M m b,
    M ⊥ m -> Mfree M b ⊥ Mfree m b.
Proof.
  intros.
  unfold disjoint in *; intros.
  specialize (H x).
  unfold Mfree; destruct x.
  destruct (Z.eq_dec b z); subst; eauto.
Qed.

Lemma Mfresh_Mfree_stable :
  forall M b,
    Mfresh b M -> Mfree M b = M.
Proof.
  intros.
  unfolds Mfresh, Mfree.
  eapply FunctionalExtensionality.functional_extensionality; intro; subst.
  destruct x. 
  destruct (Z.eq_dec b z); subst; eauto.
  destruct (M (z, i)) eqn:Heqe; eauto.
  specialize (H i).
  contradiction H; unfold indom; eauto.
Qed.

(** Auxiliary Lemmas about state Relation *)
Lemma stkRel_sep :
  forall n b F1 F2 M HF,
    stkRel (b, F1 ++ F2, M) HF -> length F1 = (2*n)%nat ->
    exists M1 M2 HF1 HF2 b', M1 ⊎ M2 = M /\ M1 ⊥ M2 /\ HF1 ++ HF2 = HF /\
                        stkRel (b, F1, M1) HF1 /\ stkRel (b', F2, M2) HF2 /\ length HF1 = n /\
                        (forall fm1 fm2 F', F1 = F' ++ [fm1; fm2] -> get_frame_nth fm2 6 = Some (Ptr (b', $ 0))) /\
                        (F1 = nil -> b = b').
Proof.
  induction n; intros.
  {
    destruct F1; simpls; tryfalse.
    exists empM M.
    exists (nil : list HFrame) HF b.
    split.
    eapply empM_merge_still_l.
    split.
    unfold disjoint; intros.
    unfold empM.
    destruct (M x); eauto.
    simpl; eauto.
    split; eauto.
    split.
    econstructor; eauto.
    split; eauto.
    split; eauto.
    split.
    intros; tryfalse.
    destruct F'; simpls; tryfalse.
    intros; eauto.
  }
  {  
    destruct F1; simpls; tryfalse.
    inv H0.
    destruct F1; simpls; tryfalse.
    rewrite <- plus_Snm_nSm, Nat.add_succ_l in H2.
    tryfalse.
    inv H.
    eapply IHn in H11; eauto.
    simpljoin1.
    exists (set_Mframe' b $ 0 fm1' ⊎ set_Mframe' b $ 32 fm2' ⊎ x) x0 ((b, f, f0) :: x1) x2 x3.

    split.
    rewrite <- merge_assoc; eauto.
    split.
    eapply disj_sym.
    eapply disj_sep_merge_still; eauto; try solve [eapply disj_sym; eauto].
    eapply disj_merge_disj_sep in H9.
    simpljoin1.
    eapply disj_sym; eauto.
    split; simpl; eauto.
    split; eauto.
  
    econstructor; eauto.
    eapply disj_merge_disj_sep in H9.
    simpljoin1; eauto.
    split; eauto.
    split; eauto.
    split.
    intros.
    destruct F'; simpls.
    inv H.
    rewrite <- H7; eauto.
    destruct F'; simpls; inv H.
    clear - H2.
    rewrite <- plus_Snm_nSm, Nat.add_succ_l in H2; simpls.
    inv H2.
    destruct x1; simpls; tryfalse.
    inv H0.
    rewrite <- plus_Snm_nSm, Nat.add_succ_l in H1.
    inv H1.
    eapply H6; eauto.
    intros; tryfalse.
    
    rewrite <- plus_Snm_nSm, Nat.add_succ_l in H2.
    inv H2; eauto.
  }
Qed.

Lemma stkRel_merge :
  forall n F1 F2 HF1 HF2 M1 M2 b1 b2,
    stkRel (b1, F1, M1) HF1 -> stkRel (b2, F2, M2) HF2 ->
    length F1 = (2*n)%nat -> length HF1 = n -> M1 ⊥ M2 ->
    (forall fm1 fm2 F', F1 = F' ++ [fm1; fm2] -> get_frame_nth fm2 6 = Some (Ptr (b2, $ 0))) ->
    (F1 = nil -> b1 = b2) ->
    stkRel (b1, F1 ++ F2, M1 ⊎ M2) (HF1 ++ HF2).
Proof.
  induction n; intros; simpls.
  {
    destruct F1; simpls; tryfalse.
    destruct HF1; simpls; tryfalse.
    inv H.
    rewrite H5; eauto.
  }
  {
    destruct F1; simpls; tryfalse.
    inv H1.
    rewrite <- plus_Snm_nSm, Nat.add_succ_l in H7.
    destruct F1; simpls; tryfalse.
    inv H.
    rewrite <- merge_assoc.
    rewrite <- app_comm_cons.
    econstructor; eauto.
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H3.
    eapply disj_merge_disj_sep1 in H3.
    eapply disj_sym; eauto.

    inv H7.
    eapply IHn; eauto.
    eapply disj_sym in H3.
    eapply disj_merge_disj_sep2 in H3.
    eapply disj_sym; eauto.

    intros.
    assert (f :: f0 :: F1 = (f :: f0 :: F') ++ [fm1; fm2]).
    {
      subst; simpl; eauto.
    }
    eapply H4 in H6; eauto.
    intros; subst.
    specialize (H4 f f0 nil); simpls.
    rewrite H4 in H15; eauto.
    inv H15; eauto.
  }
Qed.

Lemma indom_stk_ofs_in_restrict_range :
  forall Mk b F HF b' ofs',
    stkRel (b, F, Mk) HF -> indom (b', ofs') Mk ->
    int_leu $ 0 ofs' = true /\ Int.ltu ofs' $ 64 = true /\ Int.eq (ofs' modu $ 4) ($ 0) = true.
Proof.
  intros.
  generalize dependent b'.
  generalize dependent ofs'.
  remember (b, F, Mk) as LF.
  generalize dependent b.
  generalize dependent F.
  generalize dependent Mk.
  induction H; intros.
  {
    inv HeqLF.
    unfold indom, empM in *.
    simpljoin1; tryfalse.
  }
  {
    inv HeqLF.
    eapply indom_merge_indom_oneof in H4.
    destruct H4.
    {
      clear - H.
      unfold indom in *.
      simpljoin1.
      unfold set_Mframe', set_Mframe, merge in *.
      destruct fm1, fm2; simpls.

      destruct (Address_eq (b'0, ofs') (b0, ($ 0))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 28))); eauto.
      inv e; eauto.
 
      do 8 (rewrite MemMap.gso in H; eauto).
      simpl in H.

      destruct (Address_eq (b'0, ofs') (b0, ($ 32))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 28))); eauto.
      inv e; eauto.

      do 8 (rewrite MemMap.gso in H; eauto); simpls.
      unfolds empM; tryfalse.
    }
    {
      eapply IHstkRel; eauto.
    }
  }
  {
    inv HeqLF.
    eapply indom_merge_indom_oneof in H4.
    destruct H4.
    { 
      clear - H.
      unfold indom in *.
      simpljoin1.
      unfold set_Mframe', set_Mframe, merge in *.
      destruct fm1', fm2'; simpls.

      destruct (Address_eq (b'0, ofs') (b0, ($ 0))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 28))); eauto.
      inv e; eauto.
 
      do 8 (rewrite MemMap.gso in H; eauto).
      simpl in H.

      destruct (Address_eq (b'0, ofs') (b0, ($ 32))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 28))); eauto.
      inv e; eauto.

      do 8 (rewrite MemMap.gso in H; eauto); simpls.
      unfolds empM; tryfalse.
    }
    {
      eapply IHstkRel; eauto.
    }
  }
Qed.

Lemma indom_stk_ofs_in_0_inrange :
  forall Mk b F HF b' ofs',
    stkRel (b, F, Mk) HF -> indom (b', ofs') Mk ->
    indom (b', $ 0) Mk.
Proof.
  intros.
  generalize dependent b'.
  generalize dependent ofs'.
  remember (b, F, Mk) as LF.
  generalize dependent b.
  generalize dependent F.
  generalize dependent Mk.
  induction H; intros.
  {
    inv HeqLF; unfold indom, empM in *.
    simpljoin1; tryfalse.
  }
  {
    inv HeqLF.
    eapply indom_merge_indom_oneof in H4.
    destruct H4.
    {
      clear - H.
      unfold indom in *.
      simpljoin1.
      unfold set_Mframe', set_Mframe, merge in *.
      destruct fm1, fm2; simpls.
 
      destruct (Address_eq (b'0, ofs') (b0, ($ 0))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 28))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.

      destruct (Address_eq (b'0, ofs') (b0, ($ 32))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 28))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.

      do 16 (rewrite MemMap.gso in H; eauto); simpls.
      unfolds empM; tryfalse.
    }
    {
      eapply indom_merge_still2; eauto.
    }
  }
  {
    inv HeqLF.
    eapply indom_merge_indom_oneof in H4.
    destruct H4.
    {
      clear - H.
      unfold indom in *.
      simpljoin1.
      unfold set_Mframe', set_Mframe, merge in *.
      destruct fm1', fm2'; simpls.
 
      destruct (Address_eq (b'0, ofs') (b0, ($ 0))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 0) +ᵢ ($ 28))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.

      destruct (Address_eq (b'0, ofs') (b0, ($ 32))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 4))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 8))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 12))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 16))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 20))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 24))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.
      destruct (Address_eq (b'0, ofs') (b0, ($ 32) +ᵢ ($ 28))); eauto.
      inv e; eauto.
      do 7 (rewrite MemMap.gso; [idtac | intro; tryfalse]).
      rewrite MemMap.gss; eauto.

      do 16 (rewrite MemMap.gso in H; eauto); simpls.
      unfolds empM; tryfalse.
    }
    {
      eapply indom_merge_still2; eauto.
    }
  }
Qed.

Fixpoint get_block_HF (HF : list HFrame) :=
  match HF with
  | (b, _, _) :: HF' => b :: get_block_HF HF'
  | _ => nil
  end.

Lemma indom_stkRel_HF_b_0_in :
  forall HF b F M b',
    stkRel (b, F, M) HF -> In b' (get_block_HF HF) ->
    indom (b', $ 0) M.
Proof.
  induction HF; intros; simpls; tryfalse.
  destruct a.
  destruct p.
  simpl in H0.
  destruct H0; subst.
  { 
    inv H.
    
    eapply indom_merge_still; eauto.
    eapply indom_merge_still; eauto.
    unfold set_Mframe', set_Mframe.
    destruct f0; simpl.
    unfold indom.
    do 7 (rewrite MemMap.gso; [idtac | try intro; tryfalse]).
    rewrite MemMap.gss; eauto.
 
    eapply indom_merge_still; eauto.
    eapply indom_merge_still; eauto.
    unfold set_Mframe', set_Mframe.
    destruct fm1'; simpl.
    unfold indom.
    do 7 (rewrite MemMap.gso; [idtac | try intro; tryfalse]).
    rewrite MemMap.gss; eauto.
  }
  {
    inv H.
    eapply indom_merge_still2.
    eapply IHHF; eauto.
    eapply indom_merge_still2.
    eapply IHHF; eauto.
  }
Qed.
