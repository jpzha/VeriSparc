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

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(** Auxiliary Lemmas about Sep Star *)
Lemma rel_sep_star_split :
  forall S HS A w P1 P2,
    (S, HS, A, w) ||= P1 ⋆ P2 ->
    exists S1 S2 HS1 HS2 w1 w2, state_union S1 S2 S /\ hstate_union HS1 HS2 HS /\
                     (S1, HS1, A, w1) ||= P1 /\ (S2, HS2, A, w2) ||= P2 /\ w = (w1 + w1)%nat.
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
    exists idx A HS.
    split; eauto.
    simpljoin1; eauto.
    destruct x.
    do 3 eexists.
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
    exists idx A HS x2.
    split; eauto.
    destruct H4.
    split.
    left; eauto.
    simpljoin1; subst; eauto.
    simpljoin1.
    eapply LtIndex_Trans; eauto.

    split.
    right; eauto.
    simpljoin1.
    split; eauto.
    eapply LtIndex_Trans; eauto.
    simpljoin1; eauto.
    
    destruct x.
    exists (Nat.succ (Nat.succ n), n0) x0 x1 x2.
    split; eauto.
    destruct H4.
    split.
    left; eauto.
    eapply LtIndex_Trans; eauto.
    econstructor; eauto.
    split.
    right.
    simpljoin1.
    split; eauto.
    eapply Hp; eauto.
    econstructor; eauto.
    eapply LtIndex_Trans; eauto.
    econstructor; eauto.
  }
Qed.

(** Auxiliary rel_safety *)
CoInductive rel_safety_aux :
  nat -> Index -> (XCodeHeap * State * Word * Word) -> (primcom * HState) -> relasrt -> Prop :=
| aux_cons_safety : forall k idx C S pc npc A HS Q aexp rd f i,
    (C pc = Some (c (cntrans i)) \/ C pc = Some (c (cjumpl aexp rd)) \/ C pc = Some (c (cbe f))
     \/ C pc = Some (c (ccall f)) \/ C pc = Some (c cretl)) ->
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
            exists idx1,
              idx1 ⩹ idx /\ rel_safety_aux (Nat.succ k) idx1 (C, S2, pc2, npc2) (A, HS) Q
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
            exists idx1 A' HS' w,
              (Nat.eqb k 0 = true /\ exec_prim (A, HS) (A', HS') /\ (S2, HS', A', w) ||= Q /\ (0%nat, 0%nat) ⩹ idx1) \/
              (Nat.eqb k 0 = false /\ idx1 ⩹ idx /\ A' = A /\ HS = HS' /\
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
            exists S1 pc1 npc1,
              LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
              Lsafety n (k, (C, (S1, pc1, npc1))) (k', (C, (S', pc', npc')))
          )
    ) ->
    (
        forall f,
          C pc = Some (c (ccall f)) ->
          (
            (* progress *)
            exists S1 pc1 npc1 S2 pc2 npc2,
              LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
              LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2)) /\ 
              Lsafety n (Nat.succ k, (C, (S2, pc2, npc2))) (k', (C, (S', pc', npc')))
          )
    ) ->
    (
          C pc = Some (c (cretl)) ->
          (
            (* progress *)
            exists S1 pc1 npc1 S2 pc2 npc2,
              LP__ (C, (S, pc, npc)) tau (C, (S1, pc1, npc1)) /\
              LP__ (C, (S1, pc1, npc1)) tau (C, (S2, pc2, npc2)) /\ 
              (Nat.eqb k 0 = false /\ Lsafety n (Nat.pred k, (C, (S2, pc2, npc2))) (k', (C, (S', pc', npc'))))
          )
    ) ->
    Lsafety (Nat.succ n) (k, (C, (S, pc, npc))) (k', (C, (S', pc', npc'))).

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
     do 3 eexists.
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
     exists (Nat.succ x13).
     split.
     econstructor; eauto.
     intros.
     repeat (destruct H9 as [H9 | H9]; CElim C).
     Focus 2.
     intros; CElim C.
     intros.
     clear H9.
     do 6 eexists.
     split; eauto.
     split; eauto.
     split; eauto.
     intros; CElim C.
   }
   {
     do 6 eexists.
     exists 1%nat.
     split.
     econstructor; eauto.
     intros.
     repeat (destruct H6 as [H6 | H6]; CElim C).
     Focus 2.
     intros; CElim C.
     intros.
     clear H6.
     do 6 eexists.
     split; eauto.
     split; eauto.
     econstructor; eauto. 
     assert (x6 = Pdone).
     {
       inv H3; eauto.
     }
     subst x6.
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
     exists (Nat.succ x15).
     split.
     econstructor; eauto.
     intros.
     repeat (destruct H12 as [H12 | H12]; CElim C).
     intros; CElim C.
     intros.
     clear H12.
     do 6 eexists.
     split; eauto.
     split; eauto.
     split; eauto.
     intros; tryfalse.
   }
   {
     destruct H5.
     {  
       simpljoin1; subst.
       destruct x6.
       do 4 eexists.
       exists (Nat.succ n, n0).
       exists x8 0%nat. 
       split.
       econstructor; eauto.
       split; eauto.
       split; intros; eauto.
       econstructor; eauto.
       intros. 
       repeat (destruct H8 as [H8 | H8]; CElim C).
       intros; CElim C.
       intros.
       clear H8. 
       split; eauto.
       do 6 eexists; eauto.
       intros. 
       assert ((C, (x0, x2, x4)) = (C, (S1, pc1, npc1))).
       {
         eapply LP_deterministic; eauto.
         simpl; eauto.
       }
       inv H10.
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
       assert ((C, (x1, x3, x5)) = (C, (S2, pc2, npc2))).
       {
         simpljoin1.
         assert (exists cc', C npc = Some (c cc')).
         {
           destruct H10; eauto.
           repeat (destruct H10 as [H10 | H10]; eauto).
           destruct H10; eauto.
         }
         simpljoin1.
         eapply LP_deterministic; eauto.
         simpl; eauto.
       }
       inv H12.
       do 4 eexists.
       split.
       left.
       instantiate (3 := (n, n0)).
       split; econstructor; eauto.
       split.
       left; eauto.
       eauto.
     }
     {
       simpljoin1.
       do 6 eexists.
       exists 1%nat.
       split.
       econstructor; eauto.
       intros.
       repeat (destruct H8 as [H8 | H8]; CElim C).
       intros; CElim C.
       intros.
       clear H8.
       do 6 eexists.
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
    destruct H; eauto.
    repeat (destruct o as [o | o]; eauto).
  }
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
    eexists. 
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
    do 4 eexists.
    left; eauto.
    simpljoin1.
    do 4 eexists.
    right.
    split; eauto.
    inv H4.
  }
  Unshelve.
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
        instantiate (1 := f).
        instantiate (1 := rd).
        instantiate (1 := aexp).
        instantiate (1 := i).
        repeat (destruct Hcom' as [Hcom' | Hcom']; eauto).
      }
      {
        intros.
        clear H4.
        split; eauto.
        intros.
        exists (idx_sum (0%nat, n0) idx).
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

      exists (idx_sum (0%nat, n0) idx).
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
        exists (idx_sum (0%nat, n0) idx).
        do 3 eexists.
        right; eauto.
        split; eauto.
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
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact nop.
  exact (Ao (Ow ($ 1))).
  exact r0.
  exact ($ 5).
  exact nop.
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

Inductive wfHPrimExec : XCodeHeap -> primcom -> HState -> Prop :=
| cons_wfHPrimExec : forall C A HS,
    (
      forall hprim lv T t HQ pc npc HM,
        A = Pm hprim lv -> HS = (T, t, (HQ, pc, npc), HM) -> 
        HH__ C (HQ, pc, npc, HM) (Callevt pc lv) (HQ, pc, npc, HM) /\
        (exists HS' pc' npc', hprim lv HS HS' /\ get_Hs_pcont HS' = (pc', npc'))
    ) ->
    wfHPrimExec C A HS.

(** Well-formed Current Thread *)
Inductive wfCth : Index -> XCodeHeap * XCodeHeap -> LProg -> HProg -> Prop :=
| clt_wfCth : forall C Cas S HS pc npc PrimSet idx,
    wp_stateRel S HS -> wfIndex C S pc idx -> 
    get_Hs_pcont HS = (pc, npc) -> indom pc C ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS)

| prim_wfCth : forall C Cas Sc HSc S HS Sr HSr w Q Pr A pc npc PrimSet idx k,
    state_union Sc Sr S -> hstate_union HSc HSr HS ->
    rel_safety_aux k idx (Cas, Sc, pc, npc) (A, HSc) Q -> (Sr, HSr, A, w) ||= Pr -> wfHPrimExec C A HS ->
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
    exists lv hprim, PrimSet pc = Some hprim /\ wfHPrimExec C (Pm hprim lv) HS
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
    simpljoin1.
    simpl in H5.
    simpl.
    lets Hexec_prim : H7.
    inv H7.
    eapply Hret in H18; eauto.
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
Lemma wfCth_wfRdy_tau_step_preservation :
  forall idx C Cas S pc npc S' pc' npc' PrimSet T t K M Spec,
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
  intros.
  lets Ht : classic (indom pc C). 
  destruct Ht.
  { 
    inv H2.
    Focus 2.
    inv H16.
    clear - H0 H5 H20.
    unfold indom in *.
    simpljoin1.
    unfold disjoint in *.
    specialize (H0 pc).
    rewrite H in H0; simpls.
    repeat (destruct H20 as [H20 | H20]; [rewrite H20 in H0; simpls; tryfalse | idtac]).
    rewrite H20 in H0; simpls; tryfalse.

    eapply LP__local1 in H4; eauto.
    inv H4.
    inv H13.
    simpl in H10; symmetry in H10; inv H10. 
    destruct K.
    destruct p.
    destruct h.
    destruct p.
    renames h0 to HR, z to b, h to HF.
    simpl in H16; inv H16.
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
      clear - H19.
      eapply lemmas.disj_sym in H19.
      eapply lemmas_ins.disj_merge_disj_sep in H19.
      destruct H19.
      eapply lemmas.disj_sym; eauto.
    }

    assert ((Mc ⊎ (MT ⊎ MemMap.set TaskCur (Some (Ptr (t, $ 0))) empM)) ⊥ M).
    { 
      rewrite <- H2; eauto.
    }

    rewrite H4 in H18.
    eapply LH__progress_HH_progress in H18; eauto.
    Focus 2.
    rewrite <- H2; eauto.

    destruct H18 as (Mc' & M'' & K' & idx' & HLM' & Hdisj1 & Hdisj2 & Hstep
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
  }
  {
    inv H2; tryfalse.
    inv H16.
    assert ((Cas pc = Some (c (cntrans i)) \/
             Cas pc = Some (c (cjumpl aexp rd)) \/
             Cas pc = Some (c (cbe f))) \/ Cas pc = Some (c (ccall f)) \/ Cas pc = Some (c cretl)).
    {
      clear - H20.
      repeat (destruct H20 as [H20 | H20]; eauto).
    }

    clear H20.
    destruct H2.
    {
      
    }
  }
Admitted.

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
    exists T' t0 K0 M' idx1 HP',
      (
        star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\
                    HP__ HP' (out v) (C, PrimSet, (T', t0, K0, M'))
      )
      /\
      wfCth idx1 (C, Cas) (C ⊎ Cas, (S', pc', npc')) (C, PrimSet, (T', t0, K0, M')) /\
      (
        forall t1 K1, (ThrdMap.set t0 None T') t1 = Some K1 ->
                      wfRdy (C, Cas) (C, PrimSet) t1 K1 
      ).
Proof.
Admitted.

Lemma wfCth_wfRdy_abort_preservation :
  forall idx C Cas S pc npc PrimSet T t K M Spec m,
    simImpsPrimSet Spec Cas PrimSet -> C ⊥ Cas -> 
    HProgSafe (C, PrimSet, (T, t, K, M)) ->
    wfCth idx (C, Cas) (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, (T, t, K, M)) ->
    (
      forall t' K', (ThrdMap.set t None T) t' = Some K' ->
                    wfRdy (C, Cas) (C, PrimSet) t' K' 
    ) ->
    ~ (exists LP' : LProg, LP__ (C ⊎ Cas, (S, pc, npc)) m LP') ->
    exists HP' : HProg, star_tau_step HP__ (C, PrimSet, (T, t, K, M)) HP' /\ ~ (exists (HP'': HProg) m', HP__ HP' m' HP'').
Proof.
Admitted.

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
    inv H4.
    eapply wfCth_wfRdy_tau_step_preservation in Hpreserve; eauto.
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
    destruct H4 as (HP' & HHstar_steps & HHstep).
    clear - H1 HHstar_steps HHstep.
    unfolds HProgSafe.
    eapply star_tau_step_impl_star_step in HHstar_steps.
    eapply H1 in HHstar_steps.
    tryfalse.
  }
Qed.
