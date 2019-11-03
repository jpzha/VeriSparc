(** We define high-level Pseudo-SPARCv8 language in this File *)
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

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(*+ Relational Assertion Language +*)
Inductive primcom :=
| Pm : ap -> list Val -> primcom | Pdone : primcom.

(** Syntax of relational assertion language *) 
Inductive relasrt : Type :=
| RAreg : HRegName -> Val -> relasrt
| RAmapsto : Address -> Val -> relasrt
| RAEmp : relasrt
| RAcur : Tid -> tlocst -> relasrt
| RArdy : Tid -> tlocst -> relasrt
| RAlst : asrt -> relasrt
| RAprim : primcom -> relasrt
| RAtoken : nat -> relasrt
| RATimeReduce : relasrt -> relasrt
| RAtrue : relasrt
| RAfalse : relasrt
| RAconj : relasrt -> relasrt -> relasrt
| RAdisj : relasrt -> relasrt -> relasrt
| RAstar : relasrt -> relasrt -> relasrt
| RAforall (ty : Type) (P : ty -> relasrt)
| RAexists (ty : Type) (P : ty -> relasrt).

Notation "t ⇝c K" := (RAcur t K) (at level 20).
Notation "t ⇝r K" := (RArdy t K) (at level 20).
Notation "P ⤈" := (RATimeReduce P) (at level 20).
Infix "⋆" := RAstar (at level 31, right associativity).

(** relational state *)
Definition RelState : Type := State * HState * primcom * nat.

Definition hstate_union (hs1 hs2 hs : HState) :=
  match hs1, hs2 with
  | (T1, t1, K1, M1), (T2, t2, K2, M2) =>
    disjoint T1 T2 /\ disjoint M1 M2 /\ hs = (T1 ⊎ T2, t1, K1, M1 ⊎ M2) /\ t1 = t2 /\ K1 = K2
  end.

(** high-level primcom transition *)
Inductive exec_prim : primcom * HState -> primcom * HState -> Prop :=
| PrimExec : forall (prim : ap) lv hs hs',
    prim lv hs hs' -> exec_prim (Pm prim lv, hs) (Pdone, hs')
| PdoneExec : forall hs, exec_prim (Pdone, hs) (Pdone, hs).

(* get register file from current thread's local state *)
Definition getHR_K (K : tlocst) :=
  match K with
  | (Q, pc, npc) => match Q with
                   | (HR, b, HF) => HR
                   end
  end.

(* get register file from high-level state *)
Definition getHR (hs : HState) :=
  match hs with
  | (T, t, K, M) => getHR_K K
  end.

(* get memory from high-level state *)
Definition getHM (hs : HState) :=
  match hs with
  | (T, t, K, M) => M
  end.

(* get ThreadPool from high-level state *)
Definition getHThrdPool (hs : HState) :=
  match hs with
  | (T, t, K, M) => T
  end.

(* get HRstate from high-level state *)
Definition getHQ (hs : HState) :=
  match hs with
  | (T, t, K, M) => match K with
                   | (HQ, pc, npc) => HQ
                   end
  end.

(* get low state from relational state *)
Definition get_ls_rls (rls : RelState) :=
  match rls with
  | (s, hs, A, w) => s
  end.

Definition relsatEmp (rls : RelState) :=
  match rls with
  | (s, hs, A, w) => 
    match hs with
    | (T, t, K, M) => M = empM /\ T = EmpThrdPool /\ sat s Aemp
    end
  end.

Definition relsatCurSt (rls : RelState) (t' : Tid) (K' : tlocst) :=
  match rls with
  | (s, hs, A, w) =>
    match hs with
    | (T, t, K, M) => t = t' /\ K = K' /\ relsatEmp (s, hs, A, w)
    end
  end.

Definition relsatRdySt (rls : RelState) (t' : Tid) (K' : tlocst) :=
  match rls with
  | (s, hs, A, w) =>
    match hs with
    | (T, t, K, M) => T = ThrdMap.set t' (Some K') EmpThrdPool /\ M = empM /\ sat s Aemp
    end
  end.

(** Semantics of relational assertion language *)
Fixpoint relsat (rls : RelState) (P : relasrt) {struct P} : Prop :=
  match rls with
  | (s, hs, A, w) =>
    match P with
    | RAreg hrn v => exists t K, relsatCurSt (s, hs, A, w) t K /\ (getHR_K K) hrn = Some v
    | RAmapsto l v => getHM hs = MemMap.set l (Some v) empM /\
                     getHThrdPool hs = EmpThrdPool /\ sat s Aemp
    | RAEmp => relsatEmp (s, hs, A, w)
    | RAcur t K => relsatCurSt (s, hs, A, w) t K
    | RArdy t K => relsatRdySt (s, hs, A, w) t K
    | RAlst p => sat s p /\ getHM hs = empM /\ getHThrdPool hs = EmpThrdPool 
    | RAprim A' => A = A' /\ relsatEmp (s, hs, A, w)
    | RAtoken num => (num <= w)%nat /\ relsatEmp (s, hs, A, w)
    | RATimeReduce P' => exists R D, exe_delay R D = (getregs s, getdlyls s) /\
                               relsat ((upddlyls (updregs s R) D), hs, A, w) P'
    | RAtrue => True
    | RAfalse => False
    | RAconj P1 P2 => relsat (s, hs, A, w) P1 /\ relsat (s, hs, A, w) P2
    | RAdisj P1 P2 => relsat (s, hs, A, w) P1 /\ relsat (s, hs, A, w) P2
    | RAstar P1 P2 => exists hs1 hs2 s1 s2 w1 w2, hstate_union hs1 hs2 hs /\ state_union s1 s2 s /\ (w = w1 + w1)%nat /\
                                            relsat (s1, hs1, A, w1) P1 /\ relsat (s2, hs2, A, w2) P2
    | RAforall ty P' => forall (x : ty), relsat (s, hs, A, w) (P' x)
    | RAexists ty P' => exists (x : ty), relsat (s, hs, A, w) (P' x)
    end
  end.

Notation "rls '||=' P" := (relsat rls P) (at level 34, no associativity).
Notation "P ⇒ Q" :=
  (forall rls, rls ||= P -> rls ||= Q)
    (at level 34, right associativity).
Notation "P ⇔ Q" :=
  (forall rls, rls ||= P <-> rls ||= Q)
    (at level 34, right associativity).

(*+ Inference Rules for Refinement Verification +*)
Inductive Logic_var : Type :=
| logic_llvar : logicvar -> Logic_var
| logic_hreg : HRegName -> Logic_var
| logic_hfmls : HFrameList -> Logic_var.

Definition Fpre := list Logic_var -> relasrt.
Definition Fpost := list Logic_var -> relasrt.
Definition Fspec : Type := Fpre * Fpost.
Definition Funspec := Word -> option Fspec.

Definition ImplyPrim (P P' : relasrt) :=
  forall s hs A w, (s, hs, A, w) ||= P ->
              (exists hs' A' w', exec_prim (A, hs) (A', hs') /\ (s, hs', A', w') ||= P').
Notation "P ⭆ P'" := (ImplyPrim P P') (at level 34, right associativity).

Definition FretSta (P1 P2 : relasrt) :=
  forall rls rls', rls ||= P1 -> rls' ||= P2 ->
          (exists f, (getregs (get_ls_rls rls)) r15 = Some (W f) /\
                (getregs (get_ls_rls rls')) r15 = Some (W f)).

(** well-formed instruction *)
Inductive rel_wf_ins : relasrt -> ins -> relasrt -> Prop :=
| Rel_wf_ins : forall P P' Pr p p' i,
    P ⇒ (RAlst p) ⋆ Pr -> wf_ins p i p' -> RAlst p ⋆ Pr ⇒ P' ->
    rel_wf_ins P i P'.

Notation " '⊩' '{{' P '}}' i '{{' Q '}}' " := (rel_wf_ins P i Q) (at level 50).

(** well-formed instruction sequence *) Print LProg. Print XCodeHeap. Print Command.
Inductive rel_wf_seq : Funspec -> relasrt -> Label -> InsSeq -> relasrt -> Prop :=
| rel_seq_rule : forall f i I P P' Q Spec,
    ⊩ {{ P ⤈ }} i {{ P' }} -> rel_wf_seq Spec P' (f +ᵢ ($ 4)) I Q ->
    rel_wf_seq Spec P f (i ;; I) Q

| rel_call_rule : forall f f' i I P P1 P2 P' Q Pr Fp Fq (L : list Logic_var) v (Spec : Funspec),
    Spec f' = Some (Fp, Fq) ->
    (P ⤈) ⇒ (RAlst (r15 |=> v)) ⋆ P1 ->
    ⊩ {{ ((RAlst (r15 |=> W f)) ⋆ P1) ⤈ }} i {{ P2 }} ->
    P2 ⇒ Fp L ⋆ Pr -> Fq L ⋆ Pr ⇒ P'-> Fq L ⇒ RAlst ((Or r15) ==ₑ W f) ->
    rel_wf_seq Spec P' (f +ᵢ ($ 8)) I Q ->
    rel_wf_seq Spec P f (call f' # i # I) Q

| rel_retl_rule : forall P P' Q f i Spec,
    ⊩ {{ (P ⤈) ⤈ }} i {{ P' }} -> P' ⇒ Q -> FretSta ((P ⤈) ⤈) P' ->
    rel_wf_seq Spec P f (retl ;; i) Q

| rel_J_rule : forall P P1 P' Q (r1 : GenReg) f f' aexp Spec Fp Fq L v Pr i,
    (P ⤈) ⇒ RAlst (aexp ==ₓ W f') -> Spec f' = Some (Fp, Fq) ->
    (P ⤈) ⇒ RAlst (r1 |=> v) ⋆ P1 -> ⊩ {{ (RAlst (r1 |=> W f) ⋆ P1) ⤈ }} i {{ P' }} ->
    P' ⇒ Fp L ⋆ Pr -> Fq L ⋆ Pr ⇒ Q ->
    rel_wf_seq Spec P f (consJ aexp r1 i) Q

| rel_Be_rule : forall P P' Q bv Spec L f f' Pr i I Fp Fq,
    Spec f' = Some (Fp, Fq) ->
    P ⇒ RAlst (z |=> W bv) ⋆ RAtrue -> ⊩ {{ P ⤈⤈ }} i {{ P' }} ->
    (bv =ᵢ ($ 0) = true -> rel_wf_seq Spec P' (f +ᵢ ($ 8)) I Q) ->
    ((bv =ᵢ ($ 0) = false) -> ((P' ⇒ Fp L ⋆ Pr) /\ (Fq L ⋆ Pr ⇒ Q))) ->
    rel_wf_seq Spec P f (be f' # i # I) Q

| rel_ABSCSQ_rule : forall P P' Q' Q f I Spec,
    P ⭆ P' -> rel_wf_seq Spec P' f I Q' -> Q' ⭆ Q ->
    rel_wf_seq Spec P f I Q.

Notation " Spec '⊩' '{{' P '}}' f '#' I '{{' Q '}}' " :=
  (rel_wf_seq Spec P f I Q) (at level 55).

(* basic ext code block constructor *)
Inductive LookupXC : XCodeHeap -> Label -> InsSeq -> Prop :=
| XlookupNoTransIns :
    forall C f I i,
      C f = Some (c (cntrans i)) -> LookupXC C (f +ᵢ ($ 4)) I ->
      LookupXC C f (i ;; I)
| XlookupJmp :
    forall C f i aexp rr,
      C f = Some (c (cjumpl aexp rr)) ->
      C (f +ᵢ ($ 4)) = Some (c (cntrans i)) ->
      LookupXC C f (consJ aexp rr i)
| XlookupRetl :
    forall C f i,
      C f = Some (c (cretl)) -> C (f +ᵢ ($ 4)) = Some (c (cntrans i)) ->
      LookupXC C f (retl ;; i)
| XlookupCall :
    forall C f f' i I,
      C f = Some (c (ccall f')) -> C (f +ᵢ ($ 4)) = Some (c (cntrans i)) ->
      LookupXC C (f +ᵢ ($ 8)) I ->
      LookupXC C f (call f' # i # I)
| XlookupBe :
    forall C f f' i I,
      C f = Some (c (cbe f')) -> C (f +ᵢ ($ 4)) = Some (c (cntrans i)) ->
      LookupXC C (f +ᵢ ($ 8)) I ->
      LookupXC C f (be f' # i # I).

(** Well-formed Code Heap *)
Definition rel_wf_cdhp (Spec : Funspec) (C : XCodeHeap) :=
  forall f L fp fq,
    Spec f = Some (fp, fq) ->
    exists I, LookupXC C f I /\ rel_wf_seq Spec (fp L) f I (fq L).

(** Invariant *)
Definition INV (A : primcom) (w : nat) (lv : list Val) (rls : RelState) :=
  match rls with
  | (s, hs, A, w) =>
    wp_stateRel s hs /\ (exists hs', exec_prim (A, hs) (Pdone, hs')) /\ args (getHQ hs) (getHM hs) lv
  end. 

(** Well-formed Spec *)  
Inductive wdSpec : Fpre -> Fpost -> ap -> Prop :=
| consWdSpec : forall Fp Fq (hprim : ap),
    (
      forall lv hs hs' (f : Word), hprim lv hs hs' -> (getHR hs' r15 = Some (W f)) ->
                     get_Hs_pcont hs' = (f +ᵢ ($ 8), f +ᵢ ($ 12))
    ) ->
    (
      forall lv (hs1 hs1' hs_r hs hs': HState), hprim lv hs1 hs1' -> hstate_union hs1 hs_r hs ->
                          (hprim lv hs hs' /\ hstate_union hs1' hs_r hs')
    ) ->
    (
      forall lv rls rls', exists L num Pr,
        (INV (Pm hprim lv) num lv rls -> rls ||= (Fp L) ⋆ Pr) /\
        (rls' ||= (Fq L) ⋆ Pr -> exists num' lv', INV Pdone num' lv' rls')
    ) ->
    wdSpec Fp Fq hprim.

(** Well-formed Primitive *)
Definition rel_wf_prim (Spec : Funspec) (C : XCodeHeap) (PrimSet : apSet) :=
  exists Speci, rel_wf_cdhp Speci C /\
           (forall f, indom f C ->
                 (exists L Fp Fq hprim I, Spec f = Some (Fp, Fq) /\ PrimSet f = Some hprim /\ LookupXC C f I
                                   /\ wdSpec Fq Fq hprim /\ rel_wf_seq Speci (Fp L) f I (Fq L))).

(*+ Logic Soundness +*)

(** soundness of instruction rule *)
Definition rel_ins_sound P Q i :=
  forall s sh A w,
    (s, sh, A, w) ||= P -> (exists s', (Q__ s (cntrans i) s') /\ (s', sh, A, w) ||= Q).




                 

