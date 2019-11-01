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

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(*+ Relational Assertion Language +*) Print ap.
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
| RAtoken : Word -> relasrt
| RATimeReduce : relasrt -> relasrt
| RAtrue : relasrt
| RAfalse : relasrt
| RAconj : relasrt -> relasrt -> relasrt
| RAdisj : relasrt -> relasrt -> relasrt
| RAstar : relasrt -> relasrt -> relasrt
| RAforall : forall ty : Type, (ty -> relasrt) -> relasrt
| RAexists : forall ty : Type, (ty -> relasrt) -> relasrt.

Notation "t ⇝c K" := (RAcur t K) (at level 20).
Notation "t ⇝r K" := (RArdy t K) (at level 20). 

(** relational state *)
Definition RelState : Type := State * HState * primcom * Word.

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

(** Semantics of relational assertion language *) 
Fixpoint relsat (rls : RelState) (P : relasrt) {struct P} : Prop :=
  match rls with
  | (s, hs, A, w) =>
    match P with
    | RAreg hrn v => exists t K, relsat (s, hs, A, w) (t ⇝c K) /\ 
      



