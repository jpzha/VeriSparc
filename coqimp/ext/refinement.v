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

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope.

(*+ The Event Trace Refinement +*)
CoInductive Etr :=
| empEtr : Etr
| abortEtr : Etr
| outEtr : Val -> Etr -> Etr. 

Inductive star_tau_step {prog : Type} (step : prog -> msg -> prog -> Prop) :
  prog -> prog -> Prop :=
| zero_tau_step : forall p, star_tau_step step p p
| multi_tau_step : forall (p p' p'' : prog), step p tau p' -> star_tau_step step p' p''.

CoInductive Etrace {tprog} (step : tprog -> msg -> tprog -> Prop): tprog -> Etr -> Prop :=
| Etr_tau : forall P P',
    star_tau_step step P P' -> Etrace step P' empEtr -> Etrace step P empEtr
| Etr_abort : forall P P' m,
    star_tau_step step P P' -> (~ (exists P'', step P' m P'')) -> Etrace step P abortEtr
| Etr_event : forall P P' P'' v etr,
    star_tau_step step P P' -> step P' (out v) P'' ->
    Etrace step P'' etr -> Etrace step P (outEtr v etr).

Definition Etr_Refinement (LP : LProg) (HP : HProg) :=
  forall B, Etrace LP__ LP B -> Etrace HP__ HP B.

(*+ State Relation +*)
Definition TaskCur := (0%Z, $0).

Definition ctxfm R (F F' : FrameList) : Prop :=
  exists w n F2,
    get_R R cwp = Some (W w) /\ get_R R Rwim = Some (W (($ 1) <<ᵢ n)) /\ w <> n /\
    F = F' ++ F2 /\ ($ 0) <=ᵤᵢ w <=ᵤᵢ ($ 7) /\ ($ 0) <=ᵤᵢ n <=ᵤᵢ ($ 7) /\
    length F' = Nat.mul 2%nat (Z.to_nat (Int.unsigned ((N +ᵢ n -ᵢ w -ᵢ ($ 1)) modu N))).

Definition Rinj (LR : RegFile) (HR : HRegFile) :=
  (forall rr : GenReg, exists v, LR rr = Some v /\ HR rr = Some v) /\
  (forall sr : SpReg, exists w, LR sr = Some (W w)) /\ (exists w, LR cwp = Some (W w)) /\
  (exists w, LR n = Some w /\ HR fn = Some w) /\ (exists w, LR z = Some w /\ HR fz = Some w).  
  
(** Current Thread State Relation *)
Inductive curTRel : Memory * RState -> Tid * tlocst -> Prop :=
| Cur_TRel : forall M Mctx Mk,

Parameter rdyTsRel : Memory -> ThrdPool -> Prop.

(** Whole Program State Relation *)
Inductive wp_stateRel : State -> HState -> Prop :=
| Wp_stateRel : forall (M Mc MT M' : Memory) Q T t K M',
    Mc ⊎ MT ⊎ (MemMap.set TaskCur (Some (Ptr (t, $0))) empM) ⊎ M' = M ->
    Mc ⊥ MT -> (Mc ⊎ MT) ⊥ (MemMap.set TaskCur (Some (Ptr (t, $0))) empM) ->
    (Mc ⊎ MT ⊎ (MemMap.set TaskCur (Some (Ptr (t, $0))) empM)) ⊥ M' ->
    curTRel (Mc, Q) (t, K) ->
    rdyTsRel MT (ThrdMap.set t None T) ->
    wp_stateRel (M, Q, nil) (T, t, K, M').


  



    
