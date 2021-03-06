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

(*+ The Event Trace Refinement +*)
CoInductive Etr :=
| empEtr : Etr
| abortEtr : Etr
| outEtr : Val -> Etr -> Etr. 

Inductive star_tau_step {prog : Type} (step : prog -> msg -> prog -> Prop) :
  prog -> prog -> Prop :=
| zero_tau_step : forall p, star_tau_step step p p
| multi_tau_step : forall (p p' p'' : prog), star_tau_step step p p' -> step p' tau p'' ->
                                             star_tau_step step p p''.

CoInductive Etrace {tprog} (step : tprog -> msg -> tprog -> Prop): tprog -> Etr -> Prop :=
| Etr_tau : forall P P' P'',
    star_tau_step step P P' -> step P' tau P'' ->
    Etrace step P'' empEtr -> Etrace step P empEtr
| Etr_abort : forall P P',
    star_tau_step step P P' -> (~ (exists P'' m, step P' m P'')) -> Etrace step P abortEtr
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
    length F' = Nat.mul 2%nat (Z.to_nat (Int.unsigned ((N +ᵢ n -ᵢ w -ᵢ ($ 1)) modu N))) /\ length F = 13.

Definition Rinj (LR : RegFile) (HR : HRegFile) :=
  (forall rr : GenReg, exists v, LR rr = Some v /\ HR rr = Some v) /\
  (forall sr : SpReg, exists w, LR sr = Some (W w)) /\ (exists w, LR cwp = Some (W w)) /\
  (exists w, LR n = Some w /\ HR fn = Some w) /\ (exists w, LR z = Some w /\ HR fz = Some w).

Parameter ctx_s ctx_e : int.

Definition DomCtx (l : Address) (t : Tid) (b : Z) :=
  match l with
  | (b', o') => if Z.eq_dec t b' then
                 (* A location marks the name of thread and a set of locations saving context *)
                 o' = $ 0 \/ (int_leu ctx_s o' = true /\ Int.ltu o' ctx_e = true)
               else
                 if Z.eq_dec b b' then
                   int_leu ($ 0) o' = true /\ Int.ltu o' ($64) = true /\ Int.eq (o' modu ($ 4)) ($ 0) = true
                 else
                   False
  end.

Definition set_Mframe' (b : Z) (ofs : Word) (fm : Frame) :=
  set_Mframe empM (b, ofs) (b, ofs +ᵢ ($ 4)) (b, ofs +ᵢ ($ 8)) (b, ofs +ᵢ ($ 12))
             (b, ofs +ᵢ ($ 16)) (b, ofs +ᵢ ($ 20)) (b, ofs +ᵢ ($ 24)) (b, ofs +ᵢ ($ 28)) fm.

Inductive stkRel : Z * FrameList * Memory -> HFrameList -> Prop :=
| LFnilHFnil : forall b, stkRel (b, nil, empM) nil

| LFnilHFcons : forall fm1 fm2 HF M M' b b',
    M = (set_Mframe' b ($ 0) fm1) ⊎ (set_Mframe' b ($ 32) fm2) ⊎ M' ->
    (set_Mframe' b ($ 0) fm1) ⊥ (set_Mframe' b ($ 32) fm2) ->
    ((set_Mframe' b ($ 0) fm1) ⊎ (set_Mframe' b ($ 32) fm2)) ⊥ M' ->
    get_frame_nth fm2 6 = Some (Ptr (b', $ 0)) ->
    stkRel (b', nil, M') HF ->
    stkRel (b, nil, M) ((b, fm1, fm2) :: HF)
           
| LFconsHFcons : forall fm1 fm2 F HF M M' b b' fm1' fm2',
    M = (set_Mframe' b ($ 0) fm1') ⊎ (set_Mframe' b ($ 32) fm2') ⊎ M' ->
    (set_Mframe' b ($ 0) fm1') ⊥ (set_Mframe' b ($ 32) fm2') ->
    ((set_Mframe' b ($ 0) fm1') ⊎ (set_Mframe' b ($ 32) fm2')) ⊥ M' ->
    get_frame_nth fm2 6 = Some (Ptr (b', $ 0)) ->
    stkRel (b', F, M') HF ->
    stkRel (b, fm1 :: fm2 :: F, M) ((b, fm1, fm2) :: HF).

(** Current Thread State Relation *)
Inductive curTRel : Memory * RState -> Tid * tlocst -> Prop :=
| Cur_TRel : forall M Mctx Mk R F F' t HR b b' HF pc npc,
    (M = Mctx ⊎ Mk /\ Mctx ⊥ Mk) -> (forall l, (indom l Mctx <-> DomCtx l t b) /\ t <> b) ->
    ctxfm R F F' -> stkRel (b', F', Mk) HF -> Rinj R HR ->
    curTRel (M, (R, F)) (t, ((HR, b, HF), pc, npc)).

(** Ready Thread State Relation *)
Inductive rdyTsRel (restoreQ : Memory -> RState -> Prop) : Memory -> ThrdPool -> Prop :=
| thrdRel : forall t K M Q,
    restoreQ M Q -> curTRel (M, Q) (t, K) ->
    rdyTsRel restoreQ M (ThrdMap.set t (Some K) EmpThrdPool)

| thrdsRel : forall T1 T2 T M1 M2 M,
    rdyTsRel restoreQ M1 T1 -> rdyTsRel restoreQ M2 T1 ->
    M1 ⊥ M2 -> T1 ⊥ T2 -> M = M1 ⊎ M2 -> T = T1 ⊎ T2 ->
    rdyTsRel restoreQ M T.

(** Whole Program State Relation *)
Inductive wp_stateRel (restoreQ : Memory -> RState -> Prop) : State -> HState -> Prop :=
| Wp_stateRel : forall (M Mc MT M' : Memory) Q T t K M',
    Mc ⊎ MT ⊎ (MemMap.set TaskCur (Some (Ptr (t, $0))) empM) ⊎ M' = M ->
    Mc ⊥ MT -> (Mc ⊎ MT) ⊥ (MemMap.set TaskCur (Some (Ptr (t, $0))) empM) ->
    (Mc ⊎ MT ⊎ (MemMap.set TaskCur (Some (Ptr (t, $0))) empM)) ⊥ M' ->
    curTRel (Mc, Q) (t, K) ->
    rdyTsRel restoreQ MT (ThrdMap.set t None T) ->
    wp_stateRel restoreQ (M, Q, nil) (T, t, K, M').

Definition get_Hs_pcont (HS : HState) :=
  match HS with
  | (T, t, K, M) =>
    match K with
    | (HQ, pc, npc) => (pc, npc)
    end
  end.

(*+ Primitive Correctness +*)
Definition correct (Cas : XCodeHeap) (PrimSet : apSet) (restoreQ : Memory -> RState -> Prop) :=
  forall C S HS pc npc,
    wp_stateRel restoreQ S HS -> HProgSafe ((C, PrimSet), HS) ->
    get_Hs_pcont HS = (pc, npc) -> C ⊥ Cas ->
    Etr_Refinement (C ⊎ Cas, (S, pc, npc)) ((C, PrimSet), HS).


  



    
