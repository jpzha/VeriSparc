(** We define high-level Pseudo-SPARCv8 language in this File *)
Require Import Coqlib.
Require Import Maps.

Require Import Integers.
Require Import LibTactics.
Open Scope Z_scope.
Import ListNotations.

Require Import state.
Require Import language.
Require Import highlang.

(*+ The low-level Language  +*)
(* The low-level language is based on the SPARCv8 assembly defined in language.v  *)
Definition LProg : Type := XCodeHeap * (State * Word * Word).

Inductive opsave1 : RegFile * FrameList -> RegFile * FrameList -> Prop :=
| Opsave1 : forall R R' R'' F F' k k' fmo fml fmi fm1 fm2,
    get_R R cwp = Some (W k) -> k' = pre_cwp k ->
    fetch R = Some [fmo; fml; fmi] -> F = F' ++ [fm1; fm2] -> R' = set_window R fm1 fm2 fmo ->
    R'' = set_Rs R' [(Rpsr cwp, W k')] ->
    opsave1 (R, F) (R'', fml :: fmi :: F').

Inductive oprestore1 : RegFile * FrameList -> RegFile * FrameList -> Prop :=
| Oprestore1 : forall R R' R'' F F' k k' fmo fml fmi fm1 fm2,
    get_R R cwp = Some (W k) -> k' = post_cwp k -> 
    fetch R = Some [fmo; fml; fmi] -> F = fm1 :: fm2 :: F' -> R' = set_window R fmi fm1 fm2 ->
    R'' = set_Rs R' [(Rpsr cwp, W k')] ->
    oprestore1 (R, F) (R'', F' ++ [fmo; fml]).

Inductive opsave : RegName -> Val -> RegFile * FrameList -> RegFile * FrameList -> Prop :=
| Opsave : forall R R' R'' F F' k k' v v' rr fmo fml fmi fm1 fm2,
    get_R R cwp = Some (W k) -> get_R R Rwim = Some (W v) -> k' = pre_cwp k -> win_masked k' v = false ->
    fetch R = Some [fmo; fml; fmi] -> F = F' ++ [fm1; fm2] -> R' = set_window R fm1 fm2 fmo ->
    R'' = set_Rs R' [(Rpsr cwp, W k'); (rr, v')] ->
    opsave rr v' (R, F) (R'', fml :: fmi :: F').

Inductive oprestore : RegName -> Val -> RegFile * FrameList -> RegFile * FrameList -> Prop :=
| Oprestore : forall R R' R'' F F' k k' v v' rr fmo fml fmi fm1 fm2,
    get_R R cwp = Some (W k) -> get_R R Rwim = Some (W v) -> k' = post_cwp k -> win_masked k' v = false ->
    fetch R = Some [fmo; fml; fmi] -> F = fm1 :: fm2 :: F' -> R' = set_window R fmi fm1 fm2 ->
    R'' = set_Rs R' [(Rpsr cwp, W k'); (rr, v')] ->
    oprestore rr v' (R, F) (R'', F' ++ [fmo; fml]).

Fixpoint set_Ms M (vl : list (Address * Val)) :=
  match vl with
  | (l, v) :: vl =>
    set_Ms (MemMap.set l (Some v) M) vl
  | nil => M
  end.

Definition set_Mframe M (l0 l1 l2 l3 l4 l5 l6 l7 : Address) (fm : Frame) :=
  match fm with
  | consfm v0 v1 v2 v3 v4 v5 v6 v7 =>
    set_Ms M
           ((l0, v0) :: (l1, v1) :: (l2, v2) :: (l3, v3) :: (l4, v4) ::
                         (l5, v5) :: (l6, v6) :: (l7, v7) :: nil)
  end. 

Inductive win_overflow : Memory * RegFile * FrameList -> Memory * RegFile * FrameList -> Prop :=
| WinOverFlow : forall M M' M'' R R1 R2 R3 R4 R' F F1 F2 F3 F4 b fm1 fm2 fml fmi fmo w,
    opsave1 (R, F) (R1, F1) -> opsave1 (R1, F1) (R2, F2) ->
    get_R R r14 = Some (Ptr (b, $ 0)) -> 
    get_R R Rwim = Some (W (($ 1) <<ᵢ w)) ->
    fetch_frame M (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12)
                (b, $ 16) (b, $ 20) (b, $ 24) (b, $ 28) = Some fm1 ->
    fetch_frame M (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44)
                (b, $ 48) (b, $ 52) (b, $ 56) (b, $ 60) = Some fm2 ->
    fetch R2 = Some [fmo; fml; fmi] ->
    M' = set_Mframe M (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12)
                    (b, $ 16) (b, $ 20) (b, $ 24) (b, $ 28) fml ->
    M'' = set_Mframe M' (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44)
                     (b, $ 48) (b, $ 52) (b, $ 56) (b, $ 60) fmi ->
    oprestore1 (R2, F2) (R3, F3) -> oprestore1 (R3, F3) (R4, F4) ->
    set_R R4 Rwim (W (($ 1) <<ᵢ (pre_cwp w))) = R' ->
    win_overflow (M, R, F) (M', R', F4).

Inductive win_underflow : Memory * RegFile * FrameList -> Memory * RegFile * FrameList -> Prop :=
| WinUnderFlow : forall M R R1 R2 R3 R' F F1 F' b w fmo fml fmi fm1 fm2,
    oprestore1 (R, F) (R1, F1) ->
    get_R R r14 = Some (Ptr (b, $ 0)) ->
    get_R R Rwim = Some (W (($ 1) <<ᵢ w)) ->
    fetch_frame M (b, $ 0) (b, $ 4) (b, $ 8) (b, $ 12)
                (b, $ 16) (b, $ 20) (b, $ 24) (b, $ 28) = Some fm1 ->
    fetch_frame M (b, $ 32) (b, $ 36) (b, $ 40) (b, $ 44)
                (b, $ 48) (b, $ 52) (b, $ 56) (b, $ 60) = Some fm2 ->
    fetch R1 = Some [fmo; fml; fmi] ->
    set_window R1 fmi fm1 fm2 = R2 ->
    opsave1 (R2, F1) (R3, F') ->
    set_R R3 Rwim (W (($ 1) <<ᵢ (post_cwp w))) = R' ->
    win_underflow (M, R, F) (M, R', F').

Inductive LH__ : XCodeHeap -> State * Word * Word -> msg -> State * Word * Word -> Prop :=
| LNTrans : forall C i S S' pc npc,
    C pc = Some (c (cntrans i)) -> Q__ S (cntrans i) S' ->
    LH__ C (S, pc, npc) tau (S', npc, npc +ᵢ ($ 4))

| LJumpl : forall C M aexp rd R R' F D pc npc f,
    C pc = Some (c (cjumpl aexp rd)) ->
    eval_addrexp R aexp = Some (W f) -> word_aligned (W f) = true ->
    indom rd R -> set_R R rd (W pc) = R' ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M, (R', F), D), npc, f)

| LCall : forall C M (R R' : RegFile) F D pc npc f,
    C pc = Some (c (ccall f)) ->
    indom r15 R -> set_R R r15 (W pc) = R' ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M, (R', F), D), npc, f)

| LRetl : forall C M R F D pc npc f,
    C pc = Some (c cretl) ->
    get_R R r15 = Some (W f) ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M, (R, F), D), npc, f +ᵢ ($ 8))

| LBe_true : forall C M R F D pc npc f v,
    C pc = Some (c (cbe f)) ->
    get_R R z = Some (W v) -> v <> $ 0 ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M, (R, F), D), npc, f)

| LBe_false : forall C M R F D pc npc f,
    C pc = Some (c (cbe f)) ->
    get_R R z = Some (W $ 0) ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M, (R, F), D), npc, npc +ᵢ ($ 4))
         
(* We give operational semantics for Print, Psave and Prestore  *)
| LPrint : forall C M R F D pc npc v,
    C pc = Some print ->
    get_R R r8 = Some v ->
    LH__ C ((M, (R, F), D), pc, npc) (out v) ((M, (R, F), D), npc, npc +ᵢ ($ 4))

| LPsave_no_trap : forall M M' R R' D F F' b pc npc C w,
    C pc = Some (Psave w) ->
    Malloc M b ($ 0) w M' -> opsave r14 (Ptr (b, $ 0)) (R, F) (R', F') ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M', (R', F'), D), npc, npc +ᵢ ($ 4))
         
| LPsave_trap : forall M M' R R' F F' D pc npc C w k v,
    C pc = Some (Psave w) ->
    get_R R cwp = Some (W k) ->
    get_R R Rwim = Some (W v) ->
    win_masked (pre_cwp k) v = true ->
    win_overflow (M, R, F) (M', R', F') ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M', (R', F'), D), pc, npc)

| LPrestore_no_trap : forall M M' R R' F F' D pc npc b C,
    C pc = Some Prestore ->
    Mfree M b M' -> oprestore r0 (W ($ 0)) (R, F) (R', F') ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M', (R', F'), D), npc, npc +ᵢ ($ 4))

| LPrestore_trap : forall M M' R R' F F' D pc npc C w k v,
    C pc = Some (Psave w) ->
    get_R R cwp = Some (W k) ->
    get_R R Rwim = Some (W v) ->
    win_masked (post_cwp k) v = true ->
    win_overflow (M, R, F) (M', R', F') ->
    LH__ C ((M, (R, F), D), pc, npc) tau ((M', (R', F'), D), pc, npc).

Inductive LP__ : LProg -> msg -> LProg -> Prop :=
| LCstep : forall C LM LM' LR LR' LR'' D D' D'' F F' pc pc' npc npc' m,
    (LR', D') = exe_delay LR D ->
    LH__ C ((LM, (LR', F), D'), pc, npc) m ((LM', (LR'', F'), D''), pc', npc') ->
    LP__ (C, ((LM, (LR, F), D), pc, npc)) m (C, ((LM', (LR'', F'), D''), pc', npc')).
