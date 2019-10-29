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

| LPrint : forall C M R F D pc npc v,
    C pc = Some print ->
    get_R R r8 = Some v ->
    LH__ C ((M, (R, F), D), pc, npc) (out v) ((M, (R, F), D), npc, npc +ᵢ ($ 4)).
         

Inductive LP__ : LProg -> msg -> LProg -> Prop :=
| LCstep : forall C LM LM' LR LR' LR'' D D' D'' F F' pc pc' npc npc' m,
    (LR', D') = exe_delay LR D ->
    LH__ C ((LM, (LR', F), D'), pc, npc) m ((LM', (LR'', F'), D''), pc', npc') ->
    LP__ (C, ((LM, (LR, F), D), pc, npc)) m (C, ((LM', (LR'', F'), D''), pc', npc')).
