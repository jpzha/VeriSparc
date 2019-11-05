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
Require Import highlang.
Require Import lowlang.
Require Import logic.
Require Import reg_lemma.
Require Import soundness.
Require Import refinement.
Require Import rellogic.

Set Asymmetric Patterns.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope code_scope.
Open Scope mem_scope. Print LH__.

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
        HH__ C (HQ, pc, npc, HM) (Callevt pc lv) (HQ, pc, npc, HM)
    ) ->
    wfHPrimExec C A HS.

(** Well-formed Current Thread *)
Inductive wfCth : Index -> LProg -> HProg -> Prop :=
| clt_wfCth : forall C Cas S HS pc npc PrimSet idx,
    C ⊥ Cas -> indom pc C -> wp_stateRel S HS -> wfIndex C S pc idx -> 
    get_Hs_pcont HS = (pc, npc) ->
    wfCth idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS)

| prim_wfCth : forall C Cas Sc HSc S HS Sr HSr w Q Pr A pc npc PrimSet idx k,
    C ⊥ Cas -> state_union Sc Sr S -> hstate_union HSc HSr HS ->
    rel_safety k idx (Cas, Sc, pc, npc) (A, HSc) Q -> (Sr, HSr, A, w) ||= Pr -> wfHPrimExec C A HS ->
    (
      forall S' HS' w' f, (S', HS', Pdone, w') ||= Q ⋆ Pr -> getregs S' r15 = Some (W f) ->
                          HProgSafe (C, PrimSet, HS') ->
                        exists idx_j, wfCth idx_j (C ⊎ Cas, (S', f +ᵢ ($ 8), f +ᵢ ($ 12))) (C, PrimSet, HS')
    ) ->
    wfCth idx (C ⊎ Cas, (S, pc, npc)) (C, PrimSet, HS).

(* Well-formed Ready Thread *)
Inductive wfRdy : XCodeHeap -> XCodeHeap * apSet -> Tid -> tlocst -> Prop :=
| cons_wfRdy : forall S HS t K PrimSet C C',
    (
      forall f T HM pc npc, 
        wp_stateRel S HS -> HS = (T, t, K, HM) -> HProgSafe (C, PrimSet, HS) ->
        getregs S r15 = Some (W f) -> pc = f +ᵢ ($ 8) -> npc = f +ᵢ ($ 12) ->
        exists idx, wfCth idx (C, (S, pc, npc)) (C, PrimSet, HS)
    ) ->
    wfRdy C (C', PrimSet) t K.

(* Compositionality Proof *)
Lemma wfCth_wfRdy_imply_wpsim : 
