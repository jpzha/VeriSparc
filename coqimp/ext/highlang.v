(** We define high-level Pseudo-SPARCv8 language in this File *)
Require Import Coqlib.
Require Import Maps.

Require Import Integers.
Require Import LibTactics.
Open Scope Z_scope.
Import ListNotations.

Require Import state.
Require Import language.

(** Command : expanded the original command with Psave w, Prestore, print *)
Inductive Command :=
| c : command -> Command
| Psave : Word -> Command
| Prestore : Command
| print : Command. 

(** The high-level msg : tau | out(v) | call(f, list v) *)
Inductive msg :=
| tau : msg
| out : Val -> msg
| Callevt : Word -> list Val -> msg.

(** The Code heap *)
Definition XCodeHeap := CodeMap.t (option Command).

(*+ High-level Program State +*)

(*! Thread Id !*)
Definition Tid := Z.

(*! Thread Local State !*)
(* High-level RegName *)
Inductive HRegName :=
| hRr : GenReg -> HRegName
| fn : HRegName
| fz : HRegName.

Coercion hRr : GenReg >-> HRegName.

(* High-level Register File *)
Lemma HRegName_eq : forall (x y : HRegName),
    {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

Module HRegNameEq.
  Definition t := HRegName.
  Definition eq := HRegName_eq.
End HRegNameEq.

Module HRegMap := EMap(HRegNameEq).
Definition HRegFile := HRegMap.t (option Val).
Definition HEmpRFile : HRegFile := fun _ => None.

(* High-level Frame list *)
Definition HFrame : Type := Z * Frame * Frame.
Definition HFrameList := list HFrame.

(* High-level Rstate *)
Definition HRstate : Type := HRegFile * Z * HFrameList.

(* Thread local state *)
Definition tlocst : Type := HRstate * Word * Word.

(*! Thread Pool !*)
Module TidEq.
  Definition t := Tid.
  Definition eq := Z.eq_dec.
End TidEq.

Module ThrdMap := EMap(TidEq).
Definition ThrdPool := ThrdMap.t (option tlocst).
Definition EmpThrdPool : ThrdPool := fun _ => None.

(*! High-level State !*) 
Definition HState : Type := ThrdPool * Tid * tlocst * Memory.

(*! Abstract Assembly Primitive Set !*)
Definition ap := list Val -> HState -> HState -> Prop.
Definition apSet := CodeMap.t (option ap).

(*! High-level Code  !*) 
Definition HCode : Type := XCodeHeap * apSet.

(*! High-level Program !*)
Definition HProg : Type := HCode * HState.

(*+ Operational Semantics for High-level Program +*)
Definition get_HR (HR : HRegFile) (hrn : HRegName) :=
  match (HR hrn) with
  | Some v => match hrn with
             | hRr r0 => Some (W ($ 0))
             | _ => Some v
             end
  | None => None
  end.

Definition Heval_opexp (HR : HRegFile) (o : OpExp) :=
  match o with
  | Or r => get_HR HR (hRr r)
  | Ow w =>
    if andb (($-4096) <=ᵢ w) (w <=ᵢ ($4095)) then
      Some (W w)
    else
      None
  end.

Definition Heval_addrexp (HR : HRegFile) (a : AddrExp) :=
  match a with
  | Ao o => Heval_opexp HR o
  | Aro r o =>
    match get_HR HR (hRr r) with
    | Some v1 =>
      match (Heval_opexp HR o) with
      | Some v2 => val_add v1 v2
      | None => None
      end 
    | None => None
    end
  end.

Definition set_HR :=
  fun HR hrn (v : Val) => if is_indom hrn HR then HRegMap.set hrn (Some v) HR else HR.

Fixpoint set_HRs HR (vl : list (HRegName * Val)) : HRegFile :=
  match vl with
  | [] => HR
  | (hrr, v) :: vl0 => set_HRs (set_HR HR hrr v) vl0
  end.

(** Memory fresh *)
Definition Mfresh (b : Z) (M : Memory) := forall o, ~ indom (b, o) M.

(** Memory alloc *) 
Definition Malloc (M : Memory) (b : Z) (l h : Word) (M' : Memory) :=
  Mfresh b M /\ l <ᵤᵢ h /\ 
  (forall b' o', (b <> b' /\ M (b', o') = M' (b', o'))
            \/ (b = b' /\ if int_leu l o' && Int.ltu o' h then
                            (exists v, M' (b', o') = Some v)
                          else M'(b', o') = M(b', o'))).

(** Memory free *)
Definition Mfree (M : Memory) (b : Z) : Memory :=
  fun l => match l with
           | (b', o') => if Z.eq_dec b b' then None else M (b', o')
           end.

Axiom finite_memory : forall M : Memory, exists b, Mfresh b M.

Definition Hfetch HR :=
  match fetch_frame HR r8 r9 r10 r11 r12 r13 r14 r15 with
  | Some fmo =>
    match fetch_frame HR r16 r17 r18 r19 r20 r21 r22 r23 with
    | Some fml =>
      match fetch_frame HR r24 r25 r26 r27 r28 r29 r30 r31 with
      | Some fmi => Some [fmo; fml; fmi]
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Definition set_Hframe (HR : HRegFile) (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) (fm : Frame) :=
  match fm with
  | consfm v0 v1 v2 v3 v4 v5 v6 v7 =>
    set_HRs HR [(hRr rr0, v0); (hRr rr1, v1);
                  (hRr rr2, v2); (hRr rr3, v3); (hRr rr4, v4);
                    (hRr rr5, v5); (hRr rr6, v6); (hRr rr7, v7)]
  end.

Definition set_Hwindow (HR : HRegFile) (fm1 fm2 fm3 : Frame) :=
  let HR1 := set_Hframe HR r8 r9 r10 r11 r12 r13 r14 r15 fm1 in
  let HR2 := set_Hframe HR1 r16 r17 r18 r19 r20 r21 r22 r23 fm2 in
  set_Hframe HR2 r24 r25 r26 r27 r28 r29 r30 r31 fm3.

Inductive HQ__ : Memory * HRstate -> Command -> Memory * HRstate -> Prop :=
| HLd_step : forall aexp (ri : GenReg) (M : Memory) HR HR' HF addr v b,
    Heval_addrexp HR aexp = Some (Ptr addr) ->
    word_aligned (Ptr addr) = true ->
    M addr = Some v ->
    indom ri HR -> set_HR HR ri v = HR' ->
    HQ__ (M, (HR, b, HF)) (c (cntrans (ld aexp ri))) (M, (HR', b, HF))

| HST_step : forall aexp (ri : GenReg) (M M' : Memory) HR HF addr v b,
    Heval_addrexp HR aexp = Some (Ptr addr) ->
    word_aligned (Ptr addr) = true ->
    get_HR HR ri = Some v ->
    indom addr M -> MemMap.set addr (Some v) M = M' ->
    HQ__ (M, (HR, b, HF)) (c (cntrans (st ri aexp))) (M', (HR, b, HF))

| HNop_step : forall M HR b HF,
    HQ__ (M, (HR, b, HF)) (c (cntrans nop)) (M, (HR, b, HF))

| HAdd_step : forall M HR HR' oexp (rs rd : GenReg) (v1 v2 v : Val) b HF,
    get_HR HR rs = Some v1 ->
    Heval_opexp HR oexp = Some v2 ->
    indom rd HR -> set_HR HR rd v = HR' -> val_add v1 v2 = Some v ->
    HQ__ (M, (HR, b, HF)) (c (cntrans (add rs oexp rd))) (M, (HR', b, HF))

| HSub_step : forall M HR HR' oexp (rs rd : GenReg) (v1 v2 v : Val) b HF,
    get_HR HR rs = Some v1 ->
    Heval_opexp HR oexp = Some v2 ->
    indom rd HR -> set_HR HR rd v = HR' -> val_sub v1 v2 = Some v ->
    HQ__ (M, (HR, b, HF)) (c (cntrans (sub rs oexp rd))) (M, (HR', b, HF))

| HSubcc_step : forall M HR HR' oexp (rs rd : GenReg) (v1 v2 v : Word) b HF,
    get_HR HR rs = Some (W v1) ->
    Heval_opexp HR oexp = Some (W v2) ->
    indom rd HR -> indom fn HR -> indom fz HR -> v = v1 -ᵢ v2 ->
    set_HRs HR [(hRr rd, W v); (fn, W (get_range 31 31 v)); (fz, W (iszero v))] = HR' ->
    HQ__ (M, (HR, b, HF)) (c (cntrans (subcc rs oexp rd))) (M, (HR', b, HF))

(* We add two Pseudo instructions : Psave and Prestore *)
| HPsave_step : forall M M' (HR HR' : HRegFile) sz b b' (HF : HFrameList) fmo fml fmi fm1 fm2,
    Hfetch HR = Some [fmo; fml; fmi] ->
    HR' = set_Hwindow HR fm1 fm2 fmo ->
    Malloc M b' ($ 64) sz M' ->
    HQ__ (M, (HR, b, HF)) (Psave sz) (M', (HR', b', (b, fml, fmi) :: HF))

| HRestore_step : forall M M' (HR HR' : HRegFile) (b b' : Z) (HF : HFrameList) fmo fml fmi fm1 fm2,
    Hfetch HR = Some [fmo; fml; fmi] ->
    (Mfree M b = M' /\ HR r30 = Some (Ptr (b', $ 0))) ->
    HR' = set_Hwindow HR fmi fm1 fm2 ->
    HQ__ (M, (HR, b, (b', fm1, fm2) :: HF)) Prestore (M', (HR', b', HF)).

Parameter args : HRstate -> Memory -> list Val -> Prop.

Inductive HH__ : XCodeHeap -> tlocst * Memory -> msg -> tlocst * Memory -> Prop :=
| HNTrans : forall C pc npc HQ HQ' HM HM' c,
    C pc = Some c -> HQ__ (HM, HQ) c (HM', HQ') ->
    HH__ C ((HQ, pc, npc), HM) tau ((HQ', npc, npc +ᵢ ($ 4)), HM')

| HJumpl : forall C HM aexp rd HR HR' b HF pc npc f,
    C pc = Some (c (cjumpl aexp rd)) ->
    Heval_addrexp HR aexp = Some (W f) ->
    word_aligned (W f) = true -> indom rd HR -> set_HR HR rd (W pc) = HR' ->
    HH__ C (((HR, b, HF), pc, npc), HM) tau (((HR', b, HF), npc, f), HM)

| HCall : forall C HM (HR HR' : HRegFile) HF b pc npc f,
    C pc = Some (c (ccall f)) ->
    indom r15 HR -> set_HR HR r15 (W pc) = HR' ->
    HH__ C (((HR, b, HF), pc, npc), HM) tau (((HR', b, HF), npc, f), HM)

| HRetl : forall C HM HR HF pc npc f b,
    C pc = Some (c cretl) ->
    get_HR HR r15 = Some (W f) ->
    HH__ C (((HR, b, HF), pc, npc), HM) tau (((HR, b, HF), npc, f +ᵢ ($ 8)), HM)

| HBe_true : forall C HM HR HF pc npc f v b,
    C pc = Some (c (cbe f)) ->
    get_HR HR fz = Some (W v) -> v <> $ 0 ->
    HH__ C (((HR, b, HF), pc, npc), HM) tau (((HR, b, HF), npc, f), HM)

| HBe_false : forall C HM HR HF pc npc f b,
    C pc = Some (c (cbe f)) ->
    get_HR HR fz = Some (W ($ 0)) ->
    HH__ C (((HR, b, HF), pc, npc), HM) tau (((HR, b, HF), npc, npc +ᵢ ($ 4)), HM)

(* We add two rules : print, occur an output; and occur a call event *)
| HPrint : forall C HM HR HF pc npc b v,
    C pc = Some print -> get_HR HR r8 = Some v ->
    HH__ C (((HR, b, HF), pc, npc), HM) (out v) ((((HR, b, HF), npc, npc +ᵢ ($ 4)), HM))

| HCallEvt : forall C HQ (pc npc : Word) HM lv,
    ~ indom pc C -> args HQ HM lv -> npc = pc +ᵢ ($ 4) ->
    HH__ C ((HQ, pc, npc), HM) (Callevt pc lv) ((HQ, pc, npc), HM).

Definition getK_pc (K : tlocst) :=
  match K with
  | (Q, pc, npc) => pc
  end.

Definition getK_npc (K : tlocst) :=
  match K with
  | (Q, pc, npc) => npc
  end.

Inductive HP__ : HProg -> msg -> HProg -> Prop :=
| Htau_step : forall C PrimSet T t K K' HM HM',
    HH__ C (K, HM) tau (K', HM') ->
    HP__ ((C, PrimSet), (T, t, K, HM)) tau ((C, PrimSet), (T, t, K', HM'))

| He_step : forall C PrimSet T t K K' HM v,
    HH__ C (K, HM) (out v) (K', HM) ->
    HP__ ((C, PrimSet), (T, t, K, HM)) (out v) ((C, PrimSet), (T, t, K', HM))

| Hp_step : forall C (PrimSet : apSet) T T' t t' K K' K'' HM HM' f lv prim,
    HH__ C (K, HM) (Callevt f lv) (K', HM) -> PrimSet f = Some prim ->
    prim lv (T, t, K', HM) (T', t', K'', HM') ->
    HP__ ((C, PrimSet), (T, t, K, HM)) tau ((C, PrimSet), (T', t', K'', HM')).

(* star steps *)
Inductive star_step {prog msg : Type} (step : prog -> msg -> prog -> Prop) :
  prog -> prog -> Prop :=
| zero_step : forall p, star_step step p p
| multi_step : forall (p p' p'' : prog) m, star_step step p p' -> step p' m p'' ->
                                           star_step step p p''.

(* High-level Program Safety *)
Definition HProgSafe (hp : HProg) :=
  forall hp', star_step HP__ hp hp' -> (exists hp'' m,  HP__ hp' m hp'').
