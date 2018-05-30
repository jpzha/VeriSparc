Require Import Coqlib.
Require Import Maps.

Require Import Integers.
Open Scope Z_scope.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(* Word *)
Definition Word := int.

(* Address *)
Definition Address := int.

(*** Definition of Registers **)
(* General Registers *)
Inductive GenReg: Type := 
  | r0: GenReg  | r1: GenReg  | r2: GenReg  | r3: GenReg  | r4: GenReg  | r5: GenReg  | r6: GenReg  | r7: GenReg
  | r8: GenReg  | r9: GenReg  | r10: GenReg | r11: GenReg | r12: GenReg | r13: GenReg | r14: GenReg | r15: GenReg
  | r16: GenReg | r17: GenReg | r18: GenReg | r19: GenReg | r20: GenReg | r21: GenReg | r22: GenReg | r23: GenReg
  | r24: GenReg | r25: GenReg | r26: GenReg | r27: GenReg | r28: GenReg | r29: GenReg | r30: GenReg | r31: GenReg.

(* Auxiliary Registers *)
Inductive AsReg: Type :=
  | asr0: AsReg  | asr1: AsReg  | asr2: AsReg  | asr3: AsReg  | asr4: AsReg  | asr5: AsReg  | asr6: AsReg  | asr7: AsReg
  | asr8: AsReg  | asr9: AsReg  | asr10: AsReg | asr11: AsReg | asr12: AsReg | asr13: AsReg | asr14: AsReg | asr15: AsReg
  | asr16: AsReg | asr17: AsReg | asr18: AsReg | asr19: AsReg | asr20: AsReg | asr21: AsReg | asr22: AsReg | asr23: AsReg
  | asr24: AsReg | asr25: AsReg | asr26: AsReg | asr27: AsReg | asr28: AsReg | asr29: AsReg | asr30: AsReg | asr31: AsReg.

(* PSR *)
Inductive PsrReg: Type :=
| n : PsrReg
| z : PsrReg
| cwp : PsrReg.

(* Special Registers *)
Inductive SpReg: Type :=
| Rwim : SpReg
| Ry : SpReg
| Rasr : AsReg -> SpReg.
Coercion Rasr : AsReg >-> SpReg.

(* Register Name *)
Inductive RegName: Type :=
| Rr : GenReg -> RegName
| Rpsr : PsrReg -> RegName
| Rsp : SpReg -> RegName.
Coercion Rr : GenReg >-> RegName.
Coercion Rpsr : PsrReg >-> RegName.
Coercion Rsp : SpReg >-> RegName.

Lemma RegName_eq: forall (x y : RegName),
    {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

Module RegNameEq.
  Definition t := RegName.
  Definition eq := RegName_eq.
End RegNameEq.

Module RegMap := EMap(RegNameEq).
(** RegFile is a total function from regname to word *)
Definition RegFile := RegMap.t Word.

(*** Window Register  **)
(* Frame *)
Inductive Frame : Type :=
  consfm : Word -> Word -> Word -> Word -> Word -> Word -> Word -> Word -> Frame.
Notation " '[[' w0 , w1 , w2 , w3 , w4 , w5 , w6 , w7 ']]'" :=
  (consfm w0 w1 w2 w3 w4 w5 w6 w7) (at level 200): code_scope.

(* Frame List *)
Definition FrameList : Type := list Frame.

(* RState *)
Definition RState : Type := RegFile * FrameList.

(*** Delay List **)
(* DelayCycle *)
Definition DelayCycle := nat.

(* DelayItem *)
Definition DelayItem : Type := DelayCycle * SpReg * Word.

(* DelayList *)
Definition DelayList : Type := list DelayItem.

(* DelayTime *)
Definition X := 3%nat.

(* set_delay *)
Definition set_delay (rsp : SpReg) (w : Word) (D : DelayList) :=
  (X, rsp, w) :: D.

(* getRegs *)
Fixpoint getRegs (D : DelayList) :=
  match D with
  | (_, rsp, _) :: D' => rsp :: (getRegs D')
  | _ => nil
  end.

(*** Program State **)
(* Operation Expression *)  
Inductive OpExp : Type :=
| Or : GenReg -> OpExp
| Ow : Word -> OpExp.

(* Address Expression *)
Inductive AddrExp : Type :=
| Ao : OpExp -> AddrExp
| Aro : GenReg -> OpExp -> AddrExp.

(* memory *)
Module AddrEq.
  Definition t := Word.
  Definition eq := Int.eq_dec.
End AddrEq.

Module MemMap := EMap(AddrEq).
(** Memory is a partial function from address to word *)
Definition Memory := MemMap.t (option Word).

(* Some Operations for memory *)
(* disjoint *)
Definition disjoint {tp : Type} (M1 : tp -> option Word) (M2 : tp -> option Word) : Prop :=
  forall (x : tp),
    match M1 x, M2 x with
    | Some _, Some _ => False
    | Some _, None => True
    | None, Some _ => True
    | None, None => True
    end.
Notation "M1 '⊥' M2" := (disjoint M1 M2) (at level 39) : mem_scope.

(* in dom *)
Definition indom {tp : Type} (x : tp) (M : tp -> option Word) :=
  exists v, M x = Some v.

(* is in dom *)
Definition is_indom {tp : Type} (x : tp) (M : tp -> option Word) :=
  match M x with
  | Some _ => true
  | None => false
  end.
 
(* merge *)
Definition merge {tp : Type} (M1 : tp -> option Word) (M2 : tp -> option Word) :=
  fun x => match M1 x with
        | None => M2 x
        | Some b => Some b
        end.
Notation "M1 '⊎' M2" := (merge M1 M2) (at level 39) : mem_scope.

(* emp memory *)
Definition empM : Memory := fun (x : Address) => None. 

(* Label f *)
Definition Label: Type := Word.

(* Program State *)
Definition State: Type := Memory * RState * DelayList.

(*** Expression Evalution *)
Notation "$ n" := (Int.repr n)(at level 1) : code_scope.
Notation "a <<ᵢ b" := (Int.shl a b)(at level 1) : code_scope.
Notation "a >>ᵢ b" := (Int.shru a b)(at level 1) : code_scope.
Notation "a &ᵢ b" := (Int.and a b)(at level 1) : code_scope.
Notation "a |ᵢ b" := (Int.or a b)(at level 1) : code_scope.
Notation "a +ᵢ b" := (Int.add a b)(at level 1) : code_scope.
Notation "a -ᵢ b" := (Int.sub a b)(at level 1) : code_scope.
Notation "a =ᵢ b" := (Int.eq a b)(at level 1) : code_scope.
Notation "a <ᵢ b" := (Int.lt a b)(at level 1) : code_scope.
Notation "a >ᵢ b" := (Int.lt b a)(at level 1) : code_scope.
Notation "a <=ᵢ b" := (orb(Int.lt a b)(Int.eq a b))(at level 1) : code_scope.
Notation "a >=ᵢ b" := (orb(Int.lt b a)(Int.eq a b))(at level 1) : code_scope.
Notation "a !=ᵢ b" := (negb(Int.eq a b))(at level 1) : code_scope.
Notation "a 'modu' b" := (Int.modu a b)(at level 1) : code_scope.
Notation "a 'xor' b" := (Int.xor a b)(at level 1) : code_scope.

Definition int_le a b :=
  Int.lt a b || Int.eq a b.
Notation "A <ᵢ B <ᵢ C" := (Int.lt A B && Int.lt B C = true)
                            (at level 2, B at next level) : code_scope. 
Notation "A <ᵢ B <=ᵢ C" := (Int.lt A B && int_le B C = true)
                             (at level 2, B at next level) : code_scope.
Notation "A <=ᵢ B <ᵢ C" := (int_le A B && Int.lt B C = true)
                             (at level 2, B at next level) : code_scope.        
Notation "A <=ᵢ B <=ᵢ C" := (int_le A B && int_le B C = true)
                              (at level 2, B at next level) : code_scope.

Definition int_leu a b :=
  Int.ltu a b || Int.eq a b.

Notation "A <ᵤᵢ B <ᵤᵢ C" := (Int.ltu A B && Int.ltu B C = true)
                              (at level 2, B at next level) : code_scope.
Notation "A <ᵤᵢ B <=ᵤᵢ C" := (Int.ltu A B && int_leu B C = true)
                               (at level 2, B at next level) : code_scope.
Notation "A <=ᵤᵢ B <ᵤᵢ C" := (int_leu A B && Int.ltu B C = true)
                               (at level 2, B at next level) : code_scope.        
Notation "A <=ᵤᵢ B <=ᵤᵢ C" := (int_leu A B && int_leu B C = true)
                                (at level 2, B at next level) : code_scope.
Notation "A <ᵤᵢ B" := (Int.ltu A B = true)
                        (at level 2, no associativity) : code_scope.
Notation "A <=ᵤᵢ B" := (int_leu A B = true)
                         (at level 2, no associativity) : code_scope.

Open Scope code_scope.

Definition get_R (R : RegFile) (rn : RegName) :=
  match rn with
  | Rr r0 => ($ 0)
  | _ => (R rn)
  end.

Definition eval_opexp (R : RegFile) (a : OpExp) :=
  match a with
  | Or r => Some (get_R R r)
  | Ow w =>
    if andb (($-4096) <=ᵢ w) (w <=ᵢ ($4095)) then
      Some w
    else
      None
  end.

Definition eval_addrexp (R : RegFile) (b : AddrExp) :=
  match b with
  | Ao a => eval_opexp R a
  | Aro r a =>
    match get_R R r with
    | w1 =>
      match (eval_opexp R a) with
      | Some w2 => Some (w1 +ᵢ w2)
      | None => None
      end
    end
  end.

(* fetch *)
Definition fetch_frame (R : RegFile) (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) : Frame :=
  ([[(R rr0), (R rr1), (R rr2), (R rr3), (R rr4), (R rr5), (R rr6), (R rr7)]]).

Definition fetch (R : RegFile) :=
  match (fetch_frame R r8 r9 r10 r11 r12 r13 r14 r15),
        (fetch_frame R r16 r17 r18 r19 r20 r21 r22 r23),
        (fetch_frame R r24 r25 r26 r27 r28 r29 r30 r31) with
  | fmo, fml, fmi => (fmo, fml, fmi)
  end.

(** update frame *)
Definition upd_frame (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) (fm : Frame) (R : RegFile) :=
  match fm with
  | ([[ w0, w1, w2, w3, w4, w5, w6, w7 ]]) =>
    RegMap.set rr0 w0 (RegMap.set rr1 w1 (RegMap.set rr2 w2
      (RegMap.set rr3 w3 (RegMap.set rr4 w4 (RegMap.set rr5 w5
        (RegMap.set rr6 w6 (RegMap.set rr7 w7 R)))))))
  end.

Definition replace (fm1 fm2 fm3 : Frame) (R : RegFile) :=
  upd_frame r8 r9 r10 r11 r12 r13 r14 r15 fm1
            (upd_frame r16 r17 r18 r19 r20 r21 r22 r23 fm2
                       (upd_frame r24 r25 r26 r27 r28 r29 r30 r31 fm3 R)).

(* exe_delay *)
Fixpoint exe_delay (R : RegFile) (D : DelayList) : RegFile * DelayList :=
  match D with
  | (0%nat, rsp, w) :: D =>
    let (R', D') := exe_delay R D in
    (RegMap.set rsp w R', D')
  | (S k, rsp, w) :: D =>
    let (R', D') := exe_delay R D in
    (R', (k, rsp, w) :: D')
  | nil => (R, D)
  end.
