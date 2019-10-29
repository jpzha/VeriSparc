Require Import Coqlib.        
Require Import Maps.      
Require Import LibTactics.  
        
Require Import Integers.  
Open Scope Z_scope.     
Import ListNotations.
  
Set Asymmetric Patterns.  
       
Require Import state.    
Require Import language. 

Set Implicit Arguments.  
Unset Strict Implicit. 
              
Require Import logic.
   
Require Import lemmas.
Require Import lemmas_ins.

Require Import sep_lemma.
Require Import reg_lemma.

Require Import code.

Require Import Coq.Logic.FunctionalExtensionality.
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(** Some auxiliary definition *)
Definition winvalid x y :=
  win_masked x y = false.

(** Specification *)
Definition add_pre (vl : list logicvar) :=
  EX x y z w fret,
  [| vl = logic_lw x :: logic_lw y :: logic_lw z :: logic_lw fret :: nil |] **
  i0 |=> W x ** i1 |=> W y ** i2 |=> W z ** l7 |=> w ** r15 |=> W fret.

Definition add_post (vl : list logicvar) :=
  EX x y z fret,
  [| vl = logic_lw x :: logic_lw y :: logic_lw z :: logic_lw fret :: nil |] **
  i0 |=> W x ** i1 |=> W y ** i2 |=> W z ** l7 |=> W (x +ᵢ y +ᵢ z) ** r15 |=> W fret.

Definition changeY_pre (vl : list logicvar) :=
  EX fmg fmo fml fmi fret x vy vi id fm1 fm2 F,
  [| vl = logic_fm fmg :: logic_fm fmi :: logic_fm fm1 :: logic_fm fm2
          :: logic_lw x :: logic_lw fret :: logic_lw vy :: logic_lw vi :: logic_fmls F :: nil |] **
  GenRegs (fmg, fmo, fml, fmi) ** Ry |=> W vy ** Rwim |=> W vi ** {| id, fm1 :: fm2 :: F |} **
  [| get_frame_nth fmi 7 = Some (W fret) /\ get_frame_nth fmi 0 = Some (W x)
     /\ winvalid (post_cwp id) vi /\ $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 |].

Definition changeY_post (vl : list logicvar) :=
  EX fmg fmo fml fmi fret x vy vi id fm1 fm2 F,
  [| vl = logic_fm fmg :: logic_fm fmi :: logic_fm fm1 :: logic_fm fm2
          :: logic_lw x :: logic_lw fret :: logic_lw vy :: logic_lw vi :: logic_fmls F :: nil |] **
  GenRegs (fmg, (update_frame fmi 0 (W vy)), fm1, fm2) ** Ry |=> W x ** Rwim |=> W vi **
  {| post_cwp id, F ++ (fmo :: fml :: nil) |}.

Definition sum3_pre1 (vl : list logicvar) :=
  EX x y z fret fmg fmo fml fmi id vi F fm1 fm2 b o,
  [| vl = logic_lw x :: logic_lw y :: logic_lw z :: logic_lw fret :: logic_fm fmg :: logic_lv (Ptr (b, o)) :: nil |] **
  GenRegs (fmg, fmo, fml, fmi) ** Rwim |=> W vi ** {| id, F ++ (fm1 :: fm2 :: nil) |} ** 
  [| get_frame_nth fmo 0 = Some (W x) /\ get_frame_nth fmo 1 = Some (W y) /\
     get_frame_nth fmo 2 = Some (W z) /\ get_frame_nth fmo 7 = Some (W fret) /\
     winvalid id vi /\ winvalid (pre_cwp id) vi /\ $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7
     /\ get_frame_nth fmo 6 = Some (Ptr (b, o)) |].

Definition sum3_post1 (vl : list logicvar) :=
  EX x y z fret fmg fmo fml fmi id vi F fm1 fm2 b o,
  [| vl = logic_lw x :: logic_lw y :: logic_lw z :: logic_lw fret :: logic_fm fmg :: logic_lv (Ptr (b, o)) :: nil |] **
  GenRegs (fmg, fmo, fml, fmi) ** Rwim |=> W vi ** {| id, F ++ (fm1 :: fm2 :: nil) |} **
  [| get_frame_nth fmo 0 = Some (W x +ᵢ y +ᵢ z) /\ get_frame_nth fmo 7 = Some (W fret) /\
     winvalid id vi /\ winvalid (pre_cwp id) vi /\ $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 |].

Fixpoint convert_spec (ls : list (Word * fspec)) :
  funspec :=
  match ls with
  | nil => fun _ : Word => None
  | (f', spec) :: ls' =>
    fun f : Word =>
      if Int.eq_dec f f' then
        Some spec
      else
        convert_spec ls' f
  end.



  
