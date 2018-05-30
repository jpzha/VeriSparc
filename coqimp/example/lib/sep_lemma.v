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
(*Require Import lemmas_ins.*)

Require Import Coq.Logic.FunctionalExtensionality.
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

Definition FReq (p1 p2 : asrt) :=
  forall rn, (FR rn p1 -> FR rn p2) /\ (FR rn p2 -> FR rn p1).

Lemma astar_subst1 :
  forall p1 p1' p2 s,
    s |= p1 ** p2 -> p1 ==> p1' ->
    FReq p1 p1' ->
    s |= p1' ** p2.
Proof. 
  intros.
  sep_star_split_tac.
  simpl in H5.
  simpl.
  simpljoin1. 
  exists (m, (r0, f0), d0) (m0, (r0, f0), d0).
  simpl.
  do 3 (split; eauto).
  unfolds regdisj.
  intros.
  specialize (H6 rn).
  simpljoin1.
  unfolds FReq.
  specialize (H1 rn).
  simpljoin1.
  split.
  intro.
  eauto.
  intro.
  intro.
  eapply H6 in H8.
  eapply H3 in H8.
  tryfalse.
Qed.

Lemma astar_subst2 :
  forall p1 p2 p2' s,
    s |= p1 ** p2 -> p2 ==> p2' ->
    FReq p2 p2' ->
    s |= p1 ** p2'.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H5.
  simpl.
  simpljoin1.
  exists (m, (r0, f0), d0) (m0, (r0, f0), d0).
  simpl.
  split; eauto.
  do 2 (split; eauto).
  clear - H6 H1.
  unfolds regdisj.
  intro.
  specialize (H6 rn).
  simpljoin1.
  unfolds FReq.
  specialize (H1 rn).
  simpljoin1.
  split; intro; eauto.
  intro.
  eapply H2 in H4.
  eapply H0 in H4.
  tryfalse.
Qed.

Theorem astar_assoc_intro :
  forall P Q R, P ** Q ** R ==> (P ** Q) ** R.
Proof.
  intros.
  eapply sep_star_assoc; eauto.
Qed.

Theorem astar_assoc_elim :
  forall P Q R, (P ** Q) ** R ==> P ** Q ** R.
Proof.
  intros.
  eapply sep_star_assoc2; eauto.
Qed.

Theorem astar_comm :
  forall P Q,
    P ** Q ==> Q ** P.
Proof.
  intros.
  eapply sep_star_sym; eauto.
Qed.

Lemma merge_empM_r_eq :
  forall M,
    merge M empM = M.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intro.
  destruct (M x); eauto.
Qed.

Lemma merge_empM_l_eq :
  forall M,
    merge empM M = M.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
Qed.
  
Lemma astar_emp_intro_r :
  forall p,
    p ==> p ** Aemp.
Proof.
  intros.
  destruct_state s.
  simpl.
  exists (m, (r, f), d) (empM, (r, f), d).
  simpl.
  repeat (split; eauto).
  unfold disjoint.
  intro.
  destruct (m x); simpl; eauto.
  rewrite merge_empM_r_eq; eauto.
Qed.

Lemma astar_emp_elim_r :
  forall p,
    p ** Aemp ==> p.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H3.
  simpljoin1.
  simpl in H2.
  simpljoin1.
  rewrite merge_empM_r_eq; eauto.
Qed.
  
Lemma astar_emp_intro_l :
  forall p, 
    p ==> Aemp ** p.
Proof.
  intros.
  destruct_state s.
  simpl.
  exists (empM, (r, f), d) (m, (r, f), d).
  simpls.
  repeat (split; eauto).
  unfold disjoint.
  intro.
  simpl; eauto.
  destruct (m x); eauto.
Qed.

Lemma astar_emp_elim_l :
  forall p,
    Aemp ** p ==> p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  eauto.
Qed.
  
Ltac sassocr_in H :=
  match type of H with
    | _ |= (_ ** _) ** _ => apply astar_assoc_elim in H; sassocr_in H
    | _ => idtac
  end.

Ltac sassocl_in H :=
  match type of H with
    | _ |= _ ** (_ ** _) => apply astar_assoc_intro in H; sassocr_in H
    | _ => idtac
  end.

Ltac sassocr :=
  match goal with
    | |- _ |= (_ ** _) ** _ => apply astar_assoc_intro; sassocr
    | _ => idtac
  end.

Ltac sassocl :=
  match goal with
    | |- _ |= _ ** (_ ** _) => apply astar_assoc_elim; sassocl
    | _ => idtac
  end.

Ltac scomm_in H :=
  match type of H with
    | _ |= _ ** _ => apply astar_comm in H
    | _ => idtac
  end.

Ltac scomm :=
  match goal with
    | |- _ |= _ ** _ => apply astar_comm
    | _ => idtac
  end.

Tactic Notation "sep" "assocr" "in" hyp (H) :=
  sassocr_in H.
Tactic Notation "sep" "assocl" "in" hyp (H) :=
  sassocl_in H.
Tactic Notation "sep" "assocr" :=
  sassocr.
Tactic Notation "sep" "assocl" :=
  sassocl.
Tactic Notation "sep" "comm" "in" hyp (H) :=
  scomm_in H.
Tactic Notation "sep" "comm" :=
  scomm.

Ltac sliftn n :=
  match eval compute in n with
    | 0%nat => idtac
    | 1%nat => sep assocr
    | S ?n' => sep assocr; sep comm; sliftn n'
  end.

Ltac sliftn_in H n :=
  match eval compute in n with
    | 0%nat => idtac
    | 1%nat => sep assocr in H
    | S ?n' => sep assocr in H; sep comm in H; sliftn_in H n'
  end.

Fixpoint asrt_get_nth n p :=
  match n with
  | O => match p with
        | p1 ** p2 => p1
        | _ => p
        end
  | S n' =>
    match p with
    | p1 ** p2 => asrt_get_nth n' p2
    | _ => Aemp
    end
  end.

Fixpoint asrt_rm_nth n p :=
  match n with
  | O => match p with
        | p1 ** p2 => p2
        | _ => Aemp
        end
  | S n' =>
    match p with
    | p1 ** p2 => p1 ** asrt_rm_nth n' p2
    | _ => p
    end
  end.

Lemma FR_get_rm_stable_rev :
  forall p rn n,
    FR rn (asrt_get_nth n p) \/ FR rn (asrt_rm_nth n p) ->
    FR rn p.
Proof.
  intro p.
  induction p; intros;
    try solve [simpls; eauto; tryfalse];
    try solve [destruct n; simpls; eauto; try destruct H; tryfalse; eauto].

  {
    destruct n0.
    simpl in H.
    destruct_rneq_H.
    subst; eauto.
    simpl; eauto.
    destruct_rneq.
    destruct H; tryfalse.
    simpl in H.
    destruct_rneq_H.
    subst.
    simpl; eauto.
    destruct_rneq.
    destruct H; tryfalse.
  }

  {
    destruct n.
    simpl in H.
    simpl; eauto.
    simpl in H.
    assert (FR rn p1 \/ FR rn (asrt_get_nth n p2) \/ FR rn (asrt_rm_nth n p2)).
    {
      destruct H; eauto.
      destruct H; eauto.
    }
    destruct H0.
    simpl; eauto.
    eapply IHp2 in H0.
    simpl; eauto.
  }

  destruct n.
  simpl in H0.
  destruct H0; tryfalse.
  simpl; eauto.
  simpl in H0.
  destruct H0; tryfalse.
  simpl; eauto.

  destruct n.
  simpl in H0.
  destruct H0; tryfalse.
  simpl; eauto.
  simpl in H0.
  destruct H0; tryfalse.
  simpl; eauto.
Qed.

Lemma FR_get_rm_stable :
  forall p rn n,
    FR rn p ->
    FR rn (asrt_get_nth n p) \/ FR rn (asrt_rm_nth n p).
Proof.
  intro p.
  induction p; intros;
    try solve [simpls; eauto; tryfalse];
    try solve [destruct n; simpls; eauto].

  {
    simpl in H.
    destruct_rneq_H; tryfalse.
    subst.
    destruct n0; simpl; eauto.
    destruct_rneq.
    destruct_rneq.
  }

  simpl in H.
  destruct H.
  {
    eapply IHp1 with (n := n) in H.
    destruct n.
    simpl. 
    left.
    simpl.
    eapply FR_get_rm_stable_rev; eauto.
    right.
    left.
    eapply FR_get_rm_stable_rev; eauto.
  }
  {
    eapply IHp2 with (n := n) in H.
    destruct n.
    simpl.
    right.
    eapply FR_get_rm_stable_rev; eauto.
    simpl.
    eapply FR_get_rm_stable_rev in H.
    eapply or_assoc.
    assert (FR rn (asrt_get_nth n p2) \/ FR rn p1 <-> FR rn p1 \/ FR rn (asrt_get_nth n p2)).
    {
      eapply or_comm; eauto.
    }
    rewrite H0.
    eapply or_assoc.
    right.
    eapply IHp2; eauto.
  }
Qed.
  
Lemma FReq_get_rm_stable :
  forall p n,
    FReq p (asrt_get_nth n p ** asrt_rm_nth n p).
Proof.
  intros.
  unfolds FReq.
  intro.
  split.
  {
    simpl.
    intro.
    eapply FR_get_rm_stable; eauto.
  }
  {
    intro.
    simpl in H.
    eapply FR_get_rm_stable_rev in H; eauto.
  }
Qed.

Lemma FReq_sym :
  forall p1 p2,
    FReq p1 p2 <-> FReq p2 p1.
Proof.
  intros.
  split.
  intro.
  unfolds FReq.
  intro.
  specialize (H rn).
  simpljoin1; eauto.
  unfolds FReq.
  intro.
  intro.
  specialize (H rn).
  simpljoin1; eauto.
Qed.
  
Lemma asrt_lift_nth_stable :
  forall n p s,
    s |= p ->
    s |= asrt_get_nth n p ** asrt_rm_nth n p.
Proof. 
  intro n.
  induction n; intros.
  -
    destruct p;
      simpl asrt_get_nth; simpl asrt_rm_nth;
        try solve [eapply astar_emp_intro_r; eauto].
    eauto.
  -
    destruct p;
      simpl asrt_get_nth; simpl asrt_rm_nth;
        try solve [eapply astar_emp_intro_l; eauto].
    specialize (IHn p2).
    eapply astar_subst2 in H; eauto.
    eapply sep_star_lift in H; eauto. 
    eapply FReq_get_rm_stable; eauto.
Qed.

Lemma asrt_lift_nth_stable_rev :
  forall n p s,
    s |= asrt_get_nth n p ** asrt_rm_nth n p ->
    s |= p.
Proof.
  intro n.
  induction n; intros.
  -
    destruct p;
      try solve
          [
            simpls asrt_get_nth; simpls asrt_rm_nth;
            eapply astar_emp_elim_r in H; eauto
          ].
    simpls; eauto.
  -
    destruct p;
      try solve
          [
            simpls asrt_get_nth; simpls asrt_rm_nth;
            eapply astar_emp_elim_l in H; eauto
          ].
    simpl asrt_get_nth in H.
    simpl asrt_rm_nth in H.
    specialize (IHn p2).
    eapply sep_star_lift in H.
    eapply astar_subst2 in H; eauto.
    eapply FReq_sym; eauto.
    eapply FReq_get_rm_stable.
Qed.

Ltac simpl_sep_liftn_in H t :=
  match t with
  | 0%nat => idtac "n stars from 1, not 0"
  | S ?n' =>
    match type of H with
    | _ |= _ =>
        eapply asrt_lift_nth_stable with (n := n') in H;
        unfold asrt_get_nth in H; unfold asrt_rm_nth in H;
        try eapply astar_emp_elim_l in H;
        try eapply astar_emp_elim_r in H
    | _ => idtac "no assertion"
    end
  end.

Ltac simpl_sep_liftn t :=
  match t with
  | 0%nat => idtac "n stars from 1, not 0"
  | S ?n' =>
    match goal with
    | |- _ |= _ =>
      eapply asrt_lift_nth_stable_rev with (n := n');
      unfold asrt_get_nth; unfold asrt_rm_nth;
      try eapply astar_emp_intro_r;
      try eapply astar_emp_intro_l
    | _ => idtac "no assertion"
    end
  end.

Fixpoint asrt_combine_to_line (p1 : asrt) (p2 : asrt) (n : nat) :=
  match p1 with
  | p1' ** p2' => match n with
                 | 0%nat => p1 ** p2
                 | S n' => p1' ** (asrt_combine_to_line p2' p2 n')
                 end
  | _ => p1 ** p2
  end.

Lemma FR_combine_to_line_stable :
  forall p1 p2 rn n,
    FR rn (asrt_combine_to_line p1 p2 n) ->
    FR rn (p1 ** p2).
Proof.
  intro p1.
  induction p1; intros; simpl;
    try solve [destruct n; simpl in H; try destruct H; tryfalse; eauto].

  destruct n.
  {
    simpl in H.
    eauto.
  }
  {
    simpl in H.
    destruct H; eauto.
    eapply IHp1_2 in H.
    simpl in H.
    destruct H; eauto.
  }
Qed.

Lemma FR_combine_to_line_stable_rev :
  forall p1 p2 rn n,
    FR rn (p1 ** p2) ->
    FR rn (asrt_combine_to_line p1 p2 n).
Proof.
  intro p1.
  induction p1; intros; simpl;
    try solve [simpls; destruct H; tryfalse; eauto].

  {
    destruct n.
    eauto.
    simpl in H.
    rewrite or_assoc in H.
    destruct H; simpl; eauto.
  }

  simpl; eauto.
  simpl; eauto.
Qed.
  
Lemma regdisj_combine_to_line_stable :
  forall p1 p2 p3 n,
    regdisj p1 (p2 ** p3) ->
    regdisj p1 (asrt_combine_to_line p2 p3 n).
Proof.
  intros.
  unfolds regdisj.
  intro.
  specialize (H rn).
  simpljoin1.
  split.
  {
    intro.
    eapply H in H1.
    intro.
    eapply H1.
    eapply FR_combine_to_line_stable; eauto.
  }
  {
    intro.
    intro.
    eapply FR_combine_to_line_stable in H1.
    eapply H0 in H1.
    tryfalse.
  }
Qed.
  
Lemma asrt_combine_to_line_stable :
  forall n p1 p2 s,
    s |= p1 ** p2 ->
    s |= asrt_combine_to_line p1 p2 n.
Proof.
  intro n.
  induction n; intros.
  -
    destruct p1; simpls; eauto.
  - 
    destruct p1;
      try solve [simpls; eauto].
    simpl.
    sep_star_split_tac.
    simpl in H1, H3.
    simpljoin1.
    exists (m1, (r2, f2), d2) (merge m2 m0, (r2, f2), d2).
    split; eauto.
    repeat (split; eauto).
    eapply disj_sep_merge_still; eauto.
    eapply disj_sym in H3.
    eapply disj_merge_disj_sep1 in H3; eauto.
    eapply disj_sym; eauto.
    rewrite merge_assoc; eauto.
    split; eauto.
    split.
    eapply IHn; eauto. 
    simpl.
    do 2 eexists.
    split; eauto.
    Focus 2. 
    split; eauto.
    split; eauto.
    eapply regdisj_star_sepl2 in H4.
    eauto.
    simpl. 
    repeat (split; eauto).
    eapply disj_sym in H3.
    eapply disj_merge_disj_sep2 in H3.
    eapply disj_sym; eauto.
    eapply regdisj_star_sepl1 in H4.
    assert (regdisj p1_1 (p1_2 ** p2)).
    eapply regdisj_star_merge; eauto.
    eapply regdisj_combine_to_line_stable; eauto.
Qed.

Lemma FReq_combine_to_line_stable :
  forall p1 p2 n,
    FReq (p1 ** p2) (asrt_combine_to_line p1 p2 n).
Proof.
  intros.
  unfolds FReq.
  intros.
  split; eauto.
  intro.
  eapply FR_combine_to_line_stable_rev; eauto.
  intro.
  eapply FR_combine_to_line_stable; eauto.
Qed.

Lemma asrt_combine_to_line_stable_rev :
  forall n p1 p2 s,
    s |= asrt_combine_to_line p1 p2 n ->
    s |= p1 ** p2.
Proof.
  intro n.
  induction n; intros.
  -
    destruct p1; simpls; eauto.
  -
    destruct p1;
      try solve [simpls; eauto].
    simpl asrt_combine_to_line in H.
    eapply astar_assoc_intro; eauto.
    eapply astar_subst2; eauto.
    eapply FReq_sym; eauto.
    eapply FReq_combine_to_line_stable; eauto.
Qed.

Inductive asrtTree : Type :=
| empTree : asrtTree
| trueTree : asrtTree
| starTree : asrtTree -> asrtTree -> asrtTree
| pureTree : Prop -> asrtTree
| baseTree : asrt -> asrtTree.

Fixpoint toTree Hp :=
  match Hp with
    | A ** B => let tA := toTree A in
                  let tB := toTree B in
                  starTree tA tB
    | Aemp => empTree
    | Atrue => trueTree
    | [| P |] => pureTree P
    | _ => baseTree Hp
  end.

Fixpoint unTree (t:asrtTree) : asrt :=
  match t with
    | empTree => Aemp
    | trueTree => Atrue
    | starTree A B => unTree A ** unTree B
    | pureTree P => [| P |]
    | baseTree A => A
  end.

Fixpoint asrtTree_to_list' (Hp:asrtTree) (l:list asrtTree) : list asrtTree :=
  match Hp with
    | starTree A B => asrtTree_to_list' A (asrtTree_to_list' B l)
    | _ => Hp::l
  end.

Definition asrtTree_to_list (Hp:asrtTree) : list asrtTree :=
  asrtTree_to_list' Hp nil.

Fixpoint asrt_to_list' Hp l :=
  match Hp with
    | A ** B => let rl := asrt_to_list' B l in
                  asrt_to_list' A rl
    | A => A :: l
  end.
Definition asrt_to_list Hp := asrt_to_list' Hp (@nil asrt).

Fixpoint list_to_asrt l :=
  match l with
  | nil => Aemp
  | A :: l' => let ar := list_to_asrt l' in
              A ** ar
  end.

Lemma asrt_to_list'_assoc :
  forall p1 p2 p3 l,
    asrt_to_list' ((p1 ** p2) ** p3) l =
    asrt_to_list' (p1 ** p2 ** p3) l.
Proof.
  intro p1.
  induction p1; intros;
    try solve [simpl; eauto].
Qed.

Lemma asrt_to_list_app :
  forall p1 p2,
    asrt_to_list (p1 ** p2) = asrt_to_list p1 ++ asrt_to_list p2.
Proof. 
  intros.
  unfold asrt_to_list.
  generalize dependent p2.
  induction p1; intros;
    try solve [simpls; eauto]. 
  -
    assert (asrt_to_list' ((p1_1 ** p1_2) ** p2) [] =
            asrt_to_list' (p1_1 ** p1_2 ** p2) []).
    {
      rewrite asrt_to_list'_assoc; eauto.
    }
    rewrite H.
    rewrite IHp1_1; eauto.
    rewrite IHp1_2; eauto.
    rewrite IHp1_1; eauto.
    rewrite app_assoc; eauto.
Qed.

Lemma FR_lst_to_asrt_app_stable1 :
  forall l1 l2 rn,
    FR rn (list_to_asrt l1) ->
    FR rn (list_to_asrt (l1 ++ l2)).
Proof.
  intro l1.
  induction l1; intros.
  -
    simpls; tryfalse.
  -
    simpl in H.
    simpl.
    destruct H; eauto.
Qed.

Lemma FR_lst_to_asrt_app_stable2 :
  forall l1 l2 rn,
    FR rn (list_to_asrt l2) ->
    FR rn (list_to_asrt (l1 ++ l2)).
Proof.
  intro l1.
  induction l1; intros.
  -
    simpls; eauto.
  -
    simpl.
    eauto.
Qed.

Lemma FR_lst_to_asrt_app_stable_rev :
  forall l1 l2 rn,
    FR rn (list_to_asrt (l1 ++ l2)) ->
    FR rn (list_to_asrt l1) \/ FR rn (list_to_asrt l2).
Proof.
  intro l1.
  induction l1; intros.
  -
    simpls; eauto.
  -
    simpls.
    destruct H; eauto.
    eapply IHl1 in H.
    destruct H; eauto.
Qed.

Lemma FReq_list_to_asrt_stable :
  forall l1 l2,
    FReq (list_to_asrt l1 ** list_to_asrt l2) (list_to_asrt (l1 ++ l2)).
Proof.
  intros.
  unfolds FReq.
  intro.
  split.
  {
    intro.
    simpls.
    destruct H.
    eapply FR_lst_to_asrt_app_stable1; eauto.
    eapply FR_lst_to_asrt_app_stable2; eauto.
  }
  {
    intro.
    simpl.
    eapply FR_lst_to_asrt_app_stable_rev; eauto.
  }
Qed.
  
Lemma list_asrt_app :
  forall l1 l2 s,
    s |= list_to_asrt l1 ** list_to_asrt l2 ->
    s |= list_to_asrt (l1 ++ l2).
Proof.
  intro l1.
  induction l1; intros.
  -
    simpls list_to_asrt.
    eapply astar_emp_elim_l; eauto.
  -
    simpls list_to_asrt.
    eapply astar_assoc_elim in H. 
    eapply astar_subst2; eauto.
    eapply FReq_list_to_asrt_stable; eauto.
Qed.

Lemma list_asrt_app_rev :
  forall l1 l2 s,
    s |= list_to_asrt (l1 ++ l2) ->
    s |= list_to_asrt l1 ** list_to_asrt l2.
Proof.
  intro l1.
  induction l1; intros.
  -
    simpls list_to_asrt.
    eapply astar_emp_intro_l; eauto.
  -
    simpls list_to_asrt.
    eapply astar_assoc_intro; eauto.
    eapply astar_subst2; eauto.
    eapply FReq_sym.
    eapply FReq_list_to_asrt_stable; eauto.
Qed.
    
Lemma l2a_a2l_stable' :
  forall p1 p2 l1 l2 s,
    s |= list_to_asrt (asrt_to_list' p1 l1) ** list_to_asrt (asrt_to_list' p2 l2) ->
    s |= list_to_asrt (asrt_to_list' p1 l1 ++ asrt_to_list' p2 l2).
Proof.
  intro p1.
  induction p1; intros;
    simpl asrt_to_list' in *; simpl list_to_asrt in *;
      try solve [eapply astar_assoc_elim in H; eapply astar_subst2; eauto;
                try intros; eapply list_asrt_app; eauto].
  -
    eapply IHp1_1 in H; eauto.
  -
    eapply astar_assoc_elim in H0.
    eapply astar_subst2; eauto.
    intros.
    eapply list_asrt_app; eauto.
  -
    eapply astar_assoc_elim in H0.
    eapply astar_subst2; eauto.
    intros.
    eapply list_asrt_app; eauto.
Qed.

Lemma l2a_a2l_stable'_rev :
  forall p1 p2 l1 l2 s,
    s |= list_to_asrt (asrt_to_list' p1 l1 ++ asrt_to_list' p2 l2) ->
    s |= list_to_asrt (asrt_to_list' p1 l1) ** list_to_asrt (asrt_to_list' p2 l2).
Proof.
  intro p1.
  induction p1; intros;
    simpl asrt_to_list' in *; simpl list_to_asrt in *;
      try solve [eapply astar_assoc_intro; eapply astar_subst2; eauto;
                 try intros; eapply list_asrt_app_rev; eauto].
  eapply IHp1_1; eauto.
Qed.
    
Lemma asrt_to_ls_stable :
  forall p s,
    s |= p ->
    s |= list_to_asrt (asrt_to_list p).
Proof.
  intro p.
  induction p; intros;
    try solve [simpl list_to_asrt;
               simpl asrt_to_list;
               eapply astar_emp_intro_r; eauto].
  eapply astar_subst1 in H; eauto.
  eapply astar_subst2 in H; eauto.
  rewrite asrt_to_list_app.
  clear IHp1 IHp2.
  unfolds asrt_to_list.
  eapply l2a_a2l_stable'; eauto.
Qed.

Lemma asrt_to_ls_stable_rev :
  forall p s,
    s |= list_to_asrt (asrt_to_list p) ->
    s |= p.
Proof.
  intro p.
  induction p; intros;
    try solve [simpls list_to_asrt; simpls asrt_to_list;
               eapply astar_emp_elim_r; eauto].
  eapply astar_subst1; eauto.
  eapply astar_subst2; eauto.
  rewrite asrt_to_list_app in H.
  clear IHp1 IHp2.
  unfolds asrt_to_list.
  eapply l2a_a2l_stable'_rev; eauto.
Qed.

Ltac asrt_to_ls :=
  match goal with
  | |- _ |= _ =>
    eapply asrt_to_ls_stable_rev;
    simpl asrt_to_list; simpl list_to_asrt
  | _ => idtac
  end.

Ltac asrt_to_ls_in H :=
  match type of H with
  | _ |= _ =>
    eapply asrt_to_ls_stable in H;
    simpl asrt_to_list in H; simpl list_to_asrt in H
  | _ => idtac
  end.

Ltac sep_cancel1 m n :=
  let H' := fresh in
  match goal with
  | H : ?s |= _ |- ?s |= _ =>
    simpl_sep_liftn_in H m; simpl_sep_liftn n;
    eapply astar_subst2; [eauto | introv H'; clear H]
  | _ => idtac
  end.