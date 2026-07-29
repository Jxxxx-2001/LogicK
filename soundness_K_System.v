(**************************************************************************)
(*  This is part of soundness_K, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2026-2031                              *)
(*      Dakai Guo, Qiming Wang, Xiang Ji, Tingting Ji and Wensheng Yu     *)
(**************************************************************************)

(** soundness_K_System *)

Require Import Base_ML.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import consistency_K_System.

(* 3.5  *)
(* 可靠性定理引理 *)
Lemma Axiom_system_reliable : forall p , Axiom_system p -> ╞ p.
Proof.
  intros. induction H.
  - apply T_3_6_1.
  - apply T_3_6_2.  
  - apply T_3_6_3.
  - apply T_3_9. auto.
  - apply T_3_8.
  - apply T_3_7_1.
  - apply T_3_7_2.
  - apply T_3_7_3.
  - apply T_3_7_4.
  - apply T_3_7_5.
  - red. intros. simpl. destruct (classicT (satisfy_R MM v p)); auto. right. intros.
    assert(agreement_f v (value_v v x m) p).
      { red. intros. unfold value_v. destruct(classicT (x0 = x)).
        rewrite e in H0. apply H in H0. inversion H0. auto. }
    apply agree_fact_2 in H0; destruct H0. apply H0; auto.
  - apply exam_3_5. auto.
Qed.

(* 可靠性定理 *)
Theorem soundness_K : forall p Γ ,Γ ├ p -> Γ ╞ p.
Proof.
  intros; red; intros. induction H.
  - red in H0. apply H0 in H. auto.
  - apply Axiom_system_reliable. auto. 
  - apply exam_3_4 with p. red. intros.
    destruct H2; apply Single in H2; rewrite H2; auto.
Qed.

Corollary consistence_K :  consistence Φ.
Proof.
  unfold consistence. intros. intro. destruct H. apply soundness_K in H, H0. 
  red in H; red in H0. simpl in H0.
  set(mm := (Build_Module nat (fun _ => 0) (fun _ _ => 0) (fun _ _ => True))).
  set(vv := (fun (_:Var) => 0)).
  assert (satisfies mm vv Φ). { red; intros. destruct H1. }
  pose proof H mm vv H1. pose proof H0 mm vv H1. tauto.
Qed.

Corollary consistence_Γ :  forall Γ, satisfiable_Γ Γ -> consistence Γ.
Proof.
  intros. unfold consistence. intros. intro. destruct H0. 
  apply soundness_K in H0, H1. red in H0, H1. simpl in H1.
  unfold satisfiable_Γ in H. destruct H as [MM [v]]. pose proof H0 MM v H. 
  pose proof H1 MM v H. tauto.
Qed.

