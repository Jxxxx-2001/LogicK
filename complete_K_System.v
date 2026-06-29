(***************************************************************************)
(*   This is part of complete_K, it is distributed under the terms of the  *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*                        Copyright 2026-2031                              *)
(*      Xiang Ji, Dakai Guo, Guowei Dou, Jiaxin Xie and Wensheng Yu        *)
(***************************************************************************)

(** complete_K_System *)

Require Import Base_ML.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import consistency_K_System.
Require Import soundness_K_System.
Require Import complete_K_System_pre.
Require Import satisfiability_K_System.
Require Import extension_K_System.

(* 完备性定理 *)
Definition complete := forall Γ p, Γ ╞ p -> Γ ├ p.

(* 完备性定理的逆否命题 *)
Definition complete_contra := forall Γ p, ~ (Γ ├ p) -> ~ (Γ ╞ p).

(* 关于一致性的一些简单事实 *)
(* ~(Γ├p)当且仅当Γ∪[/¬p]是一致的 *)
Fact consistence_contra : forall Γ p, ~ (Γ ├ p) <-> consistence (Γ ∪ [/¬p]).
Proof.
  split; intros.
  - red; intros. intro.
    destruct H0. destruct H. pose proof rule_Indirect _ _ _ H0 H1. auto.
  - intro. red in H.
    destruct (H p). split.
    + apply subsetprove with Γ; auto. red; intros. left; auto.
    + constructor. right. split.
Qed.

(* (Γ╞p)当且仅当Γ∪[/¬p]不是可满足的 *)
Fact satisfiable_contra_le : forall Γ p, Γ ╞ p <-> ~ satisfyable_Γ (Γ ∪ [/¬p]).
Proof.
  intros. split; red; intros.
  - red in H0. destruct H0 as [MM [v H0]]. 
    assert(satisfyable MM v Γ). { red in H0. red. intros. apply H0. left. auto. } 
    apply H in H1. pose proof H0. red in H0. specialize H0 with ¬p. 
    assert(¬p ∈ (Γ ∪ [/¬p])). { right. eauto with sets. } 
    apply H0 in H3. simpl in H3. auto.
  - red in H. unfold satisfyable_Γ in H. unfold satisfyable in H0.
    destruct(classic (p ∈ Γ) ). apply H0 in H1. auto.
    destruct(classic (satisfy_R MM v p)). auto.
    assert((exists (MM: Module) (v: value MM), satisfyable MM v (Γ ∪ [/¬p]))). 
      { exists MM,v. red. intros. destruct H3. apply H0. auto. destruct H3. 
        simpl; auto. }
    apply H in H3. destruct H3.
Qed.

(* ~(Γ╞p)当且仅当Γ∪[/¬p]是可满足的*)
Fact satisfiable_contra : forall Γ p, 
  ~ (Γ ╞ p) <-> satisfyable_Γ (Γ ∪ [/¬p]).
Proof. intros; rewrite satisfiable_contra_le; tauto. Qed.

(* 目标: 一致集都是可满足的 *)
Definition consistence_satisfiable := forall Γ, consistence Γ -> satisfyable_Γ Γ.

(* 若一致集都是可满足的, 那么完备性定理成立! *)
Lemma complete_consistence_satisfiable : consistence_satisfiable -> complete.
Proof.
  red; intros. red in H. pose proof H (Γ ∪ [/¬p]).
  destruct (classic (Γ ├ p)); auto. apply consistence_contra in H2.
  apply H1 in H2. apply satisfiable_contra in H2. tauto.
Qed.

(* 完全性定理 *)
Theorem complete_K : complete.
Proof.
  apply complete_consistence_satisfiable. red; intros.
  pose proof max_consistence_extension _ H as [Γ' [? []]].
  apply double_C_satisfiable; auto. rewrite double_C_consistence in H; auto.
  red. exists (D_I Γ' H0). unfold value. exists (@ assignment Γ' H0).
  pose proof model_sat Γ' H0 H2. red; intros. apply H1 in H4. apply H3; auto.
Qed.

(* Godel完全性定理 *)
Theorem Godel_complete_theorem : forall p Γ ,Γ ├ p <-> Γ ╞ p.
Proof. split. apply soundness_K. apply complete_K. Qed.

(* Print Assumptions complete_K. *)