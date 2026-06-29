(***************************************************************************)
(* This is part of compactness_K, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                  *)
(*               (see file LICENSE for more details)                       *)
(*                                                                         *)
(*                        Copyright 2026-2031                              *)
(*      Jiaxin Xie, Xiang Ji, Dakai Guo, Guowei Dou and Wensheng Yu        *)
(***************************************************************************)


(** compactness_K_System *)

Require Import Base_ML.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import soundness_K_System.
Require Import complete_K_System_pre.
Require Import satisfiability_K_System.
Require Import extension_K_System.
Require Import complete_K_System.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.

(* 紧致性：任给公式集 Γ 和公式 p , Γ ╞ p 当且仅当存在Γ的有穷子集 Γ' 使得 Γ' ╞ p *)
Theorem compactness_K : forall Γ p,
  Γ ╞ p <-> exists Γ', Γ' ⊆ Γ /\ Finite _ Γ' /\ Γ'╞ p.
Proof.
  split; intros.
  - apply complete_K in H. eapply sy_compactness in H as [Γ' [? []]]; eauto.
    exists Γ'. do 2 (split; auto). apply soundness_K. auto.
  - destruct H as [Γ' [? []]]. apply soundness_K. apply complete_K in H1.
    eapply subsetprove; eauto.
Qed.

(**************************************************************************)
(* 一致集都是可满足的 *)
(* Definition consistence_satisfiable := forall Γ, consistence Γ -> satisfyable_Γ Γ. *)
Fact consistence_satisfiable : consistence_satisfiable. 
Proof.
  red; intros. pose proof max_consistence_extension _ H as [Γ' [? []]].
  apply double_C_satisfiable; auto. rewrite double_C_consistence in H; auto.
  red. exists (D_I Γ' H0). unfold value. exists (@ assignment Γ' H0).
  pose proof model_sat Γ' H0 H2. red; intros. apply H1 in H4. apply H3; auto.
Qed.

Fact satisfyable_subset : forall Γ1 Γ2,
  Γ1 ⊆ Γ2 -> satisfyable_Γ Γ2 -> satisfyable_Γ Γ1.
Proof.
  intros. unfold satisfyable_Γ, satisfyable in *. destruct H0 as [MM [v ?]].
  exists MM, v. intros. specialize (H0 p).
  unfold Included in H. apply H, H0 in H1. auto.
Qed.

Fact unsatisfyable : forall Γ p, Γ ╞ (p ∧ ¬p) <-> ~ satisfyable_Γ Γ.
Proof.
  intros. split.
  - intros H1 H2. destruct H2 as [MM [v ?]]. specialize (H1 MM v H).
    apply H1. left. intro. apply H1. right. intro. contradiction.
  - intros. unfold Logically_implies. intros. exfalso.
    apply H. exists MM, v. auto.
Qed.

(* 有限可满足：Γ是有限可满足的当且仅当Γ的所有有限子集Γ0都是可满足的 *)
Definition finitely_satisfiable Γ :=
  forall Γ0, Γ0 ⊆ Γ /\ Finite _ Γ0 -> satisfyable_Γ Γ0.

Corollary compactness_equiv : 
  (forall Γ p, Γ ╞ p <-> exists Γ', Γ' ⊆ Γ /\ Finite _ Γ' /\ Γ'╞ p)
    <-> (forall Γ, finitely_satisfiable Γ <-> satisfyable_Γ Γ).
Proof.
  split; intros.
  - split; intros.
    + destruct (classic (satisfyable_Γ Γ)) as [ ]; auto.
      apply consistence_satisfiable. red. intros. exfalso.
      apply <- (unsatisfyable Γ q) in H1.
      apply H in H1 as [Γ' [? []]]. apply unsatisfyable in H3.
      unfold finitely_satisfiable in H0. specialize (H0 Γ'). auto.
    + unfold satisfyable_Γ in H0. destruct H0 as [MM [v ]]. red. exists MM, v.
      unfold satisfyable in *. intros. apply H0, H1. auto.
  - split; intros.
    + apply satisfiable_contra_le in H0.
      assert (~ finitely_satisfiable (Γ ∪ [/¬p])).
        { unfold not. intros. specialize (H (Γ ∪ [/¬p])). 
          destruct H. apply H in H1; auto. }
      unfold finitely_satisfiable in H1.
      apply not_all_ex_not in H1. destruct H1 as [Γ0 H1].
      apply not_all_ex_not in H1. destruct H1 as [H2 ?].
      destruct H2. set (Γ' := fun x => Γ0 x /\ Γ x). exists Γ'. repeat split.
      * unfold Included, Γ'. intros x [HxΓ0 HxΓ]. exact HxΓ.
      * eapply Finite_downward_closed. exact H3.
        unfold Included, Γ'. intros x [Hx _]. exact Hx.
      * apply satisfiable_contra_le. unfold not. intros Hsat.
        apply H1. eapply (satisfyable_subset _ (Γ' ∪ [/¬p])); eauto.
        unfold Included, Γ'. intros x Hx. specialize (H2 x Hx).
        destruct H2; [left; split | right]; auto.
    + destruct H0 as [Γ' [? []]]. apply soundness_K.
      apply complete_K in H2. apply (subsetprove Γ' Γ p); auto.
Qed.
