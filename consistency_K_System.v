(***************************************************************************)
(* This is part of consistency_K, it is distributed under the terms of the *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*                        Copyright 2026-2031                              *)
(*       Xiang Ji, Dakai Guo, Qiming Wang, Tingting Ji and Wensheng Yu     *)
(***************************************************************************)

(** consistency_K_System *)

(* 一致与极大一致 *)
Require Import Base_ML.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.

(* 有矛盾公式集与一致集 *)
(* Definition Contradiction Γ := exists q, Γ ├ q /\ Γ ├ ¬q. *)
(* Locate Contradiction. *)

Definition consistence Γ := forall q, ~ (Γ ├ q /\ Γ ├ ¬q).

(* 一致集的性质 *)
Proposition redundancy_lemma : forall Γ p, Γ ∪ [/¬p] ├ p -> Γ ├ p.
Proof.
  intros. apply Deductive_Theorem in H. assert (Γ ├ (¬p → p) → p); autoK.
Qed.

(* 一致集的性质 *)
Proposition boom : forall Γ, ~ consistence Γ -> forall p, Γ ├ p.
Proof.
  intros. unfold consistence in H. apply not_all_not_ex in H as [? []].
  assert (Γ ├ x → ¬x → p); autoK. Unshelve. exact p. exact p. exact p. exact p.
Qed.

(* 一致集的性质 *)
Proposition No_contra : forall Γ, consistence Γ 
  -> forall p, consistence (Γ ∪ [/p]) \/ consistence (Γ ∪ [/¬p]).
Proof.
  intros. destruct (classic (consistence (Γ ∪ [/¬p]))); auto. pose proof boom.
  pose proof H1 (Γ ∪ [/¬p]) H0. pose proof H2 p. apply redundancy_lemma in H3.
  destruct (classic (consistence (Γ ∪ [/p]))); auto. pose proof H1 (Γ ∪ [/p]) H4.
  assert (forall p0, Γ ├ p0).
    { intros. pose proof H5 p0. apply Deductive_Theorem in H6.
      apply MP with p; auto. } 
  red in H. pose proof H p. destruct H7; split; auto.
Qed.

(***************************************************************************)
(*             定义与极大一致集的基本性质                                      *)
(***************************************************************************)

(* 极大一致集 *)
Definition maximal_consistent_set Γ :=
  consistence Γ /\ forall p, consistence (Γ ∪ [/p]) -> p ∈ Γ.

(* 极大一致集的基本性质 *)
(* 极大一致集Γ, Γ├p -> p∈Γ *)
Fact max_consistence_fact1 : forall Γ, maximal_consistent_set Γ
  -> forall p, Γ ├ p -> p ∈ Γ.
Proof.
  intros. destruct H. destruct (classic (p ∈ Γ)); auto.
  assert (forall p, ~ p ∈ Γ -> ~ consistence (Γ ∪ [/p])) as H1a.
    { intros. intro; auto. }
  apply H1a in H2. destruct H2. red. intros. intro. destruct H2.
  pose proof rule_Reduction_absurdity _ _ _ H2 H3. destruct (H p); tauto.
Qed.

(* 极大一致集Γ, ¬p∈Γ当且仅当p∉Γ *)
Fact max_consistence_fact2 : forall Γ, maximal_consistent_set Γ
  -> forall p, ¬p ∈ Γ <-> ~ p ∈ Γ.
Proof.
  intros. split; intros.
  - intro. destruct H. red in H. apply H with p. split; autoK.
  - pose proof H as MX. destruct H.
    assert (forall p, ~ p ∈ Γ -> ~ consistence (Γ ∪ [/p])) as H1a.
      { intros. intro; auto. }
    apply H1a in H0. red in H. unfold consistence in H0. 
    apply not_all_not_ex in H0. destruct H0 as [q []].
    pose proof rule_Reduction_absurdity _ _ _ H0 H2.
    apply max_consistence_fact1; auto.
Qed.

(* 极大一致集Γ, (p→q)∈Γ当且仅当~p∈Γ或q∈Γ *)
Fact max_consistence_fact3 : forall Γ p q, maximal_consistent_set Γ
  -> ((p → q) ∈ Γ <-> (¬p ∈ Γ \/ q ∈ Γ)).
Proof.
  intros Γ p q H. split; intros.
  - destruct (classic (q ∈ Γ)); auto. left; auto.
    apply (max_consistence_fact2 _ H) in H1. apply (max_consistence_fact2 _ H).
    intro. assert(Γ ├ p). { autoK. } assert(Γ ├ q). { autoK. }
    assert(Γ ├ ¬q). { constructor. auto. }
    destruct H as [H H6]. pose proof H q. destruct H7. auto. 
  - destruct H0.
    + destruct (classic (q ∈ Γ)).
      * assert (Γ ├ q) by autoK. assert (Γ ├ p → q). { eapply MP; eauto. autoK. }
        apply max_consistence_fact1 in H3; auto.
      * apply max_consistence_fact2 in H1; auto.
        assert (Γ ├ ¬p). { constructor. auto. }
        assert (Γ ├ ¬q). { constructor. auto. } assert (Γ ├ ¬q → ¬p) by autoK.
        assert (Γ ├ (¬ q → ¬ p) → p → q). { apply L3. }
        apply max_consistence_fact1; auto. eapply MP; eauto.
    + assert (Γ ├ q) by autoK. assert (Γ ├ p → q). { eapply MP; eauto. autoK. }
      apply max_consistence_fact1; auto.
Qed.
