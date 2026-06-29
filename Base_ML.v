(**********************************************************************)
(*  This is part of Base_ML, it is distributed under the terms of the *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*    Dakai Guo, qiming Wang, Xiang Ji, Tingting Ji and Wensheng      *)
(**********************************************************************)

(** Base_ML *)

Require Export Coq.Sets.Ensembles.

Notation "a ∈ A" := (In _ A a)(at level 10).
Notation "B ∪ C" := (Union _ B C)(at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a)(at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B)(at level 70).

Corollary UnionI : forall {U} (a: U) B C, a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. split; intros; destruct H; eauto with sets. Qed.

Corollary Single : forall {U} (a x: U), a ∈ [ x ] <-> a = x.
Proof. split; intros. destruct H; auto. rewrite H. split. Qed.

Global Hint Resolve UnionI Single: sets.

Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Epsilon.

Theorem classicT : forall (P : Prop), {P} + {~P}.
Proof.
  intros. assert {x : bool | if x then P else ~P}.
  { apply constructive_indefinite_description. destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H, x; auto.
Qed.

Lemma ex_not_not_all : forall (A : Type) (P : A -> Prop),
  (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
  intros A P [x Hx] H. apply (H x). exact Hx.
Qed.

Lemma not_all_not_ex : forall (A : Type) (P : A -> Prop),
  ~ (forall x, ~ P x) -> exists x, P x.
Proof.
  intros A P H. apply NNPP. intro H'. apply H. intros x Hx.
  apply H'. exists x. exact Hx.
Qed.

Lemma not_all_ex_not : forall (A : Type) (P : A -> Prop),
  ~ (forall x, P x) -> exists x, ~ P x.
Proof.
  intros A P H. apply not_all_not_ex. intro H'. apply H.
  intros x. apply NNPP. apply H'.
Qed.