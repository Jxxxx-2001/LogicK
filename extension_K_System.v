(***************************************************************************)
(*  This is part of extension_K, it is distributed under the terms of the  *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*                        Copyright 2026-2031                              *)
(*      Xiang Ji, Dakai Guo, Guowei Dou, Jiaxin Xie and Wensheng Yu        *)
(***************************************************************************)

(** extension_K_System *)

Require Import Base_ML.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import consistency_K_System.
Require Import complete_K_System_pre.
Require Import Mappings_ML.
Require Import bijection_nat_formula_K.

Require Import Coq.micromega.Lia.
(* Require Import Coq.Sets.Finite_sets. *)
Require Import Coq.Sets.Finite_sets_facts.
Import VectorNotations.

(**************************************************************************)
(*       在扩张了常量的一阶语言中，将一致集Γ逐步扩张为一个极大一致集Γ'            *)
(**************************************************************************)
Section max_consistence_extention.
Variable Γ : Ensemble Formula.
Hypothesis H_consistence_set : consistence Γ.
Let Γ' := double_C_set Γ.
Variable fun_NF : nat -> Formula.
Hypothesis NF_bij : function_bijective fun_NF.

(* 算出前 n 个公式里的常元最大下标 *)
Fixpoint max_c_formula_up_to n :=
  match n with
  | O => max_c_formula (fun_NF O)
  | S n' => max (max_c_formula (fun_NF (S n'))) (max_c_formula_up_to n')
  end.

(* 动态生成第 n 步所需的新奇数常元下标 *)
Definition fresh_odd_c n := 1 + 2 * (max_c_formula_up_to n + n).

(* Consistent Extence (CE) *)
(* 定义Г_i: Г_0 = Г'
 Case 1: Г_n ∪ {p_n} is not consistence. We let Г_n+1 = Г_n.
 Case 2: Г_n ∪ {p_n} is consistence, and p_n is not of the form (Not (Forall x p)),
         We let Г_n+1 = Г_n ∪ {p_n}.
 Case 3: Г_n ∪ {p_n} is consistence, and p_n is of the form (Not (Forall x p)),
         We let Г_n+1 = Г_n ∪ {p_n} ∪ (¬p[c_(2n+1)/x]). *)
Fixpoint CE (n : nat) : Ensemble Formula :=
  match n with
  | O => Γ'
  | S n' => match (classicT (consistence ((CE n') ∪ [/ (fun_NF n')]))) with
            | right _ => CE n'
            | left _ => match (fun_NF n') with
                        | Not (ForAll x p) => (CE n') ∪ [/ (fun_NF n')]
                                 ∪ [/ Not (p {x ;; (Tcon (C (fresh_odd_c n')))})]
                        | _ => (CE n') ∪ [/ (fun_NF n')]
                        end
            end
  end.

(* CE_all = ∪ (CE i) *)
Definition CE_all : Ensemble Formula := fun p => exists n, p ∈ (CE n).

Lemma sy_compactness : forall Γ p, 
  Γ ├ p <-> exists Γ', Γ' ⊆ Γ /\ Finite _ Γ' /\ Γ'├ p.
Proof.
  split; intros.
  - induction H.
    + exists [/p]. split.
      * red; intros. destruct H0. auto.
      * split; try autoK. pose proof Empty_is_finite Formula.
        assert ([/p]=(Add _ Φ p)).
          { apply Extensionality_Ensembles. split; red; intros. unfold Add. ES.
            destruct H1. ES. auto. }
        rewrite H1; constructor; auto. intro. ES.
    + exists Φ. repeat split. red; ES. constructor. apply K1. auto.
    + destruct IHdeduce_K1 as [Γ1 [? []]]. destruct IHdeduce_K2 as [Γ2 [? []]].
      exists (Γ1 ∪ Γ2). repeat split. ES. apply Union_preserves_Finite; auto.
      pose proof Union_l _ _ H3 Γ2. pose proof Union_r _ _ H6 Γ1. autoK.
  - destruct H as [? [? []]]. eapply subsetprove; eauto.
Qed.

(* 有限公式集中的变量小标拥有最大上界 *)
Fact finite_max_v : forall Γ, Finite Formula Γ ->
  exists n, forall q, q ∈ Γ -> max_v_formula q < n.
Proof.
  intros. induction H.
  - exists 0. intros q Hq. inversion Hq.
  - destruct IHFinite as [n Hn]. exists (S (max n (max_v_formula x))).
    intros. inversion H1; subst. apply Hn in H2. lia. inversion H2. subst. lia.
Qed.

(* 计算推导变量小标上界 N *)
Fact deduce_subst_c_v_bound : forall Γ p c, Γ ├ p
  -> exists N, forall y_id, y_id > N
  -> (forall q, q ∈ Γ -> ~ c ∈ (Formula_C_set q))
  -> (forall q, q ∈ Γ -> ~ (X y_id) ∈ (Formula_Ens q))
  -> ~ (X y_id) ∈ (Formula_Ens p) -> Γ ├ (p {/ c ;; Tvar (X y_id)}).
Proof.
  intros. induction H.
  - exists 0. intros. rewrite subst_fc_not_in. apply K0; auto. apply H1; auto.
  - exists 0. intros. apply K1. apply Axiom_subst_fc; auto.
  - destruct IHdeduce_K1 as [N1 HN1]. destruct IHdeduce_K2 as [N2 HN2].
    exists (max (max N1 N2) (max_v_formula p)). intros.
    assert (~ (X y_id) ∈ (Formula_Ens p)). { apply max_v_formula_bound. lia. }
    assert (~ (X y_id) ∈ (Formula_Ens (p → q))).
      { intro. simpl in H6. apply UnionI in H6 as []; contradiction. }
    assert (Γ0 ├ (p → q) {/ c ;; Tvar (X y_id)}). { apply HN1; try lia; auto. }
    assert (Γ0 ├ p {/ c ;; Tvar (X y_id)}). { apply HN2; try lia; auto. }
    eapply MP; eauto.
Qed.

(* Lemma_3_4_32_Flexible *)
Lemma Lemma_Flexible : forall Γ f0 v c, Γ ├ (f0 {v ;; Tcon c})
  -> (forall q, q ∈ Γ -> ~ c ∈ (Formula_C_set q))
  -> ~ c ∈ (Formula_C_set f0) -> Γ ├ (∀ v, f0).
Proof.
  intros Γ0 f0 v c H_ded_c H_c_gamma H_c_f0.
  apply sy_compactness in H_ded_c as [Γ0' [Hsub [Hfin Hded']]].
  pose proof (finite_max_v Γ0' Hfin) as [max_v Hmax_v].
  pose proof (deduce_subst_c_v_bound Γ0' _ c Hded') as [N HN].
  set (y_id := max (max N max_v) (max_v_formula f0) + 1).
  set (y := X y_id).
  assert (Hy_not_in_f0 : ~ y ∈ (Formula_Ens f0)).
    { eapply max_v_formula_bound. unfold y_id. lia. }
  assert (Hy_not_in_f0c : ~ y ∈ (Formula_Ens (f0 {v ;; Tcon c}))).
    { intro Hin. apply formula_Ens_subst_c in Hin.
      apply max_v_formula_bound in Hin; [contradiction|]. unfold y_id. lia. }
  assert (Hy_not_in_gamma : forall q, q ∈ Γ0' -> ~ y ∈ (Formula_Ens q)).
    { intros q Hq Hin. apply max_v_formula_bound in Hin; [contradiction|].
      pose proof (Hmax_v q Hq). unfold y_id. lia. }
  assert (H_ded_y : Γ0' ├ (f0 {v ;; Tcon c}) {/ c ;; Tvar y}).
    { apply HN; auto. unfold y_id. lia. }
  assert (H_subst_eq : (f0 {v ;; Tcon c}) {/ c ;; Tvar y} = f0 {v ;; Tvar y}).
    { eapply subst_f_fc_commute; eauto. }
  rewrite H_subst_eq in H_ded_y.
  assert (H_forall_y : Γ0' ├ (∀ y, f0 {v ;; Tvar y})).
    { apply Gen_Rule_1'; auto. intros. apply Hy_not_in_gamma in H.
      intro. apply H. apply free_contain_Ens. auto. }
  pose proof (prop_3_12_1 f0 v y Hy_not_in_f0) as H_alpha_iff.
  assert (H_alpha_deduce : Γ0' ├ (∀ y, (f0) {v;; Tvar y}) → (∀ v, f0)).
    { pose proof (Union_l Φ _ H_alpha_iff Γ0'). rewrite Union_empty_l in H.
      apply equivalent_theorem in H as [H1 H2]. auto. }
  assert (H_forall_v : Γ0' ├ (∀ v, f0)). { eapply MP; eauto. }
  eapply subsetprove; eauto.
Qed.

(**************************************************************************)
Fact max_c_formula_up_to_mono : forall n i,
  n <= i -> max_c_formula_up_to n <= max_c_formula_up_to i.
Proof.
  intros. induction H. auto. simpl.
  assert (max_c_formula_up_to m
   <= Nat.max (max_c_formula (fun_NF (S m))) (max_c_formula_up_to m)).
  { apply Nat.le_max_r. } lia.
Qed.

Fact fresh_c_mono : forall i j, i < j -> fresh_odd_c i < fresh_odd_c j.
Proof.
  intros. unfold fresh_odd_c. assert (i <= j) by lia.
  pose proof (max_c_formula_up_to_mono i j H0). lia.
Qed.

Fact fresh_c_bound : forall n, max_c_formula (fun_NF n) < fresh_odd_c n.
Proof.
  intros. assert (max_c_formula (fun_NF n) <= max_c_formula_up_to n).
  { destruct n; simpl; lia. } unfold fresh_odd_c. lia.
Qed.

Fact max_c_term_bound : forall t c_n,
  (C c_n) ∈ (term_C_set t) -> c_n <= max_c_term t.
Proof.
  fix IH 1. intros t c_n H. destruct t; simpl in *; try inversion H. lia.
  revert H. induction t; simpl; intros. inversion H.
  apply UnionI in H as [Hin_h | Hin_q].
  - apply IH in Hin_h. apply Nat.le_trans with (max_c_term h). auto.
    apply Nat.le_max_l.
  - apply IHt in Hin_q. apply Nat.le_trans with
    (let fix max_c_vc n r := match r with
                             | [] => 0
                             | h0 :: q' 
                                 => Init.Nat.max (max_c_term h0) (max_c_vc _ q')
                            end in max_c_vc n t).
    auto. apply Nat.le_max_r.
Qed.

Fact max_c_formula_bound : forall p c_n,
  (C c_n) ∈ (Formula_C_set p) -> c_n <= max_c_formula p.
Proof.
  induction p; intros c_n H; simpl in *; auto.
  - apply UnionI in H as []; apply max_c_term_bound in H; lia.
  - revert H. induction t; intros. inversion H. simpl in *. 
    apply UnionI in H as []. apply max_c_term_bound in H. lia. apply IHt in H. lia.
  - apply UnionI in H as []; [apply IHp1 in H | apply IHp2 in H]; lia.
Qed.

Fact double_C_term_even : forall t c_n,
  (C c_n) ∈ (term_C_set (double_C_term t)) -> exists k, c_n = 2 * k.
Proof.
  fix IH 1. intros t c_n H. destruct t; simpl in H. inversion H.
  - destruct c as [m]. inversion H; subst. exists m. auto.
  - revert H. induction t; simpl; intros. inversion H.
    apply UnionI in H as []. apply IH in H. auto. apply IHt in H. auto.
Qed.

Fact Gamma_prime_even : forall q c_n,
  q ∈ Γ' -> (C c_n) ∈ (Formula_C_set q) -> exists k, c_n = 2 * k.
Proof.
  intros. inversion H; subst. clear H H1. revert c_n H0.
  induction p; intros; simpl in H0; try (eapply IHp; eauto).
  - apply UnionI in H0 as []; eapply double_C_term_even; eauto.
  - revert c_n H0. induction t; intros; simpl in H0. inversion H0.
    apply UnionI in H0 as []. eapply double_C_term_even; eauto. eapply IHt; eauto.
  - apply UnionI in H0 as []. eapply IHp1; eauto. eapply IHp2; eauto.
Qed.

Fact CE_S_inversion : forall n q, q ∈ (CE (S n))
  -> (q ∈ (CE n)) \/ (q = fun_NF n)
  \/ (exists p x, fun_NF n = Not (ForAll x p)
     /\ q = Not (substitute_f p (Tcon (C (fresh_odd_c n))) x)).
Proof.
  intros n q H. simpl in H. destruct classicT.
  - destruct (fun_NF n) eqn:Enf;
    try (inversion H; subst; [left; auto | right; left; inversion H0; auto]).
    destruct f eqn : Ef;
    try do 4 (inversion H; subst; [left; auto | right; left; inversion H0; auto]).
    inversion H. inversion H0. subst; auto.
    apply Single in H2. right. left. auto. apply Single in H0. right. right.
    exists f0,v. auto.
  - left. auto.
Qed.

Fact CE_elements_source : forall n q, q ∈ (CE n)
  -> (q ∈ Γ') \/ (exists i, i < n /\ q = fun_NF i)
  \/ (exists i p x, i < n /\ fun_NF i = Not (ForAll x p) /\
                 q = Not (substitute_f p (Tcon (C (fresh_odd_c i))) x)).
Proof.
  induction n; intros. simpl in H; auto. apply CE_S_inversion in H as [H|[]].
  - apply IHn in H as []; auto. destruct H as [[i[]]|]. right. left. 
    exists i; auto. do 4 destruct H. right. right. exists x, x0, x1; auto.
  - right. left. exists n. auto.
  - right. right. destruct H as [p[]]. exists n, p, x; auto.
Qed.

Fact CE_no_fresh_c : forall n q,
  q ∈ (CE n) -> ~ (C (fresh_odd_c n)) ∈ (Formula_C_set q).
Proof.
  intros. apply CE_elements_source in H as [H |[]].
  - intro. apply Gamma_prime_even in H0 as []; auto. unfold fresh_odd_c in H0. lia.
  - destruct H as [i []]. subst q. intro. apply max_c_formula_bound in H0.
    pose proof fresh_c_bound i. apply fresh_c_mono in H. lia.
  - destruct H as [i [p [x [H [Hn Hq]]]]]. subst q. simpl. intro.
    apply C_in_subst in H0 as [].
    + assert ((C (fresh_odd_c n)) ∈ (Formula_C_set (fun_NF i))).
        { rewrite Hn. simpl. auto. }
      apply max_c_formula_bound in H1.
      pose proof (fresh_c_bound i). apply fresh_c_mono in H. lia.
    + simpl in H0. apply Single in H0. apply fresh_c_mono in H. inversion H0.
      unfold fresh_odd_c in H. lia.
Qed.

Fact fresh_c_not_in_CE : forall n q, q ∈ (CE n ∪ [/(fun_NF n)])
  -> ~ (C (fresh_odd_c n)) ∈ (Formula_C_set q).
Proof.
  intros. destruct H. eapply CE_no_fresh_c; eauto. inversion H. intro.
  apply max_c_formula_bound in H1. pose proof (fresh_c_bound n). 
  rewrite H0 in *. lia.
Qed.

Fact CE_le1 : forall n : nat, consistence (CE n).
Proof.
  induction n; simpl.
  - rewrite double_C_consistence in H_consistence_set. unfold Γ'. auto.
  - destruct classicT as [Hc | Hnc]; auto. destruct (fun_NF n) eqn: E_nf; try tauto. 
    destruct f eqn:E_f; try tauto. set (Gamma := CE n ∪ [/¬ (∀ v, f0)]) in *.
    set (c' := Tcon (C (fresh_odd_c n))) in *.
    destruct (classicT (consistence (Gamma ∪ [/¬ (f0) {v;; c'}]))); auto.
    assert (Gamma ├ ¬ (∀ v, f0)). { apply K0, UnionI. right. apply In_singleton. }
    assert (Gamma ├ (∀ v, f0)).
      { apply Lemma_Flexible with (c := (C (fresh_odd_c n))).
        - apply redundancy_lemma, boom. auto.
        - intros q Hq. apply fresh_c_not_in_CE; rewrite E_nf; auto.
        - assert ((Formula_C_set f0) = (Formula_C_set ¬f)).
            { rewrite E_f. simpl. auto. }
          rewrite H0. apply fresh_c_not_in_CE. right. rewrite E_nf.
          apply Single. rewrite E_f. auto. }
    pose proof Hc (∀ v, f0). tauto.
Qed.

(**************************************************************************)
(* for any m,n, if m <= n, then (CE m) ⊆ (CE n) *)
Fact CE_monotone : forall m n, m <= n -> (CE m) ⊆ (CE n).
Proof.
  induction n; intros; red; intros.
  - induction m; auto. inversion H.
  - assert (m <= n \/ m = S n) as []. { inversion H; auto. }
    + apply IHn in H1. apply H1 in H0. simpl. destruct classicT; simpl; auto.
      destruct (fun_NF (S n)); destruct (fun_NF n); try (left; auto);
      try (destruct f; left; try auto); try (left; auto);
      destruct f0; left; try auto; left; auto.
    + rewrite H1 in *; auto.
Qed.

Fact subsetNocontra : forall A B , A ⊆ B -> consistence B -> consistence A.
Proof.
  intros. red. intros. intro. red in H0. destruct (H0 q).
  destruct H1; split; eapply subsetprove; eauto.
Qed.

Fact CE_le2 : forall m n, (CE m) ⊆ (CE n) \/  (CE n) ⊆ (CE m).
Proof.
  intros. destruct (classicT (n <= m)). apply CE_monotone in l; auto.
  assert (m <= n). lia. apply CE_monotone in H; auto.
Qed.

Fact CE_le3 : forall p, CE_all ├ p -> exists n, (CE n) ├ p.
Proof.
  intros. induction H.
  - red in H; red in H. destruct H as [n H]. exists n; autoK.
  - exists 0. autoK.
  - destruct IHdeduce_K1, IHdeduce_K2. destruct (CE_le2 x x0).
    pose proof subsetprove _ _ _ H3 H1. exists x0. apply MP with p; auto.
    pose proof subsetprove _ _ _ H3 H2. exists x. apply MP with p; auto.
Qed.

(* CE_all是一致集 *)
Lemma CE_all_consistence : consistence CE_all.
Proof.
  red; intros. intro. destruct H. apply CE_le3 in H as [], H0 as [].
  destruct (CE_le2 x x0).
  - pose proof @ subsetprove _ _ _ H1 H. pose proof CE_le1 x0. red in H3. 
    destruct (H3 q); tauto.
  - pose proof @ subsetprove _ _ _ H1 H0. pose proof CE_le1 x.
    red in H3; destruct (H3 q); tauto.
Qed.

(* CE_all是极大的 *)
Lemma CE_all_max : forall p, ~ p ∈ CE_all -> ~ consistence (CE_all ∪ [/p]).
Proof.
  intros. intro. destruct H. inversion NF_bij. destruct (H1 p) as [pn ?].
  assert (consistence ((CE pn) ∪ [/p])).
    { apply subsetNocontra with (CE_all ∪ [/p]); auto. red; intros.
      destruct H3. left. exists pn; auto. right; auto. }
  red; red. exists (S pn). simpl. rewrite H2 in *.
  destruct (classicT (consistence (CE pn ∪ [/p]))); try tauto.
  do 2 (destruct p; try (right; split)). left; right; split.
Qed.

(* CE_all 具有亨金证据 *)
Lemma CE_all_wit : witness_property CE_all.
Proof.
  red; intros. inversion NF_bij as [NF_inj NF_sur].
  destruct (NF_sur (¬(∀ x, p))) as [n ?].
  assert (consistence ((CE n) ∪ [/ ¬(∀ x, p)])).
    { apply subsetNocontra with CE_all; auto.
      - red; intros. destruct H1. exists n; auto. destruct H1. auto.
      - apply CE_all_consistence. }
  exists (C (fresh_odd_c n)).
  assert ((CE (S n)) ⊆ CE_all). { red; intros; exists (S n); auto. }
  apply H2. simpl. rewrite H0 in *.
  destruct classicT; try tauto. right. constructor.
Qed.

End max_consistence_extention.

(******************************************************************)
(*                           公式可数性                            *)
(******************************************************************)

(* (* 自然数和公式存在一一对应. *)
Lemma bijection_nat_formula : bijection nat Formula. *)

(******************************************************************)
(*         扩张引理: 任意一致集都可以扩张成具有见证性的极大一致集        *)
(******************************************************************)

Theorem max_consistence_extension : forall Γ, consistence Γ 
  ->  exists Γ', maximal_consistent_set Γ'
   /\ double_C_set Γ ⊆ Γ' /\ witness_property Γ'.
Proof.
  intros. pose proof bijection_nat_formula as []. exists (CE_all Γ bij_f). split.
  - split. apply CE_all_consistence. auto. intros.
    destruct (classicT (p ∈ (CE_all Γ bij_f))); auto.
    pose proof (CE_all_max). apply H1 in n. contradiction. split; auto.
  - split. red; intros. red. red. exists 0. simpl. auto.
    apply CE_all_wit; auto. split; auto.
Qed.
