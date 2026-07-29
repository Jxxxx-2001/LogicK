(******************************************************************************)
(* This is part of satisfiability_K, it is distributed under the terms of the *)
(*              GNU Lesser General Public License version 3                   *)
(*                 (see file LICENSE for more details)                        *)
(*                                                                            *)
(*                          Copyright 2026-2031                               *)
(*        Dakai Guo, Qiming Wang, Xiang Ji, Tingting Ji and Wensheng Yu       *)
(******************************************************************************)

(** satisfiability_K_System *)

Require Import Base_ML.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import consistency_K_System.
Require Import complete_K_System_pre.
Require Import bijection_nat_formula_K.

Require Import Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Program.Equality.
Import VectorNotations.


Section model_existence_proof.
Variable Γ : Ensemble(Formula).
Hypothesis H_mc : maximal_consistent_set Γ.
Hypothesis H_wp : witness_property Γ.

(***************************************************************************)
(*        1     等词 与 等价                          *)
(***************************************************************************)
(* 定义两个项满足等词关系 *)
Definition term_equality_relation : term -> term -> Prop :=
  fun t1 t2 => (equality t1 t2) ∈ Γ.

(* 等词关系满足自反性 *)
Fact term_equality_relation_refl : reflexive _ term_equality_relation.
Proof.
  unfold reflexive, term_equality_relation. intro t.
  apply max_consistence_fact1; auto. apply K1. apply E1.
Qed.

(* 等词关系满足对称性 *)
Fact term_equality_relation_sym : symmetric _ term_equality_relation.
Proof.
  unfold symmetric, term_equality_relation. intros t1 t2 H.
  apply max_consistence_fact1; auto. apply MP with (equality t1 t2).
  - apply K1. apply E2.
  - apply K0. auto.
Qed.

(* 等词关系满足传递性 *)
Fact term_equality_relation_tran : transitive _ term_equality_relation.
Proof.
  unfold transitive, term_equality_relation. intros t1 t2 t3 H3 H4.
  apply max_consistence_fact1; auto. apply MP with (equality t2 t3).
  - apply MP with (equality t1 t2).
    + apply K1. apply E3.
    + apply K0. auto.
  - apply K0. auto.
Qed.

(* 等词关系满足等价关系 *)
Fact term_equality_relation_equiv : equivalence _ term_equality_relation.
Proof.
  split.
  - apply term_equality_relation_refl.
  - apply term_equality_relation_tran.
  - apply term_equality_relation_sym.
Qed.

(* 辅助引理：equality_4的性质 *)
Lemma equality_4_apply : forall (r: Formula) (m: nat) (v1 v2: Vector.t term m),
  Γ ├ equality_4 r m m v1 v2 -> Forall2 (fun t1 t2 => (equality t1 t2) ∈ Γ) v1 v2
  -> Γ ├ r.
Proof.
  intros r m v1. revert r. induction v1; intros r v2 H HForall.
  - (* 空向量情况 *)
    simpl in H. auto.
  - (* cons情况 *)
    dependent destruction v2. dependent destruction HForall. simpl in H. 
    eapply IHv1.
    + eapply MP; [apply H | apply K0; apply H0].
    + apply HForall.
Qed.

(* 对于任意n元函数符号f, 任意项s1、s2、……、sn, t1、t2、……、tn, 
   如果对任意i, si和ti满足等词关系, 
   那么f(s1, s2, ……, sn)和f(t1, t2, …… ,tn)满足等词关系 *)
Lemma If_equality' : forall f (v1 v2: Vector.t term (arity_F f)),
  Forall2 (fun t1 t2 => term_equality_relation t1 t2) v1 v2 
  -> term_equality_relation (Tfun f v1) (Tfun f v2).
Proof.
  intros. unfold term_equality_relation.
  (* 使用max_consistence_fact1 *)
  apply max_consistence_fact1; auto.
  (* 应用E5公理 *)
  pose proof (K1 Γ (equality_4 (equality (Tfun f v1) (Tfun f v2))
                     (arity_F f) (arity_F f) v1 v2) (E5 f v1 v2)).
  (* 使用equality_4_apply *)
  eapply equality_4_apply; eauto.
Qed.

(* 辅助引理: 将Forall2 term_equality_relation转换为Forall2 (equality ... ∈ Γ) *)
Lemma Forall2_term_eq_to_in_Gamma : forall {n} (v1 v2: Vector.t term n),
  Forall2 (fun t1 t2 => term_equality_relation t1 t2) v1 v2
  -> Forall2 (fun t1 t2 => (equality t1 t2) ∈ Γ) v1 v2.
Proof.
  intros n v1. induction v1; intros v2 HF.
  - dependent destruction v2. constructor.
  - dependent destruction v2. dependent destruction HF. constructor.
    + unfold term_equality_relation in HF. auto.
    + apply IHv1. auto.
Qed.

(* 向量版本的Forall2对称性引理 *)
Lemma Forall2_vec_sym : forall {A n} (R: A -> A -> Prop) (v1 v2: Vector.t A n),
  (forall x y, R x y -> R y x) -> Forall2 R v1 v2 -> Forall2 R v2 v1.
Proof.
  intros A n R v1. induction v1; intros v2 Hsym HF.
  - dependent destruction v2. constructor.
  - dependent destruction v2. dependent destruction HF. constructor.
    + apply Hsym. auto.
    + apply IHv1; auto.
Qed.

(* 对于任意n元关系符号r, 任意项s1、s2、……、sn, t1、t2、……、tn, 
   如果对任意i, 有si和ti满足等词关系, 
   那么r(s1, s2, ……, sn)∈Γ当且仅当r(t1, t2, …… ,tn)∈Γ *)
Lemma IR_equality' : forall r (v1 v2: Vector.t term (arity_R r)),
  Forall2 (fun t1 t2 => term_equality_relation t1 t2) v1 v2
  -> (atomic r v1) ∈ Γ <-> (atomic r v2) ∈ Γ.
Proof.
  intros r v1 v2 H.
  split; intros.
  - (* 正向：atomic r v1 ∈ Γ -> atomic r v2 ∈ Γ *) (* 转换Forall2 *)
    pose proof (Forall2_term_eq_to_in_Gamma v1 v2 H) as HForall.
    (* 应用E4公理 *)
    pose proof (K1 Γ (equality_4 (atomic r v1 → atomic r v2) 
                       (arity_R r) (arity_R r) v1 v2) (E4 r v1 v2)) as HE4.
    (* 使用equality_4_apply得到蕴含式 *)
    assert (Γ ├ atomic r v1 → atomic r v2) as Himpl.
      { eapply equality_4_apply; eauto. }
    (* 应用MP规则 *)
    assert (Γ ├ atomic r v2) as Hderive.
      { eapply MP. apply Himpl. apply K0. auto. }
    (* 使用max_consistence_fact1 *)
    apply max_consistence_fact1; auto.
  - (* 反向：atomic r v2 ∈ Γ -> atomic r v1 ∈ Γ *) (* 利用等词关系的对称性 *)
    assert(HForall_rev: Forall2 (fun t1 t2 => term_equality_relation t1 t2) v2 v1).
      { apply Forall2_vec_sym; auto.
        intros. apply term_equality_relation_sym. auto. }
    (* 转换Forall2 *)
    pose proof (Forall2_term_eq_to_in_Gamma v2 v1 HForall_rev) as HForall.
    (* 应用E4公理(v2到v1方向) *)
    pose proof (K1 Γ (equality_4 (atomic r v2 → atomic r v1) 
                       (arity_R r) (arity_R r) v2 v1) (E4 r v2 v1)) as HE4.
    (* 使用equality_4_apply得到蕴含式 *)
    assert (Γ ├ atomic r v2 → atomic r v1) as Himpl.
      { eapply equality_4_apply; eauto. }
    (* 应用MP规则 *)
    assert (Γ ├ atomic r v1) as Hderive.
      { eapply MP. apply Himpl. apply K0. auto. }
    (* 使用max_consistence_fact1 *)
    apply max_consistence_fact1; auto.
Qed.

(***************************************************************************)
(*             等价类                        *)

(* 定义项的等价类的集族 *)
Inductive term_equality_relation_family : (term -> Prop) -> Prop :=
  | term_equality_relation_family_intro : forall t,
      term_equality_relation_family (term_equality_relation t).

(* 等价类的非空性 *)
Fact inhabit_tecf : forall A, term_equality_relation_family A -> exists x, A x.
Proof.
  intros. destruct H. exists t. red. apply term_equality_relation_refl.
Qed.

(* 若term_equality_relation t t0,
   则term_equality_relation t = term_equality_relation t0*)
Fact eq_term_set : forall t t0, term_equality_relation t t0
  -> term_equality_relation t = term_equality_relation t0.
Proof.
  intros. apply Extensionality_Ensembles. split; red; intros.
  - red in H0; red. apply term_equality_relation_sym.
    apply term_equality_relation_sym in H0.
    apply term_equality_relation_tran with t; auto.
  - red in H0; red. apply term_equality_relation_tran with t0; auto.
Qed.

Fact term_equality_relation_family_intro_equiv : forall t t0,
  term_equality_relation t = term_equality_relation t0
  -> term_equality_relation_family (term_equality_relation t)
       = term_equality_relation_family (term_equality_relation t0).
Proof. intros. f_equal. auto. Qed.

(***************************************************************************)
(*         2    论域构造                         *)
(***************************************************************************)

(* 定义论域类型 *)
Definition domain := sig term_equality_relation_family.
Print sig.

Fact projection_injective_domain :
  forall t1 t2: domain, proj1_sig t1 = proj1_sig t2 -> t1 = t2.
Proof.
  intros. destruct t1, t2. simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.
Print proj1_sig.

(* 定义论域的元素 *)
Definition term_domain (t: term) : domain :=
  exist _ (term_equality_relation t) (term_equality_relation_family_intro t).

(* 辅助引理：从 domain 提取对应的项 *)
Fact domain_has_term : forall (m : domain), exists t, m = term_domain t.
Proof.
  intros [m_set Hm_set]. destruct Hm_set as [t]. exists t. unfold term_domain.
  apply projection_injective_domain. simpl. reflexivity.
Qed.

Fact eq_term_to_domain : forall t t0, term_equality_relation t t0
  -> term_domain t = term_domain t0.
Proof.
  intros. pose proof eq_term_set _ _ H.
  pose proof term_equality_relation_family_intro_equiv _ _ H0.
  unfold term_domain. apply projection_injective_domain. simpl. auto.
Qed.

Fact eq_domain_to_term : forall t t0, term_domain t = term_domain t0
  -> term_equality_relation t t0.
Proof.
  intros. unfold term_domain in H. inversion H. rewrite H1.
  apply term_equality_relation_refl.
Qed.

(* pick函数: 从存在性证明中提取元素 *)
Definition pick {A} {P : A -> Prop} (l : exists x, P x) :=
  proj1_sig (constructive_indefinite_description _ l).

(* 将项的等价类类型转化为term类型 *)
Definition domain_term (d: domain) : term.
  destruct d as [d Hd]. pose proof inhabit_tecf d. apply H in Hd.
  refine (pick _). apply Hd.
Defined.

Fact inv_domain_term : forall t,
  term_equality_relation (domain_term (term_domain t)) t.
Proof.
  intros. red. unfold term_domain. unfold domain_term.
  unfold pick. destruct constructive_indefinite_description. simpl.
  red in t0. apply term_equality_relation_sym. auto.
Qed.

(***************************************************************************)
(*             解释函数                        *)

(* 定义I_c *)
Definition Ic (c: Con) : domain := term_domain (Tcon c).

(* 对任意项 t，存在常元 c 使得 (c = t) ∈ Γ *)
Lemma exist_const_for_term : forall t, exists c, (equality (Tcon c) t) ∈ Γ.
Proof.
  intros t. remember (fresh_var t) as y. remember (¬(equality (Tvar y) t)) as phi.
  destruct (classic (y ∈ (term_Ens t))).
  - pose proof fresh_var_not_in t. elim H0. subst; auto.
  - assert (Hneg_forall : ¬(∀ y, phi) ∈ Γ).
    { apply max_consistence_fact1; auto.
      assert (Hneg_eq : (Γ ∪ [/∀ y, phi]) ├ ¬(equality t t)).
      { assert (Ht_free : t_x_free phi t y = true).
        { subst phi y. simpl. destruct (classicT
            (X 0 ∈ (Formula_free_Ens (¬(equality (Tvar (X 0)) t))))).
          - simpl in i. destruct i; auto.
          - auto. }
        assert (Hinst : (Γ ∪ [/∀ y, phi]) ├ (∀ y, phi) → substitute_f phi t y).
        { apply K1. apply S'. exact Ht_free. }
        assert (Hforall : (Γ ∪ [/∀ y, phi]) ├ ∀ y, phi).
        { apply K0. right. split. }
        assert (Hsubst : (Γ ∪ [/∀ y, phi]) ├ substitute_f phi t y).
        { apply MP with (∀ y, phi); auto. }
        assert (Heq_subst : substitute_f phi t y = ¬(equality t t)).
        { subst phi y. simpl. f_equal. f_equal.
          bdestruct (max_v_term t =? max_v_term t); auto.
          destruct H0; lia. pose proof subst_term_ignore. apply H0; auto. }
        rewrite Heq_subst in Hsubst. exact Hsubst. }
      assert (Heq : (Γ ∪ [/∀ y, phi]) ├ equality t t).
      { apply Union_l. apply K1. apply E1. }
      apply MP with (equality t t); autoK.
      pose proof rule_Reduction_absurdity _ _ _ Heq Hneg_eq. autoK. }
    specialize (H_wp phi y Hneg_forall). destruct H_wp as [c Hc].
    assert (Hsubst_c : substitute_f phi (Tcon c) y = ¬(equality (Tcon c) t)).
    { subst phi y. simpl. pose proof subst_term_ignore. f_equal. f_equal.
      bdestruct (max_v_term t =? max_v_term t); auto.
      destruct H1; lia. apply H0; auto. }
    rewrite Hsubst_c in Hc.
    exists c. apply max_consistence_fact1; auto. apply MP with (¬¬((Tcon c) ≃ t)).
    apply law_double_negation. apply K0. auto.
Qed.

(* 推论：Ic c 和 term_domain t 在 domain 中相等 *)
Corollary exist_const_for_domain : forall t, exists c, Ic c = term_domain t.
Proof.
  intros t. destruct (exist_const_for_term t) as [c Hc]. exists c. unfold Ic.
  apply eq_term_to_domain. unfold term_equality_relation. exact Hc.
Qed.

(* 定义I_f *)
Definition If (f: Fun) (v: Vector.t domain (arity_F f)) : domain :=
  term_domain (Tfun f (Vector.map domain_term v)).

(* 定义I_R *)
Definition IR (r: Rel) (v: Vector.t domain (arity_R r)) : Prop :=
  (atomic r (Vector.map domain_term v)) ∈ Γ.

(* 结构(domain,I) *)
Definition D_I : Module := {|
  M := domain;
  I_c := Ic;
  I_f := If;
  I_R := IR |}.

(***************************************************************************)
(*           3  指派与赋值                         *)
(***************************************************************************)

(* 定义指派 *)
Definition assignment (x: Var) : @ M D_I.
  simpl. apply term_domain. exact (Tvar x).
Defined.

(* 项向量v, 有Vector.map (assignment //) v = Vector.map term_domain v *)
(* Check @ map. *)
Definition assignment_v (n: nat) (v: Vector.t (term) n) :=
  Vector.map (assignment //) v = Vector.map term_domain v.

(* 任意项t, 有(assignment) // t = term_domain t *)
Lemma assignment_t : forall t, assignment // t = term_domain t.
Proof.
  apply Term_ind_new with assignment_v.
  - simpl. intros. unfold assignment. auto.
  - simpl. unfold Ic. auto.
  - red. intros. apply case0.
    set (fun x => Vector.map ((assignment) //) x = nil domain) as P.
    apply (case0 P). unfold P. simpl. auto.
  - intros. simpl. unfold If. simpl. rewrite H. apply eq_term_to_domain.
    apply If_equality'. destruct f. simpl in *. induction v.
    + simpl. constructor.
    + apply Forall2_cons.
      * apply inv_domain_term.
      * apply IHv. red in H. simpl in H. apply cons_inj in H. 
        destruct H. red. auto.
  - intros. red. simpl. f_equal; auto.
Qed.

Lemma assignment_v' : forall n v, assignment_v n v.
Proof.
  intros. red. induction v.
  - simpl. auto.
  - simpl. repeat rewrite -> assignment_t. f_equal; auto.
Qed.

(* 辅助引理：assignment 在常元上的值 *)
Lemma assignment_const : forall c, assignment // (Tcon c) = Ic c.
Proof. intros. simpl. unfold Ic. reflexivity. Qed.

(***************************************************************************)
(*           4  公式构造子的满足性                         *)
(***************************************************************************)

(* (equality t t0) ∈ Γ -> {D_I; assignment}|= (equality t t0) *)
Lemma model_satisfiable_le1' : forall t t0, 
  (equality t t0) ∈ Γ -> satisfy_R D_I assignment (equality t t0).
Proof.
  intros. assert(term_equality_relation t t0); auto.
  assert (term_equality_relation t = term_equality_relation t0).
    { apply Extensionality_Ensembles. split; red; intros.
      - red. red in H1. unfold term_equality_relation in *.
        apply term_equality_relation_sym in H0.
        apply term_equality_relation_tran with t; auto.
      - red. red in H1. unfold term_equality_relation in *.
        apply term_equality_relation_tran with t0; auto. }
  simpl. rewrite assignment_t. rewrite assignment_t. 
  apply eq_term_to_domain; auto.
Qed.

Lemma model_satisfiable_le1 : forall t t0, 
  (equality t t0) ∈ Γ <-> satisfy_R D_I assignment (equality t t0).
Proof.
  split; intros.
  - apply model_satisfiable_le1'; auto.
  - red in H. do 2 rewrite assignment_t in H.
    apply eq_domain_to_term in H; auto.
Qed.

Lemma model_satisfiable_le2' : forall r (s : t term (arity_R r)), 
  (atomic r s) ∈ Γ -> satisfy_R D_I assignment (atomic r s).
Proof.
  intros. simpl. unfold IR. rewrite assignment_v'.
  pose proof IR_equality' r s (map domain_term (map term_domain s)).
  apply H0; auto. clear H0. rewrite map_map. destruct r. simpl in *.
  clear H. induction s.
  - constructor.
  - apply Forall2_cons.
    + unfold pick. destruct constructive_indefinite_description. simpl; auto.
    + apply IHs.
Qed.

Lemma model_satisfiable_le2 : forall r (s : t term (arity_R r)), 
  (atomic r s) ∈ Γ <-> satisfy_R D_I assignment (atomic r s).
Proof.
  split; intros.
  - apply model_satisfiable_le2'; auto.
  - red in H. unfold I_R in H. simpl in *. red in H. rewrite assignment_v' in H.
    pose proof IR_equality' r s (map domain_term (map term_domain s)).
    apply H0; auto. clear H0. rewrite map_map. destruct r; simpl in *.
    clear H. induction s.
    + constructor.
    + apply Forall2_cons.
      * unfold pick. destruct constructive_indefinite_description. simpl; auto.
      * apply IHs.
Qed.

Lemma model_satisfiable_le3 : forall p, (p ∈ Γ <-> {D_I; assignment}|= (p))
  -> ¬p ∈ Γ <-> {D_I; assignment} |= (¬p).
Proof.
  intros. destruct (classic (p ∈ Γ)).
  - destruct H_mc. red in H2. split; intros.
    + destruct (H1 p); split; constructor; auto.
    + simpl in H3. rewrite H in H0; tauto.
  - destruct H_mc. split; intros.
    + simpl. intro. rewrite <- H in H4; tauto.
    + apply max_consistence_fact2; auto.
Qed.

Lemma model_satisfiable_le4 : forall p1 p2, (p1 ∈ Γ <-> {D_I; assignment}|= p1) 
  -> (p2 ∈ Γ <-> {D_I; assignment} |= p2)
  -> ((p1 → p2) ∈ Γ <-> {D_I; assignment}|= (p1 → p2)).
Proof.
  split; intros.
  - simpl. apply max_consistence_fact3 in H1; auto. destruct H1.
    + left. intro. apply max_consistence_fact2 in H1; auto.
      rewrite <-H in H2; auto.
    + right. apply H0; auto.
  - simpl in H1. apply max_consistence_fact3; auto. destruct H1.
    + left. apply max_consistence_fact2; auto. intro. rewrite H in H2; auto.
    + right. rewrite H0; auto.
Qed.

(***************************************************************************)
(*  Part 7: 主定理                                                          *)
(***************************************************************************)
(* (* 定义公式的复杂度(逻辑深度) *)
Fixpoint formula_rank (p: Formula) : nat :=
  match p with
  | equality _ _ => 0
  | atomic _ _ => 0
  | Not q => S (formula_rank q)
  | Contain q r => S (max (formula_rank q) (formula_rank r))
  | ForAll _ q => S (formula_rank q)
  end. *)

(* 辅助引理：替换不增加复杂度 *)
Fact subst_rank : forall p t v,
  formula_rank (substitute_f p t v) <= formula_rank p.
Proof.
  induction p; simpl; intros.
  - lia.
  - lia.
  - specialize (IHp t v). lia.
  - specialize (IHp1 t v). specialize (IHp2 t v). lia.
  - destruct (eqbv v v0); simpl; bdestruct (eqbv v0 v); subst; simpl; try lia;
    try (simpl; pose proof IHp t v0; lia).
Qed.

(* 主引理：对给定复杂度的所有公式证明 model_sat *)
Lemma model_sat_complexity : forall n p, formula_rank p <= n
  -> p ∈ Γ <-> {D_I; assignment} |= p.
Proof.
  induction n; intros p Hcomp.
  - (* Base case: n = 0 *)
    destruct p; simpl in Hcomp; try lia.
    + apply model_satisfiable_le1.
    + apply model_satisfiable_le2.
  - (* Inductive case: n = S n *)
    destruct p; simpl in Hcomp.
    + apply model_satisfiable_le1.
    + apply model_satisfiable_le2.
    + (* Not case *)
      apply model_satisfiable_le3. apply IHn. simpl in Hcomp. lia.
    + (* Contain case - 对应 Conjunction *)
      apply model_satisfiable_le4.
      * apply IHn. simpl in Hcomp. lia.
      * apply IHn. simpl in Hcomp. lia.
    + (* ForAll case *)
      split; intros.
      * (* 正向: ∀v, p ∈ Γ -> {D_I; assignment} |= ∀v, p *)
        simpl. intros m.
        (* 步骤1: 从 m ∈ domain 提取对应的项 t *)
        destruct (domain_has_term m) as [t Ht]. subst m.
        (* 现在 m = term_domain t，即 m = t^~ *)
        (* 步骤2: 我们需要找到常元 c 使得 c^~ = t^~ = term_domain t *)
        assert (Hexist_c: exists c, Ic c = term_domain t).
        { apply exist_const_for_domain. } 
        destruct Hexist_c as [c Hc].
        (* 步骤3: 从 ∀v, p ∈ Γ 推导 p[c/v] ∈ Γ *)
        assert (Ht_free: t_x_free p (Tcon c) v = true). 
        { apply free_test_1. red. auto. }
        assert (Hderiv: Γ ├ substitute_f p (Tcon c) v).
        { apply MP with (∀ v, p).
          - apply K1. apply S'. apply Ht_free.
          - apply K0. auto. }
        assert (Hsubst_in: substitute_f p (Tcon c) v ∈ Γ).
        { apply max_consistence_fact1; auto. }
        (* 步骤4: 使用归纳假设 *)
        assert (Hcomp_subst: formula_rank (substitute_f p (Tcon c) v) <= n).
        { pose proof (subst_rank p (Tcon c) v). simpl in Hcomp. lia. }
        apply IHn in Hcomp_subst. rewrite Hcomp_subst in Hsubst_in.
        (* 现在有：{D_I; assignment} ⊨ p[c/v] *)
        (* 步骤5: 应用替换定理 *)
        pose proof 
          (formula_substitution_theorem D_I p (Tcon c) v Ht_free assignment).
        destruct H0. apply H0 in Hsubst_in.
        (* 现在有：{D_I; assignment[v |-> assignment//(Tcon c)]} ⊨ p *)
        (* 步骤6: 证明 assignment // (Tcon c) = Ic c = term_domain t *)
        rewrite assignment_const in Hsubst_in. rewrite Hc in Hsubst_in.
        exact Hsubst_in.
      * (* 反向: {D_I; assignment} |= ∀v, p -> ∀v, p ∈ Γ *)
        (* 反证法: 假设 ∀v, p ∉ Γ *)
        destruct (classic (∀ v, p ∈ Γ)); auto.
        (* 由极大一致性, ¬∀v, p ∈ Γ *)
        apply max_consistence_fact2 in H0; auto.
        (* 由 witness property, 存在常元 c 使得 ¬p[c/v] ∈ Γ *)
        unfold witness_property in H_wp. specialize (H_wp p v H0).
        destruct H_wp as [c Hc].
        (* 由极大一致性引理，p[c/v] ∉ Γ *)
        assert (Hnotin: ~ substitute_f p (Tcon c) v ∈ Γ).
        { apply max_consistence_fact2 in Hc; auto. }
        (* 由归纳假设，{D_I; assignment} |≠ p[c/v] *)
        assert (Hcomp_subst: formula_rank (substitute_f p (Tcon c) v) <= n).
        { pose proof (subst_rank p (Tcon c) v). simpl in Hcomp. lia. }
        apply IHn in Hcomp_subst. rewrite Hcomp_subst in Hnotin.
        (* 由替换定理和 assignment_const *)
        assert (Ht_free: t_x_free p (Tcon c) v = true). { apply free_test_1. red. auto. }
        pose proof 
          (formula_substitution_theorem D_I p (Tcon c) v Ht_free assignment).
        destruct H1.
        (* 从假设 {D_I; assignment} |= ∀v, p，特化到 Ic c *)
        simpl in H. specialize (H (Ic c)). tauto.
Qed.

(* 主引理：{D_I; assignment} |= Γ 作为 model_sat_complexity 的推论 *)
Lemma model_sat : forall p, p ∈ Γ <-> {D_I; assignment} |= p.
Proof.
  intro p. apply model_sat_complexity with (n := formula_rank p). lia.
Qed.

(* 可满足定理: 复用 semantic_K_System 中的 satisfiable_Γ, 不再重复定义 *)
Theorem satisfiable_theorem : satisfiable_Γ Γ.
Proof. intros. red. exists D_I. exists assignment. red. apply model_sat. Qed.

End model_existence_proof.
