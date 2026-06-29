(*****************************************************************************)
(*  This is part of comolete_K_pre, it is distributed under the terms of the *)
(*              GNU Lesser General Public License version 3                  *)
(*                 (see file LICENSE for more details)                       *)
(*                                                                           *)
(*                         Copyright 2026-2031                               *)
(*       Xiang Ji, Dakai Guo, Guowei Dou, Jiaxin Xie and Wensheng Yu         *)
(*****************************************************************************)

(** complete_K_System_pre *)

Require Import Base_ML.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import consistency_K_System.

Require Import Coq.micromega.Lia.

(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Program. *)

Import VectorNotations.

(* 亨金证据 *)
(* 见证性Witness Property: Γ是一致集, 对任意p, 变元x, 若(¬(Forall x p)) ∈ Γ, 
   则存在c∈Con, 使得 ¬(p(c/x))∈Γ *)
Definition witness_property Γ := forall p x, (¬(∀ x, p)) ∈ Γ
  -> exists c, (¬(substitute_f p (Tcon c) x)) ∈ Γ.

(***************************************************************************)
(*                           变元操作                                       *)
(***************************************************************************)
(* 计算项中出现的最大变量下标 *)
Fixpoint max_v_term t :=
  match t with
  | Tvar v => match v with X n => n end
  | Tcon _ => 0
  | Tfun _ q => let fix max_v_vc (n : nat) (r : Vector.t term n) :=
                  match r with 
                  | [] => 0
                  | h :: q' => max (max_v_term h) (max_v_vc _ q') 
                  end in (max_v_vc _ q)
  end.

(* 提取项向量中的最大变元编号 *)
Fixpoint max_v_vc {n} (vec : Vector.t term n) : nat :=
  match vec with
  | [] => 0
  | h :: tail => max (max_v_term h) (max_v_vc tail)
  end.

(* 计算公式中出现的最大变量下标 *)
Fixpoint max_v_formula p :=
  match p with 
  | equality t1 t2 => max (max_v_term t1) (max_v_term t2)
  | atomic _ q => let fix max_v_vc (n : nat) (r : Vector.t term n) :=
                  match r with 
                  | [] => 0
                  | h :: q' => max (max_v_term h) (max_v_vc _ q') 
                  end in max_v_vc _ q
  | Not q => max_v_formula q
  | Contain m n => max (max_v_formula m) (max_v_formula n)
  | ForAll (X x) q => max x (max_v_formula q)
  end.

Fact max_v_term_bound : forall t n, max_v_term t < n -> ~ (X n) ∈ (term_Ens t).
Proof.
  fix IH 1. intros. destruct t as [v_var | c_con | f v_vec]; simpl in *.
  - destruct v_var. intro. apply Single in H0. inversion H0. subst. lia.
  - intro. destruct H0.
  - revert v_vec H. induction v_vec as [| h m q IH_vc]; intros Hmax H_in.
    inversion H_in. simpl in *. apply UnionI in H_in as [Hh | Hq].
    + eapply IH in Hh; eauto. lia.
    + eapply IH_vc; eauto. lia.
Qed.

Fact max_v_formula_bound : forall p n,
  max_v_formula p < n -> ~ (X n) ∈ (Formula_Ens p).
Proof.
  induction p; intros n0 Hmax; simpl in *; intro Hin.
  - apply UnionI in Hin as [H | H]; eapply max_v_term_bound in H; eauto; lia.
  - revert t Hmax Hin. induction t as [| h n q IH_vc]; intros Hmax Hin.
    + inversion Hin.
    + simpl in *. apply UnionI in Hin as [Hh | Hq].
      * eapply max_v_term_bound in Hh; eauto; lia.
      * eapply IH_vc; eauto; lia.
  - eapply IHp; eauto.
  - apply UnionI in Hin as []. eapply IHp1 in H; eauto; lia.
    eapply IHp2 in H; eauto; lia.
  - destruct v as [x]. apply UnionI in Hin as [Hin_p | His_x].
    apply IHp in Hin_p; auto; lia.
    apply Single in His_x. inversion His_x. subst x. lia.
Qed.

(* 选择一个新的变元 *)
Definition fresh_var (t : term) : Var := X (S (max_v_term t)).

(* 如果 X n ∈ term_Ens t, 则 n <= max_var_in_term t *)
Fact var_in_term_le_max : forall t n, (X n) ∈ (term_Ens t) -> n <= max_v_term t.
Proof.
  intros t. apply Term_ind_new with
  (P := fun t => forall n, (X n) ∈ (term_Ens t) -> n <= max_v_term t)
  (P0 := fun m vec => forall n, (X n) ∈ (Vector_Ens m vec) -> n <= max_v_vc vec);
  intros; simpl; try tauto.
  - destruct n. apply Single in H. inversion H. subst. lia.
  - destruct H.
  - apply (case0 (fun v => (X n) ∈ (Vector_Ens 0 v) -> n <= max_v_vc v)).
    simpl. intros. inversion H0. auto.
  - apply H. auto.
  - apply UnionI in H1 as []. specialize (H n0 H1). lia. specialize (H0 n0 H1). lia.
Qed.

(* 主引理：新的变元不在项中 *)
Lemma fresh_var_not_in : forall t, ~ (fresh_var t) ∈ (term_Ens t).
Proof.
  intros. unfold fresh_var. intro H. apply var_in_term_le_max in H. lia.
Qed.

(***************************************************************************)
(*                           常元操作                                       *)
(***************************************************************************)
(* 计算项中出现的最大常元下标 *)
Fixpoint max_c_term t :=
  match t with
  | Tcon c => match c with C n => n end
  | Tvar y => 0
  | Tfun _ q => let fix max_c_vc (n : nat) (r : Vector.t term n) :=
                  match r with 
                  |[] => 0
                  | h :: q' => max (max_c_term h) (max_c_vc _ q') 
                  end in (max_c_vc _ q)
  end.

Fixpoint max_c_vc n r :=
  match r with
  |[] => 0
  | h :: q' => max (max_c_term h) (max_c_vc _ q') 
  end.

(* 计算公式中出现的最大常元下标 *)
Fixpoint max_c_formula p :=
  match p with 
  | equality t1 t2 => max (max_c_term t1) (max_c_term t2)
  | atomic _ q => max_c_vc _ q
  | Not q => max_c_formula q
  | Contain m n => max (max_c_formula m) (max_c_formula n)
  | ForAll x q => max_c_formula q
  end.

(* 项向量中把常元c替换成t' *)
Fixpoint substitute_vc (n : nat) (r: Vector.t term n) (t' : term) (c : Con) :=
  match r with 
  | [] => []
  | h :: q => (substitute_tc h t' c) :: (substitute_vc _ q t' c)
  end.

(* 公式p中把常元c替换成t' *)
Fixpoint substitute_fc (p : Formula) (t' : term) (c : Con) :=
  match p with 
  | equality t1 t2 => equality (substitute_tc t1 t' c) (substitute_tc t2 t' c) 
  | atomic _ q => atomic _ (substitute_vc _ q t' c) 
  | Not q => Not (substitute_fc q t' c)
  | Contain m n => Contain (substitute_fc m t' c) (substitute_fc n t' c)
  | ForAll y q => ForAll y (substitute_fc q t' c)
  end.
Notation " p {/ c ;; r } ":= (substitute_fc p r c)(at level 0).

(* 项的代换交换律 *)
Lemma subst_t_tc_comm : forall t t' x c y, ~ y ∈ (term_Ens t) -> x <> y 
  -> substitute_tc (t {x ; t'}) (Tvar y) c = 
    (substitute_tc t (Tvar y) c) {x ; (substitute_tc t' (Tvar y) c)}.
Proof.
  intro t. apply Term_ind_new with
  (P := fun t => forall t' x c y, ~ y ∈ (term_Ens t) -> x <> y 
    -> substitute_tc (t {x ; t'}) (Tvar y) c = (substitute_tc t (Tvar y) c) 
      {x ; (substitute_tc t' (Tvar y) c)})
  (P0 := fun n v => forall t' x c y, ~ y ∈ (Vector_Ens n v) -> x <> y
     -> substitute_vc n (substitute_v n v t' x) (Tvar y) c = substitute_v n 
       (substitute_vc n v (Tvar y) c) (substitute_tc t' (Tvar y) c) x);
  intros; simpl; try tauto.
  - destruct (eqbv x n); auto.
  - destruct (eqbc c n) eqn : Ecn; auto. simpl. destruct (eqbv x y) eqn:Exy; auto.
    Eqbv. contradiction.
  - apply (case0 (fun s => substitute_vc 0 (substitute_v 0 s t' x) (Tvar y) c
      = substitute_v 0 (substitute_vc 0 s (Tvar y) c) (substitute_tc t' 
       (Tvar y) c) x)); auto.
  - f_equal. apply H; auto.
  - f_equal.
    + apply H; auto. intro. apply H1. simpl. now left.
    + apply H0; auto. intro. apply H1. simpl. now right.
Qed.

(* 项向量的代换交换律 *)
Lemma subst_v_vc_comm : forall n (v : Vector.t term n) t x c y,
  ~ y ∈ (Vector_Ens n v) -> x <> y 
    -> substitute_vc n (substitute_v n v t x) (Tvar y) c = substitute_v n 
      (substitute_vc n v (Tvar y) c) (substitute_tc t (Tvar y) c) x.
Proof.
  induction v; intros t x c y Hy Hxy; simpl in *; auto. f_equal.
  - apply subst_t_tc_comm; auto. intro H. apply Hy. now left.
  - apply IHv; auto. intro H. apply Hy. now right.
Qed.

(* 公式的代换交换律 *)
Lemma subst_f_fc_comm : forall p t x c y, ~ y ∈ (Formula_Ens p) -> x <> y
  -> (p {x ;; t}) {/c ;; Tvar y}
    = (p {/c ;; Tvar y}) {x ;; (substitute_tc t (Tvar y) c)}.
Proof.
  induction p; intros; simpl in *; auto.
  - repeat rewrite subst_t_tc_comm; auto; intro; apply H. right. auto. left. auto.
  - f_equal. apply subst_v_vc_comm; auto.
  - f_equal. apply IHp; auto.
  - f_equal.
    + apply IHp1; auto. intro; apply H; now left.
    + apply IHp2; auto. intro; apply H; now right.
  - destruct (eqbv x v) eqn:Exv; auto. simpl. Eqbv. f_equal.
    assert (v <> y). { intro. subst v. apply H. right. constructor. }
    apply IHp; auto. intro. apply H. left. auto.
Qed.

(* 保持equality_4 *)
Lemma subst_fc_preserves_equality_4 : forall r m n v1 v2 c y_term,
  (equality_4 r m n v1 v2) {/c ;; y_term } = equality_4 (r {/c ;; y_term }) m n 
    (substitute_vc m v1 y_term c) (substitute_vc n v2 y_term c).
Proof.
  intros r m n v1. revert r n. induction v1; intros r n' v2 c y_term.
  - simpl; auto.
  - destruct v2; simpl; auto. f_equal. apply IHv1.
Qed.

Lemma sub_cv_term_free : forall t c y x, ~ x ∈ (term_Ens t) -> x <> y
  -> ~ x ∈ (term_Ens (substitute_tc t (Tvar y) c)).
Proof.
  fix IH 1. intros. destruct t; simpl in *; auto.
  - destruct (eqbc c c0) eqn : Ec; auto. simpl. intro. apply Single in H1. auto.
  - revert H. induction t; simpl; intros. auto.
    apply union_complement_equiv in H as [Hh Ht].
    apply union_complement_equiv. split. apply IH; auto. apply IHt; auto.
Qed.

(* 针对自由变量集的引理 *)
Lemma sub_cv_free_vars_fc : forall p c y x, ~ x ∈ (Formula_free_Ens p) -> x <> y
  -> ~ x ∈ (Formula_free_Ens (p {/c ;; Tvar y})).
Proof.
  induction p; intros c y x Hfree Hneq; simpl in *; auto.
  - apply union_complement_equiv in Hfree as []. apply union_complement_equiv.
    split; apply sub_cv_term_free; auto.
  - revert t Hfree. induction t; intros; auto. simpl in Hfree. 
    apply union_complement_equiv in Hfree as [Hh Ht]. simpl.
    apply union_complement_equiv. split.
    + apply sub_cv_term_free; auto.
    + apply IHt; auto.
  - intro. destruct H; revert H; try eapply IHp1; try eapply IHp2; eauto;
    intro; apply Hfree. left. auto. right. auto.
  - intro. destruct H. revert H. apply (IHp c y x); auto.
    intro. apply Hfree. split; auto.
Qed.

(* 常元代换后项中的变量集 *)
Lemma ens_subst_tc : forall t c y z, z ∈ (term_Ens (substitute_tc t (Tvar y) c))
  -> z ∈ (term_Ens t) \/ z = y.
Proof.
  intro t. apply Term_ind_new with
  (P := fun t => forall c y z, z ∈ (term_Ens (substitute_tc t (Tvar y) c))
          -> z ∈ (term_Ens t) \/ z = y)
  (P0 := fun n v => forall c y z, z ∈ (Vector_Ens n (substitute_vc n v (Tvar y) c))
          -> z ∈ (Vector_Ens n v) \/ z = y); intros; simpl; try tauto.
  - simpl in H. destruct (eqbc c n) eqn:Ec; simpl in H. apply Single in H.
    now right. inversion H.
  - apply (case0 (fun s
      => forall z0, z0 ∈ (Vector_Ens 0 (substitute_vc 0 s (Tvar y) c))
        -> z0 ∈ (Vector_Ens 0 s) \/ z = y)). simpl. intros. inversion H0. auto.
  - simpl in H0. apply (H c y); auto.
  - simpl in *. apply UnionI in H1 as [].
    + apply H in H1 as []. left. now left. now right.
    + apply H0 in H1 as []. left. now right. now right.
Qed.

Lemma t_x_free_fc_preserve : forall p t x c y, ~ y ∈ (Formula_Ens p) -> x <> y
  -> t_x_free p t x = true
   -> t_x_free (p {/c ;; Tvar y}) (substitute_tc t (Tvar y) c) x = true.
Proof.
  induction p; intros; simpl in *; auto.
  - apply andb_prop in H1 as []. rewrite IHp1, IHp2; eauto; intro; apply H.
    now right. now left.
  - destruct (eqbv x v) eqn : Exv.
    + Eqbv. destruct (classicT (v ∈ (Formula_free_Ens (p) {/c ;; Tvar y}) ~ [/v]))
        as [Hin | Hnot]. destruct Hin as [_ ]. elim H2. constructor. auto.
    + destruct (classicT (x ∈ (Formula_free_Ens (p) {/c ;; Tvar y}) ~ [/v])); auto.
      assert (Hin_old: x ∈ (Formula_free_Ens p) ~ [/v]).
      { destruct i as [Hin_p Hnx]. split; auto.
        destruct (classicT (x ∈ (Formula_free_Ens p))); auto.
        eapply (sub_cv_free_vars_fc _ c) in n; eauto. contradiction. }
      destruct classicT; auto.
      destruct (classicT (v ∈ (term_Ens (substitute_tc t (Tvar y) c)))) as [].
      * apply ens_subst_tc in i1 as []. destruct classicT; auto. 
        destruct classicT; auto. subst v. elim H. right. constructor.
      * destruct classicT. inversion H1. apply IHp; auto. 
        intro. apply H. left. auto.
Qed.

Lemma Axiom_subst_fc : forall p c y, Axiom_system p ->  ~ y ∈ (Formula_Ens p)
  ->  Axiom_system (p {/c ;; Tvar y}).
Proof.
  intros. induction H; simpl; try constructor.
  - assert (x <> y). { intro. subst. apply H0. simpl. left. right. constructor. }
    assert (H_comm: ((p) {x ;; t}) {/c ;; Tvar y}
      = (p {/c ;; Tvar y}) {x ;; (substitute_tc t (Tvar y) c)}).
      { apply subst_f_fc_comm; auto. intro. apply H0. simpl. left. left. auto. }
    rewrite H_comm. apply S'. apply t_x_free_fc_preserve; auto.
    intro. apply H0. simpl. left. left. auto.
  - rewrite subst_fc_preserves_equality_4. simpl. constructor.
  - rewrite subst_fc_preserves_equality_4. simpl. constructor.
  - eapply sub_cv_free_vars_fc; eauto.
    intro. subst y. apply H0. simpl. right. right. constructor.
  - apply IHAxiom_system. intro. apply H0. simpl. left. auto.
Qed.

(**************************************************************************)

(* 针对项的常量集和替换 *)
Lemma subst_tc_not_in : forall t c t', ~ c ∈ (term_C_set t)
  -> substitute_tc t t' c = t.
Proof.
  fix IH 1. intros t c t' Hnot.
  destruct t as [v_var | c_con | f v_vec]; simpl in *; auto.
  - destruct (eqbc_reflect c c_con) as []; auto. subst. elim Hnot. constructor.
  - f_equal. revert Hnot. induction v_vec as [| h n q IHq]. intro. auto.
    intro. f_equal. apply IH. intro. apply Hnot. now left.
    apply IHq. intro. apply Hnot. now right.
Qed.

(* 针对项向量的常量集和替换 *)
Lemma subst_vc_not_in : forall n (v : Vector.t term n) c t',
  ~ c ∈ (Vector_C_set n v) -> substitute_vc n v t' c = v.
Proof.
  induction v; intros c t' Hnot; simpl; auto. f_equal. apply subst_tc_not_in.
  intro. apply Hnot. simpl. now left. apply IHv. intro. apply Hnot. now right.
Qed.

(* 针对公式的常量集和替换 *)
Lemma subst_fc_not_in : forall p c t', ~ c ∈ (Formula_C_set p) -> p {/c ;; t'} = p.
Proof.
  induction p; intros c t' Hnot; simpl in *.
  - f_equal; apply subst_tc_not_in; intro H; apply Hnot; [now left | now right].
  - f_equal. apply subst_vc_not_in. auto.
  - f_equal. apply IHp. assumption.
  - f_equal. apply IHp1. intro H. apply Hnot. now left.
    apply IHp2. intro H. apply Hnot. now right.
  - f_equal. apply IHp. auto.
Qed.

Lemma subst_t_tc_commute : forall t v c y_term, ~ c ∈ (term_C_set t)
  -> (substitute_tc (t {v; Tcon c}) y_term c) = t {v ; y_term}.
Proof.
  fix IH 1. intros. destruct t as [x_var | c_con | f v_vec]; simpl in *.
  - destruct (eqbv v x_var) eqn : Evx; simpl; auto.
    destruct (eqbc_reflect c c); auto. contradiction.
  - destruct (eqbc_reflect c c_con); auto. subst. elim H. constructor.
  - f_equal. revert v_vec H. induction v_vec as [| h n q IH_vc]; intro.
    auto. f_equal.
    + apply IH. intro. apply H. now left.
    + apply IH_vc. intro. apply H. now right.
Qed.

Lemma subst_v_vc_commute : forall n v_vec v c y_term, ~ c ∈ (Vector_C_set n v_vec)
  -> substitute_vc n (substitute_v n v_vec (Tcon c) v) y_term c
    = substitute_v n v_vec y_term v.
Proof.
  induction v_vec; intros; simpl in *; auto. f_equal. apply subst_t_tc_commute.
  intro. apply H. now left. apply IHv_vec. intro. apply H. now right.
Qed.

Lemma subst_f_fc_commute : forall p v c y_term, ~ c ∈ (Formula_C_set p)
  -> (p {v ;; Tcon c}) {/c ;; y_term} = p {v ;; y_term}.
Proof.
  induction p; intros v_var c y_term Hnot; simpl in *.
  - f_equal; apply subst_t_tc_commute; intro H; apply Hnot; [left | right]; auto.
  - f_equal. apply subst_v_vc_commute. auto.
  - f_equal. apply IHp. auto.
  - f_equal. apply IHp1. intro H. apply Hnot. now left.
    apply IHp2. intro H. apply Hnot. now right.
  - destruct (eqbv v_var v) eqn : Evv; simpl; f_equal.
    apply subst_fc_not_in. auto. apply IHp. auto.
Qed.

Lemma C_in_subst_term : forall t1 t2 x c_n, (C c_n) ∈ (term_C_set (t1 {x;t2}))
  -> (C c_n) ∈ (term_C_set t1) \/ (C c_n) ∈ (term_C_set t2).
Proof.
  fix IH 1. intros. destruct t1; simpl in H.
  - destruct (eqbv x v) eqn : E; auto.
  - inversion H. left. simpl. apply Single. auto.
  - assert (H_vec : forall n v,
      (C c_n) ∈ (Vector_C_set n (substitute_v n v t2 x)) 
      -> (C c_n) ∈ (Vector_C_set n v) \/ (C c_n) ∈ (term_C_set t2)).
      { induction v; intros; simpl in H0; auto. apply UnionI in H0 as [].
        + apply IH in H0 as []; auto. left. simpl. left. auto.
        + apply IHv in H0 as []; auto. left. simpl. right. auto. }
    apply H_vec in H as []; auto.
Qed.

Lemma C_in_subst : forall p t x c_n, (C c_n) ∈ (Formula_C_set (p {x;; t}))
  -> (C c_n) ∈ (Formula_C_set p) \/ (C c_n) ∈ (term_C_set t).
Proof.
  induction p; intros; simpl in H.
  - apply UnionI in H as []; apply C_in_subst_term in H as []; auto.
    left. simpl. left. auto. left. simpl. right. auto.
  - assert (H_vec : forall n v,
      (C c_n) ∈ (Vector_C_set n (substitute_v n v t0 x))
      -> (C c_n) ∈ (Vector_C_set n v) \/ (C c_n) ∈ (term_C_set t0)).
      { induction v; intros; auto. simpl in H0. apply UnionI in H0 as [].
        apply C_in_subst_term in H0 as []; auto. left. simpl. left. auto.
        apply IHv in H0 as []; auto. left. simpl. right. auto. }
    apply H_vec in H as []; auto.
  - apply IHp in H as []; auto.
  - apply UnionI in H as []; auto. apply IHp1 in H as []; auto. left. 
    simpl. left. auto. apply IHp2 in H as []; auto. left. simpl. right. auto.
  - destruct (eqbv x v) eqn : E; auto. apply IHp in H as []; auto.
Qed.

Lemma term_Ens_subst_c : forall t x c, (term_Ens (t {x ; Tcon c})) ⊆ (term_Ens t).
Proof.
  fix IH 1. intros. red. intros.
  destruct t as [v_var | c_con | f v_vec]; simpl in *.
  - destruct (eqbv x v_var) eqn:Eq; auto. simpl in H. inversion H.
  - auto.
  - revert v_vec H. induction v_vec; simpl; intros H. inversion H.
    apply UnionI in H as [Hh | Hq]; apply UnionI.
    + left. eapply IH; eauto.
    + right. eapply IHv_vec; eauto.
Qed.

Lemma formula_Ens_subst_c : forall p x c,
  (Formula_Ens (p {x ;; Tcon c})) ⊆ (Formula_Ens p).
Proof.
  induction p; intros x_var c z Hin; simpl in *.
  - apply UnionI in Hin as []; apply UnionI; eapply term_Ens_subst_c in H; eauto.
  - revert t Hin. induction t; simpl; intros Hin. inversion Hin.
    apply UnionI in Hin as [Hh | Hq]; apply UnionI.
    + left. eapply term_Ens_subst_c; eauto.
    + right. eapply IHt; eauto.
  - eapply IHp; eauto.
  - apply UnionI in Hin as []; apply UnionI. left. eapply IHp1; eauto.
    right. eapply IHp2; eauto.
  - destruct (eqbv x_var v) eqn:Eq; auto. apply UnionI in Hin as []; apply UnionI.
    left. eapply IHp; eauto. right. auto.
Qed.


(**************************************************************************)
(*                 定义通用的常元映射操作map_C及其通用一致性证明                *)
(*            因为不管是加倍还是还原,都不改变项和公式的结构, 只改变常量的标号       *)
(**************************************************************************)

Section MapC.
Variable f : nat -> nat.

(* 通用的项常量映射 *)
Fixpoint map_C_term (t : term) : term :=
  match t with
  | Tcon c => match c with
              | C n => Tcon (C (f n))
              end
  | Tvar y => Tvar y
  | Tfun  _ q => let fix map_C_vc (n : nat) (r : Vector.t term n) :=
                   match r with 
                    | [] => []
                    | h :: q => (map_C_term h) :: (map_C_vc _ q) 
                   end in (Tfun _ (map_C_vc _ q))
  end.

Fixpoint map_C_vector (n : nat) (r : Vector.t term n) : Vector.t term n :=
  match r with 
  | [] => []
  | h :: q => (map_C_term h) :: (map_C_vector _ q)
  end.

(* 通用的公式常量映射 *)
Fixpoint map_C_formula (p : Formula) : Formula :=
  match p with 
  | equality t1 t2 => equality (map_C_term t1) (map_C_term t2)
  | atomic r q => atomic r (map_C_vector _ q)
  | Not q => Not (map_C_formula q)
  | Contain m n => Contain (map_C_formula m) (map_C_formula n)
  | ForAll x q => ForAll x (map_C_formula q)
  end.

Inductive map_C_set Γ : Ensemble Formula :=
  | map_C_set_intro : forall p, p ∈ Γ -> (map_C_formula p) ∈ (map_C_set Γ).

(* ==================== 第一部分：基础同构引理 ==================== *)

(* 保持term的变元集 *)
Fact map_C_term_preserves_vars : forall t x,
  x ∈ (term_Ens t) <-> x ∈ (term_Ens (map_C_term t)).
Proof.
  intro t. apply Term_ind_new with
  (P := fun t => forall x, x ∈ (term_Ens t) 
     <-> x ∈ (term_Ens (map_C_term t)))
  (P0 := fun n v => forall x, x ∈ (Vector_Ens n v) 
     <-> x ∈ (Vector_Ens n (map_C_vector n v))); intros; simpl; try tauto.
  - split; intro H. destruct H. destruct n. simpl in H. destruct H.
  - apply (case0 (fun v => forall x0, x0 ∈ (Vector_Ens 0 v) 
                          <-> x0 ∈ (Vector_Ens 0 (map_C_vector 0 v)))).
    simpl. split; intro H; destruct H.
  - apply H.
  - repeat rewrite UnionI. rewrite H,H0. tauto.
Qed.

(* 保持公式的自由变元集 *)
Fact map_C_preserves_free_vars : forall p x,
  x ∈ (Formula_free_Ens p) <-> x ∈ (Formula_free_Ens (map_C_formula p)).
Proof.
  intro p. induction p; intro x; simpl.
  - repeat rewrite UnionI. split; intros [H | H];
    try (rewrite <- map_C_term_preserves_vars in H; auto);
    try (rewrite map_C_term_preserves_vars in H; auto).
  - assert (Hvec: forall n (v : Vector.t term n),
      x ∈ (Vector_Ens n v) <-> x ∈ (Vector_Ens n (map_C_vector n v))).
      { intros n v. induction v; simpl.
        - split; intro H; destruct H.
        - repeat rewrite UnionI. split; intros [H | H];
          try (rewrite <- map_C_term_preserves_vars in H; auto);
          try (rewrite map_C_term_preserves_vars in H; auto);
          try (apply IHv in H; auto). } apply Hvec.
  - apply IHp.
  - repeat rewrite UnionI. split; intros [H | H];
    try apply IHp1 in H; auto; try apply IHp2 in H; auto.
  - split; intro H; destruct H as [H1 H2]; split; auto; apply IHp; auto.
Qed.

(* 保持t_x_free *)
Fact map_C_preserves_t_x_free : forall p t x,
  t_x_free p t x = t_x_free (map_C_formula p) (map_C_term t) x.
Proof.
  intro p. induction p; intros t1 x1; simpl; auto.
  - rewrite <- IHp1, <- IHp2. reflexivity.
  - pose proof (map_C_preserves_free_vars (ForAll v p) x1).
    pose proof (map_C_term_preserves_vars t1 v).
    pose proof (map_C_preserves_free_vars p x1).
    repeat match goal with |- context[classicT ?P] => destruct (classicT P) end;
    simpl in *; try tauto. apply IHp.
Qed.

(* map_C_term 和 substitute_t 可交换 *)
Fact map_C_term_subst_comm : forall t t' x, 
  map_C_term (substitute_t t t' x) = substitute_t (map_C_term t) (map_C_term t') x.
Proof.
  intro t. apply Term_ind_new with
  (P := fun t => forall t' x, map_C_term (substitute_t t t' x)
     = substitute_t (map_C_term t) (map_C_term t') x)
  (P0 := fun n v => forall t' x, map_C_vector n (substitute_v n v t' x)
     = substitute_v n (map_C_vector n v) (map_C_term t') x);
  intros; simpl; try tauto.
  - destruct (eqbv x n); reflexivity.
  - destruct n; reflexivity.
  - apply (case0 (fun v => forall t' x, map_C_vector 0 (substitute_v 0 v t' x) 
      = substitute_v 0 (map_C_vector 0 v) (map_C_term t') x)). intros. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H,H0. reflexivity.
Qed.

(* 保持替换 *)
Fact map_C_preserves_subst : forall p t x, map_C_formula (substitute_f p t x)
  = substitute_f (map_C_formula p) (map_C_term t) x.
Proof.
  intro p. induction p; intros t1 x1; simpl; auto.
  - repeat rewrite map_C_term_subst_comm. reflexivity.
  - f_equal. induction t; simpl; auto. rewrite map_C_term_subst_comm. f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - destruct (eqbv x1 v) eqn:E; simpl; auto. f_equal. apply IHp.
Qed.

Fact map_C_preserves_equality_4 : forall r m n v1 v2,
  map_C_formula (equality_4 r m n v1 v2)
    = equality_4 (map_C_formula r) m n (map_C_vector m v1) (map_C_vector n v2).
Proof.
  intros r m n v1. revert r n. induction v1; intros r n' v2; destruct v2;
  simpl; auto. f_equal. repeat rewrite map_C_term_subst_comm. apply IHv1.
Qed.

(* ==================== 第二部分：map_C 保持公理和推导 ==================== *)

Lemma map_C_preserves_axiom : forall p,
  Axiom_system p -> Axiom_system (map_C_formula p).
Proof.
  intros p H. induction H; simpl; try constructor;
  try (rewrite map_C_preserves_equality_4; constructor); auto.
  - assert (Ht_free: t_x_free (map_C_formula p) (map_C_term t) x = true).
      { rewrite <- map_C_preserves_t_x_free; exact H. }
    rewrite map_C_preserves_subst. constructor. auto.
  - intro. apply H. rewrite map_C_preserves_free_vars. auto.
Qed.

Lemma map_C_preserves_deduce : forall Γ p,
  Γ ├ p -> (map_C_set Γ) ├ (map_C_formula p).
Proof.
  intros. induction H.
  - apply K0. constructor; auto.
  - apply K1. apply map_C_preserves_axiom. auto.
  - simpl in *. eapply MP; eauto.
Qed.

End MapC.

(**************************************************************************)
(*             通用常元映射的逆运算性质 (MapC Inverse)                       *)
(**************************************************************************)

Section MapC_Inverse.
(* 给定两个函数f和g, 假设g是f的左逆 *)
Variables f g : nat -> nat.
Hypothesis f_g_id : forall n, g (f n) = n.

Fact map_C_inverse_term : forall t, map_C_term g (map_C_term f t) = t.
Proof.
  intro t. apply Term_ind_new with
  (P := fun t => map_C_term g (map_C_term f t) = t)
  (P0 := fun n v => map_C_vector g n (map_C_vector f n v) = v);
  intros; simpl; try tauto.
  - destruct n. simpl. f_equal. f_equal. apply f_g_id.
  - apply (case0 (fun v => map_C_vector g 0 (map_C_vector f 0 v) = v)). auto.
  - f_equal. apply H.
  - f_equal; auto.
Qed.

Fact map_C_inverse_vector : forall n v, map_C_vector g n (map_C_vector f n v) = v.
Proof. intros. induction v; simpl; f_equal; auto using map_C_inverse_term. Qed.

Fact map_C_inverse_formula : forall p, map_C_formula g (map_C_formula f p) = p.
Proof.
  induction p; simpl; f_equal; auto using map_C_inverse_term, map_C_inverse_vector.
Qed.

Fact map_C_inverse_set : forall Γ, map_C_set g (map_C_set f Γ) = Γ.
Proof.
  intro Γ. apply Extensionality_Ensembles. split; red; intros p Hp.
  - destruct Hp as [p' Hp']. destruct Hp' as [p'' Hp''].
    rewrite map_C_inverse_formula. auto.
  - rewrite <- (map_C_inverse_formula p).
    apply map_C_set_intro, map_C_set_intro. auto.
Qed.

(* 通用模型变换: 把模型中对常元的解释套上一层映射h *)
Definition map_Module (MM : Module) (h : nat -> nat) : Module := {|
  M := @ M MM;
  I_c := fun '(C n) => @ I_c MM (C (h n));
  I_f := @ I_f MM;
  I_R := @ I_R MM |}.

(* === 正向forward: 项和公式在映射后的模型中求值, 等于先映射后在原模型中求值 === *)
Fact map_C_eval_fwd : forall MM v t,
  @ value_term MM v (map_C_term f t) = @ value_term (map_Module MM f) v t.
Proof.
  intros MM v t. apply Term_ind_new with
  (P := fun t 
     => @ value_term MM v (map_C_term f t) = @value_term (map_Module MM f) v t)
  (P0 := fun n vec => Vector.map (@value_term MM v) (map_C_vector f n vec) 
     = Vector.map (@value_term (map_Module MM f) v) vec); intros; simpl; try tauto.
  - destruct n. simpl. auto.
  - apply (case0 (fun v0 => Vector.map (@value_term MM v) (map_C_vector f 0 v0)
      = Vector.map _ v0)). auto.
  - f_equal. apply H.
  - f_equal; auto.
Qed.

Lemma map_C_satisfy_fwd : forall MM v p,
  @ satisfy_R MM v (map_C_formula f p) <-> @ satisfy_R (map_Module MM f) v p.
Proof.
  intros MM v p. revert v. induction p; intro; simpl.
  - repeat rewrite map_C_eval_fwd. tauto.
  - assert (Heq: Vector.map (@value_term MM v) (map_C_vector f _ t) 
              = Vector.map (@value_term (map_Module MM f) v) t).
      { induction t; simpl; f_equal; auto using map_C_eval_fwd. }
    rewrite Heq. tauto.
  - specialize IHp with v. split; intro; red; intro; elim H; apply IHp; auto.
  - repeat rewrite IHp1, IHp2. tauto.
  - split; intros H m; specialize (H m); apply IHp; auto.
Qed.

(* === 逆向backward: 如果g是f的左逆, 结合g转换的模型能恢复原求值 === *)
Fact map_C_eval_bwd : forall MM v t,
  @ value_term (map_Module MM g) v (map_C_term f t) = @ value_term MM v t.
Proof.
  intros MM v t. apply Term_ind_new with
  (P := fun t
     => @ value_term (map_Module MM g) v (map_C_term f t) = @ value_term MM v t)
  (P0 := fun n vec
     => Vector.map (@ value_term (map_Module MM g) v) (map_C_vector f n vec) 
     = Vector.map (@ value_term MM v) vec); intros; simpl; try tauto.
  - destruct n. simpl. f_equal. rewrite f_g_id. auto.
  - apply (case0 (fun v0
      => Vector.map _ (map_C_vector f 0 v0) = Vector.map _ v0)). auto.
  - f_equal. apply H.
  - f_equal; auto.
Qed.

Lemma map_C_satisfy_bwd : forall MM v p,
  @ satisfy_R (map_Module MM g) v (map_C_formula f p) <-> @ satisfy_R MM v p.
Proof.
  intros MM v p. revert v. induction p; intro; simpl.
  - repeat rewrite map_C_eval_bwd. tauto.
  - assert (Heq: Vector.map (@ value_term (map_Module MM g) v) (map_C_vector f _ t) 
              = Vector.map (@ value_term MM v) t).
      { induction t; simpl; f_equal; auto using map_C_eval_bwd. }
    rewrite <- Heq. tauto.
  - specialize IHp with v. split; intro; red; intro; elim H; apply IHp; auto.
  - repeat rewrite IHp1, IHp2. tauto.
  - split; intros H m; specialize (H m); apply IHp; auto.
Qed.

End MapC_Inverse.

(**************************************************************************)
(*        基于通用的 MapC 直接给出 double_C (加倍) 和 half_C (还原) 操作       *)
(**************************************************************************)

(* ========== 扩张 double_C ========== *)
Definition f_double (n : nat) := 2 * n.

Definition double_C_term := map_C_term f_double.
Definition double_C_formula := map_C_formula f_double.
Definition double_C_set := map_C_set f_double.

Lemma double_C_preserves_deduce : forall Γ p,
  Γ ├ p -> (double_C_set Γ) ├ (double_C_formula p).
Proof. apply map_C_preserves_deduce. Qed.

(* ========== 还原 half_C ========== *)
Definition f_half (n : nat) := n / 2.

Definition half_C_formula := map_C_formula f_half.
Definition half_C_set := map_C_set f_half.

Lemma half_C_preserves_deduce : forall Γ p,
  Γ ├ p -> (half_C_set Γ) ├ (half_C_formula p).
Proof. apply map_C_preserves_deduce. Qed.

(* 基本算术引理: half是double的左逆 *)
Fact half_double_id : forall n, f_half (f_double n) = n.
Proof. 
  intros. unfold f_half, f_double. rewrite Nat.mul_comm. apply Nat.div_mul. auto.
Qed.

Fact half_double_Γ : forall Γ, half_C_set (double_C_set Γ) = Γ.
Proof. apply map_C_inverse_set, half_double_id. Qed.

(* ==== 获得两种模型一致性以及可满足关系结论 ==== *)
Definition Module2C (MM : Module) := map_Module MM f_double.
Definition ModulehalfC (MM : Module) := map_Module MM f_half.

(* 关键引理: Γ的一致性保持 *)
Lemma double_C_consistence : forall Γ,
  consistence Γ <-> consistence (double_C_set Γ).
Proof.
  split; intros H; red; intros p [H1 H2].
  - apply half_C_preserves_deduce in H1, H2. 
    rewrite half_double_Γ in H1, H2. eapply H; eauto.
  - apply double_C_preserves_deduce in H1, H2. eapply H; eauto.
Qed.

(* 关键引理: Γ是可满足的当且仅当double_C_set Γ是可满足的 *)
Lemma double_C_satisfiable : forall Γ,
  satisfyable_Γ Γ <-> satisfyable_Γ (double_C_set Γ).
Proof.
  split; intros [MM [v H]]; red in H.
  - exists (ModulehalfC MM), v. red. intros p [p0 Hp0].
    apply (map_C_satisfy_bwd f_double f_half half_double_id). auto.
  - exists (Module2C MM), v. red. intros p Hp. apply (map_C_satisfy_fwd f_double).
    apply H. constructor; auto.
Qed.