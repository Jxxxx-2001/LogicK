(**************************************************************************)
(*  This is part of bijection_K, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                        Copyright 2026-2031                             *)
(*       Xiang Ji, Guowei Dou, Tingting Ji, Dakai Guo and Wensheng        *)
(**************************************************************************)

(** bijection_nat_formula_K *)

Require Import Mappings_ML.
Require Import Base_ML.
Require Import formulas_K_System.
Require Import Bernstein_theorem_ML.

Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.
(*Print epsilon_statement.*)

(**************************************************************************)
(* 项可数 *)
Print term.

(* 常量可数 *)
Fact Con_countable : Countable Con.
Proof.
  apply (@ bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  apply (Build_bijection _ _ (fun x => (C x))).
  + hnf; intros. inversion H; auto.
  + hnf; intros. destruct b. exists n. auto.
Qed.

(* 变量可数 *)
Fact Var_countable : Countable Var.
Proof.
  apply (@ bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  apply (Build_bijection _ _ (fun x => (X x))).
  + hnf; intros. inversion H; auto.
  + hnf; intros. destruct b. exists n. auto.
Qed.

(* 如果A是可数的, 那么由A的元做成的n维向量集也是可数的 *)
Fact Vec_countable : forall A n, Countable A -> Countable (Vector.t A n).
Proof.
  intros. induction n.
  - apply (@ injection_Countable _ nat).
    + exists (fun _ => 0). hnf; intros.
      (* 证明 a1 = a2 = Vector.nil *)
      assert (a1 = Vector.nil A). 
        { apply (Vector.case0 (fun v => v = Vector.nil A)); auto. }
      assert (a2 = Vector.nil A). 
        { apply (Vector.case0 (fun v => v = Vector.nil A)); auto. }
      subst; auto.
    + apply nat_Countable.
  - (* Inductive Step: S n 维向量同构于 A * Vector A n *)
    apply (@ bijection_Countable _ (A * Vector.t A n)).
    + apply (Build_bijection _ _ (fun v => (Vector.hd v, Vector.tl v))).
      * hnf; intros.
        assert (a1 = Vector.cons A (Vector.hd a1) n (Vector.tl a1)).
          { apply Vector.eta; auto. }
        assert (a2 = Vector.cons A (Vector.hd a2) n (Vector.tl a2)).
          { apply Vector.eta; auto. }
        rewrite H0, H1. inversion H. subst. auto.
      * hnf; intros. destruct b as [a v]. exists (Vector.cons A a n v). simpl. auto.
    + apply prod_Countable; auto.
Qed.
(* Vector.case0：这是一个针对 0 维向量的分类讨论工具。它证明了“如果向量长度为 0，那么它必然等于 Vector.nil”。
   Vector.hd 和 Vector.tl：分别获取向量的头部（第一个元素）和尾部（剩余部分）。
   Vector.eta：向量的“外延性”定理，即：任何非空向量 v 都等于 cons (hd v) (tl v)。
   bijection_Countable：这是一个引理，意思是通过证明 X 与已知可数类型 Y 之间存在双射，来证明 X 可数。 *)

(* 函数可数 *)
Fact Fun_countable : Countable Fun.
Proof.
  pose proof natnat_nat_bijection.
  assert (bijection Fun (nat * nat)).
  { set (F1 f := match f with | F a b => a end).
    set (F2 f := match f with | F a b => b end).
    apply (Build_bijection _ _ (fun f => (pair (F1 f) (F2 f)))).
    + hnf; intros. inversion H0. destruct a1,a2. simpl in H2,H3.
      inversion H3. subst; auto.
    + hnf; intros. destruct b. exists (F n n0). simpl; auto. }
  apply bijection_injection in H,H0.
  assert (injection Fun nat). { apply (@ injection_trans _ (nat * nat)); auto. }
  apply (@ injection_Countable _ nat); auto. apply nat_Countable.
Qed.

(* 定义项的秩(复杂度) *)
Fixpoint term_rank (t : term) : nat :=
  match t with
  | Tvar _ => 0
  | Tcon _ => 0
  | Tfun _ q => let fix term_vec_rank (n:nat) (v : Vector.t term n) :=
                match v with
                | Vector.nil _ => 0
                | Vector.cons _ t _ ts => max (term_rank t) (term_vec_rank _ ts)
                end in S (term_vec_rank _ q)
end.

Lemma Trank_countable_lemma1 : Countable (sig (fun t : term => term_rank t <= 0)).
Proof.
  apply (@ injection_Countable _ (Var + Con)).
  - apply (Build_injection _ _
    (fun x => match x with
      | exist _ (Tvar v) _ => inl v
      | exist _ (Tcon c) _ => inr c
      | exist _ (Tfun f q) Hrank => False_rect (Var + Con) (Nat.nle_succ_0 _ Hrank)
          (* 因为 Tfun 的 rank 是 S (...)，矛盾于 Hrank : rank <= 0 *)
      end)).
    hnf; intros [t1 p1] [t2 p2] Heq. destruct t1; destruct t2;
    (* 分类讨论项的结构 *)
    try (inversion Heq; subst; f_equal; try apply proof_irrelevance);
    try (simpl in *; lia).
  - solve_Countable. apply Var_countable. apply Con_countable.
Qed.

(* 如果函数项的秩 <= S n, 那么其向量中每个元素的秩 <= n *)
Fact Tfun_rank_to_vec_inv : forall f v n,
  term_rank (Tfun f v) <= S n -> (forall t, Vector.In t v -> term_rank t <= n).
Proof. simpl. intros. induction H0; try apply IHIn; lia. Qed.

(* 将一个普通的项向量（Vector.t term k）转换成
   “带证明的项”向量（Vector.t {t : term | term_rank t <= n} k） *)
Fixpoint v_sig_map {n k} (v : Vector.t term k) :
  (forall t, Vector.In t v -> term_rank t <= n) 
     -> Vector.t ({t | term_rank t <= n}) k :=
  match v with
  | Vector.nil _ => fun _ => Vector.nil _
  | Vector.cons _ h _ ts => fun H =>
      Vector.cons _ (exist _ h (H h (@ Vector.In_cons_hd term _ _ _)))
                  _ (v_sig_map ts (fun t Hin 
                                  => H t (@ Vector.In_cons_tl term _ _ _ _ Hin)))
  end.

Fact v_sig_map_injective : forall (n k : nat) (v1 v2 : Vector.t term k) H1 H2,
  @ v_sig_map n k v1 H1 = @v_sig_map n k v2 H2 -> v1 = v2.
Proof.
  intros n k v1. induction v1; intros v2 H1 H2 Heq.
  - assert (v2 = Vector.nil term). 
      { apply (Vector.case0 (fun v => v = Vector.nil term)); auto. }
    subst; reflexivity.
  - dependent destruction v2. simpl in Heq. inversion Heq.
    subst h0. f_equal.
    apply IHv1 with (H1 := (fun t Hin => H1 t (Vector.In_cons_tl t h v1 Hin)))
                    (H2 := (fun t Hin => H2 t (Vector.In_cons_tl t h v2 Hin))).
    dependent destruction H3. auto.
Qed.

(* 在 Coq 的标准库中，{x : A & P x} 是类型 sigT (fun x : A => P x) 的语法糖 *)
Lemma Trank_countable_lemma2 : forall n,
  Countable ({t: term | term_rank t <= n}).
Proof.
  induction n.
  - apply Trank_countable_lemma1.
  - set (Cn := {t : term | term_rank t <= n}). red.
    (* T_{n+1} 可以单射到 Var + Con + {f : Fun & Vector.t Cn (arity_F f)} *)
    apply (@injection_Countable _ (Var + Con + {f : Fun & Vector.t Cn (arity_F f)})).
    + (* 构造单射函数，将 Tfun f args 映射到 sigT 部分 *)
     apply (Build_injection _ _
     (fun x => match x with
        | exist _ (Tvar v) _ => inl (inl v)
        | exist _ (Tcon c) _ => inl (inr c)
        | exist _ (Tfun f v) Hf => 
            let Hinv := Tfun_rank_to_vec_inv f v n Hf in
            inr (existT _ f (v_sig_map v Hinv))
        end)).
      (* 证明单射性 *)
      hnf; intros [t1 p1] [t2 p2] Heq. destruct t1; destruct t2; inversion Heq;
      subst; f_equal; try apply proof_irrelevance. dependent destruction H1. 
      apply v_sig_map_injective in x. subst t0. f_equal. apply proof_irrelevance.
    + solve_Countable. apply Var_countable. apply Con_countable.
      apply Fun_countable. apply Vec_countable. auto.
Qed.

(* 项可数 *)
Lemma Term_countable : Countable term.
Proof.
  apply (@ injection_Countable _ ({n : nat & {t : term | term_rank t <= n}})).
  - apply (Build_injection _ _ 
      (fun t => existT (fun n => {t : term | term_rank t <= n})
                       (term_rank t) (exist _ t (le_n (term_rank t))))).
    hnf; intros. inversion H. auto.
  - repeat solve_Countable. apply Trank_countable_lemma2.
Qed.

(**************************************************************************)
(* 公式可数 *)
Print Formula.

(* 关系可数 *)
Fact Rel_countable : Countable Rel.
Proof.
  pose proof natnat_nat_bijection.
  assert (bijection Rel (nat * nat)).
    { set (R1 r := match r with | R a b => a end).
      set (R2 r := match r with | R a b => b end).
      apply (Build_bijection _ _ (fun r => (pair (R1 r) (R2 r)))).
      + hnf; intros. inversion H0. destruct a1,a2. simpl in H2,H3.
        inversion H3. subst; auto.
      + hnf; intros. destruct b. exists (R n n0). simpl; auto. }
  apply bijection_injection in H,H0.
  assert (injection Rel nat). { apply (@injection_trans _ (nat * nat)); auto. }
  apply (@ injection_Countable _ nat); auto. apply nat_Countable.
Qed.

(* 定义公式的复杂度(逻辑深度) *)
Fixpoint formula_rank (p : Formula) : nat :=
  match p with
  | equality _ _ => 0
  | atomic _ _ => 0
  | Not q => S (formula_rank q)
  | Contain q r => S (max (formula_rank q) (formula_rank r))
  | ForAll _ q => S (formula_rank q)
  end.

Lemma Formula_countable_lemma1 : Countable ({x : Formula | formula_rank x <= 0}).
Proof.
  apply (@ injection_Countable _ 
             (term * term + {r : Rel & Vector.t term (arity_R r)})).
  - apply (Build_injection _ _
      (fun x => match x with
        | exist _ (equality t1 t2) _ => inl (t1, t2)
        | exist _ (atomic r args) _ => inr (existT _ r args)
        | exist _ _ Hrank => False_rect _ (Nat.nle_succ_0 _ Hrank)
        end)).
    hnf; intros [f1 p1] [f2 p2] Heq. destruct f1; destruct f2; 
    try (inversion Heq; subst; f_equal; try apply proof_irrelevance);
    try (simpl in *; lia).
  - pose proof Term_countable. solve_Countable.
    apply Rel_countable. apply Vec_countable. auto.
Qed.

Fact rank_Sn_to_n_Not : forall q n, 
  formula_rank (Not q) <= S n -> formula_rank q <= n.
Proof. simpl; intros; lia. Qed.

Fact rank_Sn_to_n_Contain_l : forall q r n, 
  formula_rank (Contain q r) <= S n -> formula_rank q <= n.
Proof. simpl; intros; lia. Qed.

Fact rank_Sn_to_n_Contain_r : forall q r n, 
  formula_rank (Contain q r) <= S n -> formula_rank r <= n.
Proof. simpl; intros; lia. Qed.

Fact rank_Sn_to_n_ForAll : forall v q n, 
  formula_rank (ForAll v q) <= S n -> formula_rank q <= n.
Proof. simpl; intros; lia. Qed.

Lemma Formula_countable_lemma2 : forall n, 
  Countable ({x : Formula | formula_rank x <= n}).
Proof.
  induction n.
  - apply Formula_countable_lemma1.
  - set (C0 := {x : Formula | formula_rank x <= 0}).
    set (Cn := {x : Formula | formula_rank x <= n}).
    apply (@ injection_Countable _ (C0 + (Cn + (Cn * Cn) + (Var * Cn)))).
    + apply (Build_injection _ _
      (fun x => match x with
        | exist _ (equality t1 t2) p => inl (exist (fun x => formula_rank x <= 0) 
                                               (equality t1 t2) (Nat.le_refl 0))
        | exist _ (atomic r args) p  => inl (exist (fun x => formula_rank x <= 0) 
                                               (atomic r args) (Nat.le_refl 0))
        | exist _ (Not q) Hr => 
            inr (inl (inl (exist _ q (rank_Sn_to_n_Not _ _ Hr))))
        | exist _ (Contain q r) Hr =>
            inr (inl (inr (exist _ q (rank_Sn_to_n_Contain_l _ _ _ Hr), 
                           exist _ r (rank_Sn_to_n_Contain_r _ _ _ Hr))))
        | exist _ (ForAll v q) Hr =>
            inr (inr (v, exist _ q (rank_Sn_to_n_ForAll _ _ _ Hr)))
        end)).
      (* 证明单射性 *)
      hnf; intros [f1 p1] [f2 p2] Heq. destruct f1; destruct f2; inversion Heq; 
      subst; f_equal; try apply proof_irrelevance.
    + solve_Countable. apply Formula_countable_lemma1. apply Var_countable.
Qed.

(* 公式可数 *)
Theorem Formula_contable : Countable Formula.
Proof.
  apply (@ injection_Countable _ ({n : nat & {x : Formula | formula_rank x <= n}})).
  - apply (Build_injection _ _ (fun x0 => existT (fun n 
      => sig (fun x => formula_rank x <= n)) (formula_rank x0) (exist (fun x 
      => formula_rank x <= formula_rank x0) x0 (le_n (formula_rank x0))))).
    hnf; intros. inversion H. auto.
  - repeat solve_Countable. apply Formula_countable_lemma2.
Qed.

(* 自然数和公式存在一一对应 *)
Corollary bijection_nat_formula : bijection nat Formula.
Proof.
  pose proof @ Bernstein_Theorem nat Formula. pose proof Formula_contable.
  destruct X as [g Hg].
  set (f := fun (n : nat) => equality (Tvar (X n)) (Tvar (X n))).
  assert (Hf : function_injective f). { red; intros. inversion H0. auto. } 
  apply (H f g); auto. constructor. exact (f 0).
Qed.

