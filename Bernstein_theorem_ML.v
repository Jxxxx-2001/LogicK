(*****************************************************************************)
(*  This is part of Bernstein_theorem_ML, it is distributed under the terms  *)
(*            of the GNU Lesser General Public License version               *)
(*                   (see file LICENSE for more details)                     *)
(*                                                                           *)
(*                         Copyright 2026-2031                               *)
(*        Dakai Guo, qiming Wang, Xiang Ji, Tingting Ji and Wensheng         *)
(*****************************************************************************)

(** Bernstein_theorem_ML *)

Require Import Mappings_ML.
Require Import Base_ML.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
(* Require Import Coq.micromega.Lia. *)
(*Print epsilon_statement.*)

Theorem classicT : forall (P : Prop), {P} + {~P}.
Proof.
  intros. assert {x : bool | if x then P else ~P}.
  { apply constructive_indefinite_description. destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H, x; auto.
Qed.

(*Inductive function_bijective {A B} (f: A -> B): Prop :=
  | fun_bij_intro : function_injective f ->
                    function_surjective f -> function_bijective f.*)

(* 像集 *)
Inductive image_set {A B : Type} (f : A -> B)  (X: Ensemble A) : Ensemble B :=
  image_intro : forall a, a ∈ X -> (f a) ∈ (image_set f X).

(* 反函数 *)
Definition function_rev {A B : Type} (f : A -> B) (g : B -> A) := 
  forall x, g (f x) = x.

(* 根据f构造反函数 *)
Definition fun_rev {A B : Type} (f : A -> B) (a: A) (y:B) : A :=
  match (classicT (exists x, f x = y)) with
  | left l => proj1_sig (constructive_indefinite_description _ l)
  | right _ => a
  end.

(* 引理：如果A非空,f是A到B的单射函数,则f存在反函数  *)
Lemma injection_funrev : forall {A B : Type} (f : A -> B),
  inhabited A -> function_injective f -> exists g, function_rev f g.
Proof.
  intros. destruct H. exists (fun_rev f X).
  red; intros. unfold fun_rev. destruct classicT.
  - destruct constructive_indefinite_description. simpl. auto.
  - destruct n. eauto.
Qed.

Print inhabited.

Section bernstein.

Context {A B : Type} (f : A -> B) (g : B -> A).
Hypothesis Inj_f : function_injective f.
Hypothesis Inj_g : function_injective g.
Hypothesis Inhabited_B : inhabited B.

(* 令C_0=A \g[B], C_(n+1)=g[f[C_n ]] *)
Fixpoint Cn n : Ensemble A :=
  match n with
  | O => Complement _ (image_set g (Full_set B))
  | S n' => image_set g (image_set f (Cn n'))
  end.

(* 并令C=⋃_(n=0)^∞ C_n *)
Let Cset : Ensemble A := fun x => exists n, x ∈ (Cn n).

Let g_rev := proj1_sig (constructive_indefinite_description _ 
             (injection_funrev g Inhabited_B Inj_g)).
(* h(a) *)
Let h a :=
  match (classicT (a∈Cset)) with
  | left _ => f a
  | right _ => g_rev a
  end.

(* h是双射 *)
Lemma Bernstein : function_bijective h.
Proof.
  assert (grev : forall x, g_rev (g x) = x).
  { intros. unfold g_rev. destruct constructive_indefinite_description.
    simpl. apply f0. }
  assert (in_cset : forall x, ~ x ∈ Cset -> exists y, x = g y).
  { intros. destruct (classic (exists y, x = g y)); auto. destruct H. red; 
    red. exists 0. red; red; red. intro. induction H. destruct H0; eauto. }
  split.
  - hnf; intros. unfold h in H. destruct classicT, classicT.
    + apply Inj_f; auto.
    + assert (g (f a1)= a2). 
      { pose proof in_cset _ n as [y ?]. rewrite H0 in H. rewrite grev in H. 
        destruct i. destruct n. red; red. exists (S x). simpl. 
        rewrite H0, <- H. repeat apply image_intro. auto. } 
      destruct i. destruct n. red; red. exists (S x). simpl.
      rewrite <-H0. apply image_intro. apply image_intro. auto.
    + assert (g (f a2) = a1).
      { destruct (classic (exists y, a1 = g y)).
        - destruct H0 as [y ?]. rewrite H0 in H. rewrite grev in H. subst; auto.
        - destruct n. red; red. exists 0. red; red; red. intro.
          destruct H0. induction H1; eauto. }
      destruct i. destruct n. red; red. exists (S x). simpl. 
      rewrite <- H0. repeat apply image_intro. auto.
    + pose proof in_cset _ n as [y1 ?]; pose proof in_cset _ n0 as [y2 ?].
      subst. rewrite grev in H, H. f_equal; auto.
  - hnf; intros. destruct (classic (b ∈ (image_set f Cset))).
    + induction H. unfold h. exists a. destruct classicT; tauto.
    + assert (~(g b) ∈ Cset).
      { intro. destruct H0. destruct x.
        - simpl in H0. red in H0. red in H0. destruct H0.
          apply image_intro; auto. constructor.
        - simpl in H0. destruct (classic (b ∈ (image_set f (Cn x)))).
          + destruct H. induction H1. constructor. red; red. eauto.
          + remember (g b). induction H0. apply Inj_g in Heqa. subst; tauto. }
      exists (g b). unfold h. destruct classicT. tauto. rewrite grev. auto.
Qed.

(* 伯恩斯坦定理 *)
Theorem Bernstein_Theorem : bijection A B.
Proof.
  apply (Build_bijection _ _ h); apply Bernstein.
Qed.

End bernstein.