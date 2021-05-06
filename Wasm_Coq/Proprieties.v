Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.Znat.
From Coq Require Import ZArith.BinInt.
From Coq Require Import ZArith.Zbool.
From Coq Require Import Reals.RIneq.
From Coq Require Import Classes.RelationClasses.
Require Import Program.Wf.
Import N2Z.
Import Zabs2N.
Import ListNotations.

From Coq Require Import ZArith.
(*Open Scope R_scope.*)

From LF Require Import Maps Wasm.

(* Admiited things that require extra attention *)

Open Scope Z.

Open Scope positive_scope.
Close Scope positive_scope.

Lemma neg_div_pos_stays_neg :
forall (p : positive) a, a > 0 ->
(Z.neg p / a) <= 0.
Proof.
intros.
Admitted.

Lemma small_div_is_0:
forall (a b : Z), a < b -> a / b = 0.
Proof.
Admitted.

Open Scope positive_scope.
(* Demonstratia asta e redundanta dar o las aici sa imi amintesc
ca lemma de care am nevoie e Pos2Z.pos_xI *)
Lemma pos_bin_bit_1:
forall ( p : positive ), 
(Z.pos p~1)%Z = ((2 * Z.pos p ) + 1)%Z.
Proof.
intros.
(*Search (_ ~1).*) apply Pos2Z.pos_xI.
Qed.

Close Scope positive_scope.

Close Scope Z.


(* --------- General useful proprieties ---------*)

Open Scope Z.
Lemma lt1_equiv_le0:
forall (x:Z), x <= 0%Z -> x < 1%Z.
Proof.
intros.
(* Search (Z.succ _).*) assert (1 = Z.succ 0). simpl. reflexivity.
rewrite H0. apply Zle_lt_succ. assumption.
Qed.

Lemma positive_ge_10_implies_p_div_10_ge_1:
forall p : positive, (Z.pos p) >= 10 ->  Z.pos p /10 >= 1.
Proof.
 intros p.
 (*Search ( _ >= _ -> _ / _ >= _).*) apply Zdiv.Z_div_ge.
 reflexivity.
Qed.

Lemma positive_lt_than_10_implies_p_div_10_lt_1:
forall p : positive, Z.pos p < 10 -> Z.pos p / 10 < 1.
Proof.
intros p.
(*Search ( (_) / (_) = 0 ).*)
intros.
rewrite Zdiv.Zdiv_small.
- reflexivity.
- split.
-- (*Search (Z.pos).*) apply Pos2Z.is_nonneg.
-- assumption.
Qed.

Lemma negative_lt_than_10_implies_n_div_10_is_0:
forall p : positive, Z.neg p < 10 -> Z.neg p / 10 <= 0.
Proof.
intros p.
intros.
(*Search ( (_) / (_) <= _).*)
rewrite neg_div_pos_stays_neg. reflexivity. reflexivity.
Qed.

Close Scope Z.

(* --------- Proprieties of execute_instruction function ---------*)
Open Scope Z.
Lemma eval_i32_ge_s_true:
forall var_st ex_St glob_st fun_st mem a b, b >= a ->
execute_intruction (i32_ge_s) ((i32 a :: i32 b :: ex_St), var_st, glob_st, fun_st, mem) = ( i32 1:: ex_St,var_st, glob_st, fun_st, mem).
Proof.
intros var_st ex_St glob_st fun_st mem a b.
intros a_greater_than_b.
simpl.
induction b.
- induction a. auto. contradiction. auto.
- induction a. try (auto; unfold execute_i32_ge_s; unfold execute_i32_ge_s'; unfold get_execution_stack; simpl;
(*Search (_ >=? _).*) assert ((Z.pos p >=? Z.pos p0) = true);
unfold Z.geb;
case_eq (Z.pos p ?= Zpos p0); intros H0; trivial;
apply Zge_compare in a_greater_than_b;
rewrite H0 in a_greater_than_b;
exfalso; assumption;
rewrite H; reflexivity).
-- try (auto; unfold execute_i32_ge_s; unfold execute_i32_ge_s'; unfold get_execution_stack; simpl;
assert ((Z.pos p >=? Z.pos p0) = true);
unfold Z.geb;
case_eq (Z.pos p ?= Zpos p0); intros H0; trivial;
apply Zge_compare in a_greater_than_b;
rewrite H0 in a_greater_than_b;
exfalso; assumption;
rewrite H; reflexivity).
-- try (auto; unfold execute_i32_ge_s; unfold execute_i32_ge_s'; unfold get_execution_stack; simpl;
assert ((Z.pos p >=? Z.pos p0) = true);
unfold Z.geb;
case_eq (Z.pos p ?= Zpos p0); intros H0; trivial;
apply Zge_compare in a_greater_than_b;
rewrite H0 in a_greater_than_b;
exfalso; assumption;
rewrite H; reflexivity).
- induction a. contradiction.
-- unfold execute_i32_ge_s. unfold get_execution_stack. simpl. exfalso. auto.
-- unfold execute_i32_ge_s. unfold get_execution_stack. simpl.
assert ((Z.neg p >=? Z.neg p0) = true).
unfold Z.geb.
case_eq (Z.neg p ?= Zneg p0); intros H0; trivial.
apply Zge_compare in a_greater_than_b. rewrite H0 in a_greater_than_b. contradiction.
rewrite H. reflexivity.
Qed.

Lemma eval_i32_ge_s_false:
forall var_st ex_St glob_st fun_st mem a b, b < a ->
execute_intruction (i32_ge_s) ((i32 a :: i32 b :: ex_St), var_st, glob_st, fun_st, mem) = ( i32 0:: ex_St,var_st, glob_st, fun_st, mem).
Proof.
intros var_st ex_St glob_st fun_st mem a b.
intros a_greater_than_b.
simpl.
induction b.
- induction a.
-- discriminate.
-- try (auto; unfold execute_i32_ge_s; unfold execute_i32_ge_s'; unfold get_execution_stack; simpl;
assert ((Z.pos p >=? Z.pos p0) = true);
unfold Z.geb;
case_eq (Z.pos p ?= Zpos p0); intros H0; trivial;
apply Zge_compare in a_greater_than_b;
rewrite H0 in a_greater_than_b;
exfalso; assumption;
rewrite H; reflexivity).
-- discriminate.
- induction a.
-- discriminate.
-- unfold execute_i32_ge_s. unfold execute_i32_ge_s'. unfold get_execution_stack. simpl.
try (assert ((Z.pos p >=? Z.pos p0) = false);unfold "<" in a_greater_than_b; unfold ">=?"; rewrite a_greater_than_b; reflexivity; rewrite H; reflexivity).
-- unfold execute_i32_ge_s. unfold execute_i32_ge_s'. unfold get_execution_stack.
try (assert ((Z.pos p >=? Z.neg p0) = false);unfold "<" in a_greater_than_b; unfold ">=?"; rewrite a_greater_than_b; reflexivity; rewrite H; reflexivity).
- induction a.
-- unfold execute_i32_ge_s. unfold execute_i32_ge_s'. unfold get_execution_stack.
try (assert ((Z.neg p >=? 0) = false);unfold "<" in a_greater_than_b; unfold ">=?"; rewrite a_greater_than_b; reflexivity; rewrite H; reflexivity).
-- unfold execute_i32_ge_s. unfold execute_i32_ge_s'. unfold get_execution_stack.
try (assert ((Z.neg p >=? Z.pos p0) = false);unfold "<" in a_greater_than_b; unfold ">=?"; rewrite a_greater_than_b; reflexivity; rewrite H; reflexivity).
-- unfold execute_i32_ge_s. unfold execute_i32_ge_s'. unfold get_execution_stack. simpl.
try (assert ((Z.neg p >=? Z.neg p0) = false);unfold "<" in a_greater_than_b; unfold ">=?"; rewrite a_greater_than_b; reflexivity; rewrite H; reflexivity).
Qed.

Close Scope Z.

