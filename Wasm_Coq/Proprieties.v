Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
(*From Coq Require Import Arith.Arith.*)
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.Plus.
(*From Coq Require Import Lia.*)
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.Znat.
From Coq Require Import ZArith.BinInt.
(*From Coq Require Import ZArith.Zbool.*)
(*From Coq Require Import Reals.RIneq.*)
Import N2Z.
Import ListNotations.

From Coq Require Import ZArith.
(*Open Scope R_scope.*)

From LF Require Import Maps Wasm.

(** Admiited things that require extra attention *)

Open Scope Z.

Lemma a_plus_b_is_0 :
forall n m,
n = (-m) ->
n + m = 0%Z.
Proof.
intros.
rewrite H.
rewrite Z.add_opp_diag_l.
reflexivity.
Qed.

Lemma a_plus_b_is_NOT_0 :
forall n m,
n <> (-m) ->
n <> 0 \/ m <> 0 ->
(n + m =? 0) = false%Z.
Proof.
intros.
Admitted.

Lemma a_le_n_implies_a_diff_n_plus_1 :
forall (a n : Z),
a <= n -> a <> n+1.
Proof.
intros.
Admitted.

Open Scope positive_scope.
Lemma neg_div_pos_stays_neg :
forall (a : positive) b, (b > 0)%Z ->
((Z.neg a / b) <= 0)%Z.
Proof.
intros.
induction a.
+ rewrite Pos.xI_succ_xO. Search (_~1). 
Admitted.
Close Scope positive_scope.

(*Lemma small_div_is_0:
forall (a b : Z),
a >= 0 ->
a < b -> a / b = 0.
Proof.
Admitted.*)

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


(** General useful proprieties *)

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

(** Proprieties of functions defined by me*)
Open Scope Z.
Lemma load_8_from_adress_loads_1_byte :
forall
(pointer : Z)
(mem: list MemoryByte)
n,
n = (load_8_from_adress pointer mem) ->
n <= 255 /\ n >= 0.
Admitted.

Lemma signed2unsigned_of_not_0_is_not_0 :
forall (n m : Z),
n =? 0 = false ->
(m = 1 /\ (n <= 255                  /\ n >= -128) ) \/
(m = 2 /\ (n <= 65535                /\ n >= -32768) ) \/
(m = 4 /\ (n <= 4294967295           /\ n >= -2147483648) ) \/
(m = 8 /\ (n <= 18446744073709551615 /\ n >= -9223372036854775808) ) ->
(signed2unsigned n m =? 0) = false.
Proof.
intros.
unfold signed2unsigned.
induction n.
- inversion H.
- unfold "<?". 
  rewrite Zgt_pos_0. apply H.
- unfold "<?".
  rewrite Zlt_neg_0.
  destruct H0.
+ destruct H0.
  destruct H1.
  rewrite H0.
  rewrite a_plus_b_is_NOT_0.
++ reflexivity.
++
apply Z.ge_le in H2.
(*Search ( _ > _ -> _ ).
Search ( _ >= _).*)
unfold ">=" in H2.
unfold "<>".
Admitted.

Lemma unsigned2signed_of_not_0_is_not_0 :
forall (n m : Z),
n =? 0 = false ->
(m = 1 /\ (n <= 255                  /\ n >= -128) ) \/
(m = 2 /\ (n <= 65535                /\ n >= -32768) ) \/
(m = 4 /\ (n <= 4294967295           /\ n >= -2147483648) ) \/
(m = 8 /\ (n <= 18446744073709551615 /\ n >= -9223372036854775808) ) ->
(unsigned2signed n m =? 0) = false.
Proof.
intros.
unfold unsigned2signed.
destruct H0.
- induction n.
+ inversion H.
+ unfold ">=?".
  rewrite Zgt_pos_0.
destruct H0.
destruct H1.
rewrite H0.
unfold signBitIsOne.
unfold "<?".
rewrite Zgt_pos_0.
case_eq (Z.pos p >? 127).
++ intros.
unfold "=?".
apply a_plus_b_is_NOT_0.
+++ simpl.
Admitted.

Close Scope Z.

(** Proprieties of execute_instruction function*)
Open Scope Z.

(*Lemma gt :
forall (a b : Z),
(b >= a) = ((b >=? a) = true).
Proof.
intros.
Search (_ >=? _ = true).*)

Lemma eval_i32_ge_s_true 
(*cu mici modificari in loop_invariant_ge_10*):
forall var_st ex_St glob_st fun_st mem a b,
(b >=? a = true) ->
execute_instruction (i32_ge_s) ((i32 a :: i32 b :: ex_St), var_st, glob_st, fun_st, mem) = ( i32 1:: ex_St,var_st, glob_st, fun_st, mem).
Proof.
intros var_st ex_St glob_st fun_st mem a b.
intros a_greater_than_b.
simpl.
unfold execute_i32_ge_s.
simpl.
rewrite a_greater_than_b.
rewrite Z.geb_leb in a_greater_than_b.
reflexivity.
Qed.

Lemma eval_i32_ge_s_true_old:
forall var_st ex_St glob_st fun_st mem a b,
b >= a ->
execute_instruction (i32_ge_s) ((i32 a :: i32 b :: ex_St), var_st, glob_st, fun_st, mem) = ( i32 1:: ex_St,var_st, glob_st, fun_st, mem).
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
execute_instruction (i32_ge_s) ((i32 a :: i32 b :: ex_St), var_st, glob_st, fun_st, mem) = ( i32 0:: ex_St,var_st, glob_st, fun_st, mem).
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

Open Scope com_scope.


(*Lemma plus_comm1 :
forall (a b: Z)
(ex_st : list WasmType)
(var_st glob_st : VariableList)
(fun_st : FunctionList)
(mem : Memory),
(( (i32 a)::(i32 b)::ex_st), var_st ,glob_st ,fun_st, mem)=[
i32.add
]=> ( (i32 ((b+a)mod 4294967296)::ex_st), var_st ,glob_st ,fun_st, mem) / SContinue.
Proof.
intros.
apply E_i32_add.
- reflexivity.
- simpl.
  unfold execute_i32_add.
  simpl.
  reflexivity.
Qed.

Lemma plus_comm2 :
forall (a b: Z)
(ex_st : list WasmType)
(var_st glob_st : VariableList)
(fun_st : FunctionList)
(mem : Memory),
(( (i32 b)::(i32 a)::ex_st), var_st ,glob_st ,fun_st, mem)=[
i32.add
]=> ( (i32 ((a+b)mod 4294967296)::ex_st), var_st ,glob_st ,fun_st, mem) / SContinue.
Proof.
intros.
apply E_i32_add.
- reflexivity.
- simpl.
  unfold execute_i32_add.
  simpl.
  reflexivity.
Qed.*)

Lemma plus_comm :
forall (a b: Z)
(ex_st : list WasmType)
(var_st glob_st : VariableList)
(fun_st : FunctionList)
(mem : Memory),

execute_instruction (i32_add) (( (i32 a)::(i32 b)::ex_st), var_st ,glob_st ,fun_st, mem) =
execute_instruction (i32_add) (( (i32 b)::(i32 a)::ex_st), var_st ,glob_st ,fun_st, mem).
Proof.
intros.
simpl.
unfold execute_i32_add.
simpl.
rewrite Z.add_comm.
reflexivity.
Qed.

Lemma xor_n_n :
forall (n : Z)
(ex_st : list WasmType)
(var_st glob_st : VariableList)
(fun_st : FunctionList)
(mem : Memory),
(( (i32 n)::(i32 n)::ex_st), var_st ,glob_st ,fun_st, mem)=[
i32.xor
]=> ( (i32 (0)::ex_st), var_st ,glob_st ,fun_st, mem) / SContinue.
Proof.
intros.
apply E_i32_xor.
- reflexivity.
- simpl.
  unfold execute_i32_xor.
  simpl.
  rewrite Z.lxor_nilpotent.
  reflexivity.
Qed.

Close Scope Z.

