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
(*Open Scope R_scope.*)

From LF Require Import Maps Wasm Proprieties.

Open Scope Z.
Open Scope com_scope.

(*Program Fixpoint invers' (fuel : nat )(n : Z) p {measure fuel}: Z :=
match fuel with
| 0%nat => 0
| _ => if (n >=? 10) then ((invers' (fuel-1) (n/10) (p+1)) + (Z.modulo n 10) * (Z.pow 10 p)) else Z.modulo n 10
end.
Next Obligation.
induction fuel.
 - simpl. contradiction.
 - induction fuel.
 -- auto.
 -- auto.
Qed.
Definition invers (n : Z) : Z := invers' 21 n 0. *)

Require Import Coq.Init.Decimal.
Require Import Datatypes Specif.

(*Search (Z -> N).
Search (N -> uint).
Search (uint -> Z).*)

Definition invers'' (n : Decimal.uint) :=
match n with
 | D0 (n') => D0 
 | D1 (n') => D1
 | D2 (n') => D2
 | D3 (n') => D3
 | D4 (n') => D4
 | D5 (n') => D5
 | D6 (n') => D6
 | D7 (n') => D7
 | D8 (n') => D8
 | D9 (n') => D9
 | Nil => D0
end.
Fixpoint invers' (n : Decimal.uint) (inv : Decimal.uint):=
match n with
| Nil => inv
| D0 (n') => invers' n' (D0 inv)
| D1 (n') => invers' n' (D1 inv)
| D2 (n') => invers' n' (D2 inv)
| D3 (n') => invers' n' (D3 inv)
| D4 (n') => invers' n' (D4 inv)
| D5 (n') => invers' n' (D5 inv)
| D6 (n') => invers' n' (D6 inv)
| D7 (n') => invers' n' (D7 inv)
| D8 (n') => invers' n' (D8 inv)
| D9 (n') => invers' n' (D9 inv)
end.
Definition invers (n : Z) :=
match n with
| 0 => 0
| Z.pos n' => Z.of_uint (invers' (N.to_uint (ZtoN (Z.pos n'))) (Nil))
| Z.neg _ => 0
end.

(*Definition invers_fara_ultima_cifra (n : Z) :=
let inv := (invers n) in
Z.of_uint (match inv with
| Nil => Nil
| D0 (n') => n'
| D1 (n') => n'
| D2 (n') => n'
| D3 (n') => n'
| D4 (n') => n'
| D5 (n') => n'
| D6 (n') => n'
| D7 (n') => n'
| D8 (n') => n'
| D9 (n') => n'
end).*)

(*
Fixpoint nr_cifre (fuel: nat) (n:Z) : Z :=
match fuel with
| O => 0
| S f => if n >? 0 then (nr_cifre f (n/10))+1 else 0
end.

Fixpoint invers' (fuel : nat) (n : Z) (p : Z) : Z :=
match fuel with
| O => 0
| S f => if (n >=? 1) then ((Z.pow 10 p) * (Z.modulo n 10)) + (invers' f (Z.div n 10) (p - 1)) else 0
end.
Definition invers (n : Z) : Z := invers' 22 n ((nr_cifre 22 n)-1).
*)


Eval compute in invers 0.
Eval compute in invers 123.
Eval compute in invers 8.
Eval compute in invers 86.
Eval compute in invers (-3).
Eval compute in Z.modulo (-3) 10.

(*Definition one_inv_step (n : Z) : Z := *)

Definition inv : string := "inv".
Definition temp : string := "temp".
Definition IN : string := "IN".
Definition label1 : string := "label1".

Lemma loop_invariant_ge_10 :
forall (n m_inv m_init : Z) glob_st fun_st (label:string) mem, m_init >= 10 ->
([], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem) =[
 Clocal_get inv ;
 Ci32_const 10 ;
 Ci32_mul ;
 Clocal_get temp;
 Ci32_const 10 ;
 Ci32_rem_s ;
 Ci32_add ;
 Clocal_set inv ;
 Clocal_get temp ;
 Ci32_const 10 ;
 Ci32_div_s ;
 Clocal_set temp ;
 Clocal_get temp ;
 Ci32_const 1 ;
 Ci32_ge_s ;
 CBr_If label
]=> ([] , [(IN, i32 n) ;(inv, i32 ((Z.modulo (m_init) 10) + (m_inv * 10)) ); (temp, i32 (m_init / 10))], glob_st, fun_st, mem) / SBr label.
Proof.
intros n m_inv m_init glob_st fun_st label mem.
induction m_init.
- unfold ">=". simpl. contradiction.
- intros p_pos. apply E_Seq with ([i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
-- apply E_local_get. reflexivity.
-- apply E_Seq with ([i32 10; i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
--- apply E_i32_const.
--- apply E_Seq with ([i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
---- apply E_i32_mul. auto. auto.
---- apply E_Seq with ([i32 (Zpos p); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
----- apply E_local_get. auto.
----- apply E_Seq with ([i32 10; i32 (Zpos p); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
------- apply E_i32_const.
------- apply E_Seq with ([i32 (Z.modulo (Zpos p) 10); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
--------- apply E_i32_rem_s. auto. auto. auto.
--------- apply E_Seq with ([i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
---------- apply E_i32_add. auto. auto.
---------- apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
----------- apply E_local_set. auto. auto.
----------- apply E_Seq with ([i32 (Zpos p)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
------------ apply E_local_get. auto.
------------ apply E_Seq with ([i32 10; i32 (Zpos p)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
------------- apply E_i32_const.
------------- apply E_Seq with ([i32 ((Zpos p) / 10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st, mem).
-------------- apply E_i32_div_s. auto. auto. auto.
-------------- apply E_Seq with  ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st, mem).
--------------- apply E_local_set. auto. auto.
--------------- apply E_Seq with ([i32 ((Zpos p) / 10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st, mem).
---------------- apply E_local_get. auto.
---------------- apply E_Seq with ([i32 1; i32 ((Zpos p) / 10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st, mem).
----------------- apply E_i32_const.
----------------- apply E_Seq with ([i32 1], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st, mem).
------------------ apply E_i32_ge_s. auto. apply eval_i32_ge_s_true. apply positive_ge_10_implies_p_div_10_ge_1. assumption.
------------------ apply E_Br_IfTrue.
------------------- reflexivity.
------------------- reflexivity.
- intros H0. contradiction.
Qed.

Lemma loop_invariant_lt_10 :
forall n m_inv m_init m_step glob_st fun_st (label:string) mem,
m_step = ((Z.modulo (m_init) 10) + (m_inv * 10)) ->
(*m_init / 10 = 0 ->*)
m_init < 10 ->
([], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem) =[
 Clocal_get inv ;
 Ci32_const 10 ;
 Ci32_mul ;
 Clocal_get temp;
 Ci32_const 10 ;
 Ci32_rem_s ;
 Ci32_add ;
 Clocal_set inv ;
 Clocal_get temp ;
 Ci32_const 10 ;
 Ci32_div_s ;
 Clocal_set temp ;
 Clocal_get temp ;
 Ci32_const 1 ;
 Ci32_ge_s ;
 CBr_If label
]=> ([] , [(IN, i32 n) ;(inv, i32 m_step); (temp, i32 (m_init / 10))], glob_st, fun_st, mem) / SContinue.
(* Am pus ca valoarea lui temp dupa executie este (m_init / 10), nu direct 0*)
Proof.
intros n m_inv m_init m_step glob_st fun_st label mem.
intros H0 H1.
apply E_Seq with ([i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_local_get. auto.
apply E_Seq with ([i32 10; i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_i32_const.
apply E_Seq with ([i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_i32_mul. auto. auto.
apply E_Seq with ([i32 m_init; i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_local_get. auto.
apply E_Seq with ([i32 10; i32 m_init; i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_i32_const.
apply E_Seq with ([i32 (Z.modulo m_init 10); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_i32_rem_s. auto. auto. auto.
apply E_Seq with ([i32 ((Z.modulo m_init 10) + (m_inv * 10))], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_i32_add. auto. auto.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_local_set. auto. auto.
apply E_Seq with ([i32 m_init], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_local_get. auto.
apply E_Seq with ([i32 10; i32 m_init], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_i32_const.
apply E_Seq with ([i32 (m_init/10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st, mem).
apply E_i32_div_s. auto. auto. auto.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 (m_init/10))], glob_st, fun_st, mem).
apply E_local_set. auto. auto.
apply E_Seq with ([i32 (m_init/10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 (m_init/10))], glob_st, fun_st, mem).
apply E_local_get. auto.
apply E_Seq with ([i32 1; i32 (m_init/10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 (m_init/10))], glob_st, fun_st, mem).
apply E_i32_const.
induction m_init.
- apply E_Seq with ([i32 0], [(IN, i32 n) ;(inv, i32 (0 + (m_inv * 10))); (temp, i32 (0))], glob_st, fun_st, mem).
-- simpl. apply E_i32_ge_s. auto. auto.
-- apply E_Br_IfFalse. auto. simpl. rewrite H0. simpl. auto.
- apply E_Seq with ([i32 0], [(IN, i32 n); (inv, i32 (Z.pos p mod 10 + m_inv * 10)); (temp, i32 (Z.pos p / 10))], glob_st, fun_st, mem).
-- apply E_i32_ge_s. auto. apply eval_i32_ge_s_false. apply positive_lt_than_10_implies_p_div_10_lt_1. assumption.
-- apply E_Br_IfFalse. auto. rewrite Zdiv.Zdiv_small. rewrite H0. simpl. auto. split. apply Pos2Z.is_nonneg. assumption.
- apply E_Seq with ([i32 0], [(IN, i32 n); (inv, i32 (Z.neg p mod 10 + m_inv * 10)); (temp, i32 (Z.neg p / 10))], glob_st, fun_st, mem).
-- apply E_i32_ge_s. auto. simpl. apply eval_i32_ge_s_false.
assert (Z.neg p / 10 <= 0). apply negative_lt_than_10_implies_n_div_10_is_0. assumption. apply lt1_equiv_le0. assumption.
-- apply E_Br_IfFalse. auto. rewrite H0. simpl. auto.
Qed.
(*assert (Z.neg p / 10 = 0).
+ apply small_div_is_0. assumption.
+ rewrite H. trivial.
Qed.*)

Open Scope positive_scope.

Lemma loop_invariant :
forall n temp_init inv_init glob_st fun_st label mem,
([], [(IN, i32 n) ;(inv, i32 inv_init); (temp, i32 temp_init)],glob_st, fun_st, mem) =[
 Clocal_get inv ;
 Ci32_const 10%Z ;
 Ci32_mul ;
 Clocal_get temp;
 Ci32_const 10%Z ;
 Ci32_rem_s ;
 Ci32_add ;
 Clocal_set inv ;
 Clocal_get temp ;
 Ci32_const 10%Z ;
 Ci32_div_s ;
 Clocal_set temp ;
 Clocal_get temp ;
 Ci32_const 1%Z ;
 Ci32_ge_s ;
 CBr_If label
]=> ([] , [(IN, i32 n) ;(inv, i32 ((Z.modulo (temp_init) 10) + (inv_init * 10))); (temp, i32 (temp_init / 10))], glob_st, fun_st, mem) / if (temp_init) >=? 10 then SBr label else SContinue.
Proof.
intros n temp_init inv_init glob_st fun_st label mem.
induction temp_init.
- apply loop_invariant_lt_10. reflexivity. reflexivity. 
- case_eq(Z.pos p >=? 10).
-- intros. apply loop_invariant_ge_10. unfold Z.ge.
case_eq (Z.pos p ?= 10)%Z.
+ discriminate.
+ intros. unfold Z.geb in H. rewrite H0 in H. inversion H.
+ discriminate.
-- intros. apply loop_invariant_lt_10. reflexivity.  unfold Z.lt.
case_eq (Z.pos p ?= 10)%Z.
+ intros. unfold Z.geb in H. rewrite H0 in H. inversion H.
+ intros. reflexivity.
+ intros. unfold Z.geb in H. rewrite H0 in H. inversion H.
- apply loop_invariant_lt_10. reflexivity. rewrite Zlt_neg_0. reflexivity.
Qed.


Definition bintest : positive := 1~0~0.
Eval compute in bintest.
Eval compute in (Z.pos).
Eval compute in bintest~0.
Eval compute in bintest~1.

Open Scope Z.
Lemma invers_for_0_10 :
forall n,
(n < 10)%Z ->
(n >= 0)%Z  ->
invers (n) = n.
Proof.
intros.
simpl.
(*case_eq (n ?= 0%Z)%Z.
- intros. apply Z.compare_eq in H1. rewrite H1. reflexivity.
- intros. unfold ">=" in H0. contradiction.
- intros. case_eq (n ?= 1)%Z.
-- intros. apply Z.compare_eq in H2. rewrite H2. reflexivity.
-- intros. Search (_ ?= _ = Gt).
(*rewrite Z.compare_gt_iff in H1.
rewrite Z.compare_lt_iff in H2.*)
rewrite Z.compare_gt_iff in H1.
rewrite Z.compare_lt_iff in H2.
case_eq (n =? 0).
* intros. rewrite Z.eqb_eq in H3. rewrite H3. reflexivity.
* intros. Search (_ =? _ = false). rewrite Z.eqb_neq in H3.


Search ( Z.pred  _ ). apply Z.pred_inj.

+ discriminate.
+ rewrite Z.compare_lt_iff in H2. assumption.
+ .
rewrite Z.lt_succ_l in H1.
*)

case_eq (n =? 0)%Z.
- intros.
rewrite Z.eqb_eq in H1.
rewrite H1. reflexivity.
- intros. case_eq (n =? 1)%Z.
-- intros. 
rewrite Z.eqb_eq in H2.
rewrite H2. reflexivity.
-- intros. case_eq (n =? 2)%Z.
--- intros.
rewrite Z.eqb_eq in H3.
rewrite H3. reflexivity.
--- intros. case_eq (n =? 3)%Z.
---- intros.
rewrite Z.eqb_eq in H4.
rewrite H4. reflexivity.
---- intros. case_eq (n =? 4)%Z.
----- intros.
rewrite Z.eqb_eq in H5.
rewrite H5. reflexivity.
----- intros. case_eq (n =? 5)%Z.
------ intros.
rewrite Z.eqb_eq in H6.
rewrite H6. reflexivity.
------ intros. case_eq (n =? 6)%Z.
------- intros.
rewrite Z.eqb_eq in H7.
rewrite H7. reflexivity.
------- intros. case_eq (n =? 7)%Z.
-------- intros.
rewrite Z.eqb_eq in H8.
rewrite H8. reflexivity.
-------- intros. case_eq (n =? 8)%Z.
--------- intros.
rewrite Z.eqb_eq in H9.
rewrite H9. reflexivity.
--------- intros. case_eq (n =? 9)%Z.
---------- intros.
rewrite Z.eqb_eq in H10.
rewrite H10. reflexivity.
---------- intros.
Admitted.

Definition inv_loop_content :=
<{Clocal_get inv ;
 Ci32_const 10%Z ;
 Ci32_mul ;
 Clocal_get temp;
 Ci32_const 10%Z ;
 Ci32_rem_s ;
 Ci32_add ;
 Clocal_set inv ;
 Clocal_get temp ;
 Ci32_const 10%Z ;
 Ci32_div_s ;
 Clocal_set temp ;
 Clocal_get temp ;
 Ci32_const 1%Z ;
 Ci32_ge_s ;
 CBr_If label1}>.

(*  *)
Lemma example_calculeaza_invers_general:
forall n glob_st fun_st mem,
([], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)],glob_st, fun_st, mem) =[
Ci32_const 0%Z ;
Clocal_set inv ;
Clocal_get IN ;
Clocal_set temp ;
(*Clocal_get IN ;
Ci32_const 9 ;
Ci32_ge_s ;
if
 Clocal_get IN ;
 Clocal_set temp ; *)
loop (label1)
 <{Clocal_get inv ;
 Ci32_const 10%Z ;
 Ci32_mul ;
 Clocal_get temp;
 Ci32_const 10%Z ;
 Ci32_rem_s ;
 Ci32_add ;
 Clocal_set inv ;
 Clocal_get temp ;
 Ci32_const 10%Z ;
 Ci32_div_s ;
 Clocal_set temp ;
 Clocal_get temp ;
 Ci32_const 1%Z ;
 Ci32_ge_s ;
 CBr_If label1}>
 (*end*)
end ;
Clocal_get inv
]=> ([i32 (invers n)] , [(IN, i32 n) ;(inv, i32 (invers n)); (temp, i32 0)],glob_st, fun_st, mem) / SContinue.
Proof.
intros n glob_st fun_st mem.
apply E_Seq with ([i32 0], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)] ,glob_st, fun_st, mem).
apply E_i32_const.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)],glob_st, fun_st, mem).
apply E_local_set. auto. auto.
apply E_Seq with ([i32 n], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)],glob_st, fun_st, mem).
apply E_local_get. auto.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 0); (temp, i32 n)],glob_st, fun_st, mem).
apply E_local_set. auto. auto.
induction n.
- apply E_Seq with ([] , [(IN, i32 0) ;(inv, i32 (invers 0)); (temp, i32 0)],glob_st, fun_st, mem).
-- apply E_LoopOnce. apply loop_invariant.
-- apply E_local_get. auto.
- apply E_Seq with ([] , [(IN, i32 (Z.pos p)) ;(inv, i32 (invers (Z.pos p))); (temp, i32 (Z.pos p / 10))],glob_st, fun_st, mem).
-- apply E_Loop with ([] , [(IN, i32 (Z.pos p)) ;(inv, i32 ((invers (Z.pos p)) / 10)); (temp, i32 (Z.modulo (Z.pos p) 10) )],glob_st, fun_st, mem) label1.
--- induction p.
Search (Z -> uint).
+ rewrite Pos2Z.pos_xI. 
rewrite loop_invariant.

 
+ 




 case_eq(Z.pos p <? 10)%Z.
+ intros. apply E_LoopOnce.
apply loop_invariant_lt_10.
++ case_eq(Z.pos p <? 0)%Z.
+++ intros. simpl.
assert ((Z.pos p > 0)%Z).
++++ Search (Z.pos _). apply Zgt_pos_0.
++++ unfold Z.ltb in H0. rewrite H1 in H0. inversion H0.
+++ intros. rewrite invers_for_0_10.
++++ Admitted.

(*
unfold invers. unfold invers'. simpl.



(*uwu*)


assert ((Z.pos p) / 10 = 0)%Z.
++ apply small_div_is_0. unfold Z.lt.
case_eq (Z.pos p ?= 10)%Z.
+++ intros. unfold Z.ltb in H. rewrite H0 in H. inversion H.
+++ intros. reflexivity.
+++ intros. unfold Z.ltb in H. rewrite H0 in H. inversion H.
++


 apply loop_invariant_lt_10.
apply E_Loop with ([] , [(IN, i32 (Z.pos p)) ;(inv, i32 (invers (Z.pos p))); (temp, i32 0)]).
 

-- apply loop_invariant_lt_10. reflexivity. reflexivity.
-- apply E_local_get.
- apply E_Seq with ([], [(IN, i32 (Z.pos p)); (inv, i32 (invers (Z.pos p))); (temp, i32 0)]).
*)
(*(*Asta merge pentru p~1 dar are un Admit in "Proprieties.v" *)
(* Asta e stupida, prost am fost*)
--- induction p.
---- apply E_LoopOnce.
assert ((p~1) = (p*2) + 1).
----- Search (_~1).
assert ((p~1) = 3). 
+ auto. apply bin3toZ3.
+ rewrite H. apply loop_invariant_lt_10. reflexivity. reflexivity.
---- apply E_LoopOnce.
assert ((p~0) = 2).
+ Search (_ ~ 0 = _). apply bin2toZ2.
+ rewrite H. apply loop_invariant_lt_10. reflexivity. reflexivity.
---- apply E_LoopOnce. apply loop_invariant_lt_10. reflexivity. reflexivity.
--- apply E_local_get.
- apply E_Seq with ([] , [(IN, i32 (Z.neg p)) ;(inv, i32 (invers (Z.neg p))); (temp, i32 0)]).
-- induction p. 
--- apply E_LoopOnce.
assert ((p~1) = 3).
+ apply bin3toZ3.
+ rewrite H. apply loop_invariant_lt_10.  reflexivity. reflexivity.
--- apply E_LoopOnce. 
assert ((p~0) = 2).
+ apply bin2toZ2.
+ rewrite H. apply loop_invariant_lt_10.  reflexivity. reflexivity.
--- apply E_LoopOnce. apply loop_invariant_lt_10. reflexivity. reflexivity.
-- apply E_local_get.
Qed.*)



(*(* E o idee sa fac assert si sa impart in jumatati, dar ce fac mai departe? *)
assert (((p < 10) -> 
([], [(IN, i32 (Z.pos p)); (inv, i32 0); (temp, i32 (Z.pos p))]) =[
     (Clocal_get inv);
     (Ci32_const 10%Z);
     Ci32_mul;
     (Clocal_get temp);
     (Ci32_const 10%Z);
     Ci32_rem_s;
     Ci32_add;
     (Clocal_set inv);
     (Clocal_get temp);
     (Ci32_const 10%Z);
     Ci32_div_s;
     (Clocal_set temp);
     (Clocal_get temp); (Ci32_const 1%Z);
     Ci32_ge_s;
     (CBr_If label1)
]=> ([],
    [(IN, i32 (Z.pos p)); (inv, i32 (invers (Z.pos p))); (temp, i32 0)]) 
/ SContinue) /\ ((p>=10) ->
([], [(IN, i32 (Z.pos p)); (inv, i32 0); (temp, i32 (Z.pos p))]) =[
     (Clocal_get inv);
     (Ci32_const 10%Z);
     Ci32_mul;
     (Clocal_get temp);
     (Ci32_const 10%Z);
     Ci32_rem_s;
     Ci32_add;
     (Clocal_set inv);
     (Clocal_get temp);
     (Ci32_const 10%Z);
     Ci32_div_s;
     (Clocal_set temp);
     (Clocal_get temp); (Ci32_const 1%Z);
     Ci32_ge_s;
     (CBr_If label1)
]=> ([],
    [(IN, i32 (Z.pos p)); (inv, i32 (invers (Z.pos p))); (temp, i32 0)])
/ SBr
)).
+ split.
++ intros.
apply loop_invariant_lt_10.
+++ simpl.
assert ((invers (Z.pos p)) = 0%Z).
++++

assert (0%Z = Z.pos p / 10). 
+++ rewrite small_div_is_0. trivial. assumption.
+++ rewrite loop_invariant_lt_10.

 *) 




(* Asta merge dar e redundanta
apply E_Seq with ([i32 0], [(IN, i32 (Z.pos p~1)); (inv, i32 0); (temp, i32 (Z.pos p~1))]).
apply E_local_get.
apply E_Seq with ([i32 10; i32 0], [(IN, i32 (Z.pos p~1)); (inv, i32 0); (temp, i32 (Z.pos p~1))]).
apply E_i32_const.
apply E_Seq with ([i32 0], [(IN, i32 (Z.pos p~1)); (inv, i32 0); (temp, i32 (Z.pos p~1))]).
apply E_i32_mul. auto.
apply E_Seq with ([i32 (Z.pos p~1);i32 0], [(IN, i32 (Z.pos p~1)); (inv, i32 0); (temp, i32 (Z.pos p~1))]).
apply E_local_get.
apply E_Seq with ([i32 10; i32 (Z.pos p~1);i32 0], [(IN, i32 (Z.pos p~1)); (inv, i32 0); (temp, i32 (Z.pos p~1))]).
apply E_i32_const.
apply E_Seq with ([i32 (Z.modulo (Z.pos p~1) 10); i32 0], [(IN, i32 (Z.pos p~1)); (inv, i32 0); (temp, i32 (Z.pos p~1))]).
apply E_i32_rem_s. auto. auto.
apply E_Seq with ([i32 ((Z.modulo (Z.pos p~1) 10) + 0)], [(IN, i32 (Z.pos p~1)); (inv, i32 0); (temp, i32 (Z.pos p~1))]).
apply E_i32_add. auto. 
apply E_Seq with ([], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 (Z.pos p~1))]).
apply E_local_set. auto.
apply E_Seq with ([i32 (Z.pos p~1)], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 (Z.pos p~1))]).
apply E_local_get.
apply E_Seq with ([i32 10; i32 (Z.pos p~1)], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 (Z.pos p~1))]).
apply E_i32_const.
apply E_Seq with ([i32 ((Z.pos p~1)/10)], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 (Z.pos p~1))]).
apply E_i32_div_s. auto. auto.
apply E_Seq with ([], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 ((Z.pos p~1)/10))]).
apply E_local_set. auto.
apply E_Seq with ([i32 ((Z.pos p~1)/10)], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 ((Z.pos p~1)/10))]).
apply E_local_get.
apply E_Seq with ([i32 1; i32 ((Z.pos p~1)/10)], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 ((Z.pos p~1)/10))]).
apply E_i32_const.
apply E_Seq with ([i32 0], [(IN, i32 (Z.pos p~1)); (inv, i32 ((Z.modulo (Z.pos p~1) 10) + 0)); (temp, i32 ((Z.pos p~1)/10))]).
apply E_i32_ge_s. auto. apply eval_i32_ge_s_false.
----- rewrite Zdiv.Zdiv_small. reflexivity. split. apply Pos2Z.is_nonneg.
Search (Z.pos _ < _). apply Pos2Z.pos_lt_pos. unfold "<".
+ rewrite H. simpl. reflexivity.
----- apply E_Br_IfFalse. auto.
*)


(* Astea sunt idei de care nu a mai fost nevoie
 rewrite loop_invariant_lt_10.
---- apply E_LoopOnce. induction p.
---- 


- apply E_Seq with ([i32 0], [(IN, i32 0) ;(inv, i32 0); (temp, i32 0)]).
-- apply E_i32_ge_s. auto. auto.
-- apply E_Seq with ([], [(IN, i32 0) ;(inv, i32 0); (temp, i32 0)]).
--- apply E_IfFalse.
---- auto.
---- auto.
--- apply E_local_get.
- induction p.
-- apply E_Seq with ([i32 0], [(IN, i32 (Z.pos p)); (inv, i32 0); (temp, i32 0)]).
--- apply E_i32_ge_s. auto.
- apply E_Seq with ([i32 0], [(IN, i32 (Z.pos p)); (inv, i32 0); (temp, i32 0)]).
-- apply E_i32_ge_s. auto. apply eval_i32_ge_s_true.
*)

(* Asta e o incercare mai veche
Lemma loop_inv :
forall n m_inv m_init,
([], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)]) =[
 Clocal_get inv ;
 Ci32_const 10 ;
 Ci32_mul ;
 Clocal_get temp;
 Ci32_const 10 ;
 Ci32_rem_s ;
 Ci32_add ;
 Clocal_set inv ;
 Clocal_get temp ;
 Ci32_const 10 ;
 Ci32_div_s ;
 Clocal_set temp ;
 Clocal_get temp ;
 Ci32_const 1 ;
 Ci32_ge_s ;
 CBr_If label1
]=> ([] , [(IN, i32 n) ;(inv, i32 (invers m_inv) ); (temp, i32 (m_init / 10))]) / SContinue.
Proof.
intros.
induction m_init.
- apply loop_invariant_lt_10. reflexivity.
*)

Close Scope com_scope.
Close Scope Z.