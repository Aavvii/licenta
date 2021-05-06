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

Eval compute in nr_cifre 12 654.

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
forall (n m_inv m_init : Z) glob_st fun_st (label:string), m_init >= 10 ->
([], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st) =[
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
]=> ([] , [(IN, i32 n) ;(inv, i32 ((Z.modulo (m_init) 10) + (m_inv * 10)) ); (temp, i32 (m_init / 10))], glob_st, fun_st) / SBr label.
Proof.
intros n m_inv m_init glob_st fun_st label.
induction m_init.
- unfold ">=". simpl. contradiction.
- intros p_pos. apply E_Seq with ([i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st).
-- apply E_local_get.
-- apply E_Seq with ([i32 10; i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st).
--- apply E_i32_const.
--- apply E_Seq with ([i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st).
---- apply E_i32_mul. auto. auto.
---- apply E_Seq with ([i32 (Zpos p); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st).
----- apply E_local_get.
----- apply E_Seq with ([i32 10; i32 (Zpos p); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st).
------- apply E_i32_const.
------- apply E_Seq with ([i32 (Z.modulo (Zpos p) 10); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st).
--------- apply E_i32_rem_s. auto. auto. auto.
--------- apply E_Seq with ([i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 (Zpos p))], glob_st, fun_st).
---------- apply E_i32_add. auto. auto.
---------- apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st).
----------- apply E_local_set. auto.
----------- apply E_Seq with ([i32 (Zpos p)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st).
------------ apply E_local_get.
------------ apply E_Seq with ([i32 10; i32 (Zpos p)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st).
------------- apply E_i32_const.
------------- apply E_Seq with ([i32 ((Zpos p) / 10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 (Zpos p))], glob_st, fun_st).
-------------- apply E_i32_div_s. auto. auto. auto.
-------------- apply E_Seq with  ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st).
--------------- apply E_local_set. auto.
--------------- apply E_Seq with ([i32 ((Zpos p) / 10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st).
---------------- apply E_local_get.
---------------- apply E_Seq with ([i32 1; i32 ((Zpos p) / 10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st).
----------------- apply E_i32_const.
----------------- apply E_Seq with ([i32 1], [(IN, i32 n) ;(inv, i32 ((Z.modulo (Zpos p) 10) + (m_inv * 10))); (temp, i32 ((Zpos p) / 10))], glob_st, fun_st).
------------------ apply E_i32_ge_s. auto. apply eval_i32_ge_s_true. apply positive_ge_10_implies_p_div_10_ge_1. assumption.
------------------ apply E_Br_IfTrue.
------------------- reflexivity.
------------------- reflexivity.
- intros H0. contradiction.
Qed.

Lemma loop_invariant_lt_10 :
forall n m_inv m_init m_step glob_st fun_st (label:string),
m_step = ((Z.modulo (m_init) 10) + (m_inv * 10)) ->
(*m_init / 10 = 0 ->*)
m_init < 10 ->
([], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st) =[
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
]=> ([] , [(IN, i32 n) ;(inv, i32 m_step); (temp, i32 (m_init / 10))], glob_st, fun_st) / SContinue.
(* Am pus ca valoarea lui temp dupa executie este (m_init / 10), nu direct 0*)
Proof.
intros n m_inv m_init m_step glob_st fun_st label.
intros H0 H1.
apply E_Seq with ([i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st).
apply E_local_get.
apply E_Seq with ([i32 10; i32 m_inv], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st).
apply E_i32_const.
apply E_Seq with ([i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st).
apply E_i32_mul. auto. auto.
apply E_Seq with ([i32 m_init; i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st).
apply E_local_get.
apply E_Seq with ([i32 10; i32 m_init; i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st).
apply E_i32_const.
apply E_Seq with ([i32 (Z.modulo m_init 10); i32 (m_inv * 10)], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st).
apply E_i32_rem_s. auto. auto. auto.
apply E_Seq with ([i32 ((Z.modulo m_init 10) + (m_inv * 10))], [(IN, i32 n) ;(inv, i32 m_inv); (temp, i32 m_init)], glob_st, fun_st).
apply E_i32_add. auto. auto.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st).
apply E_local_set. auto.
apply E_Seq with ([i32 m_init], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st).
apply E_local_get.
apply E_Seq with ([i32 10; i32 m_init], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st).
apply E_i32_const.
apply E_Seq with ([i32 (m_init/10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 m_init)], glob_st, fun_st).
apply E_i32_div_s. auto. auto. auto.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 (m_init/10))], glob_st, fun_st).
apply E_local_set. auto.
apply E_Seq with ([i32 (m_init/10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 (m_init/10))], glob_st, fun_st).
apply E_local_get.
apply E_Seq with ([i32 1; i32 (m_init/10)], [(IN, i32 n) ;(inv, i32 ((Z.modulo m_init 10) + (m_inv * 10))); (temp, i32 (m_init/10))], glob_st, fun_st).
apply E_i32_const.
induction m_init.
- apply E_Seq with ([i32 0], [(IN, i32 n) ;(inv, i32 (0 + (m_inv * 10))); (temp, i32 (0))], glob_st, fun_st).
-- simpl. apply E_i32_ge_s. auto. auto.
-- apply E_Br_IfFalse. auto. simpl. rewrite H0. simpl. auto.
- apply E_Seq with ([i32 0], [(IN, i32 n); (inv, i32 (Z.pos p mod 10 + m_inv * 10)); (temp, i32 (Z.pos p / 10))], glob_st, fun_st).
-- apply E_i32_ge_s. auto. apply eval_i32_ge_s_false. apply positive_lt_than_10_implies_p_div_10_lt_1. assumption.
-- apply E_Br_IfFalse. auto. rewrite Zdiv.Zdiv_small. rewrite H0. simpl. auto. split. apply Pos2Z.is_nonneg. assumption.
- apply E_Seq with ([i32 0], [(IN, i32 n); (inv, i32 (Z.neg p mod 10 + m_inv * 10)); (temp, i32 (Z.neg p / 10))], glob_st, fun_st).
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
forall n temp_init inv_init glob_st fun_st label,
([], [(IN, i32 n) ;(inv, i32 inv_init); (temp, i32 temp_init)],glob_st, fun_st) =[
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
]=> ([] , [(IN, i32 n) ;(inv, i32 ((Z.modulo (temp_init) 10) + (inv_init * 10))); (temp, i32 (temp_init / 10))], glob_st, fun_st) / if (temp_init) >=? 10 then SBr label else SContinue.
Proof.
intros n temp_init inv_init glob_st fun_st label.
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

Lemma invers_for_0_10 :
forall n,
(n < 10)%Z ->
(n >= 0)%Z  ->
invers (n) = n.
Proof.
intros.
simpl.
case_eq (n =? 0)%Z.
- intros.
Admitted.

(*  *)
Lemma example_calculeaza_invers_general:
forall n glob_st fun_st,
([], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)],glob_st, fun_st) =[
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
 CBr_If label1
 (*end*)
end ;
Clocal_get inv
]=> ([i32 (invers n)] , [(IN, i32 n) ;(inv, i32 (invers n)); (temp, i32 0)],glob_st, fun_st) / SContinue.
Proof.
intros n glob_st fun_st.
apply E_Seq with ([i32 0], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)] ,glob_st, fun_st).
apply E_i32_const.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)],glob_st, fun_st).
apply E_local_set. auto.
apply E_Seq with ([i32 n], [(IN, i32 n) ;(inv, i32 0); (temp, i32 0)],glob_st, fun_st).
apply E_local_get.
apply E_Seq with ([], [(IN, i32 n) ;(inv, i32 0); (temp, i32 n)],glob_st, fun_st).
apply E_local_set. auto.
induction n.
- apply E_Seq with ([] , [(IN, i32 0) ;(inv, i32 (invers 0)); (temp, i32 0)],glob_st, fun_st).
-- apply E_LoopOnce. apply loop_invariant.
-- apply E_local_get.
- apply E_Seq with ([] , [(IN, i32 (Z.pos p)) ;(inv, i32 (invers (Z.pos p))); (temp, i32 (Z.pos p / 10))],glob_st, fun_st).
-- induction p.
+ rewrite Pos2Z.pos_xI.


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