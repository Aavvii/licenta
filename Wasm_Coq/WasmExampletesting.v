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
Import N2Z.
Import ListNotations.
(*Open Scope R_scope.*)

From LF Require Import Maps Wasm.

(* -------------------- !!! testing only for integers !!! ----------------- *)

(*------------------------- Testing execute functions ----------------------------*)
Open Scope string_scope.
Definition var_a : string := "a".
Definition var_b : string := "b".
Definition var1 : string := "Var1".

Definition execution_stack_example1 := [i32 3; i32 5].
Definition variable_stack_example1 := [(var_a, i32 2);(var_b, i32 7)].
Definition stacks_example_1 := make_stack_tuple execution_stack_example1 variable_stack_example1.

Eval compute in stacks_example_1.
Eval compute in execute_i32_const (5) stacks_example_1.

Eval compute in execute_local_set "a" stacks_example_1.

Eval compute in execute_local_get "a" stacks_example_1.
Eval compute in execute_i32_add stacks_example_1.
Eval compute in execute_i64_add stacks_example_1.

Eval compute in execute_i32_eq stacks_example_1.

Definition execution_stack_example2 := [i64 5; i64 4].
Definition variable_stack_example2 := [("b", i32 2);("a", i32 7)].
Definition stacks_example_2 := make_stack_tuple execution_stack_example2 variable_stack_example2.

Eval compute in stacks_example_2.
Eval compute in execute_i64_add stacks_example_2.

Close Scope string_scope.
(* Finished testing execute functions*)


(* ---------------------------- Testing execute_instructions ------------------------- *)
Open Scope string_scope.
Eval compute in execute_intruction (i32_const (5)) stacks_example_1.

Definition empty_stacks := make_stack_tuple [] [].

Eval compute in execute_instructions [
i32_const (5);
i32_const (6);
i32_add;
i32_const (11);
i32_eq
] empty_stacks.

Definition stacks_with_a_b_var :=
make_stack_tuple [] [("a", i32 0); ("b", (i32 0))].

Eval compute in execute_instructions [
i32_const (5);
i32_const (6);
i32_add;
local_set "a";
i32_const (7);
i32_const (4);
i32_add;
local_get "a";
i32_eq
] stacks_with_a_b_var. (*omg chiar merge*)

Close Scope string_scope.

(* Finisted testing execute_instructions *)

(* ---------------------------- Testing inference rules ------------------------------- *)

Open Scope Z.
(* Versiune cu com-uri pentru:
i32_const (i32 5);
i32_const (i32 6);
i32_add;
local_set "a";
i32_const (i32 7);
i32_const (i32 4);
i32_add;
local_get "a";
i32_eq
*)

Definition attempt1 : com := <{
 Ci32_const 5 ;
 Ci32_const 6 ;
 Ci32_add ;
 Clocal_set var1 ;
 Ci32_const 7 ;
 Ci32_const 4 ;
 Ci32_add ;
 Clocal_get var1 ;
 Ci32_eq ;
 if
    Ci32_const 5
 end
}>.
Close Scope Z.

Eval compute in ceval attempt1.

Open Scope Z.

(* --- Testing 'const', 'add', 'get', 'set' instructions with no flow control --- *)

Example example_no_if_no_while:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 Ci32_const 5 ;
 Ci32_const 6 ;
 Ci32_add ;
 Clocal_set var_a ;
 Ci32_const 7 ;
 Ci32_const 4 ;
 Ci32_add ;
 Clocal_get var_a ;
 Ci32_eq
]=> ([i32 1] , [(var_a, i32 11); (var_b, i32 0)]) / SContinue.
Proof.
  apply E_Seq with ([i32 5] , [(var_a, i32 0); (var_b, i32 0)]).
  - apply E_i32_const.
  - apply E_Seq with (([i32 6; i32 5]) , [(var_a, i32 0); (var_b, i32 0)]).
    -- apply E_i32_const.
    -- apply E_Seq with (([i32 11]) , [(var_a, i32 0); (var_b, i32 0)]).
      --- apply E_i32_add.
      --- apply E_Seq with ([] , [(var_a, i32 11); (var_b, i32 0)]).
        ---- apply E_local_set.
        ---- apply E_Seq with ([i32 7] , [(var_a, i32 11); (var_b, i32 0)]).
             ----- apply E_i32_const.
             ----- apply E_Seq with ([i32 4; i32 7] , [(var_a, i32 11); (var_b, i32 0)]).
                   ------ apply E_i32_const.
                   ------ apply E_Seq with ([i32 11] , [(var_a, i32 11); (var_b, i32 0)]).
                          ------- apply E_i32_add.
                          ------- apply E_Seq with ([i32 11; i32 11] , [(var_a, i32 11); (var_b, i32 0)]).
                                  -------- apply E_local_get.
                                  --------  apply E_i32_eq.
Qed.

Example example_if_true:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 Ci32_const 1 ;
 CIf (Ci32_const 6) ;
 Ci32_const 2
]=> ([i32 2;i32 6] , [(var_a, i32 0); (var_b, i32 0)]) / SContinue.
Proof.
  apply E_Seq with ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
  - apply E_i32_const.
  - apply E_Seq with ([i32 6] , [(var_a, i32 0); (var_b, i32 0)]).
    + apply E_IfTrue.
      ++ reflexivity.
      ++ apply E_i32_const.
    + apply E_i32_const.
Qed.

Example example_if_false:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 Ci32_const 0 ;
 CIf (Ci32_const 6) ;
 Ci32_const 2
]=> ([i32 2] , [(var_a, i32 0); (var_b, i32 0)]) / SContinue.
Proof.
  apply E_Seq with ([i32 0] , [(var_a, i32 0); (var_b, i32 0)]).
  - apply E_i32_const.
  - apply E_Seq with ([] , [(var_a, i32 0); (var_b, i32 0)]).
    + apply E_IfFalse.
      ++ reflexivity.
      ++ reflexivity.
    + apply E_i32_const.
Qed.

(* Nu are sens fiindca while nu are conditie de intrare
Example example_while_false:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 Ci32_const 0 ;
 loop
   Ci32_const 6;
   Ci32_const 3
 end
]=> ([] , [(var_a, i32 0); (var_b, i32 0)]).
Proof.
  apply E_Seq with ([i32 0] , [(var_a, i32 0); (var_b, i32 0)]).
  - apply E_i32_const.
  - apply E_WhileFalse.
    + reflexivity.
    + reflexivity.
Qed.
*)

Example example_loop_once:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 Ci32_const 1 ;
 loop
   Ci32_const 2
 end
]=> ([i32 2; i32 1] , [(var_a, i32 0); (var_b, i32 0)]) / SContinue.
Proof.
  apply E_Seq with ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
  - apply E_i32_const.
  - apply E_LoopOnce.
    + apply E_i32_const.
Qed.

Definition label1 : string := "L1".
Example example_loop_forever:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 Ci32_const 1 ;
 loop
   Ci32_const 1;
   CBr_If label1
 end
]=> ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]) / SContinue.
Proof.
  apply E_Seq with ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
  - apply E_i32_const.
  - apply E_Loop with ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
    + apply E_Seq with ([i32 1; i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
      ++ apply E_i32_const.
      ++ apply E_Br_IfTrue.
            * reflexivity.
            * reflexivity.
    + apply E_Loop with ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
      ++ apply E_Seq with ([i32 1; i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
        +++ apply E_i32_const.
        +++ apply E_Br_IfTrue.
            * reflexivity.
            * reflexivity.
      ++ Admitted. (* Ruleaza la infinit asa cum trebuie *)

Example example_loop_test_2_times:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 loop
   Clocal_get var_a;
   Ci32_const 1;
   Ci32_add;
   Clocal_set var_a;
   Clocal_get var_a;
   Ci32_const 1;
   Ci32_eq;
   CBr_If label1
 end;
 Clocal_get var_a
]=> ([i32 2] , [(var_a, i32 2); (var_b, i32 0)]) / SContinue.
Proof.
apply E_Seq with ([] , [(var_a, i32 2); (var_b, i32 0)]).
- apply E_Loop with ([] , [(var_a, i32 1); (var_b, i32 0)]).
-- apply E_Seq with ([i32 0] , [(var_a, i32 0); (var_b, i32 0)]).
--- apply E_local_get.
--- apply E_Seq with ([i32 1 ;i32 0] , [(var_a, i32 0); (var_b, i32 0)]).
---- apply E_i32_const.
---- apply E_Seq with ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
----- apply E_i32_add.
----- apply E_Seq with ([] , [(var_a, i32 1); (var_b, i32 0)]).
------ apply E_local_set.
------ apply E_Seq with ([i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
------- apply E_local_get.
------- apply E_Seq with ([i32 1;i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
-------- apply E_i32_const.
-------- apply E_Seq with ([i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
---------- apply E_i32_eq.
---------- apply E_Br_IfTrue.
----------- reflexivity.
----------- reflexivity.
-- apply E_LoopOnce.
--- apply E_Seq with ([i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
---- apply E_local_get.
---- apply E_Seq with ([i32 1 ;i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
----- apply E_i32_const.
----- apply E_Seq with ([i32 2] , [(var_a, i32 1); (var_b, i32 0)]).
------ apply E_i32_add.
------ apply E_Seq with ([] , [(var_a, i32 2); (var_b, i32 0)]).
------- apply E_local_set.
------- apply E_Seq with ([i32 2] , [(var_a, i32 2); (var_b, i32 0)]).
-------- apply E_local_get.
-------- apply E_Seq with ([i32 1;i32 2] , [(var_a, i32 2); (var_b, i32 0)]).
--------- apply E_i32_const.
--------- apply E_Seq with ([i32 0] , [(var_a, i32 2); (var_b, i32 0)]).
----------- apply E_i32_eq.
----------- apply E_Br_IfFalse.
------------ reflexivity.
------------ reflexivity.
- apply E_local_get.
Qed.

Example example_loop_test_2_times_and_ignore_lines:
([], [(var_a, i32 0); (var_b, (i32 0))]) =[
 loop
   Clocal_get var_a;
   Ci32_const 1;
   Ci32_add;
   Clocal_set var_a;
   Clocal_get var_a;
   Ci32_const 1;
   Ci32_eq;
   CBr_If label1;
   Ci32_const 42;
   Clocal_get var_a;
   Ci32_add;
   Clocal_set var_a
 end;
 Clocal_get var_a
]=> ([i32 44] , [(var_a, i32 44); (var_b, i32 0)]) / SContinue.
Proof.
apply E_Seq with ([] , [(var_a, i32 44); (var_b, i32 0)]).
- apply E_Loop with ([] , [(var_a, i32 1); (var_b, i32 0)]).
-- apply E_Seq with ([i32 0] , [(var_a, i32 0); (var_b, i32 0)]).
--- apply E_local_get.
--- apply E_Seq with ([i32 1 ;i32 0] , [(var_a, i32 0); (var_b, i32 0)]).
---- apply E_i32_const.
---- apply E_Seq with ([i32 1] , [(var_a, i32 0); (var_b, i32 0)]).
----- apply E_i32_add.
----- apply E_Seq with ([] , [(var_a, i32 1); (var_b, i32 0)]).
------ apply E_local_set.
------ apply E_Seq with ([i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
------- apply E_local_get.
------- apply E_Seq with ([i32 1;i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
-------- apply E_i32_const.
-------- apply E_Seq with ([i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
---------- apply E_i32_eq.
---------- apply E_SeqBr.
----------- apply E_Br_IfTrue.
------------ reflexivity.
------------ reflexivity.
-- apply E_LoopOnce.
--- apply E_Seq with ([i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
---- apply E_local_get.
---- apply E_Seq with ([i32 1 ;i32 1] , [(var_a, i32 1); (var_b, i32 0)]).
----- apply E_i32_const.
----- apply E_Seq with ([i32 2] , [(var_a, i32 1); (var_b, i32 0)]).
------ apply E_i32_add.
------ apply E_Seq with ([] , [(var_a, i32 2); (var_b, i32 0)]).
------- apply E_local_set.
------- apply E_Seq with ([i32 2] , [(var_a, i32 2); (var_b, i32 0)]).
-------- apply E_local_get.
-------- apply E_Seq with ([i32 1;i32 2] , [(var_a, i32 2); (var_b, i32 0)]).
--------- apply E_i32_const.
--------- apply E_Seq with ([i32 0] , [(var_a, i32 2); (var_b, i32 0)]).
----------- apply E_i32_eq.
----------- apply E_Seq with ([] , [(var_a, i32 2); (var_b, i32 0)]).
------------ apply E_Br_IfFalse.
------------- reflexivity.
------------- reflexivity.
------------ apply E_Seq with ([i32 42] , [(var_a, i32 2); (var_b, i32 0)]).
------------- apply E_i32_const.
------------- apply E_Seq with ([i32 2; i32 42] , [(var_a, i32 2); (var_b, i32 0)]).
-------------- apply E_local_get.
-------------- apply E_Seq with ([i32 44] , [(var_a, i32 2); (var_b, i32 0)]).
--------------- apply E_i32_add.
--------------- apply E_local_set.
- apply E_local_get.
Qed.

Example example_i32_ge_S:
([], []) =[
 Ci32_const 2 ;
 Ci32_const 1 ;
 Ci32_ge_s
]=> ([i32 1] , []) / SContinue.
Proof.
  apply E_Seq with ([i32 2] , []).
  - apply E_i32_const.
  - apply E_Seq with ([i32 1; i32 2] , []).
  -- apply E_i32_const.
  -- apply E_i32_ge_s.
Qed.

Example example_i64_ge_S:
([], []) =[
 Ci64_const 1 ;
 Ci64_const 2 ;
 Ci64_ge_s
]=> ([i32 0] , []) / SContinue.
Proof.
  apply E_Seq with ([i64 1] , []).
  - apply E_i64_const.
  - apply E_Seq with ([i64 2; i64 1] , []).
  -- apply E_i64_const.
  -- apply E_i64_ge_s.
Qed.

Example example_i32_rem_s:
([], []) =[
 Ci32_const 8 ;
 Ci32_const 3 ;
 Ci32_rem_s
]=> ([i32 2] , []) / SContinue.
Proof.
  apply E_Seq with ([i32 8] , []).
  - apply E_i32_const.
  - apply E_Seq with ([i32 3; i32 8] , []).
  -- apply E_i32_const.
  -- apply E_i32_rem_s.
Qed.

Example example_i64_rem_s:
([], []) =[
 Ci64_const 8 ;
 Ci64_const 3 ;
 Ci64_rem_s
]=> ([i64 2] , []) / SContinue.
Proof.
  apply E_Seq with ([i64 8] , []).
  - apply E_i64_const.
  - apply E_Seq with ([i64 3; i64 8] , []).
  -- apply E_i64_const.
  -- apply E_i64_rem_s.
Qed.

Example example_i32_div_s:
([], []) =[
 Ci32_const 8 ;
 Ci32_const 3 ;
 Ci32_div_s
]=> ([i32 2] , []) / SContinue.
Proof.
  apply E_Seq with ([i32 8] , []).
  - apply E_i32_const.
  - apply E_Seq with ([i32 3; i32 8] , []).
  -- apply E_i32_const.
  -- apply E_i32_div_s.
Qed.

Example example_i64_div_s:
([], []) =[
 Ci64_const 10 ;
 Ci64_const 3 ;
 Ci64_div_s
]=> ([i64 3] , []) / SContinue.
Proof.
  apply E_Seq with ([i64 10] , []).
  - apply E_i64_const.
  - apply E_Seq with ([i64 3; i64 10] , []).
  -- apply E_i64_const.
  -- apply E_i64_div_s.
Qed.

Example example_i32_mul:
([], []) =[
 Ci32_const 8 ;
 Ci32_const 3 ;
 Ci32_mul
]=> ([i32 24] , []) / SContinue.
Proof.
  apply E_Seq with ([i32 8] , []).
  - apply E_i32_const.
  - apply E_Seq with ([i32 3; i32 8] , []).
  -- apply E_i32_const.
  -- apply E_i32_mul.
Qed.

Example example_i64_mul:
([], []) =[
 Ci64_const 10 ;
 Ci64_const 3 ;
 Ci64_mul
]=> ([i64 30] , []) / SContinue.
Proof.
  apply E_Seq with ([i64 10] , []).
  - apply E_i64_const.
  - apply E_Seq with ([i64 3; i64 10] , []).
  -- apply E_i64_const.
  -- apply E_i64_mul.
Qed.

Definition inv : string := "inv".
Definition temp : string := "temp".
Definition IN : string := "IN".

Example example_calculeaza_invers:
([], [(IN, i32 123) ;(inv, i32 0); (temp, i32 0)]) =[
Ci32_const 0 ;
Clocal_set inv ;
Clocal_get IN ;
Ci32_const 1 ;
Ci32_ge_s ;
if
 Clocal_get IN ;
 Clocal_set temp ;
 loop
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
 end
end ;
Clocal_get inv
]=> ([i32 321] , [(IN, i32 0) ;(inv, i32 321); (temp, i32 0)]) / SContinue.
Proof.
apply E_Seq with ([i32 0], [(IN, i32 123) ;(inv, i32 0); (temp, i32 0)]).
- apply E_i32_const.
- apply E_Seq with ([], [(IN, i32 123) ;(inv, i32 0); (temp, i32 0)]).
-- apply E_local_set.
-- apply E_Seq with ([i32 123], [(IN, i32 123) ;(inv, i32 0); (temp, i32 0)]).
--- apply E_local_get.
--- apply E_Seq with ([i32 1; i32 123], [(IN, i32 123) ;(inv, i32 0); (temp, i32 0)]).
---- apply E_i32_const.
---- apply E_Seq with ([i32 1], [(IN, i32 123) ;(inv, i32 0); (temp, i32 0)]).
----- apply E_i32_ge_s.
----- apply E_Seq with ([] , [(IN, i32 0) ;(inv, i32 321); (temp, i32 0)]).
------ apply E_IfTrue.
------- reflexivity.
------- apply E_Seq with ([i32 123], [(IN, i32 123) ;(inv, i32 0); (temp, i32 0)]).
-------- apply E_local_get.
-------- apply E_Seq with ([], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
--------- apply E_local_set.
--------- apply E_Loop with ([], [(IN, i32 123) ;(inv, i32 3); (temp, i32 12)]).
---------- apply E_Seq with ([i32 0], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
----------- apply E_local_get.
----------- apply E_Seq with ([i32 10 ;i32 0], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
------------ apply E_i32_const.
------------ apply E_Seq with ([i32 0], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
------------- apply E_i32_mul.
------------- apply E_Seq with ([i32 123; i32 0], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
-------------- apply E_local_get.
-------------- apply E_Seq with ([i32 10 ;i32 123; i32 0], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
--------------- apply E_i32_const.
--------------- apply E_Seq with ([i32 3; i32 0], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
---------------- apply E_i32_rem_s.
---------------- apply E_Seq with ([i32 3], [(IN, i32 123) ;(inv, i32 0); (temp, i32 123)]).
----------------- apply E_i32_add.
----------------- apply E_Seq with ([], [(IN, i32 123) ;(inv, i32 3); (temp, i32 123)]).
------------------ apply E_local_set.
------------------ apply E_Seq with ([i32 123], [(IN, i32 123) ;(inv, i32 3); (temp, i32 123)]).
------------------- apply E_local_get.
------------------- apply E_Seq with ([i32 10; i32 123], [(IN, i32 123) ;(inv, i32 3); (temp, i32 123)]).
-------------------- apply E_i32_const.
-------------------- apply E_Seq with ([i32 12], [(IN, i32 123) ;(inv, i32 3); (temp, i32 123)]).
--------------------- apply E_i32_div_s.
--------------------- apply E_Seq with ([], [(IN, i32 123) ;(inv, i32 3); (temp, i32 12)]).
---------------------- apply E_local_set.
---------------------- apply E_Seq with ([i32 12], [(IN, i32 123) ;(inv, i32 3); (temp, i32 12)]).
----------------------- apply E_local_get.
----------------------- 


Close Scope Z.



















