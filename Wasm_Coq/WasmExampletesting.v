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
Definition var_a := "a".
Definition var_b := "b".
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
---------- apply E_SeqLoop1.
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

Close Scope Z.