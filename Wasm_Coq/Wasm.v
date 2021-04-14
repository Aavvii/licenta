(*
Require Import String.
Require Import List.
Require Import Bool.
Import ListNotations.
*)

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

From LF Require Import Maps.

(*Definition Var := string.*)

(* pentru inceput o sa definesc doar pentru integer *)

Inductive WasmType :=
 | i32 : Z -> WasmType
 | i64 : Z -> WasmType
 | None.

Definition ExecutionStack := list WasmType.
Definition VariableTuple  := (string * WasmType)%type.
Definition VariableStack  := (list VariableTuple)%type.
Definition Stacks         := (ExecutionStack * VariableStack)%type.

Definition get_variable_name (var : VariableTuple) : (string) :=
 match var with
 | (name, value) => name
 end.
Definition get_variable_value (var : VariableTuple) : (WasmType) :=
 match var with
 | (name, value) => value
 end.

Definition get_execution_stack (stacks : Stacks) : ExecutionStack :=
 match stacks with
 | (execution, variables) => execution
 end.
Definition get_variable_stack (stacks : Stacks) : VariableStack :=
 match stacks with
 | (execution, variables) => variables
 end.

(* Functia asta parea utila dar nu o folosesc pana la urma *)
Definition make_stack_tuple (execution_stack : ExecutionStack)
                            (variable_stack : VariableStack)
                            : (Stacks) :=
(execution_stack, variable_stack).

Definition get_execution_stack_head (execution_stack : ExecutionStack) : WasmType :=
match execution_stack with
| hd :: tl => hd
| [] => None
end.
Definition get_execution_stack_tail (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| hd :: tl => tl
| [] => []
end.

Definition remove_execution_stack_head (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
( get_execution_stack_tail execution_stack, variable_stack ).

(* pentru inceput o sa definesc doar pentru operatiile cele mai simple *)

Inductive exp : Type :=
| i32_const (n : Z)
| i64_const (n : Z)
| local_get (n : string )
| local_set (n : string )
| i32_add
| i64_add
| i32_mul
| i64_mul
| i32_div_s
| i64_div_s
| i32_rem_s
| i64_rem_s
| i32_eq
| i64_eq
| i32_ge_s
| i64_ge_s.

(* i32 CONST *)
Definition execute_i32_const (n : Z) (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
( (i32 n) :: execution_stack, variable_stack ).

(* i64 CONST *)
Definition execute_i64_const (n : Z) (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
( (i64 n) :: execution_stack, variable_stack ).

(* LOCAL.GET *)
Fixpoint execute_local_get' (variable : string)
                            (variable_stack : VariableStack)
                            : WasmType :=
match variable_stack with
| hd :: tl => if string_dec (get_variable_name hd) variable
              then get_variable_value hd
              else execute_local_get' variable tl
| [] => None
end.
Definition execute_local_get (variable : string) (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
((( execute_local_get' variable variable_stack ) :: execution_stack), variable_stack ).


(* LOCAL.SET *)
Fixpoint execute_local_set' (variable_name  : string)
                            (variable_new_value : WasmType)
                            (variable_stack : VariableStack)
                            : VariableStack :=
match variable_stack with
| hd :: tl => if string_dec (get_variable_name hd) variable_name
              then (variable_name, variable_new_value) :: tl
              else hd :: (execute_local_set' variable_name variable_new_value tl)
| [] => []
end.
Definition execute_local_set (variable : string) (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(get_execution_stack_tail execution_stack,
 execute_local_set' variable (get_execution_stack_head execution_stack) variable_stack ).


(* i32 PLUS *)
Open Scope Z.
Definition execute_i32_add' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (hd1 + hd2) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_add (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i32_add' execution_stack, variable_stack ).

(* i64 PLUS *)
Open Scope Z.
Definition execute_i64_add' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (hd1 + hd2) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_add (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i64_add' execution_stack, variable_stack ).

(* i32 MUL *)
Open Scope Z.
Definition execute_i32_mul' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (hd1 * hd2) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_mul (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i32_mul' execution_stack, variable_stack ).

(* i64 MUL *)
Open Scope Z.
Definition execute_i64_mul' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (hd1 * hd2) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_mul (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i64_mul' execution_stack, variable_stack ).

(* i32 DIV_S *)
Open Scope Z.
Definition execute_i32_div_s' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.div hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_div_s (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i32_div_s' execution_stack, variable_stack ).

(* i64 DIV_S *)
Open Scope Z.
Definition execute_i64_div_s' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.div hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_div_s (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i64_div_s' execution_stack, variable_stack ).

(* i32 REM_S *)
Open Scope Z.
Definition execute_i32_rem_s' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.modulo hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_rem_s (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i32_rem_s' execution_stack, variable_stack ).

(* i32 REM_S *)
Open Scope Z.
Definition execute_i64_rem_s' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.modulo hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_rem_s (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i64_rem_s' execution_stack, variable_stack ).

(* i32 EQ *)
Open Scope Z.
Definition execute_i32_eq' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (if hd1 =? hd2 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_eq (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i32_eq' execution_stack, variable_stack ).

(* i64 EQ *)
Open Scope Z.
Definition execute_i64_eq' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i64 hd1 :: i64 hd2 :: tl => i32 (if hd1 =? hd2 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_eq (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i64_eq' execution_stack, variable_stack ).

(* i32 GE_S *)
Open Scope Z.
Definition execute_i32_ge_s' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (if hd2 >=? hd1 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_ge_s (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i32_ge_s' execution_stack, variable_stack ).

(* i64 GE_S *)
Open Scope Z.
Definition execute_i64_ge_s' (execution_stack : ExecutionStack) : ExecutionStack :=
match execution_stack with
| i64 hd1 :: i64 hd2 :: tl => i32 (if hd2 >=? hd1 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_ge_s (stacks : Stacks) : Stacks :=
let execution_stack := get_execution_stack stacks in
let variable_stack := get_variable_stack stacks in
(execute_i64_ge_s' execution_stack, variable_stack ).

Definition execute_intruction (instrunction : exp)
                            (stacks : Stacks)
                            : (Stacks):=
match instrunction with
| i32_const n => execute_i32_const n stacks
| i64_const n => execute_i64_const n stacks
| local_get n => execute_local_get n stacks
| local_set n => execute_local_set n stacks
| i32_add     => execute_i32_add stacks
| i64_add     => execute_i64_add stacks
| i32_mul     => execute_i32_mul stacks
| i64_mul     => execute_i64_mul stacks
| i32_div_s   => execute_i32_div_s stacks
| i64_div_s   => execute_i64_div_s stacks
| i32_rem_s   => execute_i32_rem_s stacks
| i64_rem_s   => execute_i64_rem_s stacks
| i32_eq      => execute_i32_eq stacks
| i64_eq      => execute_i64_eq stacks
| i32_ge_s    => execute_i32_ge_s stacks
| i64_ge_s    => execute_i64_ge_s stacks
end.

Definition Stacks2Bool' (x : WasmType) : Z :=
match x with
| i32 val => val
| _ => 0
end.

Open Scope Z.
Definition Stacks2Bool (stacks : Stacks)
                            : (bool) :=
let execution_stack := get_execution_stack stacks in
let stack_head_Z_val := Stacks2Bool' (get_execution_stack_head execution_stack) in
(if (stack_head_Z_val =? ( Z.of_N 0)) then false else true).
Close Scope Z.

Fixpoint execute_instructions (intructions : list exp)
                            (stacks : Stacks)
                            : (Stacks):=
match intructions with
| hd :: tl => execute_instructions tl ( execute_intruction hd stacks )
| [] => stacks
end.

Inductive com : Type :=
  | CSkip
  | CSeq (c1 c2 : com)
  | CBr_If (label : string)
  | CIf (c : com)
  | CLoop (c : com)
  | Ci32_const (x : Z)
  | Ci64_const (x : Z)
  | Clocal_set (x : string)
  | Clocal_get (x : string)
  | Ci32_add
  | Ci64_add
  | Ci32_mul
  | Ci64_mul
  | Ci32_div_s
  | Ci64_div_s
  | Ci32_rem_s
  | Ci64_rem_s
  | Ci32_eq
  | Ci64_eq
  | Ci32_ge_s
  | Ci64_ge_s.

Inductive result : Type :=
  | SContinue
  | SBr.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Notation "'true'" := true (at level 1).
Notation "'true'" := 1 (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := 0 (in custom com at level 0).

Open Scope com_scope.

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (Ci32_const x)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation " x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'end'" :=
         (CIf x)
           (in custom com at level 89 (*, x at level 99,
            y at level 99, z at level 99*)) : com_scope.
Notation "'loop' x 'end'" :=
         (CLoop x)
            (in custom com at level 89, x at level 99 (*, y at level 99*)) : com_scope.


(* Te gandeai ca probabil instructiunile definite mai sus ca Fixpoints ar trebui transormate in relatii
Nu ar trebui sa fie greu fiindca le creezi si apoi apelezi functiile care se ocupa cu asta.
Ai mai facut asta deja un alt .v ;
Aici trebuie sa fie comenzi. Daca CAss e o comanda, in cazul tau, si add ar trebui sa fie o comanda.*)

(*Locate ";".*)

(* urma sa implementez adunarea si restul opeartiilor ca si comenzi *)

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).
Inductive ceval : com -> Stacks -> result -> Stacks -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st / SContinue
  | E_Seq : forall c1 c2 st st' st'' res,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / res ->
      st =[ c1 ; c2 ]=> st'' / res
  | E_SeqBr : forall c1 c2 st st' (*st''*),
      st =[ c1 ]=> st' / SBr ->
      (*st' =[ c2 ]=> st'' / res2 ->*)
      st =[ c1 ; c2 ]=> st' / SBr
  (* Am comentat asta fiindca am inclus-o in E_Seq
  | E_SeqLoop2 : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / SLoop ->
      st =[ c1 ; c2 ]=> st'' / SLoop *)
  | E_IfTrue : forall st st' c,
      Stacks2Bool st = true ->
      (remove_execution_stack_head st) =[ c ]=> st' / SContinue ->
      st =[ CIf c ]=> st' / SContinue (* st  =[ if c end ]=> remove_execution_stack_head st' *)
  | E_IfFalse : forall st st' c,
      Stacks2Bool st = false ->
      (remove_execution_stack_head st) = st' ->
      st =[ CIf c ]=> st' / SContinue (* st  =[ if c end ]=> remove_execution_stack_head st *)
  (* loop nu are cum sa fie fals fiindca nu verific nimic
  | E_WhileFalse : forall st st' c,
      Stacks2Bool st = false ->
      (remove_execution_stack_head st) = st' ->
      st =[ loop c end ]=> st' (* st  =[ while c end ]=> remove_execution_stack_head st *)*)
  | E_LoopOnce : forall st st' (*st''*) c,
      st =[ c ]=> st' / SContinue ->
      (*st' =[ CLoop c ]=> st'' / SContinue -> (* st' =[ while c end ]=> st'' *) *)
      st =[ CLoop c ]=> st' / SContinue     (* st  =[ while c end ]=> st'' *)
  | E_Loop : forall st st' st'' c,
      st =[ c ]=> st' / SBr ->
      st' =[ CLoop c ]=> st'' / SContinue -> (* st' =[ while c end ]=> st'' *)
      st =[ CLoop c ]=> st'' / SContinue     (* st  =[ while c end ]=> st'' *)
  | E_Br_IfTrue : forall st st' label,
      Stacks2Bool st = true ->
      (remove_execution_stack_head st) = st' ->
      st =[ CBr_If label ]=> st' / SBr
  | E_Br_IfFalse : forall st st' label,
      Stacks2Bool st = false ->
      (remove_execution_stack_head st) = st' ->
      st =[ CBr_If label ]=> st' / SContinue
  | E_local_set : forall st variable,
      (* Aici as putea sa pun conditia ca tipul variabilei sa fie acelasi cu tipul valorii de pe stiva*)
      st =[ Clocal_set variable ]=> (execute_intruction (local_set variable) st ) / SContinue
  | E_local_get : forall st variable,
      st =[ Clocal_get variable ]=> (execute_intruction (local_get variable) st ) / SContinue
  | E_i32_const : forall st variable,
      st =[ Ci32_const variable ]=> (execute_intruction (i32_const variable) st ) / SContinue
  | E_i64_const : forall st variable,
      st =[ Ci64_const variable ]=> (execute_intruction (i64_const variable) st ) / SContinue  
  | E_i32_add : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i32 *)
      st =[ Ci32_add ]=> (execute_intruction (i32_add) st ) / SContinue
  | E_i64_add : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i64 *)
      st =[ Ci64_add ]=> (execute_intruction (i64_add) st ) / SContinue
  | E_i32_mul : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i32 *)
      st =[ Ci32_mul ]=> (execute_intruction (i32_mul) st ) / SContinue
  | E_i64_mul : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i64 *)
      st =[ Ci64_mul ]=> (execute_intruction (i64_mul) st ) / SContinue
  | E_i32_div_s : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i32 *)
      st =[ Ci32_div_s ]=> (execute_intruction (i32_div_s) st ) / SContinue
  | E_i64_div_s : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i64 *)
      st =[ Ci64_div_s ]=> (execute_intruction (i64_div_s) st ) / SContinue
  | E_i32_rem_s : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i32 *)
      st =[ Ci32_rem_s ]=> (execute_intruction (i32_rem_s) st ) / SContinue
  | E_i64_rem_s : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i64 *)
      st =[ Ci64_rem_s ]=> (execute_intruction (i64_rem_s) st ) / SContinue
  | E_i32_eq : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i32 *)
      st =[ Ci32_eq ]=> (execute_intruction (i32_eq) st ) / SContinue
  | E_i64_eq : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i64 *)
      st =[ Ci64_eq ]=> (execute_intruction (i64_eq) st ) / SContinue
  | E_i32_ge_s : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i32 *)
      st =[ Ci32_ge_s ]=> (execute_intruction (i32_ge_s) st ) / SContinue
  | E_i64_ge_s : forall st,
      (* aici as putea sa pun conditia ca tipurile de date sa fie ambele i32 *)
      st =[ Ci64_ge_s ]=> (execute_intruction (i64_ge_s) st ) / SContinue
where "st =[ c ]=> st' / s " := (ceval c st s st').

(* ----------- Functioneaza const, add, get, set, if, while, br. If NU are else -------- *)

(* ----------- Urmeaza implementarea si testarea a noi instructiuni -------------------- *)

Definition var1 : string := "Var1".
Definition var_a : string := "a".
Definition var_b : string := "b".
Open Scope Z.

(* test here *)

Close Scope Z.
