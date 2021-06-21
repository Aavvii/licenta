Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.Znat.
From Coq Require Import ZArith.BinInt.
Import N2Z.
Import ListNotations.

(*From LF Require Import Maps.*)

(** Definirea tipurilor de date din Wasm *)
Inductive WasmType :=
 | i32 : Z -> WasmType
 | i64 : Z -> WasmType
 | None.

(** Definirea intructiunilor ce vor fi rulate in mod direct in Coq *)
Inductive exp : Type :=
| local_decl (name : string) (type : string)
| memory_decl (min max : Z)
| i32_load8_u
| i32_load8_u_offset (offset : Z)
| i32_load
| i32_const (n : Z)
| i64_const (n : Z)
| local_get (n : string )
| local_set (n : string )
| local_tee (n : string )
| i32_add
| i64_add
| i32_sub
| i64_sub
| i32_mul
| i64_mul
| i32_div_s
| i64_div_s
| i32_rem_s
| i64_rem_s
| i32_and
| i64_and
| i32_xor
| i64_xor
| i32_eq
| i64_eq
| i32_eqz
| i64_eqz
| i32_ge_s
| i64_ge_s
.

(** Definirea unui tip aditional de date, util apelurilor de functii *)
Inductive WasmDecl :=
 | param : (list string) -> WasmDecl
 | result   : (string) -> WasmDecl
.

(** Definirea instructiunilor pe care se vor putea aplica regulile de inferenta *)
Inductive com : Type :=
  | CNop
  | CSeq (c1 c2 : com)
  | Ci32_const (x : Z)
  | Ci64_const (x : Z)
  | Clocal_set (x : string)
  | Clocal_get (x : string)
  | Clocal_tee (x : string)
  | Ci32_add
  | Ci64_add
  | Ci32_sub
  | Ci64_sub
  | Ci32_mul
  | Ci64_mul
  | Ci32_div_s
  | Ci64_div_s
  | Ci32_rem_s
  | Ci64_rem_s
  | Ci32_and
  | Ci64_and
  | Ci32_xor
  | Ci64_xor
  | Ci32_eq
  | Ci64_eq
  | Ci32_eqz
  | Ci64_eqz
  | Ci32_ge_s
  | Ci64_ge_s
  | CFunc (name : string) (param : WasmDecl) (result : WasmDecl) (c : com)
  | CReturn
  | CCall (name : string)
  | CMemory (min max : Z)
  | Ci32_Load8_u
  | Ci32_Load8_u_offset (offset : Z)
  | Ci32_Load
  | CLocal (name : string) (type : string)
  | CBr_If (label : string)
  | CIf (label : string) (c : com)
  | CLoop (label : string) (c : com)
  | CBlock (label : string) (c : com)
.

(* Un exemplu simplu ca structura de mai sus functioneaza *)
Eval compute in CLoop "a" (Ci32_const 5).

(** Tip de date cu scopul de a ajuta la implemenatarea instructiunilor:
  - return
  - br_if
  - loop
  - block *)
Inductive Branch : Type :=
  | SContinue
  | SBr (l : string)
  | SReturn.

(** Definirea starii programului *)
Definition ExecutionStack := list WasmType.
Definition VariableTuple  := (string * WasmType)%type.
Definition VariableList   := (list VariableTuple)%type.
Definition FunctionTuple  := (string * com)%type.
Definition FunctionList   := (list FunctionTuple)%type.
Definition MemoryByte     := (Z * Z)%type.
Definition MemoryList     := (list MemoryByte)%type.
Definition Memory         := (Z * (list MemoryByte))%type.
Definition State          :=
(ExecutionStack *
VariableList *
VariableList *
FunctionList *
Memory
)%type.


(** Functii ajutatoare *)

Definition get_variable_name (var : VariableTuple) : (string) :=
 match var with
 | (name, value) => name
 end.
Definition get_variable_value (var : VariableTuple) : (WasmType) :=
 match var with
 | (name, value) => value
 end.

Definition get_function_name (var : FunctionTuple) : (string) :=
 match var with
 | (name, content) => name
 end.
Definition get_function_content (var : FunctionTuple) : (com) :=
 match var with
 | (name, content) => content
 end.


Definition get_execution_stack (state : State) : ExecutionStack :=
 match state with
 | (execution, _ , _ , _ , _) => execution
 end.
Definition get_local_var_list (state : State) : VariableList :=
 match state with
 | (_ , local_var , _ , _, _) => local_var
 end.
Definition get_global_var_list (state : State) : VariableList :=
 match state with
 | (_ , _ , global_var , _, _) => global_var
 end.
Definition get_func_list (state : State) : FunctionList :=
 match state with
 | (_ , _ , _ , func, _) => func
 end.
Definition get_memory (state : State) : Memory :=
 match state with
 | ( _ , _ , _ , _ , mem ) => mem
 end.

Definition get_memory_size (mem : Memory) : Z :=
 match mem with
 | ( size , mem ) => size
 end.
Definition get_memory_list (mem : Memory) : list MemoryByte :=
 match mem with
 | ( size , mem ) => mem
 end.

Definition get_memory_index (mem : MemoryByte) : Z :=
 match mem with
 | ( index, byte ) => index
 end.
Definition get_memory_byte (mem : MemoryByte) : Z :=
 match mem with
 | ( index, byte ) => byte
 end.

(* Functia asta este utila dar nu necesara *)
Definition make_state (execution_stack : ExecutionStack)
                      (local_variable_list : VariableList)
                      (global_variable_list : VariableList)
                      (function_list : FunctionList)
                      (memory_list : Memory)
                            : (State) :=
(execution_stack, local_variable_list, global_variable_list, function_list, memory_list).

Definition get_execution_stack_head (exec_stack : ExecutionStack) : WasmType :=
match exec_stack with
| hd :: tl => hd
| [] => None
end.
Definition get_execution_stack_tail (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| hd :: tl => tl
| [] => []
end.
Definition get_execution_stack_2nd (exec_stack : ExecutionStack) : WasmType :=
match exec_stack with
| hd1 :: hd2 :: tl => hd2
| _ => None
end.

Definition remove_execution_stack_head (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
( get_execution_stack_tail exec_stack, loc_list, glob_list, func_list, memory_list).

Definition match_wasm_types (var1 : WasmType) (var2 : WasmType) : bool :=
match var1, var2 with
| i32 a, i32 b => true
| i64 a, i64 b => true
(*| f32 a, f32 b => true
| f64 a, f64 b => true*)
| _ , _ => false
end.

Definition match_types_last_2_on_stack (state : State) : bool :=
let exec_stack := get_execution_stack state in
match_wasm_types (get_execution_stack_head exec_stack) (get_execution_stack_2nd exec_stack).

Definition match_last_on_stack_with_type (state : State) (compare : WasmType) : bool :=
let exec_stack := get_execution_stack state in
match_wasm_types (get_execution_stack_head exec_stack) compare.

Fixpoint get_variable_from_stack (variable : string)
                                 (variable_list : VariableList)
                                 : WasmType :=
match variable_list with
| hd :: tl => if string_dec (get_variable_name hd) variable
              then get_variable_value hd
              else get_variable_from_stack variable tl
| [] => None
end.

Definition local_variable_exists (name : string) (state : State) : bool :=
let loc_list := get_local_var_list state in
match (get_variable_from_stack name loc_list) with
| None => false
| _    => true
end.

Definition zero_equality_all_types (var : WasmType) : bool :=
match var with
| i32 0 => true
| i64 0 => true
(*| f32 0 => true
| f64 0 => true*)
| _ => false
end.

Definition exec_stack_head_is_zero (state : State) : bool :=
let exec_stack := get_execution_stack state in
zero_equality_all_types (get_execution_stack_head exec_stack).

Open Scope string_scope. 
Definition string_is_type (str : string) :=
match str with
| "i32" => true
| "i64" => true
(* Lipsesc tipurile cu float *)
| _ => false
end.

Definition string2type (str : string) :=
match str with
| "i32" => i32
| "i64" => i64
(* Lipsesc tipurile cu float *)
| _ => i32
end.
Close Scope string_scope.

Definition loose_integer_type (n : WasmType) : Z :=
match n with
| i32 n' => n'
| i64 n' => n'
| _      => 0
end.

Open Scope Z.

Eval compute in ((-92) + (256)). 

Definition signed2unsigned (number : Z) (nr_bytes : Z) :=
if number <? 0 then
  match nr_bytes with
  | 1 => number + 256
  | 2 => number + 65536
  | 4 => number + 4294967296
  | 8 => number + 18446744073709551616
  | _ => 0
  end
else number.

Definition signBitIsOne (number : Z) (nr_bytes : Z) :=
if number <? 0 then true else
match nr_bytes with
  | 1 => if number >? 127 then true else false
  | 2 => if number >? 32767 then true else false
  | 4 => if number >? 2147483647 then true else false
  | 8 => if number >? 9223372036854775807 then true else false
  | _ => true
end.

Definition unsigned2signed (number : Z) (nr_bytes : Z) :=
if number >=? 0 then
  if signBitIsOne number nr_bytes then
    match nr_bytes with
    | 1 => number - 256
    | 2 => number - 65536
    | 4 => number - 4294967296
    | 8 => number - 18446744073709551616
    | _ => 0
    end
  else number
else number.

Fixpoint load_8_from_adress (index : Z) (memory_list : MemoryList) : Z :=
match memory_list with
| hd :: tl => if (get_memory_index hd) =? index
              then get_memory_byte hd
              else load_8_from_adress index tl
| [] => 0
end.
Close Scope Z.

(** Impelemntari ale functionalitatilor instructiunilor *)

(** i32.const *)
Definition execute_i32_const (n : Z) (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
( (i32 n) :: exec_stack, loc_list, glob_list, func_list, memory_list).

(** i64.const *)
Definition execute_i64_const (n : Z) (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
( (i64 n) :: exec_stack, loc_list, glob_list, func_list, memory_list).

(** local.get *)
Definition execute_local_get (variable : string) (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
((( get_variable_from_stack variable loc_list ) :: exec_stack), loc_list, glob_list, func_list, memory_list ).

(** local.set *)
Fixpoint execute_local_set' (variable_name  : string)
                            (variable_new_value : WasmType)
                            (variable_list : VariableList)
                            : VariableList :=
match variable_list with
| hd :: tl => if string_dec (get_variable_name hd) variable_name
              then (variable_name, variable_new_value) :: tl
              else hd :: (execute_local_set' variable_name variable_new_value tl)
| [] => []
end.
Definition execute_local_set (variable : string) (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(get_execution_stack_tail exec_stack,
 execute_local_set' variable (get_execution_stack_head exec_stack) loc_list,
glob_list,
func_list,
memory_list
).

Definition local_set_type_check  (state : State) (variable: string) : bool :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
match_wasm_types (get_execution_stack_head exec_stack) (get_variable_from_stack variable loc_list).


(** i32.add *)
Open Scope Z.
Definition execute_i32_add' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.modulo (hd2 + hd1) 4294967296) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_add (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_add' exec_stack, loc_list, glob_list, func_list , memory_list ).

(** i64.add *)
Open Scope Z.
Definition execute_i64_add' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.modulo (hd2 + hd1) 18446744073709551616) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_add (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_add' exec_stack, loc_list, glob_list, func_list, memory_list).

(** i32.sub *)
Open Scope Z.
Definition execute_i32_sub' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.modulo (hd2 - hd1 + 4294967296) 4294967296) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_sub (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_sub' exec_stack, loc_list, glob_list, func_list , memory_list ).


(** i64.sub *)
Open Scope Z.
Definition execute_i64_sub' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.modulo (hd2 - hd1 + 18446744073709551616) 18446744073709551616) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_sub (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_sub' exec_stack, loc_list, glob_list, func_list, memory_list).


(** i32.mul *)
Open Scope Z.
Definition execute_i32_mul' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.modulo (hd2 * hd1) 4294967296 ) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_mul (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_mul' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i64.mul *)
Open Scope Z.
Definition execute_i64_mul' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.modulo (hd2 * hd1) 18446744073709551616 ) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_mul (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_mul' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i32.div_s *)
Open Scope Z.
Definition execute_i32_div_s' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.div hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_div_s (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_div_s' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i64.div_s *)
Open Scope Z.
Definition execute_i64_div_s' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.div hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_div_s (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_div_s' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i32.rem_s*)
Open Scope Z.
Definition execute_i32_rem_s' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.modulo hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_rem_s (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_rem_s' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i32.rem_s *)
Open Scope Z.
Definition execute_i64_rem_s' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.modulo hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_rem_s (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_rem_s' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i32.and *)
Open Scope Z.
Definition execute_i32_and' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.land hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_and (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_and' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i64.and *)
Open Scope Z.
Definition execute_i64_and' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.land hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_and (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_and' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i32.xor *)

Open Scope Z.
Definition execute_i32_xor' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (Z.lxor hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_xor (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_xor' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i64.xor *)

Open Scope Z.
Definition execute_i64_xor' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i64 (Z.lxor hd2 hd1) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_xor (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_xor' exec_stack, loc_list, glob_list, func_list, memory_list ).


(** i32.eq *)
Open Scope Z.
Definition execute_i32_eq' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (if hd2 =? hd1 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_eq (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_eq' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i64.eq *)
Open Scope Z.
Definition execute_i64_eq' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i32 (if hd2 =? hd1 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_eq (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_eq' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i32.eqz *)
Open Scope Z.
Definition execute_i32_eqz' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd :: tl => i32 (if hd =? 0 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_eqz (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_eqz' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i64.eqz *)
Open Scope Z.
Definition execute_i64_eqz' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd :: tl => i64 (if hd =? 0 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_eqz (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_eqz' exec_stack, loc_list, glob_list, func_list, memory_list ).


(** i32.ge_s*)
Open Scope Z.
Definition execute_i32_ge_s' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i32 hd1 :: i32 hd2 :: tl => i32 (if hd2 >=? hd1 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i32_ge_s (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i32_ge_s' exec_stack, loc_list, glob_list, func_list, memory_list ).

(** i64.ge_s *)
Open Scope Z.
Definition execute_i64_ge_s' (exec_stack : ExecutionStack) : ExecutionStack :=
match exec_stack with
| i64 hd1 :: i64 hd2 :: tl => i32 (if hd2 >=? hd1 then 1 else 0) :: tl
| stack => stack
end.
Close Scope Z.
Definition execute_i64_ge_s (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(execute_i64_ge_s' exec_stack, loc_list, glob_list, func_list, memory_list ).


(** call - apel de functie *)
Fixpoint get_function_by_name' (name : string) (func_list : FunctionList) :=
match func_list with
| hd :: tl => if string_dec name (get_function_name hd)
              then (get_function_content hd)
              else get_function_by_name' name tl
| [] => CNop
end.
Definition get_function_by_name (name : string) (state : State) : com :=
let func_list := get_func_list state in
get_function_by_name' name func_list.

Definition get_function_body' (contents : com) : com :=
match contents with
| CFunc n p r coms => coms
| _ => CNop
end.
Definition get_function_body (name : string) (state : State) : com :=
let func_content := get_function_by_name name state in
get_function_body' func_content.

Definition get_param_types (func : com) : (list string) :=
match func with
| CFunc n p r instr => match p with
                      | param l => l
                      | _ => []
                      end
| _ => []
end.

(** Declararea unei functii in tabelul de functii *)
Definition set_function (name : string) (contents : com) (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(exec_stack, loc_list, glob_list, ((name, contents):: func_list), memory_list).

(** Declarearea memoriei *)
Open Scope Z.
Definition execute_memory (max : Z) (state : State) : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory := get_memory state in
let memory_list := get_memory_list memory in
let memory_size := if ((max * 65536) >? (get_memory_size memory)) then (max * 65536) else (get_memory_size memory) in
(exec_stack, loc_list, glob_list, func_list, (memory_size, memory_list)).
Close Scope Z.

(** i32.load8_u FĂRĂ offset *)
Open Scope Z.
Definition execute_i32_load8_u (state : State) : State :=
let exec_stack := get_execution_stack state in
let memory := get_memory state in
let memory_list := get_memory_list memory in
let memory_size := get_memory_size memory in
let index := loose_integer_type (get_execution_stack_head exec_stack) in
if index <? memory_size
then
  let loc_list := get_local_var_list state in
  let glob_list := get_global_var_list state in
  let func_list := get_func_list state in
  ((i32 ((* signed2unsigned *) (load_8_from_adress index memory_list) (* 1 *)))::(get_execution_stack_tail exec_stack),
  loc_list,
  glob_list,
  func_list,
  memory)
else state.
Close Scope Z.

(** i32.load8_u CU offset *)
Open Scope Z.
Definition execute_i32_load8_u_offset (state : State) (offset : Z) : State :=
let exec_stack := get_execution_stack state in
let memory := get_memory state in
let memory_list := get_memory_list memory in
let memory_size := get_memory_size memory in
let index := (loose_integer_type (get_execution_stack_head exec_stack)) + offset in
if index <? memory_size
then
  let loc_list := get_local_var_list state in
  let glob_list := get_global_var_list state in
  let func_list := get_func_list state in
  ((i32 ((* signed2unsigned *) (load_8_from_adress index memory_list) (* 1 *)))::(get_execution_stack_tail exec_stack),
  loc_list,
  glob_list,
  func_list,
  memory)
else state.
Close Scope Z.

(** i32.load *)
Open Scope Z.
Definition execute_i32_load(state : State) : State :=
let exec_stack := get_execution_stack state in
let memory := get_memory state in
let memory_list := get_memory_list memory in
let memory_size := get_memory_size memory in
let index := loose_integer_type (get_execution_stack_head exec_stack) in
if (index + 4) <? memory_size
then
  let loc_list := get_local_var_list state in
  let glob_list := get_global_var_list state in
  let func_list := get_func_list state in
  let byte1 := ((*signed2unsigned*) (load_8_from_adress index memory_list) (*1*) ) in
  let byte2 := ((*signed2unsigned*) (load_8_from_adress (index+1) memory_list) (*1*) ) in
  let byte3 := ((*signed2unsigned*) (load_8_from_adress (index+2) memory_list) (*1*) ) in
  let byte4 := ((*signed2unsigned*) (load_8_from_adress (index+3) memory_list) (*1*) ) in
  let number :=
    (unsigned2signed (byte1 + (Z.shiftl byte2 8) + (Z.shiftl byte3 16) + (Z.shiftl byte4 24)) 4)
  in
  ((i32 (number))::(get_execution_stack_tail exec_stack),
  loc_list,
  glob_list,
  func_list,
  memory)
else state.
Close Scope Z.

(** Declararea variabilelor locale *)
Definition execute_local_decl' (loc_list : VariableList) (var_name : string) (var_type : string) : VariableList :=
if string_is_type var_type then
(var_name, string2type var_type 0) :: loc_list
else loc_list.
Definition execute_local_decl (var_name : string) (var_type : string) (state : State)  : State :=
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(exec_stack,
execute_local_decl' loc_list var_name var_type,
glob_list,
func_list,
memory_list ).

Fixpoint get_nr_of_params (l : list string) : nat :=
match l with
| hd :: tl => (get_nr_of_params tl) + 1
| [] => 0
end.
Fixpoint get_parameters_from_stack' (exec_stack : ExecutionStack) (nr : nat) : list WasmType :=
match nr with
| O => []
| S nr' => (get_execution_stack_head exec_stack) :: (get_parameters_from_stack' (get_execution_stack_tail exec_stack) nr')
end.
Definition get_parameters_from_stack (exec_stack : ExecutionStack) (l : list string) : list WasmType :=
get_parameters_from_stack' exec_stack (get_nr_of_params l).

Open Scope string_scope.
Fixpoint check_types (wasm_list : list WasmType) (type_list : list string) : bool :=
match wasm_list with
| (i32 val) :: tl1 => match type_list with
                      | "i32" :: tl2 => check_types tl1 tl2
                      | _ => false
                      end
| (i64 val) :: tl1 => match type_list with
                      | "i64" :: tl2 => check_types tl1 tl2
                      | _ => false
                      end
| (None) :: tl => false
| [] => true
end.

Definition list_of_nat_string : list string :=
["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "19"; "20"; "21"; "22"; "23"; "24"; "25"; "26"; "27"; "28"; "29"; "30"; "31"; "32"; "33"; "34"; "35"; "36"; "37"; "38"; "39"; "40"; "41"; "42"; "43"; "44"; "45"; "46"; "47"; "48"; "49"; "50"; "51"; "52"; "53"; "54"; "55"; "56"; "57"; "58"; "59"; "60"; "61"; "62"; "63"; "64"; "65"; "66"; "67"; "68"; "69"; "70"; "71"; "72"; "73"; "74"; "75"; "76"; "77"; "78"; "79"; "80"; "81"; "82"; "83"; "84"; "85"; "86"; "87"; "88"; "89"; "90"; "91"; "92"; "93"; "94"; "95"; "96"; "97"; "98"; "99"].
Fixpoint get_nth' (l: list string) (index : nat) (goal : nat) : string :=
match l with
| hd::tl => if (index =? goal)%nat then hd else get_nth' tl (index+1) goal
| [] => "a"
end.
Close Scope string_scope.
Definition get_nth (l: list string) (goal : nat) : string :=
get_nth' l 0 goal.

Fixpoint generate_locals' (wasm_list : list WasmType) (locals: VariableList) (index : nat) : VariableList :=
match wasm_list with
| (i32 val) :: tl =>  (get_nth list_of_nat_string index, (i32 val)) :: (generate_locals' tl locals (index+1))
| (i64 val) :: tl =>  (get_nth list_of_nat_string index, (i64 val)) :: (generate_locals' tl locals (index+1))
| (None) :: tl =>     (generate_locals' tl locals (index+1))
| [] => locals
end.
Definition generate_locals (wasm_list : list WasmType) (locals : VariableList) : VariableList :=
generate_locals' wasm_list locals 0.
Fixpoint remove_params_from_stack (wasm_list : ExecutionStack) (nr: nat) : ExecutionStack :=
match nr with
| O => wasm_list
| S nr' => remove_params_from_stack (get_execution_stack_tail wasm_list) nr'
end.

Definition set_function_params (name : string) (state : State) : State :=
(* get the 5 components of state*)
let exec_stack := get_execution_stack state in
let loc_list := get_local_var_list state in
let glob_list := get_global_var_list state in
let func_list := get_func_list state in
let memory_list := get_memory state in
(* get the function declaration *)
let func_content := get_function_by_name name state in
(* get the expected parameter types *)
let param_types := get_param_types func_content in
(* get the parameters from stack *)
let stack_parameters := get_parameters_from_stack (exec_stack) (param_types) in
(* check parameters fit *)
if (check_types stack_parameters param_types) then
(* generate result state *)
  (remove_params_from_stack exec_stack (get_nr_of_params param_types),
  ((generate_locals stack_parameters loc_list)),
  glob_list,
  func_list,
  memory_list)
else state.

(** Functia folosita pentru a executa toate intructiunile *)
Definition execute_instruction (instrunction : exp)
                            (state : State)
                            : (State):=
match instrunction with
| i32_const n => execute_i32_const n state
| i64_const n => execute_i64_const n state
| local_get n => execute_local_get n state
| local_set n => execute_local_set n state
| local_tee n => execute_local_get n (execute_local_set n state)
| i32_add     => execute_i32_add state
| i64_add     => execute_i64_add state
| i32_sub     => execute_i32_sub state
| i64_sub     => execute_i64_sub state
| i32_mul     => execute_i32_mul state
| i64_mul     => execute_i64_mul state
| i32_div_s   => execute_i32_div_s state
| i64_div_s   => execute_i64_div_s state
| i32_rem_s   => execute_i32_rem_s state
| i64_rem_s   => execute_i64_rem_s state
| i32_and     => execute_i32_and state
| i64_and     => execute_i64_and state
| i32_xor     => execute_i32_xor state
| i64_xor     => execute_i64_xor state
| i32_eq      => execute_i32_eq state
| i64_eq      => execute_i64_eq state
| i32_eqz     => execute_i32_eqz state
| i64_eqz     => execute_i64_eqz state
| i32_ge_s    => execute_i32_ge_s state
| i64_ge_s    => execute_i64_ge_s state
| local_decl v t            => execute_local_decl v t state
| memory_decl m1 m2    => execute_memory m2 state
| i32_load8_u          => execute_i32_load8_u state
| i32_load8_u_offset i => execute_i32_load8_u_offset state i
| i32_load    => execute_i32_load state
end.

Definition State2Bool' (x : WasmType) : Z :=
match x with
| i32 val => val
| _ => 0
end.

Open Scope Z.
Definition State2Bool (state : State)
                            : (bool) :=
let exec_stack := get_execution_stack state in
let stack_head_Z_val := State2Bool' (get_execution_stack_head exec_stack) in
(if (stack_head_Z_val =? (0%Z)) then false else true).
Close Scope Z.

Fixpoint execute_instructions (intructions : list exp)
                            (state : State)
                            : (State):=
match intructions with
| hd :: tl => execute_instructions tl ( execute_instruction hd state )
| [] => state
end.

(** Definirea notatiilor *)

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

(* Notation "'true'" := true (at level 1).
Notation "'true'" := 1 (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := 0 (in custom com at level 0). *)

Open Scope com_scope.

(* Instructions flow*)
Notation "'nop'" :=
         CNop (in custom com at level 0) : com_scope.
Notation " x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' l x 'end'" :=
         (CIf l x)
           (in custom com at level 89 (*, x at level 99,
            y at level 99, z at level 99*)) : com_scope.
Notation "'br_if' x" :=
         (CBr_If x)
           (in custom com at level 89 , x at level 99) : com_scope.
Notation "'loop' l x 'end'" :=
         (CLoop l x)
            (in custom com at level 89, x at level 99 , l at level 99) : com_scope.
Notation "'block' l x 'end'" :=
         (CBlock l x)
            (in custom com at level 89, x at level 99 , l at level 99) : com_scope.
(* declarations *)
Notation "'i32.const' x" :=
         (Ci32_const x)
            (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'i64.const' x" :=
         (Ci64_const x)
            (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'func' n p r c " :=
         (CFunc n p r c)
            (in custom com at level 89, n at level 99 , p at level 99, r at level 99, c at level 99) : com_scope.
Notation "'return'" :=
         (CReturn)
            (in custom com at level 88) : com_scope.
Notation "'call' f" :=
         (CCall f)
            (in custom com at level 88, f at level 99) : com_scope.
Notation "'memory' min max" :=
         (CMemory min max)
            (in custom com at level 88, min at level 99, max at level 99) : com_scope.
(*memory operations*)
Notation "'i32.load8_u'" :=
         (Ci32_Load8_u)
            (in custom com at level 88) : com_scope.
Notation "'i32.load8_u' 'offset=' o " :=
         (Ci32_Load8_u_offset o)
            (in custom com at level 88, o at level 99) : com_scope.
Notation "'i32.load'" :=
         (Ci32_Load)
            (in custom com at level 88) : com_scope.
Notation "'local' n t" :=
         (CLocal n t)
            (in custom com at level 88, n at level 99, t at level 99) : com_scope.
Notation "'local.set' x" :=
         (Clocal_set x)
            (in custom com at level 88, x at level 99) : com_scope.
Notation "'local.get' x" :=
         (Clocal_get x)
            (in custom com at level 88, x at level 99) : com_scope.
Notation "'local.tee' x" :=
         (Clocal_tee x)
            (in custom com at level 88, x at level 99) : com_scope.
(*math operations*)
Notation "'i32.add'" :=
         (Ci32_add)
            (in custom com at level 88) : com_scope.
Notation "'i64.add'" :=
         (Ci64_add)
            (in custom com at level 88) : com_scope.
Notation "'i32.sub'" :=
         (Ci32_sub)
            (in custom com at level 88) : com_scope.
Notation "'i64.sub'" :=
         (Ci64_sub)
            (in custom com at level 88) : com_scope.
Notation "'i32.mul'" :=
         (Ci32_mul)
            (in custom com at level 88) : com_scope.
Notation "'i64.mul'" :=
         (Ci64_mul)
            (in custom com at level 88) : com_scope.
Notation "'i32.div_s'" :=
         (Ci32_div_s)
            (in custom com at level 88) : com_scope.
Notation "'i64.div_s'" :=
         (Ci64_div_s)
            (in custom com at level 88) : com_scope.
Notation "'i32.rem_s'" :=
         (Ci32_rem_s)
            (in custom com at level 88) : com_scope.
Notation "'i64.rem_s'" :=
         (Ci64_rem_s)
            (in custom com at level 88) : com_scope.
Notation "'i32.and'" :=
         (Ci32_and)
            (in custom com at level 88) : com_scope.
Notation "'i64.and'" :=
         (Ci64_and)
            (in custom com at level 88) : com_scope.
Notation "'i32.xor'" :=
         (Ci32_xor)
            (in custom com at level 88) : com_scope.
Notation "'i64.xor'" :=
         (Ci64_xor)
            (in custom com at level 88) : com_scope.
Notation "'i32.eq'" :=
         (Ci32_eq)
            (in custom com at level 88) : com_scope.
Notation "'i64.eq'" :=
         (Ci64_eq)
            (in custom com at level 88) : com_scope.
Notation "'i32.eqz'" :=
         (Ci32_eqz)
            (in custom com at level 88) : com_scope.
Notation "'i64.eqz'" :=
         (Ci64_eqz)
            (in custom com at level 88) : com_scope.
Notation "'i32.ge_s'" :=
         (Ci32_ge_s)
            (in custom com at level 88) : com_scope.
Notation "'i64.ge_s'" :=
         (Ci64_ge_s)
            (in custom com at level 88) : com_scope.
(*Comentarii*)
Notation " ';;' a \n b " :=
          (b)
            (in custom com at level 88, b at level 99).
Notation " '(;' a ';)' b " :=
          (b)
            (in custom com at level 88, b at level 99).


(** Implementarea regulilor de inferenta *)
Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).
Inductive ceval : com -> State -> Branch -> State -> Prop :=  

  | E_Nop : forall st,
      st =[ nop ]=> st / SContinue

  | E_i32_const : forall st number,
      st =[ i32.const number ]=> (execute_instruction (i32_const number) st ) / SContinue
  | E_i64_const : forall st number,
      st =[ i64.const number ]=> (execute_instruction (i64_const number) st ) / SContinue  

  | E_i32_add : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i32_add) st = st' ->
      st =[ i32.add ]=> st' / SContinue
  | E_i64_add : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i64_add) st = st' ->
      st =[ i64.add ]=> st' / SContinue

  | E_i32_sub : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i32_sub) st = st' ->
      st =[ i32.sub ]=> st' / SContinue
  | E_i64_sub : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i64_sub) st = st' ->
      st =[ i64.sub ]=> st' / SContinue

  | E_i32_mul : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i32_mul) st = st' ->
      st =[ i32.mul ]=> st' / SContinue
  | E_i64_mul : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i64_mul) st = st' ->
      st =[ i64.mul ]=> st' / SContinue

  | E_i32_div_s : forall st st',
      match_types_last_2_on_stack st = true ->
      exec_stack_head_is_zero st = false ->
      execute_instruction (i32_div_s) st = st' ->
      st =[ i32.div_s ]=> st' / SContinue
  | E_i64_div_s : forall st st',
      match_types_last_2_on_stack st = true ->
      exec_stack_head_is_zero st = false ->
      execute_instruction (i64_div_s) st = st' ->
      st =[ i64.div_s ]=> st' / SContinue

  | E_i32_rem_s : forall st st',
      match_types_last_2_on_stack st = true ->
      exec_stack_head_is_zero st = false ->
      execute_instruction (i32_rem_s) st = st' ->
      st =[ i32.rem_s ]=> st' / SContinue
  | E_i64_rem_s : forall st st',
      match_types_last_2_on_stack st = true ->
      exec_stack_head_is_zero st = false ->
      execute_instruction (i64_rem_s) st = st' ->
      st =[ i64.rem_s ]=> st' / SContinue

  | E_i32_and : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i32_and) st = st' ->
      st =[ i32.and ]=> st' / SContinue
  | E_i64_and : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i64_and) st = st' ->
      st =[ i64.and ]=> st' / SContinue

  | E_i32_xor : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i32_xor) st = st' ->
      st =[ i32.xor ]=> st' / SContinue
  | E_i64_xor : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i64_xor) st = st' ->
      st =[ i64.xor ]=> st' / SContinue

  | E_i32_eq : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i32_eq) st = st' ->
      st =[ i32.eq ]=> st' / SContinue
  | E_i64_eq : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i64_eq) st = st' ->
      st =[ i64.eq ]=> st' / SContinue

  | E_i32_eqz : forall st st',
      match_last_on_stack_with_type st (i32 0) = true ->
      execute_instruction (i32_eqz) st = st' ->
      st =[ i32.eqz ]=> st' / SContinue
  | E_i64_eqz : forall st st',
      match_last_on_stack_with_type st (i32 0) = true ->
      execute_instruction (i64_eqz) st = st' ->
      st =[ i64.eqz ]=> st' / SContinue

  | E_i32_ge_s : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i32_ge_s) st = st' ->
      st =[ i32.ge_s ]=> st' / SContinue
  | E_i64_ge_s : forall st st',
      match_types_last_2_on_stack st = true ->
      execute_instruction (i64_ge_s) st = st' ->
      st =[ i64.ge_s ]=> st' / SContinue

  | E_Func : forall st st' name param res instr ,
      set_function name (CFunc name param res instr) st = st' ->
      st =[ CFunc name param res instr ]=> st' / SContinue
  (*| E_FuncStart : forall st st' st'' name param ret c ,
      set_function name (CFunc name param ret c) st = st' ->
      st' =[ c ]=> st'' / SContinue ->
      st =[ CFunc name param ret c ]=> st'' / SContinue*)
  | E_Return : forall st,
      st =[ return ]=> st / SReturn

  | E_Call : forall name st st' st'' res,
      (*get_function_body name st = c ->*) (* L-am pus sa puna singur c-ul*)
      set_function_params name st = st' ->
      st' =[ get_function_body name st ]=> st'' / res ->
      st =[ call name ]=> st'' / SContinue

  | E_Memory : forall min max st st',
      (execute_instruction (memory_decl min max) st) = st' ->
      st =[ CMemory min max ]=> st' / SContinue

  | E_i32_Load8_u: forall st st',
      execute_instruction (i32_load8_u) st = st' ->
      match_last_on_stack_with_type st (i32 0) = true ->
      st =[ i32.load8_u ]=> st' / SContinue
  | E_i32_Load8_u_offset: forall offset st st',
      execute_instruction (i32_load8_u_offset offset) st = st' ->
      match_last_on_stack_with_type st (i32 0) = true ->
      st =[ i32.load8_u offset= offset ]=> st' / SContinue
  | E_i32_Load: forall st st',
      execute_instruction (i32_load) st = st' ->
      match_last_on_stack_with_type st (i32 0) = true ->
      st =[ i32.load ]=> st' / SContinue

  | E_Local : forall name type st st',
       (string_is_type type) = true ->
       (execute_instruction (local_decl name type) st) = st' ->
       st =[ CLocal name type ]=> st' / SContinue

  | E_Seq : forall c1 c2 st st' st'' res,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / res ->
      st =[ c1 ; c2 ]=> st'' / res
  | E_SeqBr : forall c1 c2 st st' label (*st''*),
      st =[ c1 ]=> st' / SBr label ->
      (*res <> SContinue ->*)
      (*st' =[ c2 ]=> st'' / res2 ->*)
      st =[ c1 ; c2 ]=> st' / SBr label
  | E_SeqExpectReturn : forall c1 c2 st st' st'' (*st''*),
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / SReturn ->
      st =[ c1 ; c2 ]=> st'' / SReturn
  | E_SeqHasReturn : forall c1 c2 st st' (*st''*),
      st =[ c1 ]=> st' / SReturn ->
      (*st' =[ c2 ]=> st'' / res2 ->*)
      st =[ c1 ; c2 ]=> st' / SReturn
  (*| E_SeqFinishWithReturn : forall c1 c2 st st' (*st''*),
      st =[ c1 ]=> st' / SReturn ->
      (*st' =[ c2 ]=> st'' / res2 ->*)
      st =[ c1 ; c2 ]=> st' / SContinue*)

  (* Am comentat asta fiindca am inclus-o in E_Seq
  | E_SeqLoop2 : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / SLoop ->
      st =[ c1 ; c2 ]=> st'' / SLoop *)
  | E_IfTrue : forall st st' label c res,
      State2Bool st = true ->
      (remove_execution_stack_head st) =[ c ]=> st' / res ->
      res <> (SBr label) ->
      st =[ CIf label c ]=> st' / res
  | E_IfTrueBr : forall st st' label c,
      State2Bool st = true ->
      (remove_execution_stack_head st) =[ c ]=> st' / (SBr label) ->
      st =[ CIf label c ]=> st' / SContinue
  | E_IfTrueReturn : forall st st' label c,
      State2Bool st = true ->
      (remove_execution_stack_head st) =[ c ]=> st' / SReturn ->
      st =[ CIf label c ]=> st' / SReturn
  | E_IfFalse : forall st st' label c,
      State2Bool st = false ->
      (remove_execution_stack_head st) = st' ->
      st =[ CIf label c ]=> st' / SContinue

  | E_LoopOnce : forall st st' (*st''*) c label,
      st =[ c ]=> st' / SContinue ->
      (*st' =[ CLoop c ]=> st'' / SContinue -> (* st' =[ while c end ]=> st'' *) *)
      st =[ CLoop label c ]=> st' / SContinue     (* st  =[ while c end ]=> st'' *)
  | E_LoopOnceBrOther : forall st st' (*st''*) c label1 label2,
      st =[ c ]=> st' / SBr label2 ->
      label1 <> label2 ->
      (*st' =[ CLoop c ]=> st'' / SContinue -> (* st' =[ while c end ]=> st'' *) *)
      st =[ CLoop label1 c ]=> st' / SBr label2     (* st  =[ while c end ]=> st'' *)
  | E_Loop : forall st st' label1 c st'' label2 res,
      st =[ c ]=> st' / SBr label2 ->
      label1 = label2 ->
      st' =[ CLoop label1 c ]=> st'' / res -> (* st' =[ while c end ]=> st'' *)
      st =[ CLoop label1 c ]=> st'' / res     (* st  =[ while c end ]=> st'' *)

  | E_Block : forall st st' (*st''*) label c,
      (st =[ c ]=> st' / SContinue) \/ (st =[ c ]=> st' / SBr label) ->
      (*st' =[ CLoop c ]=> st'' / SContinue -> (* st' =[ while c end ]=> st'' *) *)
      st =[ CBlock label c ]=> st' / SContinue     (* st  =[ while c end ]=> st'' *)
  | E_BlockBrOther : forall st st' (*st''*) label1 label2 c,
      (st =[ c ]=> st' / SBr label2 ) ->
      label1 <> label2 ->
      (*st' =[ CLoop c ]=> st'' / SContinue -> (* st' =[ while c end ]=> st'' *) *)
      st =[ CBlock label1 c ]=> st' / SBr label2     (* st  =[ while c end ]=> st'' *)
  | E_BlockReturn : forall st st' label c,
      (st =[ c ]=> st' / SReturn ) ->
      st =[ CBlock label c ]=> st' / SReturn     (* st  =[ while c end ]=> st'' *)

  | E_Br_IfTrue : forall st st' label,
      State2Bool st = true ->
      (remove_execution_stack_head st) = st' ->
      st =[ CBr_If label ]=> st' / SBr label
  | E_Br_IfFalse : forall st st' label,
      State2Bool st = false ->
      (remove_execution_stack_head st) = st' ->
      st =[ CBr_If label ]=> st' / SContinue

  | E_local_set : forall st variable,
      local_set_type_check  st variable = true ->
      local_variable_exists variable st = true ->
      st =[ Clocal_set variable ]=> (execute_instruction (local_set variable) st ) / SContinue
  | E_local_get : forall st variable,
      (*local_set_type_check  st variable = true ->*)
      local_variable_exists variable st = true ->
      st =[ Clocal_get variable ]=> (execute_instruction (local_get variable) st ) / SContinue
  | E_local_tee : forall st variable,
      local_set_type_check  st variable = true ->
      local_variable_exists variable st = true ->
      st =[ Clocal_tee variable ]=> (execute_instruction (local_tee variable) st ) / SContinue


where "st =[ c ]=> st' / s " := (ceval c st s st').

(* ----------- Functioneaza const, add, get, set, if, while, br. If NU are else -------- *)

(* ----------- Urmeaza implementarea si testarea a noi instructiuni -------------------- *)

(*Definition var1 : string := "Var1".
Definition var_a : string := "a".
Definition var_b : string := "b".*)
Open Scope Z.


Close Scope Z.
Close Scope com_scope.