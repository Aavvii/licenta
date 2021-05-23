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
Import Z2Nat.
Import Zabs2N.
Import ListNotations.
(*Open Scope R_scope.*)

From LF Require Import Maps Wasm Proprieties.

Definition strlen : string := "strlen".
Definition block1 : string := "block1".
Definition L1 : string := "L1".
Definition L2 : string := "L2".
Definition L3 : string := "L3".
Definition v0 : string := "0".
Definition v1 : string := "1".
Definition v2 : string := "2".
Definition v3 : string := "3".

Open Scope string_scope.
Open Scope com_scope.
Open Scope Z.

Lemma TEMPORARELY_ADMITTED :
forall (st st': State) (c : com) (res : Branch),
st =[c]=> st' / res.
Admitted.

Fixpoint len' (index : Z) (mem : MemoryList) (memsize : nat) : Z :=
match memsize with
| O => 0
| S (memsize') => if (( load_8_from_adress index mem) =? 0)
                then 0
                else (len' (index+1) mem memsize' + 1)
end.

Definition len (index : Z) (mem : MemoryList) (memsize : Z): Z :=
len' index mem (Z.to_nat memsize).

(* Fixpoint len'' (index : Z) (initial_mem mem : MemoryList) : Z :=
match mem with
| (i, m) :: tl => if (( load_8_from_adress i initial_mem) =? 0) then 0 else (if (index =? i) then (len'' (i+1) initial_mem tl) + 1 else 0)
| [] => 0
end.
Fixpoint len' (index : Z) (initial_mem mem : MemoryList) : Z :=
match mem with
| (i, m) :: tl => if (i =? index) then (len'' (index) initial_mem ((i, m) :: tl)) else (len' (index) initial_mem tl)
| [] => 0
end.
Definition len (index : Z) (mem : MemoryList) : Z :=
len' index mem mem. *)

Eval compute in len (5) [(5, 2);(6, 2);(7, 0);(8, 2);(9, 0);(10, 2);(11, 2)] 8.

Close Scope string_scope.
Lemma len_0 :
forall (pointer l str_start str_end : Z) (loc_list glob_list : VariableList) (func_list1 func_list2 : FunctionList) (memsize : Z) (mem: list MemoryByte),
load_8_from_adress pointer (mem) = 0 ->
len (pointer) (mem) (memsize) = 0.
Proof.
intros.
unfold len.
unfold len'.
induction (Z.to_nat memsize).
- reflexivity. 
- rewrite H. simpl. reflexivity.
Qed.


Open Scope string_scope.
Definition fun_strlen :=
<{
  func ("strlen") (param ["i32"]) (result "i32")
    (local ("1") ("i32")) ; (local ("2") ("i32")); (local ("3") ("i32"));
    (local.get "0");
    (local.set "1");
    block (L1)
      (local.get ("0"));
      i32.const 3;
      i32.and;
      if (L2)
        loop (L3)
          (local.get ("1"));
          i32.load8_u;
          i32.eqz;
          (br_if (L1));
          (local.get ("1"));
          i32.const 1;
          i32.add;
          (local.tee ("1"));
          i32.const 3;
          i32.and;
          br_if (L3)
        end
      end;
      loop (L2)
        (local.get ("1"));
        (local.tee ("2"));
        i32.const 4;
        i32.add;
        (local.set ("1"));
        (local.get ("2"));
        i32.load;
        (local.tee ("3"));
        i32.const (-1);
        i32.xor;
        (local.get ("3"));
        i32.const 16843009;
        i32.sub;
        i32.and;
        i32.const -2139062144;
        i32.and;
        i32.eqz;
        br_if (L2)
      end;
      (local.get ("3"));
      i32.const 255;
      i32.and;
      i32.eqz;
      if (L2)
        (local.get ("2"));
        (local.get ("0"));
        i32.sub ;
        return
      end;
      loop (L2)
        (local.get ("2"));
        (i32.load8_u offset=1);
        (local.set ("3"));
        (local.get ("2"));
        i32.const 1;
        i32.add;
        (local.tee ("1"));
        (local.set ("2"));
        (local.get ("3"));
        br_if (L2)
      end
    end;
    (local.get ("1"));
    (local.get ("0"));
    i32.sub
}>.
Close Scope string_scope.

Definition four_byte_value_notation
(pointer l str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte) : Z :=
(unsigned2signed
       (signed2unsigned
          (load_8_from_adress pointer
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) 1 +
        signed2unsigned
          (load_8_from_adress (pointer + 1)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) 1 *
        256 +
        signed2unsigned
          (load_8_from_adress (pointer + 2)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) 1 *
        65536 +
        signed2unsigned
          (load_8_from_adress (pointer + 3)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) 1 *
        16777216) 4)
.

Definition is_any_byte_0 (n : Z) :=
let nr_unsigned := (signed2unsigned n 4) in
let byte1 := Z.modulo nr_unsigned 256 in
let byte2 := Z.modulo (Z.div nr_unsigned 256) 256 in
let byte3 := Z.modulo (Z.div nr_unsigned 65536) 256 in
let byte4 := Z.modulo (Z.div nr_unsigned 16777216) 256 in
if (byte1 =? 0) || (byte2 =? 0) || (byte3 =? 0) || (byte4 =? 0)
then true else
false.

Definition are_all_bytes_not_0_bitwise (n : Z) :=
let op_result :=
(Z.land
       (Z.land
          (Z.lxor (n) (-1))
          ( (n -16843009 ))) 
       (-2139062144))
in
if op_result =? 0 then true else false.


Eval compute in is_any_byte_0 (-2139062144).
Eval compute in is_any_byte_0 (-2147450752).

Eval compute in are_all_bytes_not_0_bitwise (-2139062144).
Eval compute in are_all_bytes_not_0_bitwise (-2147450752).
Eval compute in are_all_bytes_not_0_bitwise (197379).

(*Lemma check_any_byte_zero :
(pointer + 4) < memsize ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
=[*)



Lemma strlen_loop2_invariant :
forall
(pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_2 var_3 : Z),

(pointer + 4) < memsize ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
=[
(local.get v1);
(local.tee v2);
i32.const 4;
i32.add;
(local.set v1);
(local.get v2);
i32.load;
(local.tee v3);
i32.const (-1);
i32.xor;
(local.get v3);
i32.const 16843009;
i32.sub;
i32.and;
i32.const (-2139062144);
i32.and;
i32.eqz;
br_if L2
]=> ([],
    (v3, i32
(four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2))
    :: (v2, i32 (pointer))
       :: (v1, i32 (pointer +4)) :: (v0, i32 pointer) :: loc_list,
    glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
    (memsize,
    mem1 ++
    [(pointer, str_start)] ++
    str_middle ++ [(pointer + l, str_end)] ++ mem2)) /
if (are_all_bytes_not_0_bitwise (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2))
then SBr L2 else SContinue.
Proof.
intros.
apply E_Seq with ([i32 pointer], ( (v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
* apply E_local_get. auto.
* apply E_Seq with ([i32 pointer], ( (v3, i32 var_3) :: (v2, i32 pointer) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
** apply E_local_tee. auto. auto.
** apply E_Seq with ([i32 4; i32 pointer], ( (v3, i32 var_3) :: (v2, i32 pointer) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_i32_const.
*** apply E_Seq with ([i32 (pointer+4)], ( (v3, i32 var_3) :: (v2, i32 pointer) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_i32_add. auto. auto.
**** apply E_Seq with ([], ( (v3, i32 var_3) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_local_set. auto. auto.
***** apply E_Seq with ([i32 pointer], ( (v3, i32 var_3) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_get. auto.
****** apply E_Seq with ([i32
(four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)
], ( (v3, i32 var_3) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_i32_Load.
******** unfold execute_intruction. unfold execute_i32_load. simpl.
unfold "<?". rewrite H. simpl. reflexivity.
******** reflexivity.
******* apply E_Seq with
([i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******** apply E_local_tee.
********* reflexivity.
********* reflexivity.
******** apply E_Seq with
([i32 (-1); i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********* apply E_i32_const.
********* apply E_Seq with
([i32 ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********** apply E_i32_xor.
*********** reflexivity.
*********** reflexivity.
********** apply E_Seq with
([i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2); i32 ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*********** apply E_local_get. auto.
*********** apply E_Seq with
([i32 16843009; i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2); i32 ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************ apply E_i32_const.
************ apply E_Seq with
([i32 ((four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)-16843009); i32 ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************* apply E_i32_sub. reflexivity. reflexivity.
************* apply E_Seq with
([i32 ( Z.land  ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)-16843009) )],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************** apply E_i32_and. auto. auto.
************** apply E_Seq with
([i32 (-2139062144);i32 ( Z.land  ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)-16843009) )],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*************** apply E_i32_const.
*************** apply E_Seq with
([i32 (Z.land ( Z.land  ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)-16843009) ) (-2139062144))],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**************** apply E_i32_and. auto. auto.
**************** simpl.
case_eq(Z.land
         (Z.land
            (Z.lxor
               (four_byte_value_notation pointer l str_start
                  str_end mem1 str_middle mem2) 
               (-1))
            (four_byte_value_notation pointer l str_start str_end
               mem1 str_middle mem2 - 16843009)) 
         (-2139062144) =? 0).
+ (*case true*) intros. apply E_Seq with
([i32 1],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++ apply E_i32_eqz.
+++ auto.
+++ unfold execute_intruction. unfold execute_i32_eqz.
unfold execute_i32_eqz'. simpl.
rewrite H0. reflexivity.
++ unfold are_all_bytes_not_0_bitwise.
rewrite H0.
apply E_Br_IfTrue. reflexivity. reflexivity. 
+ (*case false*) intros. apply E_Seq with
([i32 0],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++ apply E_i32_eqz.
+++ auto.
+++ unfold execute_intruction. unfold execute_i32_eqz.
unfold execute_i32_eqz'. simpl.
rewrite H0. reflexivity.
++ unfold are_all_bytes_not_0_bitwise.
rewrite H0.
apply E_Br_IfFalse. reflexivity. reflexivity.
Qed.


Lemma strlen_works :
forall (pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z) (mem1 str_middle mem2: list MemoryByte)
(len_res : Z)
(var_2 var_3 : Z),
len_res = (len pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) memsize) ->
pointer < memsize ->
get_function_by_name strlen ([i32 pointer], loc_list, glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) = fun_strlen ->
pointer +4 < memsize ->
([i32 pointer], loc_list, glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) =[
CCall strlen
]=> ([i32 (len_res)], ( (v3, i32 0)::(v2, i32 0)::(v1 ,i32 (pointer + len_res))::(v0 ,i32 pointer)::loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2),  (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) / SContinue.
Proof.
intros.
apply E_Call with ([], ((v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
- unfold set_function_params. rewrite H1. simpl. reflexivity.
- unfold get_function_body. rewrite H1. simpl.
-- apply E_Seq with ([], ([(v1, i32 0)] ++ [(v0, i32 pointer)] ++ loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
--- apply E_Local. reflexivity. reflexivity.
--- apply E_Seq with ([], ( (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
---- apply E_Local. reflexivity. reflexivity.
---- apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
----- apply E_Local. reflexivity. reflexivity.
----- apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
------ apply E_local_get. auto.
------ apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
------- apply E_local_set. auto. auto.
------- case_eq ( load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) ?= 0).
+ (*cazul load_8_from_adress = 0*)
  case_eq ((Z.land pointer 3) =? 0).
(*programul fsce and cu 3 ca sa verifice ca
numarul e multiplu de 4 si sa poata face
eficient load de 4 biti odata (in asm)*)

(* Demonstratia ca Strlen = 0 DACA
load_8_from_adress = 0 si
(Z.land pointer 3) = 0*)

++ intros. apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++ apply E_Block. left.
apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++ apply E_local_get. auto.
++++ apply E_Seq with ([i32 3; i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++++ apply E_i32_const.
+++++ apply E_Seq with ([i32 0], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++++ apply E_i32_and.
* reflexivity.
* unfold execute_intruction. unfold execute_i32_and. unfold execute_i32_and'.
simpl.
rewrite Z.eqb_eq in H3. (* <- Lema utila *)
rewrite H3. reflexivity.
++++++ apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++++++ apply E_IfFalse.
* reflexivity.
* reflexivity.
+++++++ apply E_Seq with ([],
    (v3, i32
(four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2))
    :: (v2, i32 (pointer))
       :: (v1, i32 (pointer +4)) :: (v0, i32 pointer) :: loc_list,
    glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
    (memsize,
    mem1 ++
    [(pointer, str_start)] ++
    str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++++ apply E_LoopOnce.
(*case_eq((is_any_byte_not_0_bitwise (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2))).
*)
* intros.
induction (four_byte_value_notation pointer l str_start str_end mem1
         str_middle mem2).
** 

apply strlen_loop2_invariant.

apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
** apply E_local_get. auto.
** apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 pointer) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_local_tee. auto. auto.
*** apply E_Seq with ([i32 4; i32 pointer], ( (v3, i32 0) :: (v2, i32 pointer) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_i32_const.
**** apply E_Seq with ([i32 (4 + pointer)], ( (v3, i32 0) :: (v2, i32 pointer) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_i32_add. auto. auto.
***** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 pointer) :: (v1, i32 (4+pointer)) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_set. auto. auto.
****** apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 pointer) :: (v1, i32 (4+pointer)) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_local_get. auto.
******* apply E_Seq with ([i32
(four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)
], ( (v3, i32 0) :: (v2, i32 pointer) :: (v1, i32 (4+pointer)) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******** apply E_i32_Load.
********* unfold execute_intruction. unfold execute_i32_load. simpl.
unfold "<?". rewrite H2. simpl. reflexivity.
********* reflexivity.
******** apply E_Seq with
([i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (4+pointer)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********* apply E_local_tee.
********** reflexivity.
********** reflexivity.
********* apply E_Seq with
([i32 (-1); i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (4+pointer)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********** apply E_i32_const.
********** apply E_Seq with
([i32 ( Z.lxor (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (4+pointer)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*********** apply E_i32_xor.
************ reflexivity.
************ reflexivity.
*********** 




(*apply TEMPORARELY_ADMITTED.*)

(* Demonstratia ca Strlen = 0 DACA
load_8_from_adress = 0 si
(Z.land pointer 3) <> 0*)
++ intros.
apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++ apply E_Block. right.
    apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++ apply E_local_get. auto.
++++ apply E_Seq with ([i32 3; i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++++ apply E_i32_const.
+++++ apply E_Seq with ([i32 (Z.land pointer 3)], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++++ intros. apply E_i32_and. reflexivity. unfold execute_intruction. unfold execute_i32_and. unfold execute_i32_and'. simpl. reflexivity.
++++++ apply E_SeqBr. apply E_IfTrue.
+++++++ unfold State2Bool. unfold State2Bool'. unfold get_execution_stack_head. unfold get_execution_stack. rewrite H2. reflexivity.
+++++++ apply E_LoopOnceBrOther. simpl. apply E_Seq with (([i32 pointer], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ (strlen, fun_strlen) :: func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)))).
++++++++ apply E_local_get. auto.
++++++++ apply E_Seq with (([i32 0], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ (strlen, fun_strlen) :: func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)))).
+++++++++ apply E_i32_Load8_u.
          unfold execute_intruction.
          unfold execute_i32_load8_u. simpl.
          unfold "<?". unfold "<" in H. rewrite H0.
          unfold signed2unsigned. unfold "<?". apply Z.compare_eq in H3. simpl. simpl in H3. rewrite H3.
++++++++++ reflexivity.
++++++++++ reflexivity.
+++++++++ apply E_Seq with (([i32 1], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ (strlen, fun_strlen) :: func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)))).
++++++++++ apply E_i32_eqz.
+++++++++++ reflexivity.
+++++++++++ unfold execute_intruction. unfold execute_i32_eqz.
            unfold execute_i32_eqz'. simpl. reflexivity.
++++++++++ apply E_SeqBr. apply E_Br_IfTrue. reflexivity. reflexivity. discriminate.
++++++++ discriminate.
+++++++ discriminate.
+++++++ discriminate.
+++ apply E_Seq with ([i32 pointer], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))).
++++ apply E_local_get. auto.
++++ apply E_Seq with ([i32 pointer; i32 pointer], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))).
+++++ apply E_local_get. auto.
+++++ apply E_i32_sub. auto.
      unfold execute_intruction.
      unfold execute_i32_sub.
      unfold execute_i32_sub'. simpl. rewrite Z.sub_diag.
      rewrite len_0 in H; auto.
++++++ rewrite H. simpl. rewrite Z.add_0_r. reflexivity.
++++++ apply Z.compare_eq in H3. rewrite H3. reflexivity.
+ (*cazul load_8_from_adress < 0*) intros.
unfold len. unfold len'.
      
 unfold len''. simpl. simpl in H2.
      

      apply Z.compare_eq in H2. simpl.
Eval compute in (len pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)).




(*Definition fun_strlen :=
<{func (strlen) (param ["i32"]) (ret "i32")
(CLocal "1" "i32"); (CLocal "2" "i32"); (CLocal "3" "i32");

Clocal_get "a";
Clocal_set "b";
CBlock "block1";
Clocal_get "0";
Ci32_const 3;
Ci32_and;
if "if1"
  loop "loop1";
    Clocal_get "1";
    Ci32_load8_u;
    Ci32_eqz;
    CBr_If "block1"
    Clocal_get "1";
    Ci32_const 1;
    Ci32_add;
    Clocal_set "1"; (*\_ <=> cu CLocal_tee *)
    Clocal_get "1"; (*/ *)
    Ci32_const 3;
    Ci32_and;
    CBr_If "loop1"
  end
end
loop "loop2"
  Clocal_get "1";
  Clocal_set "2"; (*\_ <=> cu CLocal_tee *)
  Clocal_get "2"; (*/ *)
  Ci32_const 4;
  Ci32_add;
  Clocal_get "1";
  Clocal_get "2";
  Ci32_load;
  Clocal_set "3"; (*\_ <=> cu CLocal_tee *)
  Clocal_get "3";
  Ci32_const -1;
  Ci32_xor;
  Clocal_get "3";
  Ci32_const 16843009;
  Ci32_sub;
  Ci32_and;
  Ci32_const -2139062144;
  Ci32_and;
  Ci32_eqz;
end
}>.

        br_if 0 (;@2;)
      end
      local.get 3
      i32.const 255
      i32.and
      i32.eqz
      if  ;; label = @2
        local.get 2
        local.get 0
        i32.sub
        return
      end
      loop  ;; label = @2
        local.get 2
        i32.load8_u offset=1
        local.set 3
        local.get 2
        i32.const 1
        i32.add
        local.tee 1
        local.set 2
        local.get 3
        br_if 0 (;@2;)
      end
    end
    local.get 1
    local.get 0
    i32.sub)
*)
