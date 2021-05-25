(* Din strlenProof.v *)

(*(unsigned2signed
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
*)


(*Lemma four_byte_value_notation_load_equiv :
forall
(pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte),

pointer + 4 < memsize ->
execute_intruction i32_load
([i32 pointer],
loc_list,
glob_list,
func_list,
(memsize, mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)) =

([i32 (four_byte_value_notation pointer l str_start str_end mem1
       str_middle mem2)],
loc_list,
glob_list,
func_list,
(memsize, mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
Proof.
intros.
simpl.
unfold execute_i32_load.
unfold loose_integer_type.
unfold get_execution_stack_head.
unfold get_execution_stack.
unfold get_memory_size. unfold get_memory.
unfold "<?". rewrite H.
unfold four_byte_value_notation.
unfold get_local_var_list.
unfold get_global_var_list.
unfold get_func_list.
reflexivity.
Qed. *)

Lemma strlen_loop2_invariant :
forall
(pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_2 var_3 : Z)
(if_result : bool),

(pointer + 4) < memsize ->
if_result = (are_all_bytes_not_0_bitwise (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) ->
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
if if_result
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
********
simpl four_byte_value_notation.
unfold execute_intruction.
unfold execute_i32_load.
unfold get_execution_stack.
unfold get_execution_stack_head.
unfold loose_integer_type.
simpl get_memory_size.
unfold "<?". rewrite H.
simpl. 
reflexivity.
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
rewrite H1. reflexivity.
++ rewrite H0.
unfold are_all_bytes_not_0_bitwise.
rewrite H1.
apply E_Br_IfTrue. reflexivity. reflexivity. 
+ (*case false*) intros. apply E_Seq with
([i32 0],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2)) :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++ apply E_i32_eqz.
+++ auto.
+++ unfold execute_intruction. unfold execute_i32_eqz.
unfold execute_i32_eqz'. simpl.
rewrite H1. reflexivity.
++ rewrite H0.
unfold are_all_bytes_not_0_bitwise.
rewrite H1.
apply E_Br_IfFalse. reflexivity. reflexivity.
Qed.







































(* sfarsitul chestiilor in strlenProof.v *)