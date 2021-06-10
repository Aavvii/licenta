Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
(*From Coq Require Import Lia.*)
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.Znat.
From Coq Require Import ZArith.BinInt.
From Coq Require Import ZArith.Zbool.
(*From Coq Require Import Reals.RIneq.*)
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

Fixpoint len' (index : Z) (mem : MemoryList) (memsize : nat) : Z :=
match memsize with
| O => 0
| S (memsize') => if (( load_8_from_adress index mem) =? 0)
                then 0
                else (len' (index+1) mem memsize' + 1)
end.

Definition len (index : Z) (mem : MemoryList) (memsize : Z): Z :=
len' index mem (Z.to_nat memsize).

Fixpoint string_size (mem : MemoryList) : Z :=
match mem with
| [] => 0
| hd :: tl => (string_size tl) + 1
end.

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
(pointer n l str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte)
: Z :=
let byte1 :=
( (*signed2unsigned*)
          (load_8_from_adress (pointer+n)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) (*1*)) in
let byte2 := 
( (*signed2unsigned*)
          (load_8_from_adress (pointer+n+1)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) (*1*)) in
let byte3 :=
((*signed2unsigned*)
          (load_8_from_adress (pointer+n+2)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) (*1*)) in
let byte4 :=
((*signed2unsigned*)
          (load_8_from_adress (pointer+n+3)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) (*1*)) in

(unsigned2signed (byte1 + (Z.shiftl byte2 8) + (Z.shiftl byte3 16) + (Z.shiftl byte4 24)) 4).

(*
Lemma four_byte_value_notation_lt_429496729 :
forall (pointer n l str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte),

0 <= (load_8_from_adress (pointer + n)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)) < 255 ->
0 <= (load_8_from_adress (pointer + n + 1)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)) < 255 ->
0 <= (load_8_from_adress (pointer + n + 2)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)) < 255 ->
0 <= (load_8_from_adress (pointer + n + 3)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)) < 255 ->

(four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) < 429496729.
Proof.
intros.
unfold four_byte_value_notation.
(*Search ( Z.shiftl _).*)
unfold unsigned2signed.
induction (load_8_from_adress (pointer + n)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)).
- induction (load_8_from_adress (pointer + n + 1)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)).
-- induction (load_8_from_adress (pointer + n + 2)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)).
--- induction (load_8_from_adress (pointer + n + 3)
    (mem1 ++
     (pointer, str_start)
     :: str_middle ++ (pointer + l, str_end) :: mem2)).
---- simpl. reflexivity.
---- rewrite Z.shiftl_0_l.
     rewrite Z.add_0_l.
     unfold signBitIsOne.
unfold ">=?".
Search (Z.shiftl _ ).
destruct Z.shiftl_nonneg with (Z.pos p) 24.
Admitted.
(*destruct H2.
destruct H4.
----- apply H2.
----- apply Z.compare_gt_iff.*)
(*Search (_ + _).*)
(* Suma pe un numar de 4 biti este mereu un numar mai mic decat 429496729 *)
*)


(*Lemma four_byte_value_notation_and_255 :
forall n
(pointer l str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte),
load_8_from_adress pointer
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2) = n
->
(Z.land (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2) 255) = n.
Proof.
intros.
unfold four_byte_value_notation.
rewrite H.
unfold signed2unsigned.
Admitted.*)

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
          ( ( ((n - 16843009) + 4294967296) mod 4294967296 ))) 
       (-2139062144))
in
if op_result =? 0 then true else false.

Fixpoint all_chars_not_0 (str : list MemoryByte) : bool :=
match str with
| [] => true
| (hd_adr, hd_val) :: tl => if hd_val =? 0
                            then false
                            else all_chars_not_0 tl
end.


Lemma are_all_bytes_not_0_bitwise_one_bit_is_0 :
forall n,
Z.land n 255 = 0 \/ Z.land n 65280 = 0 ->
are_all_bytes_not_0_bitwise n = false.
Proof.
intros.
unfold are_all_bytes_not_0_bitwise.
destruct H.
Admitted.

Lemma four_byte_value_notation_AND_255 :
forall
(pointer l n str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte),
Z.land (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) 255
= (unsigned2signed (*(signed2unsigned*)
          (load_8_from_adress (pointer + n)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) (*1)*) 1).
Proof.
intros.
Admitted.

Lemma four_byte_value_notation_AND_65280 :
forall
(pointer n l str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte) ,
Z.land (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) 65280
= (unsigned2signed (signed2unsigned
          (load_8_from_adress (pointer+n+1)
             (mem1 ++
              (pointer, str_start)
              :: str_middle ++ (pointer + l, str_end) :: mem2)) 1) 1).
Proof.
intros.
Admitted.

(*
Eval compute in is_any_byte_0 (-2139062144).
Eval compute in is_any_byte_0 (-2147450752).
Eval compute in are_all_bytes_not_0_bitwise (-2139062144).
Eval compute in are_all_bytes_not_0_bitwise (-2147450752).
Eval compute in are_all_bytes_not_0_bitwise (197379).
*)

(*Lemma check_any_byte_zero :
(pointer + 4) < memsize ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
=[*)

Definition strlen_loop1_invariant_v1_cases
(pointer l str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte) :=
match ( (load_8_from_adress pointer
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ (pointer + l, str_end) :: mem2)) =? 0) with
| false  => (pointer +1)
| _ =>      (pointer)
end.
Definition strlen_loop1_invariant_br_cases
(pointer l str_start str_end : Z)
(mem1 str_middle mem2: list MemoryByte) :=
match ( (load_8_from_adress pointer
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ (pointer + l, str_end) :: mem2)) =? 0) with
| false  => match ((Z.land (pointer+1) 3) =? 0) with
           | true  => (SContinue)
           | false => (SBr L3)
          end
| _ =>  (SBr L1)
end.

Open Scope list_scope.

Lemma strlen_loop1_invariant_Continue :
forall
(pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_2 var_3 : Z),

(pointer) < memsize ->
((load_8_from_adress pointer
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ (pointer + l, str_end) :: mem2)) =? 0) = false ->
((Z.land (pointer+1) 3) =? 0) = true ->
0 <= pointer + 1 < 4294967296 ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
=[
(local.get (v1));
i32.load8_u;
i32.eqz;
(br_if (L1));
(local.get (v1));
i32.const 1;
i32.add;
(local.tee (v1));
i32.const 3;
i32.and;
br_if (L3)
]=>
([],
(v3, i32 var_3) :: (v2, i32 var_2) ::
    (v1, i32 (pointer+1)
) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
/ SContinue.
Proof.
intros.
apply E_Seq with ([i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
-- apply E_local_get. auto.
-- apply E_Seq with ([i32 (signed2unsigned (load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) 1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_i32_Load8_u. simpl.
    unfold execute_i32_load8_u.
    unfold get_execution_stack.
simpl.
unfold "<?". rewrite H.
simpl.
reflexivity.
reflexivity.
--- apply E_Seq with ([i32 0],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_i32_eqz.
----- reflexivity.
----- unfold execute_i32_eqz. unfold execute_instruction.
      unfold execute_i32_eqz. unfold execute_i32_eqz'.
      unfold get_execution_stack.
      rewrite signed2unsigned_of_not_0_is_not_0.
------ reflexivity.
------ apply H0.
------ left. split. reflexivity.
simpl. split. apply load_8_from_adress_loads_1_byte with 
pointer (mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2) ; reflexivity.
Search (_ >= _).
apply Zorder.Zge_trans with 0.
------- 
pose proof load_8_from_adress_loads_1_byte as load_byte.
destruct load_byte with pointer 
((mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2))
(load_8_from_adress pointer
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2)).
-------- reflexivity.
-------- apply H4.
------- discriminate.
(*
-------- reflexivity.
-------- Search (_ <> Lt). rewrite Z.compare_ge_iff.
*)
---- apply E_Seq with ([],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++ apply E_Br_IfFalse.
* reflexivity.
* reflexivity.
++ apply E_Seq with ([i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++ apply E_local_get. auto.
+++ apply E_Seq with ([i32 1; i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++ apply E_i32_const.
++++ apply E_Seq with ([i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++ apply E_i32_add.
* reflexivity.
* unfold execute_instruction.
  unfold execute_i32_add.
  unfold execute_i32_add'.
  simpl.
  rewrite Z.mod_small.
** reflexivity.
** apply H2.
+++++ apply E_Seq with ([i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++ apply E_local_tee.
* reflexivity.
* reflexivity.
++++++ apply E_Seq with ([i32 3; i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++++ apply E_i32_const.
+++++++ apply E_Seq with ([i32 (Z.land (pointer+1) 3)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++++ apply E_i32_and.
* reflexivity.
* reflexivity.
++++++++ apply E_Br_IfFalse.
** unfold State2Bool.
  unfold get_execution_stack.
  unfold get_execution_stack_head.
  unfold State2Bool'.
  rewrite H1. reflexivity.
** reflexivity.
Qed.

Lemma strlen_loop1_invariant_SBrL1 :
forall
(pointer n l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_0 var_2 var_2 var_3 : Z),

(pointer+n) < memsize ->
((load_8_from_adress (pointer+n)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ (pointer + l, str_end) :: mem2)) =? 0) = true ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 (pointer+n)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
=[
(local.get (v1));
i32.load8_u;
i32.eqz;
(br_if (L1));
(local.get (v1));
i32.const 1;
i32.add;
(local.tee (v1));
i32.const 3;
i32.and;
br_if (L3)
]=>
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 (pointer+n)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
/ SBr L1.
Proof.
intros.
apply E_Seq with ([i32 (pointer+n)],
(v3, i32 var_3)
:: (v2, i32 var_1) :: (v1, i32 (pointer + n)) :: (v0, i32 var_0) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)).
- apply E_local_get. auto.
- apply E_Seq with ([i32
(signed2unsigned
       (load_8_from_adress (pointer + n)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ (pointer + l, str_end) :: mem2)) 1)],
(v3, i32 var_3)
:: (v2, i32 var_1) :: (v1, i32 (pointer + n)) :: (v0, i32 var_0) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)).
-- apply E_i32_Load8_u.
--- unfold execute_instruction.
    unfold execute_i32_load8_u.
    simpl. unfold "<?". rewrite H.
    reflexivity.
--- auto.
-- apply E_Seq with ([i32 1],
(v3, i32 var_3)
:: (v2, i32 var_1) :: (v1, i32 (pointer + n)) :: (v0, i32 var_0) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_i32_eqz.
---- auto.
---- unfold execute_instruction.
     unfold execute_i32_eqz.
     simpl. rewrite Z.eqb_eq in H0.
     rewrite H0. auto.
--- apply E_SeqBr.
---- apply E_Br_IfTrue.
----- auto.
----- auto.
(*---- discriminate.*)
Qed.

Lemma strlen_loop1_invariant_SBrL3 :
forall
(pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_2 var_3 : Z),

(pointer) < memsize ->
((load_8_from_adress pointer
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ (pointer + l, str_end) :: mem2)) =? 0) = false ->
((Z.land (pointer+1) 3) =? 0) = false ->
0 <= pointer + 1 < 4294967296 ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
=[
(local.get (v1));
i32.load8_u;
i32.eqz;
(br_if (L1));
(local.get (v1));
i32.const 1;
i32.add;
(local.tee (v1));
i32.const 3;
i32.and;
br_if (L3)
]=>
([],
(v3, i32 var_3) :: (v2, i32 var_2) ::
    (v1, i32 (pointer+1)
) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
/ SBr L3.
Proof.
intros.
apply E_Seq with ([i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
-- apply E_local_get. auto.
-- apply E_Seq with ([i32 (signed2unsigned (load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) 1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_i32_Load8_u. simpl.
    unfold execute_i32_load8_u.
    unfold get_execution_stack.
simpl.
unfold "<?". rewrite H.
simpl.
reflexivity.
reflexivity.
--- apply E_Seq with ([i32 0],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_i32_eqz.
----- reflexivity.
----- unfold execute_i32_eqz. unfold execute_instruction.
      unfold execute_i32_eqz. unfold execute_i32_eqz'.
      unfold get_execution_stack.
      rewrite signed2unsigned_of_not_0_is_not_0.
------ reflexivity.
------ apply H0.
------ left. split. reflexivity.
simpl. split. apply load_8_from_adress_loads_1_byte with 
pointer (mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2) ; reflexivity.
Search (_ >= _).
apply Zorder.Zge_trans with 0.
------- 
pose proof load_8_from_adress_loads_1_byte as load_byte.
destruct load_byte with pointer 
((mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2))
(load_8_from_adress pointer
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2)).
-------- reflexivity.
-------- apply H4.
------- discriminate.
---- apply E_Seq with ([],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++ apply E_Br_IfFalse.
* reflexivity.
* reflexivity.
++ apply E_Seq with ([i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++ apply E_local_get. auto.
+++ apply E_Seq with ([i32 1; i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++ apply E_i32_const.
++++ apply E_Seq with ([i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++ apply E_i32_add.
* reflexivity.
* simpl.
  unfold execute_i32_add.
  simpl.
  rewrite Z.mod_small.
** reflexivity.
** apply H2.
+++++ apply E_Seq with ([i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++ apply E_local_tee.
* reflexivity.
* reflexivity.
++++++ apply E_Seq with ([i32 3; i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++++ apply E_i32_const.
+++++++ apply E_Seq with ([i32 (Z.land (pointer+1) 3)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++++ apply E_i32_and.
* reflexivity.
* reflexivity.
++++++++ (*case_eq ((Z.land (pointer+1) 3) =? 0).
* (* case ((Z.land (pointer+1) 3) =? 0) = true*)
intros.
apply Z.eqb_eq in H1.
rewrite H1.
unfold strlen_loop1_invariant_v1_cases.
(*rewrite H1.*)
apply E_Br_IfFalse.
** unfold State2Bool.
  unfold get_execution_stack.
  unfold get_execution_stack_head.
  unfold State2Bool'.
  rewrite H1. reflexivity.
** reflexivity.
* (* case ((Z.land (pointer+1) 3) =? 0) = false*)
intros. unfold strlen_loop1_invariant_br_cases.
apply Z.eqb_eq in H1. rewrite H1.
unfold strlen_loop1_invariant_v1_cases.
rewrite H0.*)
apply E_Br_IfTrue.
** unfold State2Bool.
  unfold get_execution_stack.
  unfold get_execution_stack_head.
  unfold State2Bool'.
  rewrite H1. reflexivity.
** reflexivity.
Qed.

Lemma strlen_loop1_invariant :
forall
(pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_2 var_3 : Z)
(if_result : bool),

(pointer) < memsize ->
0 <= pointer + 1 < 4294967296 ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
=[
(local.get (v1));
i32.load8_u;
i32.eqz;
(br_if (L1));
(local.get (v1));
i32.const 1;
i32.add;
(local.tee (v1));
i32.const 3;
i32.and;
br_if (L3)
]=>
([],
(v3, i32 var_3) :: (v2, i32 var_2) ::
    (v1, i32 
    (strlen_loop1_invariant_v1_cases pointer l str_start str_end mem1 str_middle mem2)
) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))
/ (strlen_loop1_invariant_br_cases pointer l str_start str_end mem1 str_middle mem2)
.
Proof.
intros.
case_eq ((load_8_from_adress pointer
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ (pointer + l, str_end) :: mem2)) =? 0).
- intros. apply E_Seq with ([i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
-- apply E_local_get. auto.
-- apply E_Seq with ([i32 (signed2unsigned (load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) 1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_i32_Load8_u. simpl.
    unfold execute_i32_load8_u.
    unfold get_execution_stack.
simpl.
unfold "<?". rewrite H.
rewrite Z.eqb_eq in H1.
simpl.
rewrite H1.
unfold signed2unsigned. simpl. reflexivity.
reflexivity.
--- apply E_Seq with ([i32 1],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_i32_eqz.
----- reflexivity.
----- unfold execute_instruction.
      unfold execute_i32_eqz.
      unfold execute_i32_eqz'.
      simpl. rewrite Z.eqb_eq in H1.
      rewrite H1. simpl. reflexivity.
---- unfold strlen_loop1_invariant_br_cases.
     rewrite H1.
     apply E_SeqBr.
     apply E_Br_IfTrue.
----- reflexivity.
----- unfold strlen_loop1_invariant_v1_cases. rewrite H1. reflexivity.
(*----- discriminate.*)
- intros. intros. apply E_Seq with ([i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
-- apply E_local_get. auto.
-- apply E_Seq with ([i32 (signed2unsigned (load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) 1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_i32_Load8_u. simpl.
    unfold execute_i32_load8_u.
    unfold get_execution_stack.
simpl.
unfold "<?". rewrite H.
simpl.
reflexivity.
reflexivity.
--- apply E_Seq with ([i32 0],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_i32_eqz.
----- reflexivity.
----- unfold execute_i32_eqz. unfold execute_instruction.
      unfold execute_i32_eqz. unfold execute_i32_eqz'.
      unfold get_execution_stack.
      rewrite signed2unsigned_of_not_0_is_not_0.
------ reflexivity.
------ apply H1.
------ left. split. reflexivity.
simpl. split. apply load_8_from_adress_loads_1_byte with 
pointer (mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2) ; reflexivity.
Search (_ >= _).
apply Zorder.Zge_trans with 0.
------- 
pose proof load_8_from_adress_loads_1_byte as load_byte.
destruct load_byte with pointer 
((mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2))
(load_8_from_adress pointer
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2)).
-------- reflexivity.
-------- apply H3.
------- discriminate.
---- apply E_Seq with ([],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++ apply E_Br_IfFalse.
* reflexivity.
* reflexivity.
++ apply E_Seq with ([i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++ apply E_local_get. auto.
+++ apply E_Seq with ([i32 1; i32 pointer],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++ apply E_i32_const.
++++ apply E_Seq with ([i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++ apply E_i32_add.
* reflexivity.
* simpl. unfold execute_i32_add. simpl.
  rewrite Z.mod_small.
** reflexivity.
** apply H0.
+++++ apply E_Seq with ([i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++ apply E_local_tee.
* reflexivity.
* reflexivity.
++++++ apply E_Seq with ([i32 3; i32 (pointer+1)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++++ apply E_i32_const.
+++++++ apply E_Seq with ([i32 (Z.land (pointer+1) 3)],
(v3, i32 var_3)
:: (v2, i32 var_2)
   :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++++ apply E_i32_and.
* reflexivity.
* reflexivity.
++++++++ case_eq ((Z.land (pointer+1) 3) =? 0).
* (* case ((Z.land (pointer+1) 3) =? 0) = true*)
intros. unfold strlen_loop1_invariant_br_cases.
rewrite H1. rewrite H2.
unfold strlen_loop1_invariant_v1_cases.
rewrite H1.
apply E_Br_IfFalse.
** unfold State2Bool.
  unfold get_execution_stack.
  unfold get_execution_stack_head.
  unfold State2Bool'.
  rewrite H2. reflexivity.
** reflexivity.
* (* case ((Z.land (pointer+1) 3) =? 0) = false*)
intros. unfold strlen_loop1_invariant_br_cases.
rewrite H1. rewrite H2.
unfold strlen_loop1_invariant_v1_cases.
rewrite H1.
apply E_Br_IfTrue.
** unfold State2Bool.
  unfold get_execution_stack.
  unfold get_execution_stack_head.
  unfold State2Bool'.
  rewrite H2. reflexivity.
** reflexivity.
Qed.

Lemma strlen_loop2_invariant_Continue :
forall
(pointer n l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_0 var_2 var_3 : Z),

(pointer + n + 4) < memsize ->
(are_all_bytes_not_0_bitwise (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) = false ->
0 <= pointer + n + 4 < 4294967296 ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 (pointer+n)) :: (v0, i32 var_0) :: loc_list,
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
(four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2))
    :: (v2, i32 (pointer+n))
       :: (v1, i32 (pointer+n +4)) :: (v0, i32 var_0) :: loc_list,
    glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
    (memsize,
    mem1 ++
    [(pointer, str_start)] ++
    str_middle ++ [(pointer + l, str_end)] ++ mem2)) / SContinue.
Proof.
intros.
apply E_Seq with ([i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 (pointer+n)) :: (v0, i32 var_0) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
* apply E_local_get. auto.
* apply E_Seq with ([i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 (pointer+n)) :: (v0, i32 var_0) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
** apply E_local_tee. auto. auto.
** apply E_Seq with ([i32 4; i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 (pointer+n)) :: (v0, i32 var_0) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_i32_const.
*** apply E_Seq with ([i32 (pointer+n+4)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 (pointer+n)) :: (v0, i32 var_0) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_i32_add. auto.
simpl.
unfold execute_i32_add.
simpl.
rewrite Z.mod_small.
- reflexivity.
- apply H1.
**** apply E_Seq with ([], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_local_set. auto. auto.
***** apply E_Seq with ([i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_get. auto.
****** apply E_Seq with ([i32
(four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)
], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_i32_Load.
******** unfold execute_instruction. unfold execute_i32_load. simpl.
unfold "<?". rewrite H. simpl.
unfold four_byte_value_notation. simpl.
 reflexivity.
******** reflexivity.
******* apply E_Seq with
([i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******** apply E_local_tee.
********* reflexivity.
********* reflexivity.
******** apply E_Seq with
([i32 (-1); i32 (four_byte_value_notation (pointer)n l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation (pointer)n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********* apply E_i32_const.
********* apply E_Seq with
([i32 ( Z.lxor (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********** apply E_i32_xor.
*********** reflexivity.
*********** reflexivity.
********** apply E_Seq with
([i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2); i32 ( Z.lxor (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*********** apply E_local_get. auto.
*********** apply E_Seq with
([i32 16843009; i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2); i32 ( Z.lxor (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************ apply E_i32_const.
************ apply E_Seq with
([i32 ((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296); i32 ( Z.lxor (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************* apply E_i32_sub. reflexivity.
simpl.
unfold execute_i32_sub.
simpl.
reflexivity.
************* apply E_Seq with
([i32 ( Z.land  ( Z.lxor (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296) )],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************** apply E_i32_and. auto. auto.
************** apply E_Seq with
([i32 (-2139062144);i32 ( Z.land  ( Z.lxor (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296) )],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*************** apply E_i32_const.
*************** apply E_Seq with
([i32 (Z.land ( Z.land  ( Z.lxor (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296) ) (-2139062144))],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**************** apply E_i32_and. auto. auto.
**************** simpl.
case_eq(Z.land
         (Z.land
            (Z.lxor
               (four_byte_value_notation (pointer) n l str_start
                  str_end mem1 str_middle mem2) 
               (-1))

            (((four_byte_value_notation pointer n l str_start str_end
              mem1 str_middle mem2) - 16843009 + 4294967296)
           mod 4294967296))
        (-2139062144)
      =? 0).
+ (*case true*) intros.
unfold are_all_bytes_not_0_bitwise in H0.
rewrite H2 in H0. inversion H0.
+ (*case false*) intros. apply E_Seq with
([i32 0],
( (v3, i32 (four_byte_value_notation (pointer) n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 var_0) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++ apply E_i32_eqz.
+++ auto.
+++ unfold execute_instruction. unfold execute_i32_eqz.
unfold execute_i32_eqz'. simpl.
rewrite H2. reflexivity.
++ apply E_Br_IfFalse. reflexivity. reflexivity.
Qed.


Lemma strlen_loop2_invariant_Br :
forall
(pointer n l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_2 var_3 : Z),

((pointer+n) + 4) < memsize ->
(are_all_bytes_not_0_bitwise (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) = true ->
0 <= pointer + n + 4 < 4294967296 ->
([],
(v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 (pointer+n)) :: (v0, i32 (pointer+n)) :: loc_list,
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
(four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2))
    :: (v2, i32 ((pointer+n)))
       :: (v1, i32 ((pointer+n) +4)) :: (v0, i32 (pointer+n)) :: loc_list,
    glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
    (memsize,
    mem1 ++
    [(pointer, str_start)] ++
    str_middle ++ [(pointer + l, str_end)] ++ mem2)) / SBr L2.
Proof.
intros.
apply E_Seq with ([i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 var_2) :: (v1, i32 (pointer+n)) :: (v0, i32 (pointer+n)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
* apply E_local_get. auto.
* apply E_Seq with ([i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 (pointer+n)) :: (v0, i32 (pointer+n)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
** apply E_local_tee. auto. auto.
** apply E_Seq with ([i32 4; i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 (pointer+n)) :: (v0, i32 (pointer+n)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_i32_const.
*** apply E_Seq with ([i32 ((pointer+n)+4)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 (pointer+n)) :: (v0, i32 (pointer+n)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_i32_add. auto. auto.
simpl.
unfold execute_i32_add.
simpl.
rewrite Z.mod_small.
- reflexivity.
- apply H1.
**** apply E_Seq with ([], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_local_set. auto. auto.
***** apply E_Seq with ([i32 (pointer+n)], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_get. auto.
****** apply E_Seq with ([i32
(four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)
], ( (v3, i32 var_3) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_i32_Load.
******** unfold execute_instruction. unfold execute_i32_load. simpl.
unfold "<?". rewrite H. simpl. reflexivity.
******** reflexivity.
******* apply E_Seq with
([i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******** apply E_local_tee.
********* reflexivity.
********* reflexivity.
******** apply E_Seq with
([i32 (-1); i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********* apply E_i32_const.
********* apply E_Seq with
([i32 ( Z.lxor (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
********** apply E_i32_xor.
*********** reflexivity.
*********** reflexivity.
********** apply E_Seq with
([i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2); i32 ( Z.lxor (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*********** apply E_local_get. auto.
*********** apply E_Seq with
([i32 16843009; i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2); i32 ( Z.lxor (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************ apply E_i32_const.
************ apply E_Seq with
([i32 ((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296); i32 ( Z.lxor (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) (-1) )],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************* apply E_i32_sub. reflexivity.
simpl.
unfold execute_i32_sub.
simpl.
 reflexivity.
************* apply E_Seq with
([i32 ( Z.land  ( Z.lxor (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296) )],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
************** apply E_i32_and. auto. auto.
************** apply E_Seq with
([i32 (-2139062144);i32 ( Z.land  ( Z.lxor (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296) )],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*************** apply E_i32_const.
*************** apply E_Seq with
([i32 (Z.land ( Z.land  ( Z.lxor (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) (-1))((four_byte_value_notation pointer n l str_start str_end mem1
        str_middle mem2 - 16843009 + 4294967296) mod 4294967296) ) (-2139062144))],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2)) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**************** apply E_i32_and. auto. auto.
**************** simpl.
case_eq(Z.land
         (Z.land
            (Z.lxor
               (four_byte_value_notation pointer n l str_start
                  str_end mem1 str_middle mem2) 
               (-1))
            (((four_byte_value_notation pointer n l str_start str_end
               mem1 str_middle mem2 - 16843009) + 4294967296 ) mod 4294967296 )) 
         (-2139062144) =? 0).
+ (*case true*) intros.
apply E_Seq with
([i32 1],
( (v3, i32 (four_byte_value_notation pointer n l str_start str_end mem1 str_middle mem2) ) :: (v2, i32 (pointer+n)) :: (v1, i32 ((pointer+n)+4)) :: (v0, i32 (pointer+n)) :: loc_list),
glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++ apply E_i32_eqz.
+++ auto.
+++ unfold execute_instruction. unfold execute_i32_eqz.
unfold execute_i32_eqz'. simpl.
rewrite H2. reflexivity.
++ apply E_Br_IfTrue. reflexivity. reflexivity.

+ (*case false*) intros.
unfold are_all_bytes_not_0_bitwise in H0.
rewrite H2 in H0. inversion H0.
Qed.


(*Lemma strlen_loop2_invariant :
forall
(pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_2 var_3 : Z)
(if_result : bool),

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
then (SBr L2) else SContinue.
Proof.
intros.
case_eq (are_all_bytes_not_0_bitwise
    (four_byte_value_notation pointer l str_start str_end mem1
       str_middle mem2)).
+ intros.
apply strlen_loop2_invariant_Br.
++ apply H.
++ apply H0.
+ intros.
apply strlen_loop2_invariant_Continue.
++ apply H.
++ apply H0.
Qed.*)

Lemma strlen_loop3_invariant_continue :
forall
(pointer l str_start str_end: Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_0 var_1 var_3 : Z)
(n : Z),

(pointer + n + 1) < memsize ->
(load_8_from_adress (pointer + n + 1)
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) = 0 ->
0 <= pointer + n + 1 < 4294967296 ->
([],
(v3, i32 var_3) :: (v2, i32 (pointer + n)) :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer+l, str_end)] ++ mem2))
=[
(local.get (v2));
(i32.load8_u offset=1);
(local.set (v3));
(local.get (v2));
i32.const 1;
i32.add;
(local.tee (v1));
(local.set (v2));
(local.get (v3));
br_if (L2)
]=>([],
(v3, i32 
(signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1)
) :: (v2, i32 (pointer+n+1)) :: (v1, i32 (pointer+n+1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer+l, str_end)] ++ mem2))
/ SContinue.
Proof.
intros.
apply E_Seq with ([i32 (pointer + n)],
(v3, i32 var_3)
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
- apply E_local_get. auto.
- apply E_Seq with ([
i32 (signed2unsigned (load_8_from_adress (pointer + n + 1)
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1)],
(v3, i32 var_3)
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
-- apply E_i32_Load8_u_offset.
* unfold execute_instruction.
  unfold execute_i32_load8_u_offset.
  simpl.
  unfold "<?". rewrite H. reflexivity.
* reflexivity.
-- apply E_Seq with ([],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer + n + 1)
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
--- apply E_local_set. auto. auto.
--- apply E_Seq with ([i32 (pointer + n)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
---- apply E_local_get. auto.
---- apply E_Seq with ([i32 1; i32 (pointer + n)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
----- apply E_i32_const.
----- apply E_Seq with ([i32 (pointer + n + 1)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
------ apply E_i32_add.
* auto.
* unfold execute_instruction.
  unfold execute_i32_add.
  simpl.
  unfold execute_i32_add.
  simpl.
  rewrite Z.mod_small.
** reflexivity.
** apply H1.
------ apply E_Seq with ([i32 (pointer + n + 1)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 (pointer + n + 1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
------- apply E_local_tee. auto. auto.
------- apply E_Seq with ([],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n + 1))
   :: (v1, i32 (pointer + n + 1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
-------- apply E_local_set. auto. auto.
-------- apply E_Seq with ([
i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n + 1))
   :: (v1, i32 (pointer + n + 1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
--------- apply E_local_get. auto.
---------
  rewrite H0.
  apply E_Br_IfFalse.
* unfold State2Bool. simpl. reflexivity.
* auto.
Qed.

Lemma strlen_loop3_invariant :
forall
(pointer l str_start str_end: Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z)
(mem1 str_middle mem2: list MemoryByte)
(var_0 var_1 var_3 : Z)
(n : Z)
(if_condition : Z),

(pointer + n + 1) < memsize ->
if_condition = (load_8_from_adress (pointer + n + 1)
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) ->
0 <= pointer + n + 1 < 4294967296 ->
([],
(v3, i32 var_3) :: (v2, i32 (pointer + n)) :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer+l, str_end)] ++ mem2))
=[
(local.get (v2));
(i32.load8_u offset=1);
(local.set (v3));
(local.get (v2));
i32.const 1;
i32.add;
(local.tee (v1));
(local.set (v2));
(local.get (v3));
br_if (L2)
]=>([],
(v3, i32 
(signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1)
) :: (v2, i32 (pointer+n+1)) :: (v1, i32 (pointer+n+1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer+l, str_end)] ++ mem2))
/ if if_condition =? 0 then
 SContinue else SBr L2.
Proof.
intros.
apply E_Seq with ([i32 (pointer + n)],
(v3, i32 var_3)
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
- apply E_local_get. auto.
- apply E_Seq with ([
i32 (signed2unsigned (load_8_from_adress (pointer + n + 1)
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1)],
(v3, i32 var_3)
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
-- apply E_i32_Load8_u_offset.
* unfold execute_instruction.
  unfold execute_i32_load8_u_offset.
  simpl.
  unfold "<?". rewrite H. reflexivity.
* reflexivity.
-- apply E_Seq with ([],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer + n + 1)
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
--- apply E_local_set. auto. auto.
--- apply E_Seq with ([i32 (pointer + n)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
---- apply E_local_get. auto.
---- apply E_Seq with ([i32 1; i32 (pointer + n)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
----- apply E_i32_const.
----- apply E_Seq with ([i32 (pointer + n + 1)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 var_1) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
------ apply E_i32_add.
* auto.
* unfold execute_instruction.
  unfold execute_i32_add.
  simpl.
  unfold execute_i32_add.
  simpl.
  rewrite Z.mod_small.
** reflexivity.
** apply H1.

------ apply E_Seq with ([i32 (pointer + n + 1)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n))
   :: (v1, i32 (pointer + n + 1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
------- apply E_local_tee. auto. auto.
------- apply E_Seq with ([],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n + 1))
   :: (v1, i32 (pointer + n + 1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
-------- apply E_local_set. auto. auto.
-------- apply E_Seq with ([
i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1)],
(v3, i32 (signed2unsigned (load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) 1))
:: (v2, i32 (pointer + n + 1))
   :: (v1, i32 (pointer + n + 1)) :: (v0, i32 var_0) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer+l, str_end)] ++ mem2)).
--------- apply E_local_get. auto.
--------- case_eq((load_8_from_adress (pointer+n+1)
          (mem1 ++
           (pointer, str_start)
           :: str_middle ++ [(pointer+l, str_end)] ++ mem2)) =? 0).
+ intros.
  rewrite H0.
  rewrite H2.
  apply E_Br_IfFalse.
* unfold State2Bool. simpl.
  rewrite Z.eqb_eq in H2.
  simpl in H2.
  rewrite H2.
  simpl.
  reflexivity.
* unfold remove_execution_stack_head.
  simpl.
  rewrite Z.eqb_eq in H2.
  simpl in H2.
  rewrite H2.
  unfold signed2unsigned.
  simpl.
  reflexivity.
+ intros. rewrite H0. rewrite H2. apply E_Br_IfTrue.
  unfold State2Bool. simpl.
  rewrite signed2unsigned_of_not_0_is_not_0.
* reflexivity.
* apply H2.
* left. split.
** reflexivity.
** split.
*** apply load_8_from_adress_loads_1_byte with 
(pointer+n+1) ((mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)). reflexivity.
*** apply Zorder.Zge_trans with 0.
pose proof load_8_from_adress_loads_1_byte as load_byte.
destruct load_byte with (pointer + n + 1)
((mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2))
(load_8_from_adress (pointer + n + 1)
  (mem1 ++
   (pointer, str_start)
   :: str_middle ++ (pointer + l, str_end) :: mem2)).
reflexivity.
apply H4.
discriminate.

(* apply load_8_from_adress_loads_1_byte with 
(pointer+n+1) ((mem1 ++
   (pointer, str_start)
   :: str_middle ++ [(pointer+l, str_end)] ++ mem2)).
reflexivity.*)
* unfold remove_execution_stack_head.
  simpl.
  reflexivity.
Qed.

Lemma strlen_works_on_empty_string :
forall (pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z) (mem1 str_middle mem2: list MemoryByte)
(len_res : Z),

len_res = (len pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) memsize) ->
pointer < memsize ->
get_function_by_name strlen ([i32 pointer], loc_list, glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) = fun_strlen ->
pointer +4 < memsize ->
(( load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) =? 0) = true ) ->
0 <= pointer + 4 < 4294967296 ->

exists (var1_fin var_2fin var_3fin : Z),
([i32 pointer], loc_list, glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) =[
CCall strlen
]=>([i32 (len_res)], ( (v3, i32 (var_3fin))::(v2, i32 var_2fin)::(v1 ,i32 var1_fin)::(v0 ,i32 pointer)::loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2),  (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) / SContinue.
Proof.
intros pointer l str_start str_end.
intros loc_list glob_list.
intros func_list1 func_list2.
intros memsize.
intros mem1 str_middle mem2.
intros len_res.
intros len_res_val.
intros str_can_load.
intros fun_strlen_exists.
intros can_load_i32.
intros str_end_is_zero.
intros pointer_limits.
(*
Nu mai e nevoie de asta fiindca acum tratez doar casul in care stringul e 0
case_eq ( load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) ?= 0).*)

+ (*cazul load_8_from_adress = 0*)
  case_eq ((Z.land pointer 3) =? 0).
(*programul fsce and cu 3 ca sa verifice ca
numarul e multiplu de 4 si sa poata face
eficient load de 4 biti odata (in asm)*)

(* Demonstratia ca Strlen = 0 DACA
load_8_from_adress = 0 si
(Z.land pointer 3) = 0*)

++ intros pointer_land_3.
exists (pointer+4).
exists pointer.
exists (four_byte_value_notation pointer 0 l str_start str_end mem1
       str_middle mem2).
apply E_Call with ([], ((v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) SReturn.
- unfold set_function_params. rewrite fun_strlen_exists. simpl. reflexivity.
- unfold get_function_body. rewrite fun_strlen_exists. simpl.
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
(*
apply E_Seq with ([i32 0],
( (v3, i32 (four_byte_value_notation pointer l str_start str_end mem1 str_middle mem2))
  :: (v2, i32 pointer) :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*)
------- apply E_SeqHasReturn.
+++ apply E_BlockReturn.
apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++ apply E_local_get. auto.
++++ apply E_Seq with ([i32 3; i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++++ apply E_i32_const.
+++++ apply E_Seq with ([i32 0], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++++ apply E_i32_and.
* reflexivity.
* unfold execute_instruction. unfold execute_i32_and. unfold execute_i32_and'.
simpl.
rewrite Z.eqb_eq in pointer_land_3. (* <- Lema utila *)
rewrite pointer_land_3. reflexivity.
++++++ apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 (pointer+0)) :: (v0, i32 (pointer+0)) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++++++ apply E_IfFalse.
* reflexivity.
* Search (_ + 0). rewrite Z.add_0_r.
 reflexivity.
+++++++ apply E_Seq with ([],
    (v3, i32
(four_byte_value_notation pointer 0 l str_start str_end mem1 str_middle mem2))
    :: (v2, i32 (pointer+0))
       :: (v1, i32 (pointer+0+4)) :: (v0, i32 (pointer+0)) :: loc_list,
    glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
    (memsize,
    mem1 ++
    [(pointer, str_start)] ++
    str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++++ apply E_LoopOnce.
* apply strlen_loop2_invariant_Continue.
** rewrite Z.add_0_r.
   apply can_load_i32.
** apply are_all_bytes_not_0_bitwise_one_bit_is_0. (* !!! *)
left.
rewrite four_byte_value_notation_AND_255.         (* !!! *)
apply Z.eqb_eq in str_end_is_zero. simpl in str_end_is_zero.
rewrite Z.add_0_r.
rewrite str_end_is_zero. auto.
** rewrite Z.add_0_r. apply pointer_limits.

++++++++ apply E_Seq with
([i32
  (four_byte_value_notation pointer 0 l str_start str_end mem1
     str_middle mem2)],
(v3,
i32
  (four_byte_value_notation pointer 0 l str_start str_end mem1
     str_middle mem2))
:: (v2, i32 pointer)
   :: (v1, i32 (pointer + 4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++++++ rewrite Z.add_0_r. apply E_local_get. auto.
+++++++++ apply E_Seq with
([i32 255; i32
  (four_byte_value_notation pointer 0 l str_start str_end mem1
     str_middle mem2)],
(v3,
i32
  (four_byte_value_notation pointer 0 l str_start str_end mem1
     str_middle mem2))
:: (v2, i32 pointer)
   :: (v1, i32 (pointer + 4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++++++ apply E_i32_const.
++++++++++ apply E_Seq with
([i32 (Z.land
  (four_byte_value_notation pointer 0 l str_start str_end mem1
     str_middle mem2) 255)],
(v3,
i32
  (four_byte_value_notation pointer 0 l str_start str_end mem1
     str_middle mem2))
:: (v2, i32 pointer)
   :: (v1, i32 (pointer + 4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
+++++++++++ apply E_i32_and. reflexivity. auto.
+++++++++++ apply E_Seq with
([i32 1],
(v3,
i32
  (four_byte_value_notation pointer 0 l str_start str_end mem1
     str_middle mem2))
:: (v2, i32 pointer)
   :: (v1, i32 (pointer + 4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
str_middle ++ [(pointer + l, str_end)] ++ mem2)).
++++++++++++ apply E_i32_eqz.
* reflexivity.
* unfold execute_instruction.
unfold execute_i32_eqz.
unfold execute_i32_eqz'.
simpl.
rewrite four_byte_value_notation_AND_255.
apply Z.eqb_eq in str_end_is_zero. simpl in str_end_is_zero.
rewrite Z.add_0_r.
rewrite str_end_is_zero. simpl.
reflexivity.
++++++++++++ apply E_SeqHasReturn.
+++++++++++++ apply E_IfTrueReturn.
* reflexivity.
* apply E_Seq with
([i32 pointer],
  (v3,
  i32
    (four_byte_value_notation pointer 0 l str_start str_end mem1
       str_middle mem2))
  :: (v2, i32 pointer)
     :: (v1, i32 (pointer + 4)) :: (v0, i32 pointer) :: loc_list,
  glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
  (memsize,
  mem1 ++
  [(pointer, str_start)] ++
  str_middle ++ [(pointer + l, str_end)] ++ mem2)).
** apply E_local_get. auto.
** apply E_Seq with
([i32 pointer; i32 pointer],
  (v3,
  i32
    (four_byte_value_notation pointer 0 l str_start str_end mem1
       str_middle mem2))
  :: (v2, i32 pointer)
     :: (v1, i32 (pointer + 4)) :: (v0, i32 pointer) :: loc_list,
  glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
  (memsize,
  mem1 ++
  [(pointer, str_start)] ++
  str_middle ++ [(pointer + l, str_end)] ++ mem2)).
*** apply E_local_get. auto.
*** apply E_SeqExpectReturn with
([i32 0],
  (v3,
  i32
    (four_byte_value_notation pointer 0 l str_start str_end mem1
       str_middle mem2))
  :: (v2, i32 pointer)
     :: (v1, i32 (pointer + 4)) :: (v0, i32 pointer) :: loc_list,
  glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
  (memsize,
  mem1 ++
  [(pointer, str_start)] ++
  str_middle ++ [(pointer + l, str_end)] ++ mem2)).
**** apply E_i32_sub.
***** auto.
***** unfold execute_instruction. unfold execute_i32_sub.
unfold execute_i32_sub'. simpl.
rewrite Z.sub_diag.
reflexivity.
****
rewrite len_0 in len_res_val. simpl. auto;rewrite len_res_val; auto.
***** apply E_Return.
***** trivial.
***** trivial.
***** trivial.
***** trivial.
***** trivial.
***** trivial.
***** trivial.
***** apply Z.eqb_eq in str_end_is_zero. rewrite str_end_is_zero. reflexivity.

(* Demonstratia ca Strlen = 0 DACA
load_8_from_adress = 0 si
(Z.land pointer 3) <> 0*)

++ intros pointer_land_3.
exists pointer.
exists 0.
exists 0.
apply E_Call with ([], ((v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) SContinue.
- unfold set_function_params. rewrite fun_strlen_exists. simpl. reflexivity.
- unfold get_function_body. rewrite fun_strlen_exists. simpl.
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
(* ---- *)
------- apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++ apply E_Block. right.
    apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++ apply E_local_get. auto.
++++ apply E_Seq with ([i32 3; i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
+++++ apply E_i32_const.
+++++ apply E_Seq with ([i32 (Z.land pointer 3)], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
++++++ intros. apply E_i32_and. reflexivity. unfold execute_instruction. unfold execute_i32_and. unfold execute_i32_and'. simpl. reflexivity.
++++++ apply E_SeqBr. apply E_IfTrue.
+++++++ unfold State2Bool. unfold State2Bool'. unfold get_execution_stack_head. unfold get_execution_stack. rewrite pointer_land_3. reflexivity.
+++++++ apply E_LoopOnceBrOther. simpl. apply E_Seq with (([i32 pointer], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ (strlen, fun_strlen) :: func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)))).
++++++++ apply E_local_get. auto.
++++++++ apply E_Seq with (([i32 0], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ (strlen, fun_strlen) :: func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)))).
+++++++++ apply E_i32_Load8_u.
          unfold execute_instruction.
          unfold execute_i32_load8_u. simpl.
          unfold "<?". unfold "<" in pointer_land_3. rewrite str_can_load.
          unfold signed2unsigned. unfold "<?". apply Z.eqb_eq in str_end_is_zero. simpl. simpl in str_end_is_zero. rewrite str_end_is_zero.
++++++++++ reflexivity.
++++++++++ reflexivity.
+++++++++ apply E_Seq with (([i32 1], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ (strlen, fun_strlen) :: func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)))).
++++++++++ apply E_i32_eqz.
+++++++++++ reflexivity.
+++++++++++ unfold execute_instruction. unfold execute_i32_eqz.
            unfold execute_i32_eqz'. simpl. reflexivity.
++++++++++ apply E_SeqBr. apply E_Br_IfTrue. reflexivity. reflexivity. (* discriminate.*)
++++++++ discriminate.
+++++++ discriminate.
(*+++++++ discriminate.*)
+++ apply E_Seq with ([i32 pointer], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))).
++++ apply E_local_get. auto.
++++ apply E_Seq with ([i32 pointer; i32 pointer], (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list, glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2, (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2))).
+++++ apply E_local_get. auto.
+++++ apply E_i32_sub. auto.
      unfold execute_instruction.
      unfold execute_i32_sub.
      unfold execute_i32_sub'. simpl. rewrite Z.sub_diag.
      rewrite len_0 in len_res_val; auto.
++++++ rewrite len_res_val. simpl. (*rewrite Z.add_0_r.*) reflexivity.
++++++ apply Z.eqb_eq in str_end_is_zero. rewrite str_end_is_zero. reflexivity.
Qed.

(*
+ (*cazul load_8_from_adress < 0*) intros.
unfold len. unfold len'.
simpl. simpl in H3.

Eval compute in (len pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)).

(*apply TEMPORARELY_ADMITTED.*)
Admitted.
*)

Lemma strlen_works_on_non_empty_string :
forall (pointer l str_start str_end : Z)
(loc_list glob_list : VariableList)
(func_list1 func_list2 : FunctionList)
(memsize : Z) (mem1 str_middle mem2: list MemoryByte)
(len_res : Z),

( load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) =? 0) = false ->
(*len_res = (len pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) memsize) ->*)
get_function_by_name strlen ([i32 pointer], loc_list, glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) = fun_strlen ->
pointer + 4 < memsize ->
pointer + 4*(l+1) < memsize ->
(( load_8_from_adress (pointer + l) (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) =? 0) = true ) ->
l = (string_size str_middle) + 1 ->
pointer + l < memsize ->
all_chars_not_0 str_middle = true ->
0 <= pointer < 4294967296 ->
0 <= pointer + (l) + 4 < 4294967296 ->

exists (var1_fin var_2fin var_3fin : Z),
([i32 pointer], loc_list, glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) =[
CCall strlen
]=>([i32 (l)], ( (v3, i32 (var_3fin))::(v2, i32 var_2fin)::(v1 ,i32 var1_fin)::(v0 ,i32 pointer)::loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2),  (memsize, (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) / SContinue.
Proof.
intros pointer l str_start str_end.
intros loc_list glob_list.
intros func_list1 func_list2.
intros memsize.
intros mem1 str_middle mem2.
intros len_res.
intros str_start_not_zero.
intros fun_strlen_exists.
intros can_load_i32.
intros str_max_mem_need.
intros str_end_is_zero.
intros str_char_count.
intros str_can_load.
intros str_middle_not_0.
intros pointer_limits_low.
intros pointer_limits_high.
(*case_eq ( load_8_from_adress pointer (mem1 ++ [(pointer, str_start)] ++ str_middle ++ [(pointer + l, str_end)] ++ mem2) =? 0).
+ intros.
apply strlen_works_on_empty_string.
- apply H.
- apply H0.
- apply H1.
- apply H2.
- apply H6.
+ 
intros.*)
(*generalize dependent str_middle.
induction l.
- intros. admit.
- intros. replace
([(pointer, str_start)] ++
  str_middle ++ [(pointer + Z.pos p, str_end)] ++ mem2)
with
([(pointer, str_start)] ++
  str_middle ++ mem2).
-- *)

(* generalize dependent [(pointer, str_start)]. *)
induction str_middle.
+ intros.
 case_eq ((Z.land (pointer) 3) =? 0).
- intros pointer_and_3.
exists (pointer+1).
exists (pointer+1).
exists (signed2unsigned
     (load_8_from_adress (pointer + 1)
        (mem1 ++
         (pointer, str_start) :: (pointer + l, str_end) :: mem2))
     1).
(* Partea in care se creeaza variabilele locale *)
apply E_Call with ([], ((v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ) SContinue.
* unfold set_function_params. rewrite fun_strlen_exists. simpl. reflexivity.
* unfold get_function_body. rewrite fun_strlen_exists. simpl.
** apply E_Seq with ([], ([(v1, i32 0)] ++ [(v0, i32 pointer)] ++ loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_Local. reflexivity. reflexivity.
*** apply E_Seq with ([], ( (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_Local. reflexivity. reflexivity.
**** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_Local. reflexivity. reflexivity.
***** apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_get. auto.
****** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_local_set. auto. auto.
******* (* Partea in care se executa functia efectiva *)
apply E_Seq with ([],
(v3, i32 
(signed2unsigned (load_8_from_adress (pointer+0+1)
          (mem1 ++
           (pointer, str_start)
           :: [] ++ [(pointer+l, str_end)] ++ mem2)) 1)
) :: (v2, i32 (pointer+0+1)) :: (v1, i32 (pointer+0+1)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer+l, str_end)] ++ mem2)).
-- apply E_Block. left.
apply E_Seq with ([i32 pointer],
(v3, i32 0)
:: (v2, i32 0)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_local_get. auto.
--- apply E_Seq with ([i32 3; i32 pointer],
(v3, i32 0)
:: (v2, i32 0)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_i32_const.
---- apply E_Seq with ([i32(Z.land pointer 3)],
(v3, i32 0)
:: (v2, i32 0)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
----- apply E_i32_and. auto. auto.
----- apply E_Seq with ([],
(v3, i32 0)
:: (v2, i32 0)
   :: (v1, i32 (pointer+0)) :: (v0, i32 (pointer+0)) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
------ apply E_IfFalse.
------- unfold State2Bool. simpl. rewrite pointer_and_3. reflexivity.
------- rewrite Z.add_0_r. reflexivity.
------ apply E_Seq with ([],
(v3, i32 
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+0))
   :: (v1, i32 (pointer+0+4)) :: (v0, i32 (pointer+0)) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
------- apply E_LoopOnce.
simpl in str_char_count. rewrite str_char_count.
apply strlen_loop2_invariant_Continue.
-------- rewrite Z.add_0_r. apply can_load_i32.
--------
rewrite are_all_bytes_not_0_bitwise_one_bit_is_0.
--------- reflexivity.
--------- right.
          rewrite four_byte_value_notation_AND_65280.
          apply Z.eqb_eq in str_end_is_zero.
          simpl in str_end_is_zero.
          simpl load_8_from_adress.
          rewrite str_char_count in str_end_is_zero.
          rewrite Z.add_0_r.
          rewrite str_end_is_zero.
          simpl.
          auto.
-------- rewrite Zplus_assoc_reverse in pointer_limits_high.
         rewrite Zplus_assoc_reverse.
         rewrite str_char_count in pointer_limits_high.
         simpl in pointer_limits_high.
         simpl.
         split.
--------- apply Z.le_trans with (0).
          reflexivity.
          destruct pointer_limits_low.
          (*Search (_ <= _ -> _ <= _).*)
          apply Z.le_trans with (pointer).
---------- apply H.
---------- (*Search (_ + 0).*)
          replace pointer with (pointer+0).
          replace (pointer+0+4) with (pointer+4).
----------- apply Zorder.Zplus_le_compat_l. discriminate.
----------- rewrite Z.add_0_r. reflexivity.
----------- rewrite Z.add_0_r. reflexivity.
--------- destruct pointer_limits_high.
          apply Z.lt_trans with (pointer+5).
---------- apply Zorder.Zplus_lt_compat_l. reflexivity.
---------- apply H0.

------- apply E_Seq with ([i32
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
],
(v3, i32 
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 pointer)
   :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
-------- rewrite Z.add_0_r. apply E_local_get. auto.
-------- apply E_Seq with ([i32 255;
i32 (four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
],
(v3, i32 
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 pointer)
   :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
--------- apply E_i32_const.
--------- apply E_Seq with ([i32 (Z.land
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
255)
],
(v3, i32 
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 pointer)
   :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
---------- apply E_i32_and. auto. auto.
---------- apply E_Seq with ([i32 0],
(v3, i32 
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 pointer)
   :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
----------- apply E_i32_eqz.
------------ auto.
------------ unfold execute_instruction.
             unfold execute_i32_eqz. simpl.
             rewrite four_byte_value_notation_AND_255.
             rewrite unsigned2signed_of_not_0_is_not_0.
------------- reflexivity.
------------- simpl. simpl in str_start_not_zero.
              rewrite Z.add_0_r.
              rewrite str_start_not_zero. reflexivity.
------------- left. split.
-------------- reflexivity.
-------------- split.
--------------- simpl. rewrite Z.add_0_r.
 apply load_8_from_adress_loads_1_byte with 
pointer (mem1 ++ (pointer, str_start) :: (pointer + l, str_end) :: mem2); reflexivity.
--------------- simpl. rewrite Z.add_0_r.

apply Zorder.Zge_trans with 0.
pose proof load_8_from_adress_loads_1_byte as load_byte.
destruct load_byte with (pointer)
(mem1 ++ (pointer, str_start) :: (pointer + l, str_end) :: mem2)
(load_8_from_adress (pointer)
  (mem1 ++ (pointer, str_start) :: (pointer + l, str_end) :: mem2)).
reflexivity.
apply H0.
discriminate.

(* apply load_8_from_adress_loads_1_byte with 
pointer (mem1 ++ (pointer, str_start) :: (pointer + l, str_end) :: mem2); reflexivity.*)
----------- apply E_Seq with ([],
(v3, i32 
(four_byte_value_notation pointer 0 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+0))
   :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
------------ apply E_IfFalse. auto. rewrite Z.add_0_r. auto.
------------ apply E_LoopOnce.
apply strlen_loop3_invariant_continue.
------------- rewrite Z.add_0_r.
unfold "<".
rewrite Z.lt_trans with (pointer+1) (pointer+4) memsize.
-------------- auto.
-------------- unfold "<".
rewrite Zorder.Zplus_lt_compat_l with 1 4 pointer.
--------------- reflexivity.
--------------- reflexivity.
-------------- apply can_load_i32.
------------- apply Z.eqb_eq in str_end_is_zero.
              simpl in str_char_count.
              rewrite str_char_count in str_end_is_zero.
              simpl. simpl in str_end_is_zero.
              rewrite Z.add_0_r.
              rewrite str_char_count.
              apply str_end_is_zero.
------------- rewrite Zplus_assoc_reverse in pointer_limits_high.
         rewrite Zplus_assoc_reverse.
         rewrite str_char_count in pointer_limits_high.
         simpl in pointer_limits_high.
         simpl.
         split.
-------------- apply Z.le_trans with (0).
          reflexivity.
          destruct pointer_limits_low.
          (*Search (_ <= _ -> _ <= _).*)
          apply Z.le_trans with (pointer).
--------------- apply H.
--------------- (*Search (_ + 0).*)
          replace pointer with (pointer+0).
          replace (pointer+0+1) with (pointer+1).
---------------- apply Zorder.Zplus_le_compat_l. discriminate.
---------------- rewrite Z.add_0_r. reflexivity.
---------------- rewrite Z.add_0_r. reflexivity.
-------------- destruct pointer_limits_low.
          apply Z.lt_trans with (pointer+5).
--------------- apply Zorder.Zplus_lt_compat_l. reflexivity.
--------------- destruct pointer_limits_high. apply H2.

-- apply E_Seq with ([i32 (pointer+1)],
(v3, i32 
(signed2unsigned (load_8_from_adress (pointer+1)
          (mem1 ++
           (pointer, str_start)
           :: [] ++ [(pointer+l, str_end)] ++ mem2)) 1)
) :: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+0+1)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer+l, str_end)] ++ mem2)).
--- rewrite Z.add_0_r. apply E_local_get. auto.
--- apply E_Seq with ([i32 pointer; i32 (pointer+1)],
(v3, i32 
(signed2unsigned (load_8_from_adress (pointer+1)
          (mem1 ++
           (pointer, str_start)
           :: [] ++ [(pointer+l, str_end)] ++ mem2)) 1)
) :: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+0+1)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer+l, str_end)] ++ mem2)).
---- apply E_local_get. auto.
---- apply E_i32_sub.
----- auto.
----- unfold execute_instruction.
      unfold execute_i32_sub.
      simpl.
      rewrite Z.add_simpl_l.
      simpl in str_char_count.
      rewrite str_char_count in str_start_not_zero.
      simpl in str_start_not_zero.
      rewrite Z.add_0_r.
      rewrite str_char_count.
      reflexivity.
- intros pointer_and_3.
case_eq ((Z.land (pointer+1) 3) =? 0).
++ intros pointer_plus_1_and_3.
(*Probabil o sa trebuiasca schimbate astea*)
exists (pointer+1+4).
exists (pointer+1).
exists (four_byte_value_notation pointer 1 l str_start str_end mem1
         [] mem2).
(* Partea in care se creeaza variabilele locale *)
apply E_Call with ([], ((v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ) SReturn.
* unfold set_function_params. rewrite fun_strlen_exists. simpl. reflexivity.
* unfold get_function_body. rewrite fun_strlen_exists. simpl.
** apply E_Seq with ([], ([(v1, i32 0)] ++ [(v0, i32 pointer)] ++ loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_Local. reflexivity. reflexivity.
*** apply E_Seq with ([], ( (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_Local. reflexivity. reflexivity.
**** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_Local. reflexivity. reflexivity.
***** apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_get. auto.
****** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_local_set. auto. auto.
******* (* Partea in care se executa functia efectiva *)
(* Seq-ul asta o sa trebuiasca ajustat cu rezultatul dupa block *)
apply E_SeqHasReturn. (*with ([i32 1],
(v3, i32 
(signed2unsigned (load_8_from_adress (pointer+0+1)
          (mem1 ++
           (pointer, str_start)
           :: [] ++ [(pointer+l, str_end)] ++ mem2)) 1)
) :: (v2, i32 (pointer+0+1)) :: (v1, i32 (pointer+0+1)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer+l, str_end)] ++ mem2)).
*)
-- apply E_BlockReturn.
apply E_Seq with ([i32 pointer],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_local_get. auto.
--- apply E_Seq with ([i32 3; i32 pointer],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_i32_const.
---- apply E_Seq with ([i32 (Z.land pointer 3)],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
----- apply E_i32_and. auto. auto.
----- apply E_Seq with ([],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
------- apply E_IfTrue.
-------- unfold State2Bool. simpl.
         rewrite pointer_and_3. reflexivity.
-------- apply E_LoopOnce.
--------- apply strlen_loop1_invariant_Continue. auto.
---------- unfold "<".
           rewrite Z.lt_trans with (pointer) (pointer+4) memsize.
----------- reflexivity.
----------- unfold "<".
            replace (pointer) with (pointer+0).
            replace (pointer+0+4) with (pointer+4).
------------ rewrite Zorder.Zplus_lt_compat_l with 0 4 pointer.
------------- reflexivity.
------------- reflexivity.
------------ rewrite Z.add_0_r. reflexivity.
------------ rewrite Z.add_0_r. reflexivity.
----------- apply can_load_i32.
---------- apply str_start_not_zero.
---------- apply pointer_plus_1_and_3.
---------- simpl in str_char_count.
           rewrite str_char_count in pointer_limits_high.
           rewrite Zplus_assoc_reverse in pointer_limits_high.
           simpl in pointer_limits_high.
           simpl.
           split.
-------------- apply Z.le_trans with (0).
          reflexivity.
          destruct pointer_limits_low.
          (*Search (_ <= _ -> _ <= _).*)
          apply Z.le_trans with (pointer).
--------------- apply H.
--------------- (*Search (_ + 0).*)
          replace pointer with (pointer+0).
          replace (pointer+0+1) with (pointer+1).
---------------- apply Zorder.Zplus_le_compat_l. discriminate.
---------------- rewrite Z.add_0_r. reflexivity.
---------------- rewrite Z.add_0_r. reflexivity.
-------------- destruct pointer_limits_low.
          apply Z.lt_trans with (pointer+5).
--------------- apply Zorder.Zplus_lt_compat_l. reflexivity.
--------------- destruct pointer_limits_high. apply H2.
-------- discriminate.
------- (* de ajustat sa mearga cu ce da loop*)
apply E_Seq with ([],
(v3, i32 
(four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
-------- apply E_LoopOnce.

(* Trebuie sa repar invariantul
Problema e ca inlocuieste pointer+1 peste tot, inclusiv
in memorie*)
apply strlen_loop2_invariant_Continue.
--------- simpl in str_char_count.
          rewrite Zplus_assoc_reverse. simpl.
          rewrite str_char_count in str_max_mem_need.
          (*rewrite Zplus_assoc_reverse in str_max_mem_need.*)
          simpl in str_max_mem_need.
          unfold "<".
          rewrite Z.lt_trans with (pointer+5) (pointer+8) memsize.
---------- reflexivity.
---------- unfold "<".
           rewrite Zorder.Zplus_lt_compat_l with 5 8 pointer.
----------- reflexivity.
----------- reflexivity.
---------- apply str_max_mem_need.
--------- rewrite are_all_bytes_not_0_bitwise_one_bit_is_0.
---------- reflexivity.
---------- left. rewrite four_byte_value_notation_AND_255.
           rewrite Z.eqb_eq in str_end_is_zero.
           simpl in str_char_count.
           rewrite str_char_count.
           rewrite str_char_count in str_end_is_zero.
           simpl in str_end_is_zero. simpl.
           rewrite str_end_is_zero.
           auto.
--------- simpl.
rewrite Zplus_assoc_reverse in pointer_limits_high.
         rewrite Zplus_assoc_reverse.
simpl in str_char_count.
rewrite str_char_count in pointer_limits_high.
simpl in pointer_limits_high.
simpl.
apply pointer_limits_high.

-------- apply E_Seq with ([
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
--------- apply E_local_get. auto.
--------- apply E_Seq with ([i32 255;
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
---------- apply E_i32_const.
---------- apply E_Seq with ([ i32 (Z.land
(four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
255) ],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
----------- apply E_i32_and. auto. auto.
----------- apply E_Seq with ([i32 1],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
------------ apply E_i32_eqz.
------------- auto.
------------- unfold execute_instruction.
              unfold execute_i32_eqz. simpl.
              rewrite four_byte_value_notation_AND_255.
              simpl in str_char_count.
              rewrite str_char_count in str_end_is_zero.
              rewrite str_char_count.
              simpl in str_end_is_zero.
              simpl.
              rewrite Z.eqb_eq in str_end_is_zero.
              rewrite str_end_is_zero.
              auto.
------------ apply E_SeqHasReturn. (* with ([i32 1],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
*)
------------- apply E_IfTrueReturn.
-------------- auto.
-------------- apply E_Seq with ([i32 (pointer+1)],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
--------------- apply E_local_get. auto.
--------------- apply E_Seq with ([i32 (pointer);i32 (pointer+1)],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
---------------- apply E_local_get. auto.
---------------- apply E_Seq with ([i32 1],
(v3,
i32 (four_byte_value_notation pointer 1 l str_start str_end mem1 [] mem2)
)
:: (v2, i32 (pointer+1)) :: (v1, i32 (pointer+1+4)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
----------------- apply E_i32_sub.
------------------ auto.
------------------ unfold execute_instruction.
                   unfold execute_i32_sub.
                   simpl.
                   rewrite Z.add_simpl_l.
                   reflexivity.
----------------- simpl in str_char_count.
                  rewrite str_char_count.
                  apply E_Return.

++ (*case ((Z.land (pointer+1) 3) =? 0) = false*)
intros pointer_plus_1_and_3.
exists (pointer+1).
exists (0).
exists (0).
(* Partea in care se creeaza variabilele locale *)
apply E_Call with ([], ((v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ) SContinue.
* unfold set_function_params. rewrite fun_strlen_exists. simpl. reflexivity.
* unfold get_function_body. rewrite fun_strlen_exists. simpl.
** apply E_Seq with ([], ([(v1, i32 0)] ++ [(v0, i32 pointer)] ++ loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_Local. reflexivity. reflexivity.
*** apply E_Seq with ([], ( (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_Local. reflexivity. reflexivity.
**** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_Local. reflexivity. reflexivity.
***** apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_get. auto.
****** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_local_set. auto. auto.
******* (* Partea in care se executa functia efectiva *)
(* Seq-ul asta o sa trebuiasca ajustat cu rezultatul dupa block *)
apply E_Seq with ([],
(v3, i32 0) :: (v2, i32 (0)) :: (v1, i32 (pointer+0+1)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer+l, str_end)] ++ mem2)).
-- apply E_Block. right.
apply E_Seq with ([i32 pointer],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
--- apply E_local_get. auto.
--- apply E_Seq with ([i32 3; i32 pointer],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_i32_const.
---- apply E_Seq with ([i32 (Z.land pointer 3)],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
----- apply E_i32_and. auto. auto.
-----
 apply E_SeqBr. (*with ([],
(v3, i32 0)
:: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
*)
------- apply E_IfTrue.
-------- unfold State2Bool. simpl.
         rewrite pointer_and_3. reflexivity.
-------- apply E_Loop with 
(([]),
  (v3, i32 0)
  :: (v2, i32 0) :: (v1, i32 (pointer+1)) :: (v0, i32 pointer) :: loc_list,
  glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
  (memsize,
  mem1 ++ [(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)) (L3).
--------- apply strlen_loop1_invariant_SBrL3. auto.
---------- unfold "<".
           rewrite Z.lt_trans with (pointer) (pointer+4) memsize.
----------- reflexivity.
----------- unfold "<".
            replace (pointer) with (pointer+0).
            replace (pointer+0+4) with (pointer+4).
------------ rewrite Zorder.Zplus_lt_compat_l with 0 4 pointer.
------------- reflexivity.
------------- reflexivity.
------------ rewrite Z.add_0_r. reflexivity.
------------ rewrite Z.add_0_r. reflexivity.
----------- apply can_load_i32.
---------- apply str_start_not_zero.
---------- apply pointer_plus_1_and_3.
---------- 
rewrite Zplus_assoc_reverse in pointer_limits_high.
simpl in str_char_count.
rewrite str_char_count in pointer_limits_high.
simpl in pointer_limits_high.
         split.
-------------- apply Z.le_trans with (0).
          reflexivity.
          destruct pointer_limits_low.
          (*Search (_ <= _ -> _ <= _).*)
          apply Z.le_trans with (pointer).
--------------- apply H.
--------------- (*Search (_ + 0).*)
          replace pointer with (pointer+0).
          replace (pointer+0+1) with (pointer+1).
---------------- apply Zorder.Zplus_le_compat_l. discriminate.
---------------- rewrite Z.add_0_r. reflexivity.
---------------- rewrite Z.add_0_r. reflexivity.
-------------- destruct pointer_limits_low.
          apply Z.lt_trans with (pointer+5).
--------------- apply Zorder.Zplus_lt_compat_l. reflexivity.
--------------- destruct pointer_limits_high. apply H2.
--------- reflexivity.
--------- apply E_LoopOnceBrOther.
---------- rewrite Zplus_assoc_reverse.
           simpl.
replace (mem1 ++ (pointer, str_start) :: (pointer + l, str_end) :: mem2)
with ((mem1 ++ (pointer, str_start) :: [] ++ (pointer + l, str_end) :: mem2)).

(*De ce nu merge asta???*)
apply strlen_loop1_invariant_SBrL1.
----------- trivial.
----------- simpl in str_char_count.
            rewrite str_char_count in str_can_load.
            apply str_can_load.
----------- simpl in str_char_count.
            rewrite str_char_count in str_end_is_zero.
            rewrite str_char_count.
            apply Z.eqb_eq in str_end_is_zero.
            simpl. simpl in str_end_is_zero.
            rewrite str_end_is_zero.
            auto.
----------- simpl. reflexivity.
---------- discriminate.
-------- discriminate.
(*------- discriminate.*)
-- apply E_Seq with ([i32 (pointer+1)],
(v3, i32 0)
:: (v2, i32 0)
   :: (v1, i32 (pointer + 1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
--- rewrite Z.add_0_r. apply E_local_get. auto.
--- apply E_Seq with ([i32 pointer; i32 (pointer+1)],
(v3, i32 0)
:: (v2, i32 0)
   :: (v1, i32 (pointer + 1)) :: (v0, i32 pointer) :: loc_list,
glob_list, func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++ [] ++ [(pointer + l, str_end)] ++ mem2)).
---- apply E_local_get. auto.
---- apply E_i32_sub.
----- auto.
----- unfold execute_instruction.
      unfold execute_i32_sub.
      simpl.
      rewrite Z.add_simpl_l.
      simpl in str_char_count.
      rewrite str_char_count in str_start_not_zero.
      simpl in str_start_not_zero.
      rewrite str_char_count.
      reflexivity.
+ 

Admitted.

(* <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<*)



(*
exists (pointer+1).
exists (0).
exists (0).
(* Partea in care se creeaza variabilele locale *)
apply E_Call with ([], ((v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ a :: str_middle ++ [(pointer + l, str_end)] ++ mem2)) ) SContinue.
* unfold set_function_params. rewrite fun_strlen_exists. simpl. reflexivity.
* unfold get_function_body. rewrite fun_strlen_exists. simpl.
** apply E_Seq with ([], ([(v1, i32 0)] ++ [(v0, i32 pointer)] ++ loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ a :: str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
*** apply E_Local. reflexivity. reflexivity.
*** apply E_Seq with ([], ( (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ a :: str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
**** apply E_Local. reflexivity. reflexivity.
**** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ a :: str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
***** apply E_Local. reflexivity. reflexivity.
***** apply E_Seq with ([i32 pointer], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 0) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ a :: str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
****** apply E_local_get. auto.
****** apply E_Seq with ([], ( (v3, i32 0) :: (v2, i32 0) :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list), glob_list, (func_list1 ++ [(strlen ,fun_strlen)] ++ func_list2), (memsize, (mem1 ++ [(pointer, str_start)] ++ a :: str_middle ++ [(pointer + l, str_end)] ++ mem2)) ).
******* apply E_local_set. auto. auto.
******* (* Partea in care se executa functia efectiva *)
(* Seq-ul asta o sa trebuiasca ajustat cu rezultatul dupa block *)
apply E_Seq with ([],
(v3, i32 0) :: (v2, i32 (0)) :: (v1, i32 (pointer+0+1)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize, mem1 ++ [(pointer, str_start)] ++ a :: str_middle ++ [(pointer+l, str_end)] ++ mem2)).


apply IHstr_middle.






Admitted.*)




(*
-------- apply E_Seq with ([i32 pointer],
(v3, i32 0)
:: (v2, i32 0)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
--------- apply E_local_get. auto.
--------- apply E_Seq with ([i32 pointer],
(v3, i32 0)
:: (v2, i32 pointer)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
---------- apply E_local_tee. auto. auto.
---------- apply E_Seq with ([i32 4;i32 pointer],
(v3, i32 0)
:: (v2, i32 pointer)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
----------- apply E_i32_const.
----------- apply E_Seq with ([i32 (pointer+4)],
(v3, i32 0)
:: (v2, i32 pointer)
   :: (v1, i32 pointer) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
------------ apply E_i32_add. auto. auto.
------------ apply E_Seq with ([],
(v3, i32 0)
:: (v2, i32 pointer)
   :: (v1, i32 (pointer+4)) :: (v0, i32 pointer) :: loc_list,
glob_list,
func_list1 ++ [(strlen, fun_strlen)] ++ func_list2,
(memsize,
mem1 ++
[(pointer, str_start)] ++
[] ++ [(pointer + l, str_end)] ++ mem2)).
*)


























Close Scope string_scope.
Close Scope Z.