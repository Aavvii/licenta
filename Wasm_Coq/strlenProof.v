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

Definition strlen : string := "strlen".
Definition block1 : string := "block1".
Definition L1 : string := "L1".
Definition L2 : string := "L2".
Definition L3 : string := "L3".

Open Scope string_scope.
Open Scope com_scope.
Open Scope Z.

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
