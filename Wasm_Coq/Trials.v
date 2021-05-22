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
Import Pos2Z.

From Coq Require Import ZArith.
(*Open Scope R_scope.*)

From LF Require Import Maps Wasm Proprieties.

Open Scope Z.

Require Import Coq.Init.Decimal.
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

Definition loop_instr (n : Z) :=
n * 10.

Inductive mini_ceval : Z -> Z -> Prop :=
| mini_LoopOnce : forall ( f : Z->Z ) n n',
  (f n) = n' ->
  mini_ceval (f n) n'
| mini_Loop : forall ( f : Z->Z ) n n',
  (f n) = n' ->
  mini_ceval (f n) n'.

Example a :=


Lemma exemplu :
forall (n : Z),
(loop_instr n) = n *10.
Proof.
intros.
apply mini_LoopOnce.
induction n.
- reflexivity.
- induction p.


















