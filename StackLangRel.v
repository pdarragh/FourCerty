From FourCerty Require Import Utility StackLang.

Import Utility StackLang.

Module StackLangRel.

Open Scope Z_scope.

Inductive do_cmp_R : ins_cmp -> Z -> Z -> bool -> Prop :=
  | DC_Eq : forall i1 i2,
      do_cmp_R C_Eq i1 i2 (i1 =? i2)
  | DC_Ne : forall i1 i2,
      do_cmp_R C_Ne i1 i2 (negb (i1 =? i2))
  | DC_Lt : forall i1 i2,
      do_cmp_R C_Lt i1 i2 (i1 <? i2)
  | DC_Le : forall i1 i2,
      do_cmp_R C_Le i1 i2 (i1 <=? i2)
  | DC_Gt : forall i1 i2,
      do_cmp_R C_Gt i1 i2 (i1 >? i2)
  | DC_Ge : forall i1 i2,
      do_cmp_R C_Ge i1 i2 (i1 >=? i2).

Inductive do_uop_R : ins_uop -> ins_val -> ins_val -> Prop :=
  | DU_Add1 : forall i,
      do_uop_R U_Add1 (V_Int i) (V_Int (i + 1))
  | DU_Sub1 : forall i,
      do_uop_R U_Sub1 (V_Int i) (V_Int (i - 1))
  | DU_NotFalse : do_uop_R U_Not (V_Bool false) (V_Bool true)
  | DU_NotTrue : do_uop_R U_Not (V_Bool true) (V_Bool false)
  | DU_NotInt : forall i, do_uop_R U_Not (V_Int i) (V_Bool false).

Inductive do_bop_R : ins_bop -> ins_val -> ins_val -> ins_val -> Prop :=
  | DB_Add : forall i1 i2,
      do_bop_R B_Add (V_Int i1) (V_Int i2) (V_Int (i1 + i2))
  | DB_Sub : forall i1 i2,
      do_bop_R B_Sub (V_Int i1) (V_Int i2) (V_Int (i1 - i2))
  | DB_And : forall b1 b2,
      do_bop_R B_And (V_Bool b1) (V_Bool b2) (V_Bool (b1 && b2))
  | DB_Or : forall b1 b2,
      do_bop_R B_Or (V_Bool b1) (V_Bool b2) (V_Bool (b1 || b2)).

Inductive eval_tm_R : nat -> partial_map stk_fun -> stk_tm -> list ins_val -> list ins_val -> Prop :=
  | E_End : forall f funs vs,
      eval_tm_R f funs End vs vs
  | E_InsCall : forall f f' funs inss' inss'' args rst fn n vs1 vs2 vs3,
      f = S f' ->
      args = firstn n vs1 ->
      rst = skipn n vs1 ->
      List.length args = n ->
      Ok (Fun fn n inss'') = lookup funs fn ->
      eval_tm_R f' funs inss'' args vs2 ->
      eval_tm_R f funs inss' (vs2 ++ rst) vs3 ->
      eval_tm_R f funs (Ins (Call fn n) inss') vs1 vs3
  | E_InsPush : forall f funs v inss' vs1 vs2,
      eval_tm_R f funs inss' (v :: vs1) vs2 ->
      eval_tm_R f funs (Ins (Push v) inss') vs1 vs2
  | E_InsPop : forall f funs inss' v rst vs,
      eval_tm_R f funs inss' rst vs ->
      eval_tm_R f funs (Ins Pop inss') (v :: rst) vs
  | E_InsSwap : forall f funs inss' v1 v2 rst vs,
      eval_tm_R f funs inss' (v2 :: v1 :: rst) vs ->
      eval_tm_R f funs (Ins Swap inss') (v1 :: v2 :: rst) vs
  | E_InsStkRef : forall f funs inss' n v vs1 vs2,
      Some v = nth_error vs1 n ->
      eval_tm_R f funs inss' (v :: vs1) vs2 ->
      eval_tm_R f funs (Ins (StkRef n) inss') vs1 vs2
  | E_InsUop : forall f funs inss' op v1 v2 rst vs,
      do_uop_R op v1 v2 ->
      eval_tm_R f funs inss' (v2 :: rst) vs ->
      eval_tm_R f funs (Ins (Uop op) inss') (v1 :: rst) vs
  | E_InsBop : forall f funs inss' op v1 v2 v3 rst vs,
      do_bop_R op v1 v2 v3 ->
      eval_tm_R f funs inss' (v3 :: rst) vs ->
      eval_tm_R f funs (Ins (Bop op) inss') (v2 :: v1 :: rst) vs
  | E_InsCmp : forall f funs inss' op i1 i2 b rst vs,
      do_cmp_R op i1 i2 b ->
      eval_tm_R f funs inss' ((V_Bool b) :: rst) vs ->
      eval_tm_R f funs (Ins (Cmp op) inss') ((V_Int i2) :: (V_Int i1) :: rst) vs
  | E_IfFalse : forall f funs thn els nxt rst vs1 vs2,
      eval_tm_R f funs els rst vs1 ->
      eval_tm_R f funs nxt vs1 vs2 ->
      eval_tm_R f funs (If thn els nxt) ((V_Bool false) :: rst) vs2
  | E_IfTrue : forall f funs thn els nxt v rst vs1 vs2,
      eval_tm_R f funs thn rst vs1 ->
      eval_tm_R f funs nxt vs1 vs2 ->
      eval_tm_R f funs (If thn els nxt) (v :: rst) vs2.

End StackLangRel.
