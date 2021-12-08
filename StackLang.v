Require Import Lists.List ZArith.
From FourCerty Require Import Maps.

Module StackLang.

Inductive ins_val : Type :=
  | V_Int (i : Z)
  | V_Bool (b : bool).

Inductive ins_cmp : Type :=
  | C_Eq
  | C_Ne
  | C_Lt
  | C_Le
  | C_Gt
  | C_Ge.

Definition do_cmp (c : ins_cmp) (i1 : Z) (i2 : Z) :=
  match c with
  | C_Eq => Z.eqb i1 i2
  | C_Ne => negb (Z.eqb i1 i2)
  | C_Lt => Z.ltb i1 i2
  | C_Le => Z.leb i1 i2
  | C_Gt => Z.ltb i2 i1
  | C_Ge => Z.leb i2 i1
  end.

Inductive ins_uop : Type :=
  | U_Add1
  | U_Sub1
  | U_Not.

Definition do_uop (u : ins_uop) (v : ins_val) :=
  match u with
  | U_Add1 =>
    match v with
    | V_Int i => Some (V_Int (i + 1))
    | _ => None
    end
  | U_Sub1 =>
    match v with
    | V_Int i => Some (V_Int (i - 1))
    | _ => None
    end
  | U_Not =>
    match v with
    | V_Bool b => Some (V_Bool (negb b))
    | _ => None
    end
  end.

Inductive ins_bop : Type :=
  | B_Add
  | B_Sub
  | B_And
  | B_Or.

Definition do_bop (b : ins_bop) (v1 v2 : ins_val) :=
  match b with
  | B_Add =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Some (V_Int (i1 + i2))
    | _, _ => None
    end
  | B_Sub =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Some (V_Int (i1 - i2))
    | _, _ => None
    end
  | B_And =>
    match v1, v2 with
    | V_Bool b1, V_Bool b2 => Some (V_Bool (andb b1 b2))
    | _, _ => None
    end
  | B_Or =>
    match v1, v2 with
    | V_Bool b1, V_Bool b2 => Some (V_Bool (orb b1 b2))
    | _, _ => None
    end
  end.

Inductive result : Type :=
  | OOF
  | Error
  | Value (v : ins_val).

Inductive stk_ins : Type :=
  | Call (l : string) (n : nat)
  | Ret
  | Push (v : ins_val)
  | Pop
  | StkRef (n : nat)
  | Uop (u : ins_uop)
  | Bop (b : ins_bop)
  | Cmp (c : ins_cmp)
  | If (thn : list stk_ins) (els : list stk_ins).

Inductive stk_fun : Type :=
  Fun (l : string) (n : nat) (ins : list stk_ins).

Inductive stk_prg : Type :=
  Prg (funs : list stk_fun) (inss : list stk_ins).

Inductive stk_stk : Type :=
  | MtStk
  | Frame (inss : list stk_ins) (vals : list ins_val) (rst : stk_stk).

Definition eval_ins :=
  fun (funs : partial_map stk_fun) =>
  fix eval' (f : nat) :=
  let oof_check :=
    match f with
    | O => fun _ _ _ => OOF
    | S f' => eval' f'
    end in
  fix eval'' (call_stack : stk_stk) :=
  fix eval''' (inss : list stk_ins) :=
  fun (val_stack : list ins_val) =>

  match inss with
  | nil =>
    match val_stack with
    | nil => Error
    | v :: _ => Value v
    end
  | ins :: inss' =>
    match ins with
    | Call l n =>
      let args := firstn n val_stack in
      let rst := skipn n val_stack in
      if List.length args <? n then
        Error
      else
        match funs l with
        | None => Error
        | Some (Fun _ m inss'') =>
          if m =? n then
            oof_check (Frame inss' rst call_stack) inss'' args
          else
            Error
        end
    | Ret =>
      match call_stack with
      | MtStk => Error
      | Frame inss'' vals rst =>
        match val_stack with
        | nil => Error
        | v :: _ => eval'' rst inss'' (v :: vals)
        end
      end
    | Push v => eval''' inss' (v :: val_stack)
    | Pop =>
      match val_stack with
      | nil => Error
      | v :: rst => eval''' inss' rst
      end
    | StkRef n =>
      match nth_error val_stack n with
      | None => Error
      | Some v => eval''' inss' (v :: val_stack)
      end
    | Uop u =>
      match val_stack with
      | v :: rst =>
        match do_uop u v with
        | None => Error
        | Some v => eval''' inss' (v :: rst)
        end
      | _ => Error
      end
    | Bop b =>
      match val_stack with
      | v2 :: v1 :: rst =>
        match do_bop b v1 v2 with
        | None => Error
        | Some v => eval''' inss' (v :: rst)
        end
      | _ => Error
      end
    | Cmp c =>
      match val_stack with
      | V_Int i1 :: V_Int i2 :: rst => eval''' inss' (V_Bool (do_cmp c i1 i2) :: rst)
      | _ => Error
      end
    | If thn els =>
      match val_stack with
      | V_Bool true :: rst => oof_check call_stack (thn ++ inss') rst
      | V_Bool false :: rst => oof_check call_stack (els ++ inss') rst
      | _ => Error
      end
    end
  end.

Fixpoint extract_funs (funs : list stk_fun) :=
  match funs with
  | nil => empty
  | Fun l n inss :: rst => update (extract_funs rst) l (Fun l n inss)
  end.

Definition eval (f : nat) (prg : stk_prg) :=
  match prg with
  | Prg funs inss => eval_ins (extract_funs funs) f MtStk inss nil
  end.

End StackLang.