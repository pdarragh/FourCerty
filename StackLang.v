From FourCerty Require Import Utility.

Import Utility.

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

Definition do_uop (u : ins_uop) (v : ins_val) : result ins_val :=
  match u with
  | U_Add1 =>
    match v with
    | V_Int i => Ok (V_Int (i + 1))
    | _ => Err Error
    end
  | U_Sub1 =>
    match v with
    | V_Int i => Ok (V_Int (i - 1))
    | _ => Err Error
    end
  | U_Not =>
    match v with
    | V_Bool false => Ok (V_Bool true)
    | _ => Ok (V_Bool false)
    end
  end.

Inductive ins_bop : Type :=
  | B_Add
  | B_Sub
  | B_And
  | B_Or.

Definition do_bop (b : ins_bop) (v1 v2 : ins_val) : result ins_val :=
  match b with
  | B_Add =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Ok (V_Int (i1 + i2))
    | _, _ => Err Error
    end
  | B_Sub =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Ok (V_Int (i1 - i2))
    | _, _ => Err Error
    end
  | B_And =>
    match v1, v2 with
    | V_Bool b1, V_Bool b2 => Ok (V_Bool (andb b1 b2))
    | _, _ => Err Error
    end
  | B_Or =>
    match v1, v2 with
    | V_Bool b1, V_Bool b2 => Ok (V_Bool (orb b1 b2))
    | _, _ => Err Error
    end
  end.

Inductive stk_ins : Type :=
  | StkErr
  | Call (l : string) (n : nat)
  | Push (v : ins_val)
  | Pop
  | Swap
  | StkRef (n : nat)
  | Uop (u : ins_uop)
  | Bop (b : ins_bop)
  | Cmp (c : ins_cmp).

Inductive stk_tm : Type :=
  | End
  | Ins (ins : stk_ins) (rst : stk_tm)
  | If (thn : stk_tm) (els : stk_tm) (rst : stk_tm).

Inductive stk_fun : Type :=
  Fun (l : string) (n : nat) (ins : stk_tm).

Inductive stk_prg : Type :=
  Prg (funs : list stk_fun) (inss : stk_tm).

Fixpoint extract_funs (funs : list stk_fun) :=
  match funs with
  | nil => empty
  | Fun l n inss :: rst => update (extract_funs rst) l (Fun l n inss)
  end.

Definition eval' (funs : partial_map stk_fun) :=
  fix eval_fuel (f : nat) :=
    fix eval_tm (inss : stk_tm) (val_stack : list ins_val) : result (list ins_val) :=
      match inss with
      | End => Ok val_stack
      | Ins ins inss' =>
          match ins with
          | StkErr => Err Error
          | Call l n =>
              let args := firstn n val_stack in
              let rst := skipn n val_stack in
              if List.length args <? n
              then Err Error
              else '(Fun _ m inss'') <- lookup funs l;;
                   if m =? n
                   then match f with
                        | O => Err OOF
                        | S f' =>
                            vs <- eval_fuel f' inss'' args;;
                            eval_tm inss' (vs ++ rst)
                        end
                   else Err Error
          | Push v => eval_tm inss' (v :: val_stack)
          | Pop =>
              match val_stack with
              | [] => Err Error
              | v :: rst => eval_tm inss' rst
              end
          | Swap =>
              match val_stack with
              | v1 :: v2 :: rst =>
                  eval_tm inss' (v2 :: v1 :: rst)
              | _ => Err Error
              end
          | StkRef n =>
              match nth_error val_stack n with
              | None => Err Error
              | Some v => eval_tm inss' (v :: val_stack)
              end
          | Uop u =>
              match val_stack with
              | [] => Err Error
              | v :: rst =>
                  v <- do_uop u v;;
                  eval_tm inss' (v :: rst)
              end
          | Bop b =>
              match val_stack with
              | v2 :: v1 :: rst =>
                  v <- do_bop b v1 v2;;
                  eval_tm inss' (v :: rst)
              | _ => Err (ErrorMsg "not enough values on stack")
              end
          | Cmp c =>
              match val_stack with
              | V_Int i2 :: V_Int i1 :: rst =>
                  eval_tm inss' (V_Bool (do_cmp c i1 i2) :: rst)
              | _ => Err Error
              end
          end
      | If thn els nxt =>
          match val_stack with
          | V_Bool false :: rst =>
              vs <- eval_tm els rst;;
              eval_tm nxt vs
          | _ :: rst =>
              vs <- eval_tm thn rst;;
              eval_tm nxt vs
          | _ => Err Error
          end
      end.

Definition eval (f : nat) (prg : stk_prg) :=
  match prg with
  | Prg funs inss => eval' (extract_funs funs) f inss nil
  end.

End StackLang.
