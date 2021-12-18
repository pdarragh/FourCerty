From FourCerty Require Import Utility.

Import Utility.

Module SourceLang.

Inductive val : Type :=
  | V_Bool (b : bool)
  | V_Int (i : Z).

Notation environment := (partial_map val).

Inductive prim1 : Type :=
  | P_add1
  | P_sub1
  | P_not.

Inductive prim2 : Type :=
  | P_add
  | P_sub
  | P_and
  | P_or
  | P_eq
  | P_lt
  | P_le.

Inductive tm : Type :=
  | Const (v : val)
  | Var (x : string)
  | Prim1 (op : prim1) (t : tm)
  | Prim2 (op : prim2) (t1 : tm) (t2 : tm)
  | App (f : string) (ts : tm)
  | ArgCons (t : tm) (tRst : tm)
  | ArgNil
  | If (t1 : tm) (t2 : tm) (t3 : tm)
  | Let (x : string) (t1 : tm) (t2 : tm).

Inductive defn : Type :=
  Defn (f : string) (xs : list string) (body : tm).

Notation fundefns := (partial_map defn).

Inductive prg : Type :=
  Prg (funs : list defn) (e : tm).

Fixpoint build_env (xs : list string) (vs : list val) : result environment :=
  match xs, vs with
  | nil,nil => Ok empty
  | x :: xs', v :: vs' =>
      env <- build_env xs' vs';;
      ret (update env x v)
  | _, _ => Err Error
  end.

Definition do_prim1 (op : prim1) (v : val) : result val :=
  match op with
  | P_add1 =>
    match v with
    | V_Int i => Ok (V_Int (i + 1))
    | _ => Err Error
    end
  | P_sub1 =>
    match v with
    | V_Int i => Ok (V_Int (i - 1))
    | _ => Err Error
    end
  | P_not =>
    match v with
    | V_Bool false => Ok (V_Bool true)
    | _ => Ok (V_Bool false)
    end
  end.

Definition do_prim2 (op : prim2) (v1 : val) (v2 : val) : result val :=
  match op with
  | P_add =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Ok (V_Int (i1 + i2))
    | _, _ => Err Error
    end
  | P_sub =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Ok (V_Int (i1 - i2))
    | _, _ => Err Error
    end
  | P_and =>
    match v1, v2 with
    | V_Bool b1, V_Bool b2 => Ok (V_Bool (b1 && b2))
    | _, _ => Err Error
    end
  | P_or =>
    match v1, v2 with
    | V_Bool b1, V_Bool b2 => Ok (V_Bool (b1 || b2))
    | _, _ => Err Error
    end
  | P_eq =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Ok (V_Bool (Z.eqb i1 i2))
    | _, _ => Err Error
    end
  | P_lt =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Ok (V_Bool (Z.ltb i1 i2))
    | _, _ => Err Error
    end
  | P_le =>
    match v1, v2 with
    | V_Int i1, V_Int i2 => Ok (V_Bool (Z.leb i1 i2))
    | _, _ => Err Error
    end
  end.

Fixpoint extract_funs (funs : list defn) : fundefns :=
  match funs with
  | nil => empty
  | (Defn fn xs t) :: funs' => update (extract_funs funs') fn (Defn fn xs t)
  end.

Definition eval' (funs : fundefns) :=
  fix eval_fuel (f : nat) :=
    fix eval_tm (t : tm) (env : environment) : result val :=
      match t with
      | Const v => Ok v
      | Var x => lookup env x
      | Prim1 op t' =>
          v <- eval_tm t' env;;
          do_prim1 op v
      | Prim2 op t1 t2 =>
          v1 <- eval_tm t1 env;;
          v2 <- eval_tm t2 env;;
          do_prim2 op v1 v2
      | App fn t_args =>
          let fix eval_arg_list (t_al : tm) :=
            match t_al with
            | ArgNil => Ok []
            | ArgCons t_arg t_al' =>
                v <- eval_tm t_arg env;;
                vl <- eval_arg_list t_al';;
                Ok (v :: vl)
            | _ => Err Error
            end in
          vs <- eval_arg_list t_args;;
          '(Defn _ xs t) <- lookup funs fn;;
          env' <- build_env xs vs;;
          match f with
          | O => Err OOF
          | S f' => eval_fuel f' t env'
          end
      | ArgCons _ _ => Err Error
      | ArgNil => Err Error
      | If t1 t2 t3 =>
          v1 <- eval_tm t1 env;;
          match v1 with
          | V_Bool false => eval_tm t3 env
          | _ => eval_tm t2 env
          end
      | Let x t1 t2 =>
          v <- eval_tm t1 env;;
          eval_tm t2 (update env x v)
      end.

Definition eval (f : nat) (p : prg) :=
  match p with
  | Prg funs t => eval' (extract_funs funs) f t empty
  end.

End SourceLang.
