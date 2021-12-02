Require Import Strings.String Lists.List ZArith.
From FourCerty Require Import Maps.

Module SourceLang.

Inductive val : Type :=
  | V_Bool (b : bool)
  | V_Int (i : Z).

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
  | Prim1 (op : prim1) (t : tm)
  | Prim2 (op : prim2) (t1 : tm) (t2 : tm)
  | App (f : string) (ts : list tm)
  | If (t1 : tm) (t2 : tm) (t3 : tm)
  | Let (x : string) (t1 : tm) (t2 : tm).

Inductive defn : Type :=
  Defn (f : string) (xs : list string) (body : tm).

Inductive prg : Type :=
  Prg (funs : list defn) (e : tm).

Inductive err : Type :=
  | OOF
  | Error.

Inductive result {A : Type} : Type :=
  | Err (e : err)
  | Ok (v : A).

Fixpoint build_env (xs : list string) (vs : list val) :=
  match xs, vs with
  | nil,nil => Some empty
  | x :: xs', v :: vs' =>
    match build_env xs' vs' with
    | None => None
    | Some env => Some (update env x v)
    end
  | _, _ => None
  end.

Definition do_prim1 (op : prim1) (v : val) :=
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

Definition do_prim2 (op : prim2) (v1 : val) (v2 : val) :=
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

Definition eval_tm :=
  fun (funs : partial_map defn) =>
  fix eval' (f : nat) :=
  fix eval'' (t : tm) :=
  fun (env : partial_map val) =>

  match t with
  | Const v => Ok v
  | Prim1 op t' =>
    match eval'' t' env with
    | Err e => Err e
    | Ok v => do_prim1 op v
    end
  | Prim2 op t1 t2 =>
    match eval'' t1 env with
    | Err e => Err e
    | Ok v1 =>
      match eval'' t2 env with
      | Err e => Err e
      | Ok v2 => do_prim2 op v1 v2
      end
    end
  | App fn ts =>
    let fix eval_lst ts :=
      match ts with
      | nil => Ok nil
      | t' :: ts' =>
        match eval'' t' env with
        | Err e => Err e
        | Ok v =>
          match eval_lst ts' with
          | Err e => Err e
          | Ok vs => Ok (v :: vs)
          end
        end
      end in
    match eval_lst ts with
    | Err e => Err e
    | Ok vs =>
      match env fn with
      | Some _ => Err Error
      | None =>
        match funs fn with
        | None => Err Error
        | Some (Defn _ xs t) =>
          match build_env xs vs with
          | None => Err Error
          | Some env' =>
            match f with
            | O => Err OOF
            | S f' => eval' f' t env'
            end
          end
        end
      end
    end
  | If t1 t2 t3 =>
    match eval'' t1 env with
    | Ok (V_Bool false) => eval'' t3 env
    | Ok _ => eval'' t2 env
    | Err e => Err e
    end
  | Let x t1 t2 =>
    match eval'' t1 env with
    | Err e => Err e
    | Ok v => eval'' t2 (update env x v)
    end
  end.

Fixpoint extract_funs (funs : list defn) :=
  match funs with
  | nil => empty
  | (Defn fn xs t) :: funs' => update (extract_funs funs') fn (Defn fn xs t)
  end.

Definition eval (f : nat) (p : prg) :=
  match p with
  | Prg funs t => eval_tm (extract_funs funs) f t empty
  end.

End SourceLang.