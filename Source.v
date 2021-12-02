Require Import Strings.String Lists.List ZArith.
From FourCerty Require Import Maps.

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

Inductive ctx : Type :=
  | MtCtx
  | Bind (x : string) (v : val) (rst : ctx).

Inductive err : Type :=
  | OOF
  | Error.

Inductive result {A : Type} : Type :=
  | Err (e : err)
  | Ok (v : A).

Fixpoint lookup (env : ctx) (x : string) :=
  match env with
  | MtCtx => None
  | Bind y v rst =>
    if eqb x y then
      Some v
    else
      lookup rst x
  end.

Fixpoint build_ctx (xs : list string) (vs : list val) :=
  match xs, vs with
  | nil,nil => Some MtCtx
  | x :: xs', v :: vs' =>
    match build_ctx xs' vs' with
    | None => None
    | Some env => Some (Bind x v env)
    end
  | _, _ => None
  end.

Definition eval_tm : partial_map defn -> nat -> tm -> ctx -> @result val :=
  fun (funs : partial_map defn) =>
  fix eval' (f : nat) :=
  fix eval'' (t : tm) :=
  fun (env : ctx) =>

  match t with
  | Const v => Ok v
  | Prim1 op t' => Err Error (* todo *)
  | Prim2 op t1 t2 => Err Error (* todo *)
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
      match lookup env fn with
      | Some _ => Err Error
      | None =>
        match funs fn with
        | None => Err Error
        | Some (Defn _ xs t) =>
          match build_ctx xs vs with
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
    | Ok v => eval'' t2 (Bind x v env)
    end
  end.

