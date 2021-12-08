Require Import Strings.String Lists.List ZArith.
From FourCerty Require Import Source StackLang.
Import ListNotations.

Module SourceToStack.

Definition left_append {A} (l1 : list A) (l2 : list A) := l2 ++ l1.

Definition compile_val (v : SourceLang.val) :=
  match v with
  | SourceLang.V_Bool b => StackLang.V_Bool b
  | SourceLang.V_Int i => StackLang.V_Int i
  end.

Definition compile_prim1 (op : SourceLang.prim1) : StackLang.ins_uop :=
  match op with
  | SourceLang.P_add1 => StackLang.U_Add1
  | SourceLang.P_sub1 => StackLang.U_Sub1
  | SourceLang.P_not => StackLang.U_Not
  end.

Definition compile_prim2 (op : SourceLang.prim2) : StackLang.stk_ins :=
  match op with
  | SourceLang.P_add => StackLang.Bop StackLang.B_Add
  | SourceLang.P_sub => StackLang.Bop StackLang.B_Sub
  | SourceLang.P_and => StackLang.Bop StackLang.B_And
  | SourceLang.P_or => StackLang.Bop StackLang.B_Or
  | SourceLang.P_eq => StackLang.Cmp StackLang.C_Eq
  | SourceLang.P_lt => StackLang.Cmp StackLang.C_Lt
  | SourceLang.P_le => StackLang.Cmp StackLang.C_Le
  end.

Fixpoint lookup_depth (gamma : list (option string)) (x : string) :=
  match gamma with
  | nil => None
  | None :: gamma' => option_map S (lookup_depth gamma' x)
  | Some y :: gamma' => if eqb x y then Some 0 else option_map S (lookup_depth gamma' x)
  end.

Fixpoint compile_tm (gamma : list (option string)) (e : SourceLang.tm)
    : option (list StackLang.stk_ins) :=
  match e with
  | SourceLang.Const v => Some [StackLang.Push (compile_val v)]
  | SourceLang.Var x =>
    match lookup_depth gamma x with
    | None => None
    | Some n => Some [StackLang.StkRef n]
    end
  | SourceLang.Prim1 op e' =>
    match compile_tm gamma e' with
    | None => None
    | Some ins => Some (ins ++ [StackLang.Uop (compile_prim1 op)])
    end
  | SourceLang.Prim2 op e1 e2 =>
    match compile_tm gamma e1 with
    | None => None
    | Some ins1 =>
      match compile_tm (None :: gamma) e2 with
      | None => None
      | Some ins2 => Some (ins1 ++ ins2 ++ [compile_prim2 op])
      end
    end
  | SourceLang.App l es =>
    let fix compile_tms gamma es :=
      match es with
      | nil => Some nil
      | e :: es' =>
        match compile_tm gamma e with
        | None => None
        | Some ins =>
          match compile_tms (None :: gamma) es' with
          | None => None
          | Some inss => Some (ins ++ inss)
          end
        end
      end in
    match compile_tms gamma es with
    | None => None
    | Some ins => Some (ins ++ [StackLang.Call l (length es)])
    end
  | SourceLang.If e1 e2 e3 =>
    match compile_tm gamma e1 with
    | None => None
    | Some ins1 =>
      match compile_tm gamma e2 with
      | None => None
      | Some ins2 =>
        match compile_tm gamma e3 with
        | None => None
        | Some ins3 => Some (ins1 ++ [StackLang.If ins2 ins3])
        end
      end
    end
  | SourceLang.Let x e1 e2 =>
    match compile_tm gamma e1 with
    | None => None
    | Some ins1 =>
      match compile_tm (Some x :: gamma) e2 with
      | None => None
      | Some ins2 => Some (ins1 ++ ins2)
      end
    end
  end.

Definition compile_defn (defn: SourceLang.defn) : option StackLang.stk_fun :=
  match defn with
  | SourceLang.Defn l xs e =>
    match compile_tm (map Some (List.rev xs)) e with
    | None => None
    | Some ins => Some (StackLang.Fun l (length xs) ins)
    end
  end.

Fixpoint join_option_list {A} (lst : list (option A)) : option (list A) :=
  match lst with
  | nil => Some nil
  | None :: _ => None
  | Some a :: rst => option_map (cons a) (join_option_list rst)
  end.

Definition compile (src : SourceLang.prg) : option StackLang.stk_prg :=
  match src with
  | SourceLang.Prg funs e =>
    match join_option_list (map compile_defn funs) with
    | None => None
    | Some inss =>
      match compile_tm [] e with
      | None => None
      | Some ins => Some (StackLang.Prg inss ins)
      end
    end
  end.

Theorem compiler_correctness : forall (f : nat) (prg : SourceLang.prg) (v : SourceLang.val),
  SourceLang.eval f prg = SourceLang.Ok v ->
  exists (stk : StackLang.stk_prg), compile prg = Some stk ->
  exists (f' : nat), StackLang.eval f' stk = StackLang.Value (compile_val v).
Proof.
Admitted.

End SourceToStack.