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
    : list StackLang.stk_ins :=
  match e with
  | SourceLang.Const v => [StackLang.Push (compile_val v)]
  | SourceLang.Var x =>
    match lookup_depth gamma x with
    | None => [StackLang.Err]
    | Some n => [StackLang.StkRef n]
    end
  | SourceLang.Prim1 op e' => compile_tm gamma e' ++ [StackLang.Uop (compile_prim1 op)]
  | SourceLang.Prim2 op e1 e2 => compile_tm gamma e1 ++ compile_tm (None :: gamma) e2 ++ [compile_prim2 op]
  | SourceLang.App l es =>
    let fix compile_tms gamma es :=
      match es with
      | [] => []
      | e :: es' => compile_tm gamma e ++ compile_tms (None :: gamma) es'
      end in
    compile_tms gamma es ++ [StackLang.Call l (length es)]
  | SourceLang.If e1 e2 e3 => compile_tm gamma e1 ++ [StackLang.If (compile_tm gamma e2) (compile_tm gamma e3)]
  | SourceLang.Let x e1 e2 => compile_tm gamma e1 ++ compile_tm (Some x :: gamma) e2
  end.

Definition compile_defn (defn: SourceLang.defn) : StackLang.stk_fun :=
  match defn with
  | SourceLang.Defn l xs e => StackLang.Fun l (length xs) (compile_tm (map Some (List.rev xs)) e)
  end.

Fixpoint join_option_list {A} (lst : list (option A)) : option (list A) :=
  match lst with
  | nil => Some nil
  | None :: _ => None
  | Some a :: rst => option_map (cons a) (join_option_list rst)
  end.

Definition compile (src : SourceLang.prg) : StackLang.stk_prg :=
  match src with
  | SourceLang.Prg funs e => StackLang.Prg (map compile_defn funs) (compile_tm [] e)
  end.

Definition compile_result (res : SourceLang.result) :=
  match res with
  | SourceLang.Err SourceLang.OOF => StackLang.OOF
  | SourceLang.Err SourceLang.Error => StackLang.Error
  | SourceLang.Ok v => StackLang.Value (compile_val v)
  end.

Theorem compiler_correctness : forall (f : nat) (prg : SourceLang.prg),
  compile_result (SourceLang.eval f prg) = StackLang.eval f (compile prg).
Proof.
  intros f prg.
Admitted.

End SourceToStack.