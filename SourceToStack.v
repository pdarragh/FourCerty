Require Import Strings.String Lists.List ZArith.
From FourCerty Require Import Source StackLang.
Import ListNotations.

Module SourceToStack.

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

Fixpoint compile_tm (gamma : list (option string)) (e : SourceLang.tm) : list StackLang.stk_ins :=
  match e with
  | SourceLang.Const v => [StackLang.Push (compile_val v)]
  | SourceLang.Prim1 op e' => compile_tm gamma e' ++ [StackLang.Uop (compile_prim1 op)]
  | SourceLang.Prim2 op e1 e2 => compile_tm gamma e1 ++ compile_tm (None :: gamma) e2 ++ [compile_prim2 op]
  | SourceLang.App l es => fold_right (fun e acc => compile_tm gamma e ++ acc) [] es ++ [StackLang.Call l]
  | SourceLang.If e1 e2 e3 => compile_tm gamma e1 ++ [StackLang.If (compile_tm gamma e2) (compile_tm gamma e3)]
  | SourceLang.Let x e1 e2 => compile_tm gamma e1 ++ compile_tm (Some x :: gamma) e2
  end.

Definition compile_defn (defn: SourceLang.defn) : StackLang.stk_fun :=
  match defn with
  | SourceLang.Defn l xs e => StackLang.Fun l (compile_tm (map Some (List.rev xs)) e)
  end.

Definition compile (src : SourceLang.prg) : StackLang.stk_prg :=
  match src with
  | SourceLang.Prg funs e => StackLang.Prg (map compile_defn funs) (compile_tm [] e)
  end.

Theorem compiler_correctness : forall (f : nat) (prg : SourceLang.prg) (v : SourceLang.val),
  SourceLang.eval f prg = SourceLang.Ok v
  ->
  exists (f' : nat), StackLang.eval f' (compile prg) = StackLang.Values [compile_val v].
Admitted.

End SourceToStack.