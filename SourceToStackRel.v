From FourCerty Require Import Utility Source StackLang.

Import Utility.

Module STSRel.

Inductive compile_val_R : SourceLang.val -> StackLang.ins_val -> Prop :=
  | CVR_Bool : forall b,
      compile_val_R (SourceLang.V_Bool b) (StackLang.V_Bool b)
  | CVR_Int : forall i,
      compile_val_R (SourceLang.V_Int i) (StackLang.V_Int i).

Inductive compile_prim1_R : SourceLang.prim1 -> StackLang.ins_uop -> Prop :=
  | CP1R_add1 : compile_prim1_R SourceLang.P_add1 StackLang.U_Add1
  | CP1R_sub1 : compile_prim1_R SourceLang.P_sub1 StackLang.U_Sub1
  | CP1R_not : compile_prim1_R SourceLang.P_not StackLang.U_Not.

Inductive compile_prim2_R : SourceLang.prim2 -> StackLang.stk_ins -> Prop :=
  | CP2R_add : compile_prim2_R SourceLang.P_add (StackLang.Bop StackLang.B_Add)
  | CP2R_sub : compile_prim2_R SourceLang.P_sub (StackLang.Bop StackLang.B_Sub)
  | CP2R_and : compile_prim2_R SourceLang.P_add (StackLang.Bop StackLang.B_And)
  | CP2R_or : compile_prim2_R SourceLang.P_or (StackLang.Bop StackLang.B_Or)
  | CP2R_eq : compile_prim2_R SourceLang.P_eq (StackLang.Cmp StackLang.C_Eq)
  | CP2R_lt : compile_prim2_R SourceLang.P_lt (StackLang.Cmp StackLang.C_Lt)
  | CP2R_le : compile_prim2_R SourceLang.P_le (StackLang.Cmp StackLang.C_Le).

Inductive context_contains : list (option string) -> string -> Prop :=
  | CC_eq : forall x xs, context_contains ((Some x) :: xs) x
  | CC_next_none : forall x xs, context_contains (None :: xs) x -> context_contains xs x
  | CC_next_some : forall x y xs,
      context_contains (Some y :: xs) x ->
      x <> y ->
      context_contains xs x.

Fixpoint lookup_depth (gamma : list (option string)) (x : string) :=
  match gamma with
  | nil => None
  | None :: gamma' => option_map S (lookup_depth gamma' x)
  | Some y :: gamma' => if eqb x y then Some 0 else option_map S (lookup_depth gamma' x)
  end.

Inductive compile_tm_R : list (option string) -> StackLang.stk_tm -> SourceLang.tm -> StackLang.stk_tm -> Prop :=
  | CST_Const : forall gamma k v1 v2,
      compile_val_R v1 v2 ->
      compile_tm_R gamma k (SourceLang.Const v1) (StackLang.Ins (StackLang.Push v2) k)
  | CST_Var : forall gamma k x n,
      context_contains gamma x ->
      Some n = lookup_depth gamma x ->
      compile_tm_R gamma k (SourceLang.Var x) (StackLang.Ins (StackLang.StkRef n) k)
  | CST_Prim1 : forall gamma k op uop e t,
      compile_prim1_R op uop ->
      compile_tm_R gamma (StackLang.Ins (StackLang.Uop uop) k) e t ->
      compile_tm_R gamma k (SourceLang.Prim1 op e) t
  | CST_Prim2 : forall gamma k op bop_ins e1 e2 t1 t2,
      compile_prim2_R op bop_ins ->
      compile_tm_R (None :: gamma) (StackLang.Ins bop_ins k) e2 t1 ->
      compile_tm_R gamma t1 e1 t2 ->
      compile_tm_R gamma k (SourceLang.Prim2 op e1 e2) t2
  | CST_App_nil : forall gamma k l es,
      es = [] ->
      compile_tm_R gamma k (SourceLang.App l es) (StackLang.Ins (StackLang.Call l (List.length es)) k)
  | CST_App_cons : forall gamma k l es e es' t1 t2,
      es = e :: es' ->
      compile_tm_R (None :: gamma) k (SourceLang.App l es') t1 ->
      compile_tm_R gamma t1 e t2 ->
      compile_tm_R gamma k (SourceLang.App l es) t2
  | CST_If : forall gamma k e1 e2 e3 t1 t2 t3,
      compile_tm_R gamma StackLang.End e3 t1 ->
      compile_tm_R gamma StackLang.End e2 t2 ->
      compile_tm_R gamma StackLang.End e1 t3 ->
      compile_tm_R gamma k (SourceLang.If e1 e2 e3) t3
  | CST_Let : forall gamma k x e1 e2 t1 t2,
      compile_tm_R (Some x :: gamma) k e2 t1 ->
      compile_tm_R gamma t1 e1 t2 ->
      compile_tm_R gamma k (SourceLang.Let x e1 e2) t2.

Inductive compile_defn_R : SourceLang.defn -> StackLang.stk_fun -> Prop :=
  | CD_Defn : forall l xs e t,
      compile_tm_R (map Some (List.rev xs)) StackLang.End e t ->
      compile_defn_R (SourceLang.Defn l xs e) (StackLang.Fun l (List.length xs) t).

Inductive compile_defns_R : list SourceLang.defn -> list StackLang.stk_fun -> Prop :=
  | CDs_nil : compile_defns_R [] []
  | CDs_cons : forall f fs cf cfs,
      compile_defn_R f cf ->
      compile_defns_R fs cfs ->
      compile_defns_R (f :: fs) (cf :: cfs).

Inductive compile_R : SourceLang.prg -> StackLang.stk_prg -> Prop :=
  | C_Prg : forall fs cfs e t,
      compile_defns_R fs cfs ->
      compile_tm_R [] StackLang.End e t ->
      compile_R (SourceLang.Prg fs e) (StackLang.Prg cfs t).

End STSRel.
