Require Import Strings.String Lists.List ZArith.
From ExtLib.Structures Require Import Monad.
From FourCerty Require Import Utility Source StackLang.

Import Utility.

Import ListNotations.
Import MonadNotation.

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

Fixpoint lookup_depth (gamma : list (option string)) (x : string) :=
  match gamma with
  | nil => None
  | None :: gamma' => option_map S (lookup_depth gamma' x)
  | Some y :: gamma' => if eqb x y then Some 0 else option_map S (lookup_depth gamma' x)
  end.

Fixpoint compile_tm (gamma : list (option string)) (e : SourceLang.tm) k
    : StackLang.stk_tm :=
  match e with
  | SourceLang.Const v => StackLang.Ins (StackLang.Push (compile_val v)) k
  | SourceLang.Var x =>
    match lookup_depth gamma x with
    | None => StackLang.Ins StackLang.StkErr k
    | Some n => StackLang.Ins (StackLang.StkRef n) k
    end
  | SourceLang.Prim1 op e' => compile_tm gamma e' (StackLang.Ins (StackLang.Uop (compile_prim1 op)) k)
  | SourceLang.Prim2 op e1 e2 => compile_tm gamma e1 (compile_tm (None :: gamma) e2 (StackLang.Ins (compile_prim2 op) k))
  | SourceLang.App l es =>
    let fix compile_tms gamma es :=
      match es with
      | [] => StackLang.Ins (StackLang.Call l (List.length es)) k
      | e :: es' => compile_tm gamma e (compile_tms (None :: gamma) es')
      end in
    compile_tms gamma es
  | SourceLang.If e1 e2 e3 => compile_tm gamma e1 (StackLang.If (compile_tm gamma e2 StackLang.End) (compile_tm gamma e3 StackLang.End) k)
  | SourceLang.Let x e1 e2 => compile_tm gamma e1 (compile_tm (Some x :: gamma) e2 k)
  end.

Definition compile_defn (defn: SourceLang.defn) : StackLang.stk_fun :=
  match defn with
  | SourceLang.Defn l xs e => StackLang.Fun l (List.length xs) (compile_tm (map Some (List.rev xs)) e StackLang.End)
  end.

Definition compile (src : SourceLang.prg) : StackLang.stk_prg :=
  match src with
  | SourceLang.Prg funs e => StackLang.Prg (map compile_defn funs) (compile_tm [] e StackLang.End)
  end.

Definition compile_result (res : result SourceLang.val) (rst : list StackLang.ins_val)
    : result (list StackLang.ins_val) :=
  v <- res;;
  ret ([compile_val v] ++ rst).

Fixpoint stk_append inss1 inss2 :=
  match inss1 with
  | StackLang.End => inss2
  | StackLang.Ins ins rst => StackLang.Ins ins (stk_append rst inss2)
  | StackLang.If thn els rst => StackLang.If thn els (stk_append rst inss2)
  end.

Lemma seq_eval_ins_end :
    forall (funs : partial_map StackLang.stk_fun)
           (f : nat)
           (ins : StackLang.stk_ins)
           (inss : StackLang.stk_tm)
           (stk : list StackLang.ins_val),
  StackLang.eval' funs f (StackLang.Ins ins inss) stk
  =
  vs <- StackLang.eval' funs f (StackLang.Ins ins StackLang.End) stk;;
  StackLang.eval' funs f inss vs.
Proof.
  intros funs f ins inss stk.
  destruct ins; try (induction f; reflexivity).
  - (* Call *)
    induction f.
    + simpl. destruct (Datatypes.length (firstn n stk) <? n); [reflexivity|].
      destruct (Utility.lookup funs l); [reflexivity|].
      destruct v. destruct (n0 =? n); reflexivity.
    + simpl. destruct (Datatypes.length (firstn n stk) <? n); [reflexivity|].
      destruct (Utility.lookup funs l); [reflexivity|].
      destruct v. destruct (n0 =? n); [|reflexivity].
      destruct (StackLang.eval' funs f ins (firstn n stk)); reflexivity.
  - (* Pop *)
    induction f; destruct stk; reflexivity.
  - (* Swap *)
    induction f; simpl; destruct stk; [reflexivity| |reflexivity|];
    destruct stk; [reflexivity| |reflexivity|]; reflexivity.
  - (* StkRef *)
    induction f; simpl; destruct (nth_error stk n); reflexivity.
  - (* Uop *)
    induction f; simpl; destruct stk; [reflexivity| |reflexivity|];
    destruct (StackLang.do_uop _ _); reflexivity.
  - (* Bop *)
    induction f; simpl; destruct stk; [reflexivity| |reflexivity|];
    destruct stk; [reflexivity| |reflexivity|];
    destruct (StackLang.do_bop _ _); reflexivity.
  - (* Cmp *)
    induction f; simpl; destruct stk; [reflexivity| |reflexivity|]; destruct i;
    destruct stk; try reflexivity;
    destruct i0; reflexivity.
Qed.

Lemma eval_if_false :
    forall (funs : partial_map StackLang.stk_fun)
           (f : nat)
           (inss1 : StackLang.stk_tm)
           (inss2 : StackLang.stk_tm)
           (inss3 : StackLang.stk_tm)
           (stk : list StackLang.ins_val),
  StackLang.eval' funs f (StackLang.If inss1 inss2 inss3) (StackLang.V_Bool false :: stk)
  =
  vs <- StackLang.eval' funs f inss2 stk;;
  StackLang.eval' funs f inss3 vs.
Proof.
  intros funs f inss1 inss2 inss3 stk.
  induction f; reflexivity.
Qed.

Lemma eval_if_true :
    forall (funs : partial_map StackLang.stk_fun)
           (f : nat)
           (inss1 : StackLang.stk_tm)
           (inss2 : StackLang.stk_tm)
           (inss3 : StackLang.stk_tm)
           (v : StackLang.ins_val)
           (stk : list StackLang.ins_val),
  v <> StackLang.V_Bool false ->
    StackLang.eval' funs f (StackLang.If inss1 inss2 inss3) (v :: stk)
    =
    vs <- StackLang.eval' funs f inss1 stk;;
    StackLang.eval' funs f inss3 vs.
Proof.
  intros funs f inss1 inss2 inss3 v stk H.
  destruct v.
  - induction f; reflexivity.
  - destruct b.
    + induction f; reflexivity.
    + contradiction.
Qed.

Lemma seq_eval_if_end : 
    forall (funs : partial_map StackLang.stk_fun)
           (f : nat)
           (inss1 : StackLang.stk_tm)
           (inss2 : StackLang.stk_tm)
           (inss3 : StackLang.stk_tm)
           (stk : list StackLang.ins_val),
  StackLang.eval' funs f (StackLang.If inss1 inss2 inss3) stk
  =
  vs <- StackLang.eval' funs f (StackLang.If inss1 inss2 StackLang.End) stk;;
  StackLang.eval' funs f inss3 vs.
Proof.
  intros funs f inss1 inss2 inss3 stk.
  destruct stk; [induction f; reflexivity|].
  destruct i.
  - induction f;
    rewrite eval_if_true; try discriminate;
    rewrite eval_if_true; try discriminate;
    destruct (StackLang.eval' funs _ inss1 stk); reflexivity.
  - destruct b.
    + induction f;
      rewrite eval_if_true; try discriminate;
      rewrite eval_if_true; try discriminate;
      destruct (StackLang.eval' funs _ inss1 stk); reflexivity.
    + induction f;
      rewrite eval_if_false; rewrite eval_if_false;
      destruct (StackLang.eval' funs _ inss2 stk); reflexivity.
Qed.

Lemma seq_eval_append :
    forall (funs : partial_map StackLang.stk_fun)
           (f : nat)
           (tm1 : StackLang.stk_tm)
           (tm2 : StackLang.stk_tm)
           (stk : list StackLang.ins_val),
  StackLang.eval' funs f (stk_append tm1 tm2) stk
  =
  vs <- StackLang.eval' funs f tm1 stk;;
  StackLang.eval' funs f tm2 vs.
Proof.
  intros funs f tm1.
  induction tm1.
  - induction f; reflexivity.
  - intros tm2 stk.
    simpl (stk_append (StackLang.Ins _ _) _).
    rewrite seq_eval_ins_end.
    rewrite seq_eval_ins_end with (inss:=tm1).
    destruct (StackLang.eval' _ _ (StackLang.Ins _ _) _); [reflexivity|].
    simpl. rewrite IHtm1.
    reflexivity.
  - intros tm2 stk.
    simpl (stk_append (StackLang.If _ _ _) _).
    rewrite seq_eval_if_end.
    rewrite seq_eval_if_end with (inss3:=tm1_3).
    destruct (StackLang.eval' _ _ (StackLang.If _ _ _) _); [reflexivity|].
    simpl. rewrite IHtm1_3.
    reflexivity.
Qed.

Lemma seq_eval_compile :
    forall (funs : partial_map StackLang.stk_fun)
           (f : nat)
           (e : SourceLang.tm)
           (inss : StackLang.stk_tm)
           (gamma : list (option string))
           (stk : list StackLang.ins_val),
  StackLang.eval' funs f (compile_tm gamma e inss) stk
  =
  vs <- StackLang.eval' funs f (compile_tm gamma e StackLang.End) stk;;
  StackLang.eval' funs f inss vs.
Proof.
  intros funs f e.
  induction e.
  - (* Const *) induction f; reflexivity.
  - (* Var *) admit.
  - (* Prim1 *)
    intros inss gamma stk.
    simpl compile_tm.
    rewrite IHe.
    rewrite IHe with (inss:=(StackLang.Ins _ _)).
    destruct (StackLang.eval' funs f (compile_tm _ e _) stk); [reflexivity|].
    simpl. rewrite seq_eval_ins_end. reflexivity.
  - (* Prim2 *)
    intros inss gamma stk.
    simpl compile_tm.
    rewrite IHe1.
    rewrite IHe1 with (inss:=(compile_tm _ _ _)).
    destruct (StackLang.eval' funs f (compile_tm _ e1 _) stk); [reflexivity|].
    simpl.
    rewrite IHe2.
    rewrite IHe2 with (inss:=(StackLang.Ins _ _)).
    destruct (StackLang.eval' funs f (compile_tm _ e2 _) v); [reflexivity|].
    simpl. rewrite seq_eval_ins_end. reflexivity.
  - (* App *) admit.
  - (* If *)
    intros inss gamma stk.
    simpl compile_tm.
    rewrite IHe1.
    rewrite IHe1 with (inss:=(StackLang.If _ _ _)).
    destruct (StackLang.eval' funs f (compile_tm _ e1 _) stk); [reflexivity|].
    simpl. rewrite seq_eval_if_end. reflexivity.
  - (* Let *)
    intros inss gamma stk.
    simpl compile_tm.
    rewrite IHe1.
    rewrite IHe1 with (inss:=(compile_tm _ _ _)).
    destruct (StackLang.eval' funs f (compile_tm _ e1 _)); [reflexivity|].
    simpl. rewrite IHe2. reflexivity.
Admitted.

Lemma eval_prim1 : forall funs f op e env,
    SourceLang.eval' funs f (SourceLang.Prim1 op e) env
    =
    v <- SourceLang.eval' funs f e env;;
    SourceLang.do_prim1 op v.
Proof.
  intros funs f op e env.
  induction f; reflexivity.
Qed.

Lemma eval_prim2 : forall funs f op e1 e2 env,
    SourceLang.eval' funs f (SourceLang.Prim2 op e1 e2) env
    =
    v1 <- SourceLang.eval' funs f e1 env;;
    v2 <- SourceLang.eval' funs f e2 env;;
    SourceLang.do_prim2 op v1 v2.
Proof.
  intros funs f op e env.
  induction f; reflexivity.
Qed.

Lemma compile_prim1_correct : forall op v stk,
    compile_result (SourceLang.do_prim1 op v) stk
    =
    v' <- StackLang.do_uop (compile_prim1 op) (compile_val v);;
    Ok (v' :: stk).
Proof.
  intros op v stk.
  destruct op.
  - (* Add1 *) destruct v; reflexivity.
  - (* Sub1 *) destruct v; reflexivity.
  - (* Not *)
    destruct v.
    + destruct b; reflexivity.
    + reflexivity.
Qed.

Lemma compile_prim2_correct : forall funs f op v1 v2 stk,
    compile_result (SourceLang.do_prim2 op v1 v2) stk
    =
    StackLang.eval' funs f (StackLang.Ins (compile_prim2 op) StackLang.End)
      (compile_val v2 :: compile_val v1 :: stk).
Proof.
  intros funs f op v1 v2 stk.
  destruct op; destruct v1; destruct v2; induction f; reflexivity.
Qed.

Lemma compile_tm_correct :
    forall (s_funs : partial_map SourceLang.defn)
           (sl_funs : partial_map StackLang.stk_fun)
           (f : nat)
           (e : SourceLang.tm)
           (gamma : list (option string))
           (env : SourceLang.environment)
           (stk : list StackLang.ins_val),
  compile_result (SourceLang.eval' empty f e env) stk
  =
  StackLang.eval' empty f (compile_tm gamma e StackLang.End) stk.
Proof.
  intros _ _ f e.
  induction e.
  - (* Const *) induction f; reflexivity.
  - (* Var *)   admit.
  - (* Prim1 *)
    intros gamma env stk.
    simpl compile_tm.
    rewrite seq_eval_compile.
    rewrite <- IHe with gamma env stk.
    rewrite eval_prim1.
    destruct (SourceLang.eval' _ _ e _); [reflexivity|].
    simpl. rewrite compile_prim1_correct. induction f; reflexivity.
  - (* Prim2 *)
    intros gamma env stk.
    simpl compile_tm.
    rewrite seq_eval_compile.
    rewrite <- IHe1 with gamma env stk.
    rewrite eval_prim2.
    destruct (SourceLang.eval' _ _ e1 _); [reflexivity|].
    simpl.
    rewrite seq_eval_compile.
    rewrite <- IHe2 with (None :: gamma) env (compile_val v :: stk).
    destruct (SourceLang.eval' _ _ e2 _); [reflexivity|].
    simpl. apply compile_prim2_correct.
  - (* App *)   admit.
  - (* If *)    admit.
  - (* Let *)   admit.
Admitted.

Theorem compiler_correctness : forall (f : nat) (prg : SourceLang.prg),
  compile_result (SourceLang.eval f prg) [] = StackLang.eval f (compile prg).
Proof.
  intros f prg.
  induction prg.
  unfold compile, SourceLang.eval, StackLang.eval.
  induction e.
  - (* Const *) induction f; reflexivity.
  - (* Var *)   induction f; reflexivity.
  - (* Prim1 *) admit.
  - (* Prim2 *) admit.
  - (* App *)   admit.
  - (* If *)    admit.
  - (* Let *)   admit.
Admitted.

End SourceToStack.
