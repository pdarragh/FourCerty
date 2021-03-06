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
  | SourceLang.Prim1 op e' =>
      compile_tm gamma e' (StackLang.Ins (StackLang.Uop (compile_prim1 op)) k)
  | SourceLang.Prim2 op e1 e2 =>
      compile_tm gamma e1 (compile_tm (None :: gamma) e2 (StackLang.Ins (compile_prim2 op) k))
  | SourceLang.App l e =>
      compile_tm gamma e (StackLang.Ins (StackLang.Call l 1) k)
  | SourceLang.If e1 e2 e3 =>
      compile_tm gamma e1 (StackLang.If (compile_tm gamma e2 StackLang.End)
                                        (compile_tm gamma e3 StackLang.End) k)
  | SourceLang.Let x e1 e2 =>
      compile_tm gamma e1 (compile_tm (Some x :: gamma) e2 (StackLang.Ins StackLang.Swap
                                                           (StackLang.Ins StackLang.Pop k)))
  end.

Definition compile_defn (defn: SourceLang.defn) : StackLang.stk_fun :=
  match defn with
  | SourceLang.Defn l x e =>
      StackLang.Fun l 1 (compile_tm [Some x] e (StackLang.Ins StackLang.Swap
                                                 (StackLang.Ins StackLang.Pop StackLang.End)))
  end.

Definition compile (src : SourceLang.prg) : StackLang.stk_prg :=
  match src with
  | SourceLang.Prg funs e =>
      StackLang.Prg (map compile_defn funs) (compile_tm [] e StackLang.End)
  end.

Definition compile_result (res : result SourceLang.val)
    : result (list StackLang.ins_val) :=
  v <- res;;
  ret [compile_val v].

(* Evaluation Lemmas *)

Lemma eval_if_false :
    forall (funs : partial_map (nat * StackLang.stk_tm))
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
    forall (funs : partial_map (nat * StackLang.stk_tm))
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

Lemma eval_app : forall funs f fn e env,
    SourceLang.eval' funs f (SourceLang.App fn e) env
    =
    v <- SourceLang.eval' funs f e env;;
    '(x, t) <- lookup funs fn;;
    match f with
    | O => Err OOF
    | S f' => SourceLang.eval' funs f' t (update empty x v)
    end.
Proof.
  intros funs f fn e env.
  induction f; reflexivity.
Qed.

Lemma eval_if : forall funs f e1 e2 e3 env,
    SourceLang.eval' funs f (SourceLang.If e1 e2 e3) env
    =
    v1 <- SourceLang.eval' funs f e1 env;;
    match v1 with
    | SourceLang.V_Bool false => SourceLang.eval' funs f e3 env
    | _ => SourceLang.eval' funs f e2 env
    end.
Proof.
  intros funs f e1 e2 e3 env.
  induction f; reflexivity.
Qed.

Lemma eval_let : forall funs f x e1 e2 env,
    SourceLang.eval' funs f (SourceLang.Let x e1 e2) env
    =
    v <- SourceLang.eval' funs f e1 env;;
    SourceLang.eval' funs f e2 (update env x v).
Proof.
  intros funs f x e1 e2 env.
  induction f; reflexivity.
Qed.

Lemma eval_var : forall funs f x env,
    SourceLang.eval' funs f (SourceLang.Var x) env = lookup env x.
Proof.
  intros funs f x env.
  induction f; reflexivity.
Qed.

(* Sequencing Lemmas *)

Lemma seq_eval_ins_end :
    forall (funs : partial_map (nat * StackLang.stk_tm))
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
      destruct (StackLang.eval' funs f s (firstn n stk)); reflexivity.
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

Lemma seq_eval_if_end :
    forall (funs : partial_map (nat * StackLang.stk_tm))
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

Fixpoint stk_append inss1 inss2 :=
  match inss1 with
  | StackLang.End => inss2
  | StackLang.Ins ins rst => StackLang.Ins ins (stk_append rst inss2)
  | StackLang.If thn els rst => StackLang.If thn els (stk_append rst inss2)
  end.

Lemma seq_eval_append :
    forall (funs : partial_map (nat * StackLang.stk_tm))
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
    forall (funs : partial_map (nat * StackLang.stk_tm))
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
  - (* Const *)
    induction f; reflexivity.
  - (* Var *)
    intros inss gamma stk.
    simpl compile_tm.
    destruct (lookup_depth gamma x); rewrite seq_eval_ins_end; reflexivity.
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
  - (* App *)
    intros inss gamma stk.
    simpl compile_tm.
    rewrite IHe.
    rewrite IHe with (inss:=(StackLang.Ins _ _)).
    destruct (StackLang.eval' funs f (compile_tm _ e _)); [reflexivity|].
    simpl. rewrite seq_eval_ins_end. reflexivity.
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
    simpl.
    rewrite IHe2.
    rewrite IHe2 with (inss:=(StackLang.Ins StackLang.Swap
                               (StackLang.Ins StackLang.Pop StackLang.End))).
    destruct (StackLang.eval' _ _ (compile_tm _ e2 _)); [reflexivity|].
    simpl.
    assert (H: (StackLang.Ins StackLang.Swap (StackLang.Ins StackLang.Pop inss))
               = (stk_append (StackLang.Ins StackLang.Swap
                               (StackLang.Ins StackLang.Pop StackLang.End))
                             inss)). { reflexivity. }
    rewrite H. rewrite seq_eval_append. reflexivity.
Qed.

(* Consistency Lemmas *)

Inductive consistent_envs :
    SourceLang.environment -> list (option string) -> list StackLang.ins_val -> Prop :=
  | consistent_empty : consistent_envs empty [] []
  | consistent_var env gamma stk x v (c : consistent_envs env gamma stk) :
      consistent_envs (x |-> v; env) (Some x :: gamma) (compile_val v :: stk)
  | consistent_val env gamma stk v (c : consistent_envs env gamma stk) :
      consistent_envs env (None :: gamma) (v :: stk).

Lemma consistent_envs_in_scope :
    forall env gamma stk,
      consistent_envs env gamma stk ->
        forall x v, lookup env x = Ok v ->
          exists n, lookup_depth gamma x = Some n /\ nth_error stk n = Some (compile_val v).
Proof.
  intros env gamma stk HC.
  induction HC.
  - (* empty *)
    intros x v H. discriminate.
  - (* push var *)
    intros x0 v0 H. simpl.
    destruct (eqb x0 x) eqn:E.
    + (* var on top of stack *)
      apply eqb_eq in E as Heq.
      unfold lookup in H.
      rewrite Heq in H.
      rewrite update_eq in H.
      injection H as H.
      exists 0.
      simpl. rewrite H.
      split; reflexivity.
    + (* var lower *)
      apply eqb_neq in E as Hneq.
      unfold lookup in H, IHHC.
      rewrite update_neq in H; [|auto].
      apply IHHC in H as [n [H1 H2]].
      rewrite H1.
      exists (S n).
      split.
      * reflexivity.
      * assumption.
  - (* push unnamed value *)
    intros x v0 H. simpl.
    apply IHHC in H as [n [H1 H2]].
    rewrite H1.
    exists (S n).
    split.
    * reflexivity.
    * assumption.
Qed.

Lemma consistent_envs_err :
    forall env gamma stk,
      consistent_envs env gamma stk ->
        forall x, lookup env x = Err Error -> lookup_depth gamma x = None.
Proof.
  intros env gamma stk HC.
  induction HC.
  - (* empty *)
    intros x H. reflexivity.
  - (* push var *)
    intros x0 H. simpl.
    destruct (x0 =? x)%string eqn:E.
    + apply eqb_eq in E as Heq.
      unfold lookup in H.
      rewrite Heq in H.
      rewrite update_eq in H.
      discriminate.
    + apply eqb_neq in E as Hneq.
      unfold lookup in H, IHHC.
      rewrite update_neq in H; [|auto].
      specialize IHHC with x0.
      apply IHHC in H.
      rewrite H.
      reflexivity.
  - (* push val *)
    intros x H.
    simpl.
    rewrite (IHHC x H).
    reflexivity.
Qed.

Inductive consistent_funs :
    partial_map (string * SourceLang.tm) -> partial_map (nat * StackLang.stk_tm) -> Prop :=
  | consistent_funs_empty : consistent_funs empty empty
  | consistent_funs_update l x t s_funs sl_funs (c : consistent_funs s_funs sl_funs) :
      consistent_funs (l |-> (x, t); s_funs)
                      (l |-> (1, compile_tm [Some x] t
                                   (StackLang.Ins StackLang.Swap
                                   (StackLang.Ins StackLang.Pop StackLang.End)));
                             sl_funs).

Definition consistent_funs_consistent
    (s_funs : partial_map (string * SourceLang.tm))
    (sl_funs : partial_map (nat * StackLang.stk_tm)) :=
  consistent_funs s_funs sl_funs ->
  forall (x : string),
    (lookup s_funs x = Err Error /\ lookup sl_funs x = Err Error)
    \/
    (exists (y : string) (e : SourceLang.tm),
      lookup s_funs x = Ok (y, e)
      /\
      lookup sl_funs x = Ok (1, (compile_tm [Some y] e
                                  (StackLang.Ins StackLang.Swap
                                    (StackLang.Ins StackLang.Pop StackLang.End))))
      /\
      (forall (s_funs : partial_map (string * SourceLang.tm))
              (sl_funs : partial_map (nat * StackLang.stk_tm))
              (f : nat) (v : SourceLang.val),
        consistent_funs s_funs sl_funs
        ->
        compile_result (SourceLang.eval' s_funs f e (y |-> v))
        =
        StackLang.eval' sl_funs f (compile_tm [Some y] e
                                    (StackLang.Ins StackLang.Swap
                                      (StackLang.Ins StackLang.Pop StackLang.End)))
                        [compile_val v])).

(* Correctness Lemmas *)

Definition append_result (res : result (list StackLang.ins_val)) (rst : list StackLang.ins_val)
    : result (list StackLang.ins_val) :=
  vs <- res;;
  ret (vs ++ rst).

Lemma compile_prim1_correct : forall op v stk,
    append_result (compile_result (SourceLang.do_prim1 op v)) stk
    =
    v' <- StackLang.do_uop (compile_prim1 op) (compile_val v);;
    Ok (v' :: stk).
Proof.
  intros op v.
  destruct op.
  - (* Add1 *) destruct v; reflexivity.
  - (* Sub1 *) destruct v; reflexivity.
  - (* Not *)
    destruct v.
    + destruct b; reflexivity.
    + reflexivity.
Qed.

Lemma compile_prim2_correct : forall funs f op v1 v2 stk,
    append_result (compile_result (SourceLang.do_prim2 op v1 v2)) stk
    =
    StackLang.eval' funs f (StackLang.Ins (compile_prim2 op) StackLang.End)
      (compile_val v2 :: compile_val v1 :: stk).
Proof.
  intros funs f op v1 v2.
  destruct op; destruct v1; destruct v2; induction f; reflexivity.
Qed.

Lemma compile_tm_correct :
    forall (s_funs : partial_map (string * SourceLang.tm))
           (sl_funs : partial_map (nat * StackLang.stk_tm))
           (f : nat)
           (e : SourceLang.tm)
           (env : SourceLang.environment)
           (gamma : list (option string))
           (stk : list StackLang.ins_val),
  consistent_funs s_funs sl_funs ->
  consistent_funs_consistent s_funs sl_funs ->
  consistent_envs env gamma stk ->
    append_result (compile_result (SourceLang.eval' s_funs f e env)) stk
    =
    StackLang.eval' sl_funs f (compile_tm gamma e StackLang.End) stk.
Proof.
  intros s_funs sl_funs f e.
  induction e.
  - (* Const *)
    induction f; reflexivity.
  - (* Var *)
    intros env gamma stk HF HF' HC.
    simpl compile_tm.
    rewrite eval_var.
    destruct (lookup env x) eqn:E.
    + assert (Herr : e = Error).
      { unfold lookup in E.
        destruct (env x); [discriminate|].
        injection E as E. auto. }
      rewrite Herr in *.
      apply (consistent_envs_err env gamma stk HC) in E as Hdepth.
      rewrite Hdepth.
      induction f; reflexivity.
    + apply (consistent_envs_in_scope env gamma stk HC) in E as [n [H1 H2]].
      rewrite H1.
      induction f; simpl; rewrite H2; reflexivity.
  - (* Prim1 *)
    intros env gamma stk HF HF' HC.
    simpl compile_tm.
    rewrite seq_eval_compile.
    rewrite <- (IHe env gamma stk HF HF' HC).
    rewrite eval_prim1.
    destruct (SourceLang.eval' _ _ e _); [reflexivity|].
    simpl. rewrite compile_prim1_correct. induction f; reflexivity.
  - (* Prim2 *)
    intros env gamma stk HF HF' HC.
    simpl compile_tm.
    rewrite seq_eval_compile.
    rewrite <- (IHe1 env gamma stk HF HF' HC).
    rewrite eval_prim2.
    destruct (SourceLang.eval' _ _ e1 _); [reflexivity|].
    simpl.
    rewrite seq_eval_compile.
    rewrite <- (IHe2 env (None :: gamma) (compile_val v :: stk) HF HF'
                     (consistent_val env gamma stk (compile_val v) HC)).
    destruct (SourceLang.eval' _ _ e2 _); [reflexivity|].
    simpl. rewrite compile_prim2_correct with (funs:=sl_funs) (f:=f).
    induction f; reflexivity.
  - (* App *)
    intros env gamma stk HF HF' HC.
    simpl compile_tm.
    rewrite seq_eval_compile.
    rewrite <- (IHe env gamma stk HF HF' HC).
    rewrite eval_app.
    destruct (SourceLang.eval' s_funs f e env); [reflexivity|].
    simpl.
    destruct (HF' HF f0).
    destruct (lookup s_funs f0) eqn:E.
    + destruct H. injection H as H. rewrite H. destruct f; simpl; rewrite H0; reflexivity.
    + destruct H. discriminate.
    + destruct H as [x [e' [H1 [H2 H3]]]].
      rewrite H1.
      destruct f.
      * simpl. rewrite H2. reflexivity.
      * simpl. rewrite H2. simpl.
        rewrite H3 with (sl_funs:=sl_funs); [|assumption].
        induction f; reflexivity.
  - (* If *)
    intros env gamma stk HF HF' HC.
    simpl compile_tm.
    rewrite seq_eval_compile.
    rewrite <- (IHe1 env gamma stk HF HF' HC).
    rewrite eval_if.
    destruct (SourceLang.eval' _ _ e1 _); [reflexivity|].
    simpl. destruct v.
    + (* v is bool *)
      destruct b.
      * (* true *)
        rewrite (IHe2 env gamma stk HF HF' HC).
        simpl compile_val.
        rewrite eval_if_true; [|discriminate].
        destruct (StackLang.eval' _ _ (compile_tm _ e2 _) _); [reflexivity|].
        induction f; reflexivity.
      * (* false *)
        rewrite (IHe3 env gamma stk HF HF' HC).
        simpl compile_val.
        rewrite eval_if_false.
        destruct (StackLang.eval' _ _ (compile_tm _ e3 _) _); [reflexivity|].
        induction f; reflexivity.
    + rewrite (IHe2 env gamma stk HF HF' HC).
      simpl compile_val.
      rewrite eval_if_true; [|discriminate].
      destruct (StackLang.eval' _ _ (compile_tm _ e2 _) _); [reflexivity|].
      induction f; reflexivity.
  - (* Let *)
    intros env gamma stk HF HF' HC.
    simpl compile_tm.
    rewrite seq_eval_compile.
    rewrite <- (IHe1 env gamma stk HF HF' HC).
    rewrite eval_let.
    destruct (SourceLang.eval' _ _ e1 _); [reflexivity|].
    simpl. rewrite seq_eval_compile.
    simpl. rewrite <- (IHe2 (x |-> v; env) (Some x :: gamma) (compile_val v :: stk) HF HF'
                            (consistent_var env gamma stk x v HC)).
    destruct (SourceLang.eval' _ _ e2 _); [reflexivity|].
    induction f; reflexivity.
Qed.

(* Stronger Consistency Lemmas *)

Theorem append_result_empty : forall (res : result (list StackLang.ins_val)),
  res = append_result res [].
Proof.
  intros res.
  destruct res.
  - reflexivity.
  - unfold append_result. simpl.
    rewrite app_nil_r.
    reflexivity.
Qed.

Lemma compile_funs_consistent :
    forall (defns : list SourceLang.defn),
  consistent_funs (SourceLang.extract_funs defns)
                  (StackLang.extract_funs (map compile_defn defns)).
Proof.
  intros defns.
  induction defns.
  - simpl. apply consistent_funs_empty.
  - simpl. destruct a.
    apply consistent_funs_update.
    apply IHdefns.
Qed.

Lemma consistent_funs_indeed_consistent :
    forall (s_funs : partial_map (string * SourceLang.tm))
           (sl_funs : partial_map (nat * StackLang.stk_tm)),
  consistent_funs s_funs sl_funs ->
  consistent_funs_consistent s_funs sl_funs.
Proof.
  intros s_funs sl_funs H.
  induction H.
  - unfold consistent_funs_consistent.
    intros H x.
    left. split; reflexivity.
  - unfold consistent_funs_consistent.
    intros H' y.
    destruct (l =? y)%string eqn:E.
    + apply eqb_eq in E.
      right.
      exists x. exists t.
      rewrite E.
      split. { unfold lookup. rewrite update_eq. reflexivity. }
      split. { unfold lookup. rewrite update_eq. reflexivity. }
      intros.
      rewrite seq_eval_compile.
      rewrite <- compile_tm_correct with (s_funs:=s_funs0) (env:=(x |-> v)).
      * destruct (SourceLang.eval' _ _ _ _); [reflexivity|].
        destruct f; reflexivity.
      * assumption.
      * admit.
      * apply consistent_var.
        apply consistent_empty.
    + apply eqb_neq in E.
      apply IHconsistent_funs in H as H''.
      destruct (H'' y).
      * left. unfold lookup in *. simpl in *.
        rewrite update_neq; [|assumption].
        rewrite update_neq; [|assumption].
        assumption.
      * right. destruct H0 as [y0 [e [H1 [H2 H3]]]].
        exists y0. exists e.
        unfold lookup in *. simpl in *.
        rewrite update_neq; [|assumption].
        rewrite update_neq; [|assumption].
        split; [assumption|].
        split; [assumption|].
        assumption.
Admitted.

(* Full Correctness Theorem *)

Theorem compiler_correctness : forall (f : nat) (prg : SourceLang.prg),
  compile_result (SourceLang.eval f prg) = StackLang.eval f (compile prg).
Proof.
  intros f prg.
  rewrite (append_result_empty (compile_result _)).
  induction prg.
  unfold compile, SourceLang.eval, StackLang.eval.
  apply compile_tm_correct.
  - apply compile_funs_consistent.
  - apply consistent_funs_indeed_consistent.
    apply compile_funs_consistent.
  - apply consistent_empty.
Qed.

End SourceToStack.
