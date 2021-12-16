From FourCerty Require Import Utility Source.

Import Utility SourceLang.

Module SourceRel.

Inductive do_prim1_R : prim1 -> val -> val -> Prop :=
  | DP1R_add1 : forall i, do_prim1_R P_add1 (V_Int i) (V_Int (i + 1))
  | DP1R_sub1 : forall i, do_prim1_R P_sub1 (V_Int i) (V_Int (i - 1))
  | DP1R_not_false : do_prim1_R P_not (V_Bool false) (V_Bool true)
  | DP1R_not_true : do_prim1_R P_not (V_Bool true) (V_Bool false)
  | DP1R_not_int : forall i, do_prim1_R P_not (V_Int i) (V_Bool false).

Inductive do_prim2_R : prim2 -> val -> val -> val -> Prop :=
  | DP2R_add : forall i1 i2, do_prim2_R P_add (V_Int i1) (V_Int i2) (V_Int (i1 + i2))
  | DP2R_sub : forall i1 i2, do_prim2_R P_sub (V_Int i1) (V_Int i2) (V_Int (i1 - i2))
  | DP2R_and : forall b1 b2, do_prim2_R P_and (V_Bool b1) (V_Bool b2) (V_Bool (b1 && b2))
  | DP2R_or : forall b1 b2, do_prim2_R P_or (V_Bool b1) (V_Bool b2) (V_Bool (b1 || b2))
  | DP2R_eq : forall i1 i2, do_prim2_R P_eq (V_Int i1) (V_Int i2) (V_Bool (Z.eqb i1 i2))
  | DP2R_lt : forall i1 i2, do_prim2_R P_lt (V_Int i1) (V_Int i2) (V_Bool (Z.ltb i1 i2))
  | DP2R_le : forall i1 i2, do_prim2_R P_le (V_Int i1) (V_Int i2) (V_Bool (Z.leb i1 i2)).

Inductive eval_tm_R : nat -> partial_map defn -> partial_map val -> tm -> val -> Prop :=
  | E_Const : forall f funs env v, eval_tm_R f funs env (Const v) v
  | E_Var : forall f funs env x v,
      Ok v = lookup env x ->
      eval_tm_R f funs env (Var x) v
  | E_Prim1 : forall f funs env op t v1 v2,
      eval_tm_R f funs env t v1 ->
      do_prim1_R op v1 v2 ->
      eval_tm_R f funs env (Prim1 op t) v2
  | E_Prim2 : forall f funs env op t1 t2 v1 v2 v3,
      eval_tm_R f funs env t1 v1 ->
      eval_tm_R f funs env t2 v2 ->
      do_prim2_R op v1 v2 v3 ->
      eval_tm_R f funs env (Prim2 op t1 t2) v3
  | E_AppNil : forall f f' funs env fn xs t v,
      f = S f' ->
      Ok (Defn fn xs t) = lookup funs fn ->
      eval_tm_R f' funs env t v ->
      eval_tm_R f funs env (App fn []) v
(* TODO: Need a case for App with non-zero list of arguments. *)
  | E_IfTrue : forall f funs env t1 t2 t3 v,
      eval_tm_R f funs env t1 (V_Bool true) ->
      eval_tm_R f funs env t2 v ->
      eval_tm_R f funs env (If t1 t2 t3) v
  | E_IfFalse : forall f funs env t1 t2 t3 v,
      eval_tm_R f funs env t1 (V_Bool false) ->
      eval_tm_R f funs env t3 v ->
      eval_tm_R f funs env (If t1 t2 t3) v
  | E_Let : forall f funs env x t1 t2 v1 v2,
      eval_tm_R f funs env t1 v1 ->
      eval_tm_R f funs (update env x v1) t2 v2 ->
      eval_tm_R f funs env (Let x t1 t2) v2.

Inductive extract_funs_R : list defn -> partial_map defn -> Prop :=
  | EF_Nil : extract_funs_R [] empty
  | EF_Cons : forall ds es fn xs t,
      extract_funs_R ds es ->
      extract_funs_R ((Defn fn xs t) :: ds) (update es fn (Defn fn xs t)).

Inductive eval_R : nat -> prg -> val -> Prop :=
  | E_Prg : forall f fs ds t v,
      extract_funs_R ds fs ->
      eval_tm_R f fs empty t v ->
      eval_R f (Prg ds t) v.

End SourceRel.

Module SourceRelExamples.

Import SourceRel.

Definition true := (Const (V_Bool true)).
Definition false := (Const (V_Bool false)).

Definition zero := (Const (V_Int 0)).
Definition one := (Const (V_Int 1)).
Definition two := (Const (V_Int 2)).
Definition three := (Const (V_Int 3)).

Definition if1 := (If true (Prim1 P_add1 two) (Prim2 P_sub three one)).
Definition if2 := (If (Prim2 P_le if1 three) zero false).

Lemma eval_example1 :
  eval_R 0 (Prg [] if1) (V_Int 3).
Proof with (repeat constructor).
  eapply E_Prg...
  eapply E_Prim1...
Qed.

Lemma eval_example2 :
  eval_R 0 (Prg [] if2 ) (V_Int 0).
Proof with (repeat constructor).
  eapply E_Prg; [apply EF_Nil|]...
  eapply E_Prim2...
  - eapply E_Prim1...
  - eapply DP2R_le...
Qed.

(* TODO: Add more examples that actually do function lookup/application. *)

End SourceRelExamples.
