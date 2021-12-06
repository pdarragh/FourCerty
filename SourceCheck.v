(* Strings *)
Require Import Strings.String ZArith.
Open Scope string_scope.

(* QuickChick *)
From QuickChick Require Import QuickChick.
Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* Notations *)
Import MonadNotation.
Import QcDefaultNotation.

(* Source *)
From FourCerty Require Import Source.
Import SourceLang.

(* Begin! *)
Module SourceCheck.

Definition show_val' (v : val) : string :=
  match v with
  | V_Bool true => "true"
  | V_Bool false => "false"
  | V_Int i => show i
  end.

Instance show_val : Show val :=
  { show := show_val' }.

Definition show_prim1' (op : prim1) : string :=
  match op with
  | P_add1 => "add1"
  | P_sub1 => "sub1"
  | P_not => "not"
  end.

Instance show_prim1 : Show prim1 :=
  { show := show_prim1' }.

Definition show_prim2' (op : prim2) : string :=
  match op with
  | P_add => "+"
  | P_sub => "-"
  | P_and => "&&"
  | P_or => "||"
  | P_eq => "=="
  | P_lt => "<"
  | P_le => "<="
  end.

Instance show_prim2 : Show prim2 :=
  { show := show_prim2' }.

Fixpoint show_tm' (t : tm) : string :=
  match t with
  | Const v => show v
  | Prim1 op t' => show op ++ " (" ++ show_tm' t' ++ ")"
  | Prim2 op t1 t2 => "(" ++ show_tm' t1 ++ ") " ++ show op ++ " (" ++ show_tm' t2 ++ ")"
  | App f ts => "(" ++ f ++ " " ++ (concat " " (List.map show_tm' ts)) ++ ")"
  | If t1 t2 t3 => "if (" ++ show_tm' t1 ++ ") then (" ++ show_tm' t2 ++ ") else (" ++ show_tm' t3 ++ ")"
  | Let x t1 t2 => "let " ++ x ++ " = (" ++ show_tm' t1 ++ ") in (" ++ show_tm' t2 ++ ")"
  end.

Instance show_tm : Show tm :=
  { show := show_tm' }.

Definition gen_val : G val :=
  oneOf [ ret (V_Bool true);
          ret (V_Bool false);
          liftGen (fun i => V_Int i) arbitrary ].

Definition gen_prim1 : G prim1 :=
  elems [ P_add1;
          P_sub1;
          P_not ].

Definition gen_prim2 : G prim2 :=
  elems [ P_add;
          P_sub;
          P_and;
          P_or;
          P_eq;
          P_lt;
          P_le ].

(* TODO: This should instead be made to select a function from a given
         collection. I don't think it would be useful to generate random
         strings that are known to not correspond to functions in-scope. *)
Definition gen_fn_in_env : G string :=
  ret "my great function".

Definition gen_var_name : G string :=
  elems ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
         "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z" ].

Definition gen_trivial_tm : G tm :=
  liftM Const gen_val.

(* NOTE: Generations dependent on function names currently disabled. *)
Fixpoint gen_tm (f : nat) : G tm :=
  match f with
  | O => gen_trivial_tm
  | S f' =>
      freq [ (1, liftM Const gen_val);
             (2, liftM2 Prim1 gen_prim1 (gen_tm f')) ;
             (2, liftM3 Prim2 gen_prim2 (gen_tm f') (gen_tm f')) ;
             (0, liftM2 App gen_fn_in_env (listOf (gen_tm f'))) ;
             (3, liftM3 If (gen_tm f') (gen_tm f') (gen_tm f')) ;
             (3, liftM3 Let gen_var_name (gen_tm f') (gen_tm f')) ]
  end.

End SourceCheck.
