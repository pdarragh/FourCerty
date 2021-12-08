Require Import Lists.List Strings.String ZArith.

(* Make string literals work. *)
Open Scope string_scope.

(* QuickChick *)
From QuickChick Require Import QuickChick.
Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* Notations *)
Import ListNotations.
Import MonadNotation.
Import QcDefaultNotation.

(* SourceLang *)
From FourCerty Require Import SourceDef.
Import SourceDef.

(* Begin! *)
Module SourceCheck.

Inductive val_ty : Type :=
  | T_Bool
  | T_Int.

Inductive ty : Type :=
  | T_Val (Tv : val_ty)
  | T_Fun (Tas : list ty) (Tr : ty).

Fixpoint show_ty' (T : ty) : string :=
  match T with
  | T_Val T_Bool => "bool"
  | T_Val T_Int => "int"
  | T_Fun Tas Tr => "(" ++ concat " -> " (List.map show_ty' Tas) ++ " -> " ++ show_ty' Tr ++ ")"
  end.

Instance show_ty : Show ty :=
  { show := show_ty' }.

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
  | Var x => x
  | Prim1 op t' => show op ++ " (" ++ show_tm' t' ++ ")"
  | Prim2 op t1 t2 => "(" ++ show_tm' t1 ++ ") " ++ show op ++ " (" ++ show_tm' t2 ++ ")"
  | App f ts => "(" ++ f ++ " " ++ (concat " " (List.map show_tm' ts)) ++ ")"
  | If t1 t2 t3 => "(if (" ++ show_tm' t1 ++ ") then (" ++ show_tm' t2 ++ ") else (" ++ show_tm' t3 ++ "))"
  | Let x t1 t2 => "(let " ++ x ++ " = (" ++ show_tm' t1 ++ ") in (" ++ show_tm' t2 ++ "))"
  end.

Instance show_tm : Show tm :=
  { show := show_tm' }.

Definition show_defn' (d : defn) : string :=
  match d with
  | Defn f xs body => "(fun " ++ f ++ " (" ++ concat " " xs ++ ") " ++ show body ++ ")"
  end.

Instance show_defn : Show defn :=
  { show := show_defn' }.

Definition show_prg' (p : prg) : string :=
  match p with
  | Prg funs e => "<{ [ " ++ concat " | " (List.map show funs) ++ " ] " ++ show e ++ " }>"
  end.

Instance show_prg : Show prg :=
  { show := show_prg' }.

(* Definition gen_val (T : val_ty) : G val := *)
(*   match val_ty with *)
(*   | T_Bool => elems [ V_Bool true; *)
(*                      V_Bool false ] *)
(*   | T_Int => liftM V_Int arbitrary *)
(*   end. *)

Definition gen_val : G val :=
  oneOf [ ret (V_Bool true);
          ret (V_Bool false);
          liftM V_Int arbitrary ].

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

Definition gen_val_ty : G val_ty :=
  elems [ T_Bool;
          T_Int ].

(* Definition gen_fn_ty (f : nat) : G ty := *)
(*   match f with *)
(*   | O => liftM T_Val gen_val_ty *)
(*   | S f' => *)
(*       gen_val_ty *)
(*         >>= (fun T => liftM (T_Fun T) (gen_fn_ty f')). *)

Definition VAR_NAMES :=
  ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
   "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z" ].

Definition gen_var_name : G string :=
  elems_ "" VAR_NAMES.

Definition gen_trivial_tm (names : list string) : G tm :=
  match names with
  | [] => liftM Const gen_val
  | default_name :: _ =>
      freq [ (1, liftM Const gen_val);
             (5, liftM Var (elems_ default_name names)) ]
  end.

Definition pick_func_name (funcs : list string) : G string :=
  elems_ "" funcs.

Fixpoint gen_tm (f : nat) (funcs : list string) (vars : list string) : G tm :=
  let app_mult :=
    (* This allows us to disable generation of terms requiring at least one
       function to be defined. *)
    match funcs with
    | [] => 0
    | _ => 1
    end in
  match f with
  | O => gen_trivial_tm vars
  | S f' =>
      freq [ (1, gen_trivial_tm vars);
             (2, liftM2 Prim1 gen_prim1 (gen_tm f' funcs vars)) ;
             (2, liftM3 Prim2 gen_prim2 (gen_tm f' funcs vars) (gen_tm f' funcs vars)) ;
             (2 * app_mult,
               liftM2 App (pick_func_name funcs) (listOf (gen_tm f' funcs vars))) ;
             (3, liftM3 If (gen_tm f' funcs vars) (gen_tm f' funcs vars) (gen_tm f' funcs vars)) ;
             (3, gen_var_name
                   >>= (fun name =>
                          let vars := name :: vars in
                          liftM2 (Let name) (gen_tm f' funcs vars) (gen_tm f' funcs vars))) ]
  end.

Fixpoint remove {A : Type} (n : nat) (xs : list A) :=
  match n with
  | O => xs
  | S n' =>
      match xs with
      | [] => []
      | x::xs' => x::(remove n' xs')
      end
  end.

Definition rand_select_remove {A : Type} (def : A) (xs : list A) : G (A * list A) :=
  match xs with
  | [] => ret (def, xs)
  | _ => (choose (0, List.length xs - 1))
          >>= (fun n => let elem := List.nth n xs def in
                     ret (elem, remove n xs))
  end.

Fixpoint rand_select_n {A : Type} (n : nat) (def : A) (xs : list A) : G (list A) :=
  match n with
  | O => ret []
  | S n' =>
      (rand_select_remove def xs)
        >>= (fun '(r, xs') =>
               (rand_select_n n' def xs')
                 >>= (fun rs =>
                        ret (r :: rs)))
  end.

Definition gen_args (min max : nat) : G (list string) :=
  (choose (min, max))
    >>= (fun argc =>
           rand_select_n argc "" VAR_NAMES).

Definition ARG_MIN := 1.        (* Functions cannot be thunks. *)
Definition ARG_MAX := 5.

Definition gen_defn (func_name : string) (funcs : list string) (tm_fuel : nat) : G defn :=
  (gen_args ARG_MIN ARG_MAX)
    >>= (fun args =>
           (gen_tm tm_fuel funcs args)
             >>= (fun tm =>
                    ret (Defn func_name args tm))).

Definition DEFN_TM_FUEL := 1.

Fixpoint gen_defns (funcs : list string) : G (list defn) :=
  let fix gen_defns' (remaining_names : list string) :=
    match remaining_names with
    | [] => ret []
    | name :: names' =>
        (gen_defn name funcs DEFN_TM_FUEL)
          >>= (fun defn =>
                 (gen_defns' names')
                   >>= (fun defns =>
                          ret (defn :: defns)))
    end in
  gen_defns' funcs.

Fixpoint build_defn_names (n : nat) : list string :=
  match n with
  | O => []
  | S n' => ("func" ++ show n) :: (build_defn_names n')
  end.

Definition DEFNS_MAX := 5.
Definition PRG_TM_FUEL := 3.

Definition gen_prg : G prg :=
  (choose (0, DEFNS_MAX))
    >>= (fun defnc =>
           let funcs := build_defn_names defnc in
           (gen_defns funcs)
             >>= (fun defns =>
                    (gen_tm PRG_TM_FUEL funcs [])
                      >>= (fun tm =>
                             ret (Prg defns tm)))).

Sample gen_prg.

End SourceCheck.
