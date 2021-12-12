From FourCerty Require Import Utility Source.

Import Utility SourceLang.

(* Make string literals work. *)
Open Scope string_scope.

(* QuickChick *)
From QuickChick Require Import QuickChick.
Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* Notations *)
Import QcDefaultNotation.

(* Begin! *)
Module SourceCheck.

Inductive val_ty : Type :=
  | T_Bool
  | T_Int.

Instance dec_eq_val_ty (T1 T2 : val_ty) : Dec (T1 = T2).
Proof. dec_eq. Qed.

Definition show_val_ty' (T : val_ty) : string :=
  match T with
  | T_Bool => "bool"
  | T_Int => "int"
  end.

Instance show_val_ty : Show val_ty :=
  { show := show_val_ty' }.

Inductive fun_ty : Type :=
  | T_Fun (Tas : list val_ty) (Tr : val_ty).

Definition show_fun_ty' (T : fun_ty) : string :=
  match T with
  | T_Fun Tas Tr => "((" ++ concat ", " (List.map show Tas) ++ ") -> " ++ show Tr ++ ")"
  end.

Instance show_fun_ty : Show fun_ty :=
  { show := show_fun_ty' }.

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

Definition gen_val (T : val_ty) : G val :=
  match T with
  | T_Bool => elems [ V_Bool true;
                     V_Bool false ]
  | T_Int => liftM V_Int arbitrary
  end.

Definition gen_prim1 (T : val_ty) : G prim1 :=
  match T with
  | T_Bool => ret P_not
  | T_Int => elems [ P_add1; P_sub1 ]
  end.

Definition gen_prim2 (T : val_ty) : G prim2 :=
  match T with
  | T_Bool => elems [ P_and; P_or ]
  | T_Int => elems [P_add; P_sub; P_eq; P_lt; P_le ]
  end.

Definition gen_val_ty : G val_ty :=
  elems [ T_Bool;
          T_Int ].

Definition VAR_NAMES :=
  ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
   "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z" ].

Definition gen_var_name : G string :=
  elems_ "" VAR_NAMES.

Definition gen_trivial_tm (T : val_ty) (vars : list (string * val_ty)) : G tm :=
  let vars := List.map fst (List.filter (fun '(n, Tn) => Tn = T?) vars) in
  match vars with
  | [] => liftM Const (gen_val T)
  | default_name :: _ =>
      freq [ (1, liftM Const (gen_val T));
             (5, liftM Var (elems_ default_name vars)) ]
  end.

Definition pick_func_name (funcs : list string) : G string :=
  elems_ "" funcs.

Definition app_multiplier {A : Type} (funcs : list A) : nat :=
  match funcs with
  | [] => 0
  | _ => 1
  end.

Definition gen_var : G (string * val_ty) :=
  name <- gen_var_name;;
  T <- gen_val_ty;;
  ret (name, T).

Fixpoint gen_tm
         (T : val_ty)
         (f : nat)
         (funcs : list (string * fun_ty))
         (vars : list (string * val_ty)) : G tm :=
  let t_funcs := List.filter (fun '(f, (T_Fun Tas Tr)) => Tr = T?) funcs in
  let app_mult := app_multiplier t_funcs in
  match f with
  | O => gen_trivial_tm T vars
  | S f' =>
      freq [ (1, gen_trivial_tm T vars);
             (2, liftM2 Prim1 (gen_prim1 T) (gen_tm T f' funcs vars));
             (2, liftM3 Prim2
                        (gen_prim2 T)
                        (gen_tm T f' funcs vars)
                        (gen_tm T f' funcs vars));
             (2 * app_mult,
               (rand_select ("", T_Fun [] T_Int) t_funcs)
                 >>= (fun '(f, (T_Fun Tas _)) =>
                        (sequenceM (List.map (fun Ta => gen_tm Ta f' funcs vars) Tas))
                          >>= (fun args =>
                                 ret (App f args))));
             (3, liftM3 If
                        (gen_tm T_Bool f' funcs vars)
                        (gen_tm T f' funcs vars)
                        (gen_tm T f' funcs vars));
             (3, gen_var
                   >>= (fun '(var, Tv) =>
                          (gen_tm Tv f' funcs vars)
                            >>= (fun val =>
                                   let vars := (var, Tv) :: vars in
                                   liftM (Let var val) (gen_tm T f' funcs vars)))) ]
  end.

Definition ARG_MIN := 1.        (* Functions cannot be thunks. *)
Definition ARG_MAX := 5.

Definition gen_fn_ty : G fun_ty :=
  argc <- (choose (ARG_MIN, ARG_MAX));;
  Tas <- (vectorOf argc gen_val_ty);;
  Tr <- gen_val_ty;;
  ret (T_Fun Tas Tr).

Definition gen_args (Tas : list val_ty) : G (list (string * val_ty)) :=
  let fix gen_args'
          (rem_Tas : list val_ty)
          (avail_names : list string) : G (list (string * val_ty)) :=
    match rem_Tas with
    | [] => ret []
    | Ta :: Tas' =>
        '(name, rem_names) <- (rand_select_remove "" avail_names);;
        args <- (gen_args' Tas' rem_names);;
        ret ((name, Ta) :: args)
    end in
  gen_args' Tas VAR_NAMES.

Definition gen_defn
           (func_name : string)
           (T : fun_ty)
           (funcs : list (string * fun_ty))
           (tm_fuel : nat) : G defn :=
  match T with
  | T_Fun Tas Tr =>
      args <- (gen_args Tas);;
      tm <- (gen_tm Tr tm_fuel funcs args);;
      ret (Defn func_name (List.map fst args) tm)
  end.

Definition DEFN_TM_FUEL := 1.

Definition gen_defns (funcs : list (string * fun_ty)) : G (list defn) :=
  let fix gen_defns' (remaining_funcs : list (string * fun_ty)) :=
    match remaining_funcs with
    | [] => ret []
    | (name, T) :: funcs' =>
        defn <- (gen_defn name T funcs DEFN_TM_FUEL);;
        defns <- (gen_defns' funcs');;
        ret (defn :: defns)
    end in
  gen_defns' funcs.

Fixpoint build_defn_shapes (n : nat) : G (list (string  * fun_ty)) :=
  match n with
  | O => ret []
  | S n' =>
      Tf <- gen_fn_ty;;
      shapes <- (build_defn_shapes n');;
      ret ((("func" ++ show n), Tf) :: shapes)
  end.

Definition DEFNS_MAX := 5.
Definition PRG_TM_FUEL := 3.

Definition gen_prg : G prg :=
  defnc <- (choose (0, DEFNS_MAX));;
  funcs <- (build_defn_shapes defnc);;
  defns <- (gen_defns funcs);;
  T <- gen_val_ty;;
  tm <- (gen_tm T PRG_TM_FUEL funcs []);;
  ret (Prg defns tm).

Sample gen_prg.

End SourceCheck.
