(* Strings *)
Require Import Lists.List Strings.String ZArith.
Open Scope string_scope.

(* QuickChick *)
From QuickChick Require Import QuickChick.
Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* Notations *)
Import ListNotations.
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
  | Var x => x
  | Prim1 op t' => show op ++ " (" ++ show_tm' t' ++ ")"
  | Prim2 op t1 t2 => "(" ++ show_tm' t1 ++ ") " ++ show op ++ " (" ++ show_tm' t2 ++ ")"
  | App f ts => "(" ++ f ++ " " ++ (concat " " (List.map show_tm' ts)) ++ ")"
  | If t1 t2 t3 => "if (" ++ show_tm' t1 ++ ") then (" ++ show_tm' t2 ++ ") else (" ++ show_tm' t3 ++ ")"
  | Let x t1 t2 => "let " ++ x ++ " = (" ++ show_tm' t1 ++ ") in (" ++ show_tm' t2 ++ ")"
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
  | Prg funs e => "<{ [" ++ concat " | " (List.map show funs) ++ " ] " ++ show e ++ " }>"
  end.

Instance show_prg : Show prg :=
  { show := show_prg' }.

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

(* NOTE: Generations dependent on function names currently disabled. *)
Fixpoint gen_tm (f : nat) (names : list string) : G tm :=
  match f with
  | O => gen_trivial_tm names
  | S f' =>
      freq [ (1, gen_trivial_tm names);
             (2, liftM2 Prim1 gen_prim1 (gen_tm f' names)) ;
             (2, liftM3 Prim2 gen_prim2 (gen_tm f' names) (gen_tm f' names)) ;
             (0, liftM2 App gen_fn_in_env (listOf (gen_tm f' names))) ;
             (3, liftM3 If (gen_tm f' names) (gen_tm f' names) (gen_tm f' names)) ;
             (3, gen_var_name
                   >>= (fun name =>
                          let names := name :: names in
                          liftM2 (Let name) (gen_tm f' names) (gen_tm f' names))) ]
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

Definition gen_args (n : nat) : G (list string) :=
  (choose (0, n))
    >>= (fun argc =>
           rand_select_n argc "" VAR_NAMES).

Definition ARG_MAX := 5.

Definition gen_defn (next_num : nat) (tm_fuel : nat) : G defn :=
  let func_name := "func" ++ show next_num in
  (gen_args ARG_MAX)
    >>= (fun args =>
           (gen_tm tm_fuel args)
             >>= (fun tm =>
                    ret (Defn func_name args tm))).

Definition DEFN_TM_FUEL := 3.

Fixpoint gen_defns (n : nat) : G (list defn) :=
  match n with
  | O => ret []
  | S n' =>
      (gen_defn n DEFN_TM_FUEL)
        >>= (fun defn =>
               (gen_defns n')
                 >>= (fun defns =>
                        ret (defn :: defns)))
  end.

Definition DEFNS_MAX := 5.
Definition PRG_TM_FUEL := 5.

Definition gen_prg : G prg :=
  (choose (0, DEFNS_MAX))
    >>= (fun defnc =>
           (gen_defns defnc)
             >>= (fun defns =>
                    (gen_tm PRG_TM_FUEL [])
                      >>= (fun tm =>
                             ret (Prg defns tm)))).

End SourceCheck.
