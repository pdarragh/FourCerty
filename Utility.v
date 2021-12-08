Require Import Lists.List Strings.String ZArith.

From QuickChick Require Import QuickChick.
Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Import ListNotations.
Import MonadNotation.

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
  | _ => n <- (choose (0, List.length xs - 1));;
        let elem := List.nth n xs def in
        ret (elem, remove n xs)
  end.

Definition rand_select {A : Type} (def : A) (xs : list A) : G A :=
  let fix rand_select' (n : nat) (xs : list A) : G A :=
    match xs with
    | [] => ret def
    | x::xs' => if n =? 0 then ret x else rand_select' (n - 1) xs'
    end in
  n <- (choose (0, List.length xs));;
    rand_select' n xs.

Fixpoint rand_select_n {A : Type} (n : nat) (def : A) (xs : list A) : G (list A) :=
  match n with
  | O => ret []
  | S n' =>
      '(r, xs') <- (rand_select_remove def xs);;
      rs <- (rand_select_n n' def xs');;
      ret (r :: rs)
  end.

Definition mapM@{d c +}
           {m : Type@{d} -> Type@{c}}
           {M : Monad m}
           {a b} : (a -> m b) -> list a -> m (list b) :=
  fun f =>
    let k a r :=
      x <- (f a);;
      xs <- r;;
      ret (x :: xs) in
    fun xs =>
      List.fold_right k (ret []) xs.

Definition sequenceM@{d c}
           {m : Type@{d} -> Type@{c}}
           {M : Monad m}
           {a} : list (m a) -> m (list a) :=
  mapM (fun x => x).
