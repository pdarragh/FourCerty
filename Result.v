Require Import Strings.String.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.

Module Result.

Inductive error : Type :=
| OOF
| Error
| ErrorMsg (s : string).        (* In case we want it. *)

Inductive result (A : Type) : Type :=
| Err (e : error)
| Ok (v : A).

Arguments result _%type_scope.
Arguments Err {A}%type_scope.
Arguments Ok {A}%type_scope v.

Instance monad_result : Monad result :=
  { ret := fun _ v => Ok v
  ; bind := fun _ _ c1 c2 =>
              match c1 with
              | Err e => Err e
              | Ok v => c2 v
              end }.

End Result.
