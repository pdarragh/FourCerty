Require Import Nat.

(* These implementations are based heavily on Coq.Vectors.VectorDef. However,
   there are some notable distinctions.

   The biggest differences is that our implementation only permits non-empty
   vectors. This allows us to ensure we can always retrieve items from a vector,
   thus completely side-stepping the issue of providing proofs of non-emptiness.
   This also allows us to skip out on using a dedicated type for indexing into a
   vector like Coq.Vectors.Fin.t.

   The caveat to this is that our [nth] implementation has a quirk: any index
   given that is too large for the vector simply retrieves the last element in
   the vector. In many cases, this might not be ideal, but since we only use
   vectors for the set-up of the a86 machine in Target.v, this seemed a
   reasonable conceit. *)

Inductive nevector (A : Type) : nat -> Type :=
  | nevbase : forall (a : A), nevector A 1
  | nevcons : forall (a : A) (n : nat), nevector A n -> nevector A (S n).

Arguments nevector _%type_scope.
Arguments nevbase {A}%type_scope.
Arguments nevcons {A}%type_scope.

Fixpoint nth {A : Type} {m : nat} (nev : nevector _ m) (n : nat) : A :=
  match nev with
  | nevbase a => a
  | nevcons a _ nev' =>
      if n =? 0
      then a
      else nth nev' (n - 1)
  end.

Fixpoint append {A : Type} {m n : nat} (vl : nevector _ m) (vr : nevector _ n) : nevector A (m + n) :=
  match vl with
  | nevbase a => nevcons a n vr
  | nevcons a m' vl' => nevcons a (m' + n) (append vl' vr)
  end.

Fixpoint replicate1 {A : Type} (a : A) (n : nat) : nevector A (n + 1) :=
  match n with
  | 0 => nevbase a
  | S n' => nevcons a _ (replicate1 a n')
  end.

Module NEVectorNotations.

Declare Scope nevector_scope.
Delimit Scope nevector_scope with nevector.
Notation "[[ x ]]" := (nevbase x) : nevector_scope.
Notation "[[ w ; x ; .. ; y ; z ]]" := ((nevcons w _) ((nevcons x _) .. ((nevcons y _) (nevbase z)) ..)) : nevector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : nevector_scope.
Open Scope nevector_scope.

End NEVectorNotations.
