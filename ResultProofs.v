Require Import ExtLib.Structures.Monad.

From FourCerty Require Import Result.

Import Result.

Module ResultProofs.

Theorem nested_result@{T U V +} : forall {T U V : Type}
                                    (c1 : result T)
                                    (c2 : result U)
                                    (c3 : result V),
    bind (bind c1 (fun t => c2)) (fun u => c3) = bind c1 (fun t => (bind c2 (fun u => c3))).
Proof.
  intros.
  destruct c1; reflexivity.
Qed.

End ResultProofs.
