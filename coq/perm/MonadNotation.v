From ExtLib Require Import Structures.Monads.

Module MonadNotation.
Delimit Scope monad_scope with monad. 
Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 62, right associativity) : monad_scope.
Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 62, right associativity) : monad_scope.

(* Notation "e1 ;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad)) (at level 62, right associativity) : monad_scope. *)

Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2)) (at level 62, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end)) (at level 62, pat pattern, c1 at next level, right associativity) : monad_scope.
End MonadNotation.
