From Coq Require Import
     List
     Classes.RelationClasses
     Morphisms
     Arith.Arith
     Lia
     Logic.FinFun
     Program.Basics
.

From stdpp Require Import gmultiset list.

(* From ExtLib Require Import *)
(*      Structures.Monads *)
(*      . *)

(* From ITree Require Import *)
(*      ITree. *)

From Equations Require Import
     Equations.


Import ListNotations.
Import Relation_Definitions.

(* Import Monads. *)
(* Import MonadNotation. *)

(* Local Open Scope monad_scope. *)
Local Open Scope list_scope.

Module Type PermutationSig.
  Context `{Countable A}.
  Parameter Permutation : list A -> list A -> Prop.

  Parameter Permutation_rel : relation (list A).

  Parameter Permutation_inj_rel : forall (l1 l2: list A), Permutation l1 l2 -> Permutation_rel l1 l2.

  Parameter Permutation_rel_Reflexive : Reflexive (@Permutation_rel).

  Parameter Permutation_rel_Symmetric : Symmetric (@Permutation_rel).

  Parameter Permutation_rel_Transitive : Transitive (@Permutation_rel).

  Parameter Permutation_Proper : Proper (Permutation_rel ==> Permutation_rel ==> iff) (@Permutation_rel).
End PermutationSig.

(* Module OrderPerm <: PermutationSig. *)
(*  - Context `{Countable A}. *)
  
