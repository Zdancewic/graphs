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

(*
  Theorems we want to prove for each instances:
Lemma Permutation_length : forall {A} (l1 l2 : list A) (HP : Permutation l1 l2),
    length l1 = length l2.

Lemma Permutation_symmetric :
  forall {A:Type} (xs ys: list A)
    (H : Permutation xs ys), Permutation ys xs.
 *)

Section def.
  Context `{Countable A}.
  Definition Permutation (l1 l2: list A): Prop :=
    list_to_set_disj l1 =@{gmultiset A} list_to_set_disj l2.

End def.
