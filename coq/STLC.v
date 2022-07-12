From Coq Require Import List.

From ExtLib Require Import
     Structures.Monads
     .

From ITree Require Import
     ITree.

From Equations Require Import
     Equations.

Import Monads.
Import MonadNotation.
Import ListNotations.
Open Scope list_scope.

Local Open Scope monad_scope.


From Graph Require Import Permutations.

Definition var := nat.

Inductive tp :=
| TBase
| TArr (S:tp) (T:tp).

Inductive tm :=
| Var (x:var)
| Abs (T:tp) (t:tm)
| App (t1 t2:tm).




Definition ctxt := list tp.

Inductive wf : ctxt -> tm -> tp -> Prop :=
| wf_Var : forall G (x:var) T, List.nth_error G x = Some T -> wf G (Var x) T
| wf_Abs : forall G (S T:tp) (t:tm), wf (S::G) t T -> wf G (Abs T t) (TArr S T)
| wf_App : forall G (S T:tp) (t s:tm),
    wf G t (TArr S T) ->
    wf G s S ->
    wf G (App t s) S.


