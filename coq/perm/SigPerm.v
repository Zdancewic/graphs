From Coq Require Import
     List
     Classes.RelationClasses
     Morphisms
     Arith.Arith
     Lia
     Logic.FinFun
     Program.Basics
.

From stdpp Require Import gmultiset.

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

Section Permutation_rel.
  Context `{Countable A}.
   Variable Permutation : list A -> list A -> Type.

   Definition _Permutation_rel : relation (list A) :=
     fun l1 l2 => exists (p : Permutation l1 l2), True.
  
  Program Definition _Permutation_inj_rel {l1 l2 : list A} (p : Permutation l1 l2) :
    _Permutation_rel l1 l2 :=
    _.
  Next Obligation.
    red. exists p. auto.
  Defined.
End Permutation_rel.

Class PermRel {A : Type} `{Countable A} (Permutation : list A -> list A -> Type) := {
    Permutation_rel : relation (list A) := _Permutation_rel Permutation;
    Permutation_inj_rel {l1 l2 : list A} : Permutation l1 l2 -> Permutation_rel l1 l2 := _Permutation_inj_rel Permutation
  }.

(* Class Perm {A : Type} `{Countable A} (Permutation : list A -> list A -> Type) := { *)
(*     Permutation_rel : relation (list A) := *)
(*       fun l1 l2 => exists (p : Permutation l1 l2), True; *)
(*     Permutation_inj_rel {l1 l2 : list A} (p : Permutation l1 l2) : Permutation_rel l1 l2 *)
(*   }. *)
Arguments Permutation_rel {_ _ _} _ {_}.
Arguments Permutation_inj_rel {_ _ _} _ {_}.

Class PermRelLaw {A : Type} `{Countable A} (Permutation : list A -> list A -> Type) `{PermRel _ Permutation} := {
    Permutation_reflexive :> Reflexive (Permutation_rel Permutation);
    Permutation_symmetric :> Symmetric (Permutation_rel Permutation);
    Permutation_transitive :> Transitive (Permutation_rel Permutation);
    Permutation_proper :> Proper (Permutation_rel Permutation ==> Permutation_rel Permutation ==> iff) (Permutation_rel Permutation)
  }.

Section OrderPerm.
  Context `{Countable A}.

  Inductive OrderPerm : list A -> list A -> Type :=
  | orderperm_id: forall l, OrderPerm l l
  | orderperm_swap x y l : OrderPerm ([y] ++ [x] ++ l) ([x] ++ [y] ++ l)
  | orderperm_comp l1 l2 l3 :
    OrderPerm l1 l2 -> OrderPerm l2 l3 -> OrderPerm l1 l3
  | orderperm_plus l11 l12 l21 l22 :
    OrderPerm l11 l21 -> OrderPerm l12 l22 -> OrderPerm (l11 ++ l12) (l21 ++ l22).

  #[global]
    Instance PermRel_OrderPerm : PermRel OrderPerm := {}.

  Lemma OrderPerm_symmetric :
    forall (xs ys: list A)
      (HP : OrderPerm xs ys), OrderPerm ys xs.
  Proof.
    intros.
    induction HP.
    - apply orderperm_id.
    - apply orderperm_swap.
    - eapply orderperm_comp; eauto.
    - apply orderperm_plus; eauto.
  Qed.    
  
  Section OrderPermLaws.
    Notation pr_or := (Permutation_rel OrderPerm).
  (* Lemma Permutation_rel_Reflexive : forall {A : Type}, Reflexive (@Permutation_rel). *)
  Instance OrderPerm_rel_Reflexive : Reflexive pr_or.
  Proof.
    repeat red.
    intros. exists (orderperm_id x). auto.
  Qed.

  Instance Permutation_rel_Symmetric : Symmetric pr_or.
  Proof.
    repeat red.
    intros x y HP. destruct HP as [P].
    exists (OrderPerm_symmetric x y P). auto.
  Qed.

  Instance Permutation_rel_Transitive : Transitive pr_or.
  Proof.
    repeat red.
    intros x y z HP0 HP1. destruct HP0 as [P]. destruct HP1 as [Q].
    exists (orderperm_comp x y z P Q). auto.
  Qed.
  
  Instance Permutation_Proper : Proper (pr_or ==> pr_or ==> iff) pr_or. 
  Proof.
    repeat red.
    intros x0 y0 HP0 x1 y1 HP1.
    split; intros HP2.
    - apply symmetry.  eapply transitivity. 2:{ apply HP0. }  apply symmetry. eapply transitivity; eauto.
    - eapply transitivity. apply HP0. eapply transitivity. apply HP2. apply symmetry. auto.
  Qed.
  
End OrderPerm.

End OrderPerm.

Section OrderPerm.
  Context `{Countable A}.

  Inductive OrderPerm : list A -> list A -> Type :=
  | perm_id: forall l, OrderPerm l l
  | perm_swap x y l : OrderPerm ([y] ++ [x] ++ l) ([x] ++ [y] ++ l)
  | perm_comp l1 l2 l3 :
    OrderPerm l1 l2 -> OrderPerm l2 l3 -> OrderPerm l1 l3
  | perm_plus l11 l12 l21 l22 :
    OrderPerm l11 l21 -> OrderPerm l12 l22 -> OrderPerm (l11 ++ l12) (l21 ++ l22).

  Definition OrderPerm_Permutation_rel : relation (list A) :=
    fun l1 l2 => exists (p : OrderlPerm l1 l2), True.

  Program Definition OrderPerm_Permutation_inj_rel {l1 l2 : list A} (p : Permutation l1 l2) :
    Permutation_rel l1 l2 :=
    _.
  Next Obligation.
    red. exists p. auto.
  Defined.
  
End OrderPerm.

Module Type PermutationSig.
  Context `{Countable A}.
  Parameter Permutation : list A -> list A -> Type.

  Parameter Permutation_rel : relation (list A).

  Parameter Permutation_inj_rel : forall (l1 l2: list A), Permutation l1 l2 -> Permutation_rel l1 l2.

  Parameter Permutation_rel_Reflexive : Reflexive Permutation_rel.

  Parameter Permutation_rel_Symmetric : Symmetric Permutation_rel.

  Parameter Permutation_rel_Transitive : Transitive Permutation_rel.

  Parameter Permutation_Proper : Proper (Permutation_rel ==> Permutation_rel ==> iff) Permutation_rel.

End PermutationSig.


Module OrderPerm <: PermutationSig.
  Context `{Countable A}.

  Inductive _Permutation : list A -> list A -> Type :=
  | perm_id: forall l, _Permutation l l
  | perm_swap x y l : _Permutation ([y] ++ [x] ++ l) ([x] ++ [y] ++ l)
  | perm_comp l1 l2 l3 :
    _Permutation l1 l2 -> _Permutation l2 l3 -> _Permutation l1 l3
  | perm_plus l11 l12 l21 l22 :
    _Permutation l11 l21 -> _Permutation l12 l22 -> _Permutation (l11 ++ l12) (l21 ++ l22).

  Definition Permutation : list A -> list A -> Type :=
    _Permutation.

  (* Inductive Permutation : list A -> list A -> Type := *)
  (* | perm_id: forall l, Permutation l l *)
  (* | perm_swap x y l : Permutation ([y] ++ [x] ++ l) ([x] ++ [y] ++ l) *)
  (* | perm_comp l1 l2 l3 : *)
  (*   Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3 *)
  (* | perm_plus l11 l12 l21 l22 : *)
  (*   Permutation l11 l21 -> Permutation l12 l22 -> Permutation (l11 ++ l12) (l21 ++ l22). *)

  Definition Permutation_rel : relation (list A) :=
    fun l1 l2 => exists (p : Permutation l1 l2), True.

  Lemma Permutation_symmetric :
    forall (xs ys: list A)
      (HP : Permutation xs ys), Permutation ys xs.
  Proof.
    intros.
    induction HP.
    - apply perm_id.
    - apply perm_swap.
    - eapply perm_comp; eauto.
    - apply perm_plus; eauto.
  Qed.    
  
  Program Definition Permutation_inj_rel {l1 l2 : list A} (p : Permutation l1 l2) :
    Permutation_rel l1 l2 :=
    _.
  Next Obligation.
    red. exists p. auto.
  Defined.

  (* Lemma Permutation_rel_Reflexive : forall {A : Type}, Reflexive (@Permutation_rel). *)
  Instance Permutation_rel_Reflexive : Reflexive Permutation_rel.
  Proof.
    repeat red.
    intros. exists (perm_id x). auto.
  Qed.

  Instance Permutation_rel_Symmetric : Symmetric Permutation_rel.
  Proof.
    repeat red.
    intros x y HP. destruct HP as [P].
    exists (Permutation_symmetric x y P). auto.
  Qed.

  Instance Permutation_rel_Transitive : Transitive Permutation_rel.
  Proof.
    repeat red.
    intros x y z HP0 HP1. destruct HP0 as [P]. destruct HP1 as [Q].
    exists (perm_comp x y z P Q). auto.
  Qed.
  
  Instance Permutation_Proper : Proper (Permutation_rel ==> Permutation_rel ==> iff) Permutation_rel.
  Proof.
    repeat red.
    intros x0 y0 HP0 x1 y1 HP1.
    split; intros HP2.
    - apply symmetry.  eapply transitivity. 2:{ apply HP0. }  apply symmetry. eapply transitivity; eauto.
    - eapply transitivity. apply HP0. eapply transitivity. apply HP2. apply symmetry. auto.
  Qed.
  
End OrderPerm.

Module MultisetPerm <: PermutationSig.
  Context `{Countable A}.
  Definition Permutation (l1 l2 : list A) : Prop :=
    list_to_set_disj l1 =@{gmultiset A} list_to_set_disj l2.

  Import OrderPerm.

  Theorem OrderPerm_MultisetPerm_Equivalence : forall (l1 l2 : list A), Permutation l1 l2 <-> OrderPerm.Permutation l1 l2.
