From Coq Require Import
  List
  Classes.RelationClasses
  Morphisms
  Arith.Arith
  Lia
  Logic.FinFun
  Program.Basics
.

From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

From Equations Require Import Equations.

Local Existing Instance config.default_checker_flags.
Import MCMonadNotation.

From Graph Require Import Bij MonadNotation SigPerm.

(* Steps for building a solver for permutation *)
(* Can try to mimic Metacoq's tauto example *)
(* Step 1: Creating a data structure that one can reify into *)
(*
The data structure should account for the following:
term := c | X | [] | v | f

Some thoughts:
1. first create a datastructure with the above
2. Then we may also need another data structure that bag the terms
   i.e. a record with
        - mapc : c -> nat
        - mapX : X -> nat
        - mapV : X -> nat
   so that we can then reduce from both sides
 *)

(*  *)
(* Step 2: Proof that this data structure is equivalent to permutation *)
(* Step 3: Reduce to normal form *)
(* Step 4: Have some iteration over all solutions *)
(*
The difficulties of these steps are:
1. Prove of completeness theorem
2. Prove of valid proof steps.
   This requires various lemmas on permutation
 *)
(* Step 5: For each solution, need to carry on the proof search *)

(** Data Structures *)
Definition var := nat.

Lemma eq_var_dec (x y : var) : {x=y}+{x<>y}.
Proof.
  apply eq_nat_dec.
Defined.

Definition A := nat.

(* TODO: Trivial example: Without variable for constants *)
(* TODO: First implement this when constant is nat *)


Inductive ltyp :=
| LF_var (x : var) : ltyp 
| LF_nil : ltyp 
(* | LF_app (l1 : lform) (l2 : lform) : lform *)
| LF_const (a : A) : ltyp 
.

Definition lform := list ltyp.

Lemma eq_lform_dec (l1 l2 : lform) : {l1=l2}+{l1<>l2}.
Proof.
  repeat decide equality.
Defined.

Definition size_ltyp t :=
  match t with
  | LF_var _ | LF_nil | LF_const _ => 1
  (* | LF_app l1 l2 => size_lform l1 + size_lform l2 *)
  end.

Definition size_lform (f : lform) :=
  List.fold_right (fun x acc => size_ltyp x + acc) 0 f.

(* HXC: Need a datatype that represents equations. i.e. left and right *)
(* TODO: not sure if I can add neq in *)
(* Inductive popter := *)
(* | PEq | PNeq. *)

Record plform :=
  mkPlform {
      Pleft : lform;
      Pright : lform
    }.

Definition size_plform p :=
  size_lform (Pleft p) + (size_lform) (Pright p).

Record seq := mkS { hyps : list plform; concl : plform}.


Definition hyps_size_plform h :=
  List.fold_right (fun h n => n + size_plform h) 0 h.

Definition seq_size s :=
  hyps_size_plform (hyps s) + size_plform (concl s).

(* Then we need to define what it means for a term to evaluate to true
   Fortunately this should be done in permutation
 *)

Definition P : lform -> lform -> Type := OrderPerm.

Lemma eq_plform_dec (p1 p2 : plform) : {p1=p2}+{p1<>p2}.
Proof.
  repeat decide equality.
Defined.

Definition plform_comm (p : plform) :=
  mkPlform (Pright p) (Pleft p).

Definition plform_equiv (p1 p2 : plform) :=
  ((Pleft p1) ≡[P] (Pright p2) /\ (Pright p1) ≡[P] (Pleft p2)) \/
    ((Pleft p1) ≡[P] (Pleft p1) /\ (Pright p1) ≡[P] (Pright p2)).

(* TODO: Need to refactor SigPerm to not depend on the Countable class
   Otherwise the space for permutation is restricted
 *)
Lemma perm_lform_dec (l1 l2 : lform) : {l1 ≡[P] l2}+{~(l1 ≡[P] l2)}.
Proof.
  revert l2.
  induction l1; destruct l2.
  - left. reflexivity.
  - right. intros Hcontra.
    admit.
  - admit.
  -
    (* Destruct a = l
       If it is the case, done
       If not, check if a is in l2. Then uses induction hypothesis.
     *)
Admitted.

(* TODO: substitution replacing var with var or Prop *)
Definition subst_var_ltyp (f : var -> var) (t : ltyp) : ltyp :=
  match t with
  | LF_var x => LF_var (f x)
  | LF_nil => LF_nil
  | LF_const c => LF_const c
  end.

Definition subst_var_lform (f : var -> var) : lform -> lform :=
  List.map (subst_var_ltyp f).

Definition plform_valid (p : plform) :=
  Pleft p ≡[P] Pright p.

Definition subst_var_plform (f : var -> var) (p : plform) : plform :=
  mkPlform (subst_var_lform f (Pleft p)) (subst_var_lform f (Pright p)).

Definition valid s :=
  forall f, (forall h, In h (hyps s) -> plform_valid (subst_var_plform f h)) -> plform_valid (subst_var_plform f (concl s)).


Lemma perm_plform_dec (p1 p2 : plform) : {plform_equiv p1 p2}+{not (plform_equiv p1 p2)}.
Proof.
  




(* Aggregate List *)
Section AList.
  Variable (A : Type).
  (* We need:
     1. A map from constants to number of occurrence
     2. A map from variable constants to number of occurrence
     3. A map from List variables to number of occurrence
   *)
  
  Record AList : Type :=
    mkAList
      { constants : list A;
        varconsts : list A;
        varvars : list (list A)
      }.

  (* How to represents variables in Gallina in here *)

  
  
End AList.
 
