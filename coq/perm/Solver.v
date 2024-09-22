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

From Graph Require Import Bij SigPerm.

From stdpp Require Import base.



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
Inductive atom :=
| avar (x : var) : atom
| alit (c : A) : atom.

Inductive atyp :=
| AT_atom (a : atom) : atyp
| AT_var (x : var)  : atyp
| AT_nil : atyp 
.

Definition lform := list atyp.

Lemma eq_atom_dec (a1 a2 : atom) : {a1=a2}+{a1<>a2}.
Proof.
  repeat decide equality.
Defined.

#[global]
  Instance EqDecision_atom : EqDecision atom.
red. intros. apply eq_atom_dec.
Defined.

Lemma eq_atyp_dec (t1 t2 : atyp) : {t1=t2}+{t1<>t2}.
Proof.
  repeat decide equality.
Defined.

#[global]
  Instance EqDecision_atyp : EqDecision atyp.
red. intros. apply eq_atyp_dec.
Defined.

Lemma eq_lform_dec (l1 l2 : lform) : {l1=l2}+{l1<>l2}.
Proof.
  repeat decide equality.
Defined.

#[global]
  Instance EqDecision_lform : EqDecision lform.
red. intros. apply eq_lform_dec.
Defined.

Definition size_atyp t :=
  match t with
  | AT_var _ | AT_nil | AT_atom _ => 1
  (* | LF_app l1 l2 => size_lform l1 + size_lform l2 *)
  end.

Definition size_lform (f : lform) :=
  List.fold_right (fun x acc => size_atyp x + acc) 0 f.

(* HXC: Need a datatype that represents equations. i.e. left and right *)
(* TODO: not sure if I can add neq in *)
(* Inductive popter := *)
(* | PEq | PNeq. *)

Inductive peqn :=
| PE_perm (l1 l2 : lform) : peqn
| PE_aeq (a1 a2 : atom) : peqn.

Definition size_peqn (p : peqn) :=
  match p with
  | PE_perm l1 l2 => size_lform l1 + size_lform l2
  | PE_aeq a1 a2 => 2
  end.

(* TODO: Not sure this helps *)
Lemma eq_plform_dec (p1 p2 : peqn) : {p1=p2}+{p1<>p2}.
Proof.
  repeat decide equality.
Defined.

Record seq := mkS { hyps : list peqn; concl : peqn}.

Definition hyps_size_peqn h :=
  List.fold_right (fun h n => n + size_peqn h) 0 h.

Definition seq_size s :=
  hyps_size_peqn (hyps s) + size_peqn (concl s).

(* Then we need to define what it means for a term to evaluate to true
   Fortunately this should be done in permutation
 *)
Definition P : list atyp -> list atyp -> Type := OrderPerm.

#[global]
 Instance PermConvertible_P : PermConvertible atyp P.
Proof.
  apply PermConvertible_OrderPerm.
Qed.

Definition peqn_comm (p : peqn) :=
  match p with
  | PE_perm l1 l2 => PE_perm l2 l1
  | PE_aeq a1 a2 => PE_aeq a2 a1
  end.

(* TODO: Whether I want to also do comm equiv or not, but maybe this strict version is fine *)
Definition peqn_equiv (p1 p2 : peqn) : Prop :=
  match p1, p2 with
  | PE_perm l11 l12, PE_perm l21 l22 =>
      l11 ≡[P] l21 /\ l12 ≡[P] l22
  | PE_aeq a11 a12, PE_aeq a21 a22 =>
      a11 = a21 /\ a12 = a22
  | _, _ => False
  end.

Import ConvertTactics.

Lemma perm_peqn_dec (l1 l2 : lform) : {l1 ≡[P] l2}+{~(l1 ≡[P] l2)}.
Proof.
  revert l2.
  induction l1; destruct l2.
  - left. reflexivity.
  - right. intros Hcontra.
    apply Permutation_rel_length in Hcontra. discriminate.
  - right. intros Hcontra.
    apply Permutation_rel_length in Hcontra. discriminate.
  - pose proof EqDecision_atyp. destruct (decide_rel eq a a0).
    + specialize (IHl1 l2). destruct IHl1.
      * left. convert_mfperm.
        subst.
        apply Permutation_rel_cons. auto.
      * right. intros Hcontra. subst.
        apply Permutation_rel_cons_inv in Hcontra. auto.
    + admit.
Admitted.


(** Substitution *)
(* TODO: substitution replacing var with var or Prop *)
Definition subst_var_atyp (v v' : var) (t : atyp) : atyp :=
  match t with
  | AT_var x => if eq_dec x v then AT_var v' else AT_var x
  | AT_nil => AT_nil
  | AT_atom c => AT_atom c
  end.

Definition subst_var_atom (v v' : var) (a : atom) : atom :=
  match a with
  | avar x => if eq_dec x v then avar v' else avar x
  | alit i => alit i
  end.

Definition subst_atom_atyp (f : atom -> atom) (t : atyp) : atyp :=
  match t with
  | AT_var x => AT_var x
  | AT_nil => AT_nil
  | AT_atom c => AT_atom (f c)
  end.

Definition subst_atyp_lform (f : atyp -> atyp) : lform -> lform :=
  List.map f.

(* Definition subst_atom_lform (f : atom -> atom) : lform -> lform := *)
(*   List.map (subst_atom_atyp f). *)

Definition subst_atyp_peqn (f : atyp -> atyp) (eqn : peqn) : peqn :=
  match eqn with
  | PE_perm l1 l2 =>
      PE_perm (subst_atyp_lform f l1) (subst_atyp_lform f l2)
  | PE_aeq a1 a2 => PE_aeq a1 a2
  end.

Definition subst_atom_peqn (f : atom -> atom) (eqn : peqn) : peqn :=
  match eqn with
  | PE_perm l1 l2 =>
      PE_perm (subst_atyp_lform l1) l2
  | PE_aeq a1 a2 => PE_aeq a1 a2
  end.
      


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
 
