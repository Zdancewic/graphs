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

From stdpp Require Import base countable fin_maps gmap gmultiset.



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
| A_lit (c : A) : atom
| A_var (x : var) : atom.

Inductive atyp :=
| AT_nil : atyp 
| AT_atom (a : atom) : atyp
| AT_var (x : var)  : atyp
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
| PE_aeq (a1 a2 : atom) : peqn
| PE_false
.

Definition size_peqn (p : peqn) :=
  match p with
  | PE_perm l1 l2 => size_lform l1 + size_lform l2
  | PE_aeq a1 a2 => 2
  | PE_false => 1
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
  | PE_false => PE_false
  end.

(* TODO: Whether I want to also do comm equiv or not, but maybe this strict version is fine *)
Definition peqn_equiv (p1 p2 : peqn) : Prop :=
  match p1, p2 with
  | PE_perm l11 l12, PE_perm l21 l22 =>
      l11 ≡[P] l21 /\ l12 ≡[P] l22
  | PE_aeq a11 a12, PE_aeq a21 a22 =>
      a11 = a21 /\ a12 = a22
  | PE_false, PE_false => True
  | _, _ => False
  end.

Import ConvertTactics.

(* Lemma perm_peqn_dec (l1 l2 : lform) : {l1 ≡[P] l2}+{~(l1 ≡[P] l2)}. *)
(* Proof. *)
(*   revert l2. *)
(*   induction l1; destruct l2. *)
(*   - left. reflexivity. *)
(*   - right. intros Hcontra. *)
(*     apply Permutation_rel_length in Hcontra. discriminate. *)
(*   - right. intros Hcontra. *)
(*     apply Permutation_rel_length in Hcontra. discriminate. *)
(*   - pose proof EqDecision_atyp. destruct (decide_rel eq a a0). *)
(*     + specialize (IHl1 l2). destruct IHl1. *)
(*       * left. convert_mfperm. *)
(*         subst. *)
(*         apply Permutation_rel_cons. auto. *)
(*       * right. intros Hcontra. subst. *)
(*         apply Permutation_rel_cons_inv in Hcontra. auto. *)
(*     + admit. *)
(* Admitted. *)

(* TODO: This is a bit restricted, but maybe this is the right notion *)
Lemma peqn_dec (p1 p2 : peqn) : {p1 = p2} + {~(p1 = p2)}.
Proof.
  repeat decide equality.
Defined.

(** Substitution *)
(* TODO: substitution replacing var with var or Prop *)
Definition subst_var_atyp (v v' : var) (t : atyp) : atyp :=
  match t with
  | AT_var x => if eq_dec x v then AT_var v' else AT_var x
  | AT_nil => AT_nil
  | AT_atom c => AT_atom c
  end.

Definition subst_avar_atom (v v' : var) (a : atom) : atom :=
  match a with
  | A_var x => if eq_dec x v then A_var v' else A_var x
  | A_lit i => A_lit i
  end.

Definition subst_avar_atyp (v v' : var) (t : atyp) : atyp :=
  match t with
  | AT_var x => AT_var x
  | AT_nil => AT_nil
  | AT_atom c => AT_atom (subst_avar_atom v v' c)
  end.

Definition subst_var_lform (v v' : var) : lform -> lform :=
  List.map (subst_var_atyp v v').

Definition subst_avar_lform (v v' : var) : lform -> lform :=
  List.map (subst_avar_atyp v v').

Definition subst_var_peqn (v v' : var) (p : peqn) : peqn :=
  match p with
  | PE_perm l1 l2 =>
      PE_perm (subst_var_lform v v' l1) (subst_var_lform v v' l2)
  | PE_aeq a1 a2 => PE_aeq a1 a2
  | PE_false => PE_false
  end.

Definition subst_avar_peqn (v v' : var) (p : peqn) : peqn :=
  match p with
  | PE_perm l1 l2 =>
      PE_perm (subst_avar_lform v v' l1) (subst_avar_lform v v' l2)
  | PE_aeq a1 a2 => PE_aeq (subst_avar_atom v v' a1) (subst_avar_atom v v' a2)
  | PE_false => PE_false
  end.

Definition subst_peqn (var_bindings : list (var * var)) (avar_bindings : list (var * var)) (p : peqn) : peqn :=
  let p' := List.fold_left (fun acc '(v, v') => subst_var_peqn v v' acc) var_bindings p in
  List.fold_left (fun acc '(v, v') => subst_avar_peqn v v' acc) avar_bindings p'.

Definition peqn_valid (p : peqn) :=
  match p with
  | PE_perm l1 l2 =>
      l1 ≡[P] l2
  | PE_aeq a1 a2 => a1 = a2
  | PE_false => False
  end.

Definition valid s :=
  forall vb avb, (forall h, In h (hyps s) -> peqn_valid (subst_peqn vb avb h)) -> peqn_valid (subst_peqn vb avb (concl s)).

Definition is_leaf s :=
  let cl := concl s in
  let dec_leaf h :=
    if peqn_dec PE_false h then true else
      if peqn_dec h cl then true else false
  in
  List.fold_left (fun b h => orb b (dec_leaf h)) (hyps s) false.

Lemma subst_PE_false_reflexive :
  forall vb avb, subst_peqn vb avb PE_false = PE_false.
Proof.
  intros vb.
  unfold subst_peqn.
  induction vb; intros; simpl.
  - induction avb; simpl; auto.
    destruct a.
    rewrite IHavb. simpl. auto.
  - destruct a. apply IHvb.
Qed.

Lemma is_leaf_sound_in h hs:
  valid {| hyps := h :: hs; concl := h |}.
Proof.
  red; simpl; intros.
  assert (h = h \/ In h hs) by intuition.
  apply H in H0; auto.
Qed.
  (* H : valid {| hyps := h; concl := cl |} *)
  (* ============================ *)
(* valid {| hyps := PE_perm l1 l2 :: h; concl := cl |} *)

Lemma valid_weakening : forall h hs cl,
  valid {| hyps := hs; concl := cl|} ->
  valid {| hyps := h :: hs; concl := cl|}.
Proof.
  unfold valid. intros.
  apply H.
  intros; simpl in *.
  assert (Hin: h = h0 \/ In h0 hs) by intuition.
  apply H0 in Hin; intuition.
Qed.

Lemma valid_ex_falso : forall hs cl,
    valid {| hyps := PE_false :: hs; concl := cl |}.
Proof.
  red; intros; simpl in *.
  assert (H' :  PE_false = PE_false \/ In PE_false hs) by intuition.
  apply H in H'. red in H'. rewrite subst_PE_false_reflexive in H'. destruct H'.
Qed.
  
Lemma is_leaf_sound s :
  is_leaf s = true -> valid s.
Proof.
  unfold is_leaf.
  destruct s as (h, cl); simpl. revert cl.
  induction h; simpl; intros.
  discriminate.
  destruct a.
  - destruct (peqn_dec (PE_perm l1 l2) cl).
    + subst. apply is_leaf_sound_in.
    + apply IHh in H. apply valid_weakening; intuition.
  - destruct (peqn_dec (PE_aeq a1 a2) cl).
    + subst. apply is_leaf_sound_in.
    + apply IHh in H. apply valid_weakening; intuition.
  - apply valid_ex_falso.
Qed.

Definition subgoal := list (list seq).

(* TODO: Check this *)
Definition valid_subgoal (sg:subgoal) :=
  exists2 sl, In sl sg & forall s, In s sl -> valid s.

Fixpoint pick {A} (h : list A) :=
  match h with
  | nil => nil
  | a :: l =>
      (a, l)::List.map (fun p => (fst p, a :: snd p)) (pick l)
  end.

Inductive result := Valid | CounterModel | Abort.

(* HXC: I need a semantic for reasoning
   In the example we are given a type class that takes in a type and have different semantics for them
 *)
(* Algorithm *)
(* Step 1:
Reduce to normal form i.e. if one side has some coefficient, the other side should not have coefficient

1. Transform into a bag form
2. Proof the identity rule
 *)

(* First define countable instances for var, atom, and atyp *)
(* Increment by 1 so maintain uniqueness *)
Definition encode_var (x : var) : positive :=
  Pos.of_succ_nat x.

Definition decode_var (p : positive) : option var :=
  Some (Pos.to_nat p - 1).

#[global]
  Program Instance Countable_var : Countable var :=
  {| encode := encode_var;
    decode := decode_var
  |}.
Next Obligation.
  intros.
  unfold decode_var, encode_var.
  rewrite SuccNat2Pos.id_succ. simpl.
  rewrite Nat.sub_0_r. reflexivity.
Defined.

Section CountableInstances.
  Context `{Countable A}.
  Definition encode_atom (a : atom) : positive :=
    match a with
    | A_var v => (encode v)~0
    | A_lit a => (encode a)~1
    end.

  Definition decode_atom (p : positive) : option atom :=
    match p with
    | xH => None
    | xO p => A_var <$> (decode p)
    | xI p => A_lit <$> (decode p)
    end.

    Global Program Instance Countable_atom : Countable atom :=
    {| encode := encode_atom;
      decode := decode_atom
    |}.
  Next Obligation.
    intros. unfold decode_atom, encode_atom. destruct x.
    - rewrite decode_encode. auto.
    - rewrite decode_encode. auto.
  Defined.

  Definition encode_atyp (a : atyp) : positive :=
    match a with
    | AT_atom a => (encode a)~0
    | AT_var v => (encode v)~1
    | AT_nil => 1
    end.

  Definition decode_atyp (p : positive) : option atyp :=
    match p with
    | xH => Some AT_nil
    | xO p => AT_atom <$> (decode p)
    | xI p => AT_var <$> (decode p)
    end.

    Global Program Instance Countable_atyp : Countable atyp :=
    {| encode := encode_atyp;
      decode := decode_atyp
    |}.
    Next Obligation.
      intros. unfold decode_atyp, encode_atyp.
      destruct x; try rewrite decode_encode; simpl; auto.
    Defined.

    Global Program Instance Insert_atyp_gmultiset : Insert atyp nat (gmultiset A).
    Next Obligation.
    Admitted.
    
    Global Program Instance SingletonMS_atyp_gmultiset : SingletonMS atyp (gmultiset A) := fun a => <[ a := 1 ]> ∅.
    
End CountableInstances.

From Coq Require Import
  FSets.FMapAVL
  Structures.OrderedTypeEx
  FSets.FMapFacts
  Compare_dec
.

Definition atom_lt (a1 a2 : atom) : Prop :=
  match a1, a2 with
  | A_lit c1, A_lit c2 => c1 < c2
  | A_lit _, A_var _ => True
  | A_var _, A_lit _ => False
  | A_var v1, A_var v2 => v1 < v2
  end.

Module Atom_as_OT <: UsualOrderedType.

  Definition t := atom.
  Definition eq : atom -> atom -> Prop := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := atom_lt.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z. destruct x, y, z; intros; simpl in *; auto.
    - eapply Nat_as_OT.lt_trans; eauto.
    - eapply Nat_as_OT.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof.
    intros x y. destruct x, y; intros; unfold eq; simpl in *; auto.
    - intros Hcontra. injection Hcontra; intros; lia.
    - intros Hcontra. injection Hcontra; intros; lia.
  Qed.
  
  Definition compare (x y : atom) : (@Compare atom lt eq x y).
    destruct x, y.
    - destruct (Nat_as_OT.compare c c0).
      + assert (lt (A_lit c) (A_lit c0)).
        {unfold lt, atom_lt. unfold Nat_as_OT.lt in *. lia. }
        exact (LT H).
      + assert (eq (A_lit c) (A_lit c0)).
        {unfold eq. unfold Nat_as_OT.eq in *. subst; auto. }
        exact (EQ H).
      + assert (lt (A_lit c0) (A_lit c)).
        {unfold lt, atom_lt. unfold Nat_as_OT.lt in *. lia. }
        exact (GT H).
    - assert (lt (A_lit c) (A_var x)) by (repeat red; auto).
      exact (LT H).
    - assert (lt (A_lit c) (A_var x)) by (repeat red; auto).
      exact (GT H).
    - destruct (Nat_as_OT.compare x x0).
      + assert (lt (A_var x) (A_var x0)).
        {unfold lt, atom_lt. unfold Nat_as_OT.lt in *. lia. }
        exact (LT H).
      + assert (eq (A_var x) (A_var x0)).
        {unfold eq. unfold Nat_as_OT.eq in *. subst; auto. }
        exact (EQ H).
      + assert (lt (A_var x0) (A_var x)).
        {unfold lt, atom_lt. unfold Nat_as_OT.lt in *. lia. }
        exact (GT H).
  Defined.
  
  Definition eq_dec := eq_atom_dec.
End Atom_as_OT.

Definition atyp_lt (a1 a2 : atyp) : Prop :=
  match a1 with
  | AT_nil =>
      match a2 with
      | AT_nil => False
      | _ => True
      end
  | AT_atom at1 =>
      match a2 with
      | AT_nil => False
      | AT_atom at2 => Atom_as_OT.lt at1 at2
      | _ => True
      end
  | AT_var v1 =>
      match a2 with
      | AT_var v2 => v1 < v2
      | _ => False
      end
  end.

Module Atyp_as_OT <: UsualOrderedType.

  Definition t := atyp.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := atyp_lt.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z. destruct x, y, z; unfold lt, atom_lt; simpl in *; auto.
    - apply Atom_as_OT.lt_trans.
    - apply Nat_as_OT.lt_trans.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    intros x y. destruct x, y; unfold lt, atom_lt, eq; intros; simpl in *; auto.
    - intros Hcontra.  injection Hcontra; intros; subst.
      apply Atom_as_OT.lt_not_eq in H.
      unfold Atom_as_OT.eq in H.
      specialize (H (Atom_as_OT.eq_refl a0)). inversion H.
    - intros Hcontra. injection Hcontra; intros; subst.
      apply Nat_as_OT.lt_not_eq in H.
      unfold Nat_as_OT.eq in H.
      specialize (H (Nat_as_OT.eq_refl x0)). inversion H.
  Qed.

  Definition compare x y : Compare lt eq x y.
    destruct x, y.
    - exact (EQ (eq_refl AT_nil)).
    - assert (lt AT_nil (AT_atom a)) by (repeat red; auto).
      exact (LT H).
    - assert (lt AT_nil (AT_var x)) by (repeat red; auto).
      exact (LT H).
    - assert (lt AT_nil (AT_atom a)) by (repeat red; auto).
      exact (GT H).
    - destruct (Atom_as_OT.compare a a0).
      + assert (lt (AT_atom a) (AT_atom a0)) by (repeat red in *; auto).
        exact (LT H).
      + assert (eq (AT_atom a) (AT_atom a0)). {repeat red in e; subst. repeat red.  auto. }
        exact (EQ H).
      + assert (lt (AT_atom a0) (AT_atom a)) by (repeat red in *; auto).
        exact (GT H).
    - assert (lt (AT_atom a) (AT_var x)) by (repeat red; auto).
      exact (LT H).
    - assert (lt AT_nil (AT_var x)) by (repeat red; auto).
      exact (GT H).
    - assert (lt (AT_atom a) (AT_var x)) by (repeat red; auto).
      exact (GT H).
    - destruct (Nat_as_OT.compare x x0).
      + assert (lt (AT_var x) (AT_var x0)) by (repeat red in *; auto).
        exact (LT H).
      + assert (eq (AT_var x) (AT_var x0)). {repeat red in e; subst. repeat red.  auto. }
        exact (EQ H).
      + assert (lt (AT_var x0) (AT_var x)) by (repeat red in *; auto).
        exact (GT H).
  Defined.

  Definition eq_dec := eq_atyp_dec.
End Atyp_as_OT.

Module NatMap := FMapAVL.Make(Nat_as_OT).
(* Examples for using natmap *)
Definition my_map := NatMap.add 1 42 (NatMap.empty _).
Compute NatMap.find 1 my_map.
Compute NatMap.find 2 my_map.
Definition my_map_removed := NatMap.remove 1 my_map.
Compute NatMap.find 1 my_map_removed.
Module Facts := FMapFacts.WFacts_fun Nat_as_OT NatMap.
Lemma find_add_eq : forall (k v : nat) m,
  NatMap.find k (NatMap.add k v m) = Some v.
Proof.
  intros. apply Facts.find_mapsto_iff. apply NatMap.add_1. reflexivity.
Qed.
Section ReduceMap.
  Notation lbag := (NatMap.t atyp).
  Definition incr_count (a : atyp) (lbag : lbag) : lbag :=
    match NatMap.find a lbag with
    | None => NatMap.add a 1 lbag
    | Some (c)
  Definition list_to_lbag : list -> lbag :=
    List.fold_right (fun a acc => NatMap.add)
End ReduceMap.

(* Section ReduceMap. *)
(*   (* Convert to map *) *)
(*   Context `{Countable A}. *)
(*   Notation lbag := (gmultiset A). *)

(*   (* Need to convert list to gmultiset  *)
(*      Write a function that converts from gmultiset back to list, and argue that it's a permutation of the original list *)
(*      Write a function that argues that if the original peqn is valid then converted and converted back is valid (should be a corollary from the above) *)
(*      Write a reduce function *)
(*      Argue that the original peqn is valid iff the reduced peqn is valid. *)
(*    *) *)
(*   Definition list_to_multiset (l : list atyp) : gmultiset A := *)
(*     list_to_set_disj l. *)
  
(*   Definition pe_perm_to_multiset (l1 l2 : list atyp) : gmultiset A * gmultiset A := *)
(*     (list_to_set_disj l1, list_to_set_disj l2). *)
(*   (* Proof that if original peqn is valid then the converted peqn is valid *) *)
(*   Lemma multiset_elements_perm : forall (l1 l2 : list atyp), l1 ≡[P] l2 -> elements (list_to_multiset l1) ≡[P] elements (list_to_multiset l2). *)
(* End ReduceMap. *)

Section Reification.
  Equations reify (Σ : global_env_ext) (Γ : context) (P : term) : option form by (wf ())
End Reification.
  
