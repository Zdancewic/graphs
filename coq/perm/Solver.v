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
  FSets.FMapList
  FSets.FMapFacts
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

(* Module NatMap := FMapAVL.Make(Nat_as_OT). *)
(* (* Examples for using natmap *) *)
(* Definition my_map := NatMap.add 1 42 (NatMap.empty _). *)
(* Compute NatMap.find 1 my_map. *)
(* Compute NatMap.find 2 my_map. *)
(* Definition my_map_removed := NatMap.remove 1 my_map. *)
(* Compute NatMap.find 1 my_map_removed. *)
(* Lemma find_add_eq : forall (k v : nat) m, *)
(*   NatMap.find k (NatMap.add k v m) = Some v. *)
(* Proof. *)
(*   intros. apply Facts.find_mapsto_iff. apply NatMap.add_1. reflexivity. *)
(* Qed. *)

Module AMap := FMapList.Make(Atyp_as_OT).
Module Facts_AMap := Facts AMap.
Module Properties_AMap := Properties AMap.
Module OrdProperites_AMap := OrdProperties AMap.

Instance Proper_f_eq3 : forall A B C D (f : B -> C -> D -> A), Proper (eq ==> eq ==> eq ==> eq) f.
Proof.
  repeat red; intros.
  subst; auto.
Qed.

Import ConvertTactics.

Section ReduceMap.
  Definition incr_count (a : atyp) (lbag : AMap.t nat) : AMap.t nat :=
    match AMap.find a lbag with
    | None => AMap.add a 1 lbag
    | Some c => AMap.add a (c + 1) lbag
    end.
  
  Definition list_to_bag_atyp : list atyp -> AMap.t nat :=
    List.fold_right (fun a acc => incr_count a acc) (AMap.empty _).

  Definition bag_to_list_atyp : AMap.t nat -> list atyp :=
    fun m => AMap.fold (fun k v acc => List.repeat k v ++ acc) m [].
  
  Lemma Empty_empty_AMap : forall elt m,
      @AMap.Empty elt m <-> m = AMap.empty elt.
  Proof.
    intros. split; intros.
    - destruct m. admit.
    - rewrite H. apply AMap.empty_1.
  Admitted.
  
  Lemma incr_count_bag_empty : forall a,
      incr_count a (AMap.empty _) = AMap.add a 1 (AMap.empty _).
  Proof.
    intros.
    unfold incr_count.
    rewrite Facts_AMap.empty_o. reflexivity.
  Qed.

  Hint Resolve Permutation_rel_Reflexive.
  Hint Resolve Equivalence_OrderPerm_rel : core.
  Hint Resolve AMap.empty_1 : core.
  Hint Resolve Proper_OrderPerm_rel1 : core.
  Hint Resolve Proper_OrderPerm_rel2 : core.
  Hint Resolve Proper_OrderPerm_rel3 : core.
  Hint Resolve Proper_f_eq3 : core.
(* Proper_MidPerm_rel: *)
(*   ∀ {A : Type}, *)
(*     EqDecision A *)
(*     → Proper (Permutation_rel MidPerm ==> Permutation_rel MidPerm ==> iff) *)
  (*         (Permutation_rel MidPerm) *)
  (* Lemma Proper_OrderPerm_rel2 : forall f, Proper (eq ==> eq ==> Permutation_rel OrderPerm ==> Permutation_rel OrderPerm) f. *)

  Lemma incr_count_Equal : forall a m m',
      AMap.Equal m m' ->
      AMap.Equal (incr_count a m)  (incr_count a m').
  Proof.
    intros.
    unfold incr_count.
    erewrite Facts_AMap.find_m; eauto.
    destruct (AMap.find (elt:=nat) a m').
    + erewrite Facts_AMap.add_m; eauto.
      reflexivity.
    + erewrite Facts_AMap.add_m; eauto.
      reflexivity.
  Qed.
  Instance Proper_incr_count_aux : Proper (eq ==> eq ==> Permutation_rel P ==> Permutation_rel P)
                                     (λ (k : AMap.key) (v : nat) (acc : list AMap.key), repeat k v ++ acc).
  Proof.
    do 4 red. intros.
    subst.
    rewrite H1. reflexivity.
  Qed.
  Hint Resolve Proper_incr_count_aux : core.

  Lemma transpose_neq_key_repeat_app :
    Properties_AMap.transpose_neqkey
      (Permutation_rel P)
      (λ (k : AMap.key) (v : nat) (acc : list AMap.key), repeat k v ++ acc).
  Proof.
    red. intros.
    do 2 rewrite app_assoc.
    assert (repeat k e ++ repeat k' e' ≡[P] repeat k' e' ++ repeat k e) by apply Permutation_rel_exchange.
    rewrite H0. reflexivity.
  Qed.
  Hint Resolve transpose_neq_key_repeat_app : core.

  Lemma empty_non_in : forall a, ¬ AMap.In (elt:=nat) a (AMap.empty nat).
  Proof.
    intros a H. apply Facts_AMap.empty_in_iff in H; auto.
  Qed.
  Hint Resolve empty_non_in : core.

  (* TODO: Should be true *)
  Lemma AMap_add_shadow {A} : forall a (v1 : A) (v2 : A) b,
      AMap.Equal (AMap.add a v1 (AMap.add a v2 b)) (AMap.add a v1 b).
  Proof.
  Admitted.

  Lemma AMap_add_neq_comm {A} : forall a a' (v1 : A) (v2 : A) b,
      a <> a' ->
      AMap.Equal (AMap.add a v1 (AMap.add a' v2 b)) (AMap.add a' v2 (AMap.add a v1 b)).
  Proof.
  Admitted.
  
  Lemma incr_count_add_eq : forall a v b,
      AMap.Equal (incr_count a (AMap.add a v b)) (AMap.add a (v + 1) b).
  Proof.
    intros.
    unfold incr_count.
    rewrite Facts_AMap.add_eq_o; auto.
    rewrite AMap_add_shadow.
    reflexivity.
  Qed.

  Lemma incr_count_add_eq2 :
    forall a v b
      (H : ¬ AMap.In (elt:=nat) a b),
      AMap.Equal (incr_count a (AMap.add a v b)) (AMap.add a (v + 1) (incr_count a b)).
  Proof.
    intros. unfold incr_count.
    rewrite Facts_AMap.add_eq_o; auto.
    apply Facts_AMap.not_find_in_iff in H. rewrite H.
    repeat rewrite AMap_add_shadow. reflexivity.
  Qed.

  Lemma incr_count_add_neq : forall a a' v b
                               (Hne : a <> a'),
      AMap.Equal (incr_count a (AMap.add a' v b)) (AMap.add a' v (incr_count a b)).
  Proof.
    intros.
    unfold incr_count.
    rewrite Facts_AMap.add_neq_o; auto.
    destruct (AMap.find (elt:=nat) a b).
    - rewrite AMap_add_neq_comm; auto.
      reflexivity.
    - rewrite AMap_add_neq_comm; auto.
      reflexivity.
  Qed.

  Lemma map_fold_nin_add :
    forall k v b l
      (H : ¬ AMap.In (elt:=nat) k b),
      AMap.fold (fun k v acc => repeat k v ++ acc) (AMap.add k v b) l
        ≡[P] repeat k v ++ (AMap.fold (fun k v acc => repeat k v ++ acc) b l).
  Proof.
    intros k v b l H.
    remember (fun k v acc => repeat k v ++ acc) as f.
    assert (repeat k v ++ (AMap.fold f b l) = f k v (AMap.fold f b l)).
    { rewrite Heqf; auto.
    }
    rewrite H0.
    apply Properties_AMap.fold_Add; subst; auto.
    constructor.
  Qed.

  Lemma incr_count_nin :
    forall k m a
      (HNE: a <> k)
      (HNIN : ¬ AMap.In (elt:=nat) k m),
      ¬ AMap.In (elt:=nat) k (incr_count a m).
  Proof.
    intros.
    unfold incr_count.
    destruct (AMap.find (elt:=nat) a m); intros H'; apply Facts_AMap.add_neq_in_iff in H'; auto.
  Qed.

  Lemma incr_count_fold_nin :
    forall k m
      (HNIN: ¬ AMap.In (elt:=nat) k m),
      AMap.fold (fun k0 v acc => repeat k0 v ++ acc) (incr_count k m) [] ≡[P] repeat k 1 ++ AMap.fold (fun k0 v acc => repeat k0 v ++ acc) m [].
  Proof.
    intros k m HNIN.
    unfold incr_count.
    pose proof HNIN as HNIN'.
    apply Facts_AMap.not_find_in_iff in HNIN. rewrite HNIN.
    rewrite map_fold_nin_add; auto. reflexivity.
  Qed.

  Lemma repeat_app_eq {A} : forall (k : A) a b,
      repeat k a ++ repeat k b = repeat k (a + b).
  Proof.
    intros k a. revert k. induction a; intros; simpl; auto.
    rewrite IHa. reflexivity.
  Qed.
    
  Lemma incr_count_bag_list : forall a b,
      bag_to_list_atyp (incr_count a b) ≡[P] a :: bag_to_list_atyp b.
  Proof.
    intros a b. revert a. unfold bag_to_list_atyp. apply Properties_AMap.fold_rec_weak; intros.
    - assert (AMap.Equal (incr_count a0 m) (incr_count a0 m')). {apply incr_count_Equal. apply H. }
      rewrite <- H0.
      apply (@Properties_AMap.fold_Equal _ _ (Permutation_rel P)); auto.
      symmetry; auto.
    - rewrite incr_count_bag_empty.
      rewrite Properties_AMap.fold_add; auto.
      apply Permutation_rel_cons.
      rewrite Properties_AMap.fold_Empty; auto.
      reflexivity.
    - destruct (eq_atyp_dec a0 k).
      + subst.
        apply transitivity with (y := repeat k e ++ k :: a).
        2: {
          replace (repeat k e ++ k :: a) with (repeat k e ++ [k] ++ a) by auto.
          replace (k :: repeat k e ++ a) with ([k] ++ repeat k e ++ a) by auto.
          repeat rewrite app_assoc.
          assert (repeat k e ++ [k] ≡[P] [k] ++ repeat k e) by apply Permutation_rel_exchange.
          rewrite H1. reflexivity.
        }
        rewrite <- H0.
        assert (HFI: AMap.fold (fun k0 v acc => repeat k0 v ++ acc) (incr_count k (AMap.add k e m)) [] ≡[P] AMap.fold(fun k0 v acc => repeat k0 v ++ acc) (AMap.add k (e + 1) m) []).
        {
          apply Properties_AMap.fold_Equal; auto.
          apply incr_count_add_eq; auto.
        }
        eapply transitivity; eauto.
        rewrite map_fold_nin_add; auto.
        replace (repeat k (e + 1)) with (repeat k e ++ repeat k 1) by apply repeat_app_eq.
        rewrite <- app_assoc.
        rewrite incr_count_fold_nin; auto.
        reflexivity.
      + 
        assert (HFI: AMap.fold (fun k0 v acc => repeat k0 v ++ acc) (incr_count a0 (AMap.add k e m)) [] ≡[P] AMap.fold (fun k0 v acc => repeat k0 v ++ acc) (AMap.add k e (incr_count a0 m)) []).
        {
          apply Properties_AMap.fold_Equal; auto.
          apply incr_count_add_neq; auto.
        }
        eapply transitivity; eauto.
        apply transitivity with (y := repeat k e ++ a0 :: a).
        2: {
          replace (repeat k e ++ a0 :: a) with (repeat k e ++ [a0] ++ a) by auto.
          replace (a0 :: repeat k e ++ a) with ([a0] ++ repeat k e ++ a) by auto.
          repeat rewrite app_assoc.
          assert (repeat k e ++ [a0] ≡[P] [a0] ++ repeat k e) by apply Permutation_rel_exchange.
          rewrite H1. reflexivity.
        }
        rewrite <- H0.
        eapply map_fold_nin_add; auto.
        apply incr_count_nin; auto.
  Qed.

  Lemma list_bag_identity : forall l,
      bag_to_list_atyp (list_to_bag_atyp l) ≡[P] l.
  Proof.
    intros l. induction l.
    - simpl. 
      unfold bag_to_list_atyp.
      rewrite Properties_AMap.fold_Empty; auto.
      reflexivity.
    - simpl in *.
      rewrite incr_count_bag_list.
      rewrite IHl. reflexivity.
  Qed.

  Lemma incr_count_swap_amap : forall a b m m',
      AMap.Equal m m' ->
      AMap.Equal (incr_count a (incr_count b m)) (incr_count b (incr_count a m')).
  Proof.
    intros.
    destruct (eq_atyp_dec a b).
    - subst.
      unfold incr_count.
      remember (AMap.find (elt:=nat) b m) as ob.
      destruct ob.
      + pose proof Facts_AMap.find_m as HFM.
        specialize (@HFM _ b _ eq_refl _ _ H).
        rewrite <- HFM, <- Heqob.
        repeat rewrite Facts_AMap.add_o.
        destruct (AMap.E.eq_dec b b); intuition.
        repeat rewrite AMap_add_shadow.
        apply Facts_AMap.add_m; auto.
      + pose proof Facts_AMap.find_m as HFM.
        specialize (@HFM _ b _ eq_refl _ _ H).
        rewrite <- HFM, <- Heqob.
        repeat rewrite Facts_AMap.add_o.
        destruct (AMap.E.eq_dec b b); intuition.
        repeat rewrite AMap_add_shadow.
        apply Facts_AMap.add_m; auto.
    - unfold incr_count.
      pose proof Facts_AMap.find_m as HFMA.
      specialize (@HFMA _ a _ eq_refl _ _ H).
      pose proof Facts_AMap.find_m as HFMB.
      specialize (@HFMB _ b _ eq_refl _ _ H).
      remember (AMap.find (elt:=nat) a m) as oa.
      remember (AMap.find (elt:=nat) b m) as ob.
      destruct oa, ob.
      +
        try rewrite <- HFMA; try rewrite <- HFMB.
        repeat rewrite Facts_AMap.add_o.
        destruct (AMap.E.eq_dec b a). symmetry in e. intuition.
        destruct (AMap.E.eq_dec a b); intuition.
        repeat (try rewrite <- Heqoa; try rewrite <- Heqob; try rewrite <- HFMA; try rewrite <- HFMB). 
        rewrite AMap_add_neq_comm; auto. 
        repeat (apply Facts_AMap.add_m; auto).
      +
        try rewrite <- HFMA; try rewrite <- HFMB.
        repeat rewrite Facts_AMap.add_o.
        destruct (AMap.E.eq_dec b a). symmetry in e. intuition.
        destruct (AMap.E.eq_dec a b); intuition.
        repeat (try rewrite <- Heqoa; try rewrite <- Heqob; try rewrite <- HFMA; try rewrite <- HFMB). 
        rewrite AMap_add_neq_comm; auto. 
        repeat (apply Facts_AMap.add_m; auto).
      +
        try rewrite <- HFMA; try rewrite <- HFMB.
        repeat rewrite Facts_AMap.add_o.
        destruct (AMap.E.eq_dec b a). symmetry in e. intuition.
        destruct (AMap.E.eq_dec a b); intuition.
        repeat (try rewrite <- Heqoa; try rewrite <- Heqob; try rewrite <- HFMA; try rewrite <- HFMB). 
        rewrite AMap_add_neq_comm; auto. 
        repeat (apply Facts_AMap.add_m; auto).
      +
        try rewrite <- HFMA; try rewrite <- HFMB.
        repeat rewrite Facts_AMap.add_o.
        destruct (AMap.E.eq_dec b a). symmetry in e. intuition.
        destruct (AMap.E.eq_dec a b); intuition.
        repeat (try rewrite <- Heqoa; try rewrite <- Heqob; try rewrite <- HFMA; try rewrite <- HFMB). 
        rewrite AMap_add_neq_comm; auto. 
        repeat (apply Facts_AMap.add_m; auto).
  Qed.
    
  Lemma list_to_bag_equiv_inj :
    forall l1 l2
      (HP : l1 ≡[P] l2),
      AMap.Equal (list_to_bag_atyp l1) (list_to_bag_atyp l2).
  Proof.
    intros.
    convert_skip.
    induction HP; try reflexivity.
    - simpl. apply incr_count_swap_amap; auto.
    - simpl. apply incr_count_Equal; auto.
    - eapply transitivity; eauto.
  Qed.

  Lemma amap_incr_not_empty : forall a m, ¬ AMap.Empty (incr_count a m).
  Proof.
    intros a m H.
    unfold incr_count in *.
    destruct (AMap.find (elt:=nat) a m).
    - unfold AMap.Empty in H.
      unfold AMap.Raw.Empty in H.
      assert (AMap.Raw.PX.MapsTo a (n + 1) (AMap.this (AMap.add a (n + 1) m))).
      {
        apply AMap.Raw.add_1; auto.
      }
      apply H in H0. destruct H0.
    - unfold AMap.Empty in H.
      unfold AMap.Raw.Empty in H.
      assert (AMap.Raw.PX.MapsTo a 1 (AMap.this (AMap.add a 1 m))).
      {
        apply AMap.Raw.add_1; auto.
      }
      apply H in H0. destruct H0.
  Qed.
  
  Lemma list_to_bag_equiv_surj :
    forall l1 l2
      (HM : AMap.Equal (list_to_bag_atyp l1) (list_to_bag_atyp l2)),
      l1 ≡[P] l2.
  Proof.
    intros l1. induction l1; intros; simpl in *.
    - destruct l2; try reflexivity.
      apply Properties_AMap.F.Empty_m in HM.
      pose proof (@AMap.empty_1 nat) as HE.
      apply HM in HE.
      simpl in *.
      apply amap_incr_not_empty in HE. destruct HE.
    - destruct l2.
      + apply Properties_AMap.F.Empty_m in HM.
        pose proof (@AMap.empty_1 nat) as HE.
        apply HM in HE; simpl in *.
        apply amap_incr_not_empty in HE. destruct HE.
      + admit.
  Admitted.

  (** Decrementing *)
  (* Next step is to reduce the two sides into normal form *)
End ReduceMap.

From Coq Require Import
  Sorting.Mergesort
  Sorting.Sorted
  Orders
.

Module AtomOrder <: TotalLeBool.
  Definition t := atom.
  Definition leb (a1 a2 : atom) : bool :=
    match a1, a2 with
    | A_lit c1, A_lit c2 => c1 <=? c2
    | A_lit _, A_var _ => true
    | A_var _, A_lit _ => false
    | A_var v1, A_var v2 => v1 <=? v2
    end.
  Infix "<=?" := leb (at level 70).
  Theorem leb_total : forall (a1 a2 : t), a1 <=? a2 \/ a2 <=? a1.
  Proof.
    intros a1 a2.
    destruct a1, a2; intuition; simpl; apply NatOrder.leb_total.
  Qed.
End AtomOrder.

Module AtypOrder <: TotalLeBool.
  Definition t := atyp.
  
  Definition leb (a1 a2 : t) : bool :=
    match a1 with
    | AT_nil => true
    | AT_atom at1 =>
        match a2 with
        | AT_nil => false
        | AT_atom at2 => AtomOrder.leb at1 at2
        | _ => true 
        end
    | AT_var v1 =>
        match a2 with
        | AT_var v2 => v1 <=? v2
        | _ => false
        end
    end.
  Infix "<=?" := leb (at level 70).
  Theorem leb_total : forall (a1 a2 : t), a1 <=? a2 \/ a2 <=? a1.
  Proof.
    intros a1 a2.
    destruct a1, a2; intuition; simpl.
    apply AtomOrder.leb_total.
    apply NatOrder.leb_total.
  Qed.
End AtypOrder.

(** Mergesort: On list level *)
Module Import ASort := Sort AtypOrder.

Search nat.
(* Nat.compare: nat → nat → comparison *)
Definition atom_compare (a1 a2 : atom) : comparison :=
  match a1, a2 with
  | A_lit c1, A_lit c2 => Nat.compare c1 c2
  | A_lit _, A_var _ => Lt 
  | A_var _, A_lit _ => Gt
  | A_var v1, A_var v2 => Nat.compare v1 v2
  end.

Definition atyp_compare (a1 a2 : atyp) : comparison :=
  match a1 with
  | AT_nil =>
      match a2 with
      | AT_nil => Eq
      | _ => Lt
      end
  | AT_atom at1 =>
      match a2 with
      | AT_nil => Gt
      | AT_atom at2 => atom_compare at1 at2
      | _ => Lt
      end
  | AT_var v1 =>
      match a2 with
      | AT_var v2 => Nat.compare v1 v2
      | _ => Gt
      end
  end.

(** Reduce both lists at the same time *)
Definition filter_empty (l : list atyp) : list atyp :=
  let filter_aux :=
    fun x =>
      match atyp_compare x AT_nil with
      | Eq => false 
      | _ => true 
      end
  in
  List.filter filter_aux l.

Lemma atom_compare_lt_neq : forall a b,
    Lt = atom_compare a b -> a <> b.
Proof.
  intros a b. destruct a, b; intros; try discriminate; simpl in *.
  - intros HC. injection HC; intros; subst.
    symmetry in H. apply nat_compare_Lt_lt in H. lia.
  - intros HC. injection HC; intros; subst.
    symmetry in H. apply nat_compare_Lt_lt in H. lia.
Qed.

Lemma atyp_compare_lt_neq : forall a b,
    Lt = atyp_compare a b -> a <> b.
Proof.
  intros a b. destruct a, b; intros; try discriminate.
  - simpl in H. apply atom_compare_lt_neq in H.
    intros HC. injection HC; intuition.
  - simpl in H. intros HC.
    injection HC; intros; subst. symmetry in H. apply nat_compare_Lt_lt in H. lia.
Qed.

Lemma atom_compare_gt_neq : forall a b,
    Gt = atom_compare a b -> a <> b.
Proof.
  intros a b. destruct a, b; intros; try discriminate; simpl in *.
  - intros HC. injection HC; intros; subst.
    symmetry in H. apply nat_compare_Gt_gt in H. lia.
  - intros HC. injection HC; intros; subst.
    symmetry in H. apply nat_compare_Gt_gt in H. lia.
Qed.

Lemma atyp_compare_gt_neq : forall a b,
    Gt = atyp_compare a b -> a <> b.
Proof.
  intros a b. destruct a, b; intros; try discriminate.
  - simpl in H. apply atom_compare_gt_neq in H.
    intros HC. injection HC; intuition.
  - simpl in H. intros HC.
    injection HC; intros; subst. symmetry in H. apply nat_compare_Gt_gt in H. lia.
Qed.

Lemma filter_empty_out :
  forall l l'
    (HL : l' = filter_empty l)
  ,
    ¬ (List.In AT_nil l').
Proof.
  intros l.
  induction l; intros.
  - subst. apply in_nil.
  - remember (atyp_compare a AT_nil) as HA.
    unfold filter_empty in HL.
    replace (a :: l) with ([a] ++ l) in HL by auto.
    rewrite filter_app in HL.
    destruct HA; simpl in *; rewrite <- HeqHA in HL; simpl in *.
    + apply IHl in HL; intuition.
    + subst; intros HC.
      simpl in HC. destruct HC.
      * apply atyp_compare_lt_neq in HeqHA; intuition.
      * specialize (IHl (filter_empty l) eq_refl). apply IHl in H; intuition.
    + subst; intros HC.
      simpl in HC. destruct HC.
      * apply atyp_compare_gt_neq in HeqHA; intuition.
      * specialize (IHl (filter_empty l) eq_refl). apply IHl in H; intuition.
Qed.

Equations reduce_pe_perm (l1 : list atyp) (l2 : list atyp) : (list atyp * list atyp) by wf (length l1 + length l2) lt :=
  reduce_pe_perm (a1::l1') (a2::l2') :=
      match atyp_compare a1 a2 with
      | Lt =>
          let '(l1'', l2'') := reduce_pe_perm l1' (a2::l2') in
          (a1::l1'', l2'')
      | Eq => reduce_pe_perm l1' l2'
      | Gt =>
          let '(l1'', l2'') := reduce_pe_perm (a1::l1') l2' in
          (l1'', a2::l2'')
      end;
  reduce_pe_perm l1 l2 := (l1, l2).
Next Obligation.
  lia.
Defined.
Next Obligation.
  lia.
Defined.

Definition pe_perm_nf1 (l1 l2 : list atyp) :=
  forall x, In x l1 -> ¬ In x l2.

Definition pe_perm_nf (l1 l2 : list atyp) :=
  pe_perm_nf1 l1 l2 /\ pe_perm_nf1 l2 l1.
Search atyp.
(* AMap.Raw.MX.TO.le: atyp → atyp → Prop *)
Definition ASorted := LocallySorted AMap.Raw.MX.TO.le.

(* TODO: Prove this *)
Lemma reduce_pe_perm_nf : forall l1 l2,
    ASorted l1 -> ASorted l2 ->
    uncurry pe_perm_nf (reduce_pe_perm l1 l2).
Abort.









(* TODO: Not sure which one to use *)
(* Fixpoint reduce_aux (l1 : list atyp) (l2 : list atyp) (fuel : nat) : (list atyp * list atyp) := *)
(*   match fuel with *)
(*   | O => (l1, l2) *)
(*   | S fuel' => *)
(*       match l1, l2 with *)
(*       | a1::l1', a2::l2' => *)
(*           match atyp_compare a1 a2 with *)
(*           | Lt => *)
(*               let '(l1'', l2'') := reduce_aux l1' l2 fuel' in *)
(*               (a1::l1'', l2'') *)
(*           | Eq => reduce_aux l1' l2' fuel' *)
(*           | Gt => *)
(*               let '(l1'', l2'') := reduce_aux l1 l2' fuel' in *)
(*               (l1'', a2::l2'') *)
(*           end *)
(*       | _, _ => (l1, l2) *)
(*       end *)
(*   end. *)

(* Definition reduce (l1 : list atyp) (l2 : list atyp) : list atyp * list atyp := *)
(*   reduce_aux l1 l2 (length l1 + length l2). *)




Section Reification.
  Equations reify (Σ : global_env_ext) (Γ : context) (P : term) : option form by (wf ())
End Reification.
  
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
