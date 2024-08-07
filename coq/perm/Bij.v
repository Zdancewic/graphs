(** BIJ *)
(** This files contains the bij relations used in other files *)
From Coq Require Import
     List
     Classes.RelationClasses
     Morphisms
     Arith.Arith
     Lia
     Logic.FinFun
     Program.Basics
.

(* From stdpp Require Import gmultiset base. *)

From ExtLib Require Import
     Structures.Monads
     .

From ITree Require Import
     ITree.

From Equations Require Import
     Equations.


Import ListNotations.
Import Relation_Definitions.

Import Monads.
(* Import Monads. *)
(* Import MonadNotation. *)

(* Local Open Scope monad_scope. *)
Local Open Scope list_scope.

Inductive bij : nat -> Set :=
| bij_id : forall (n:nat), bij n
| bij_swap : forall (n:nat), bij (2 + n)
| bij_comp : forall (n:nat) (s1 s2 : bij n), bij n
| bij_plus : forall (n m:nat) (s1 : bij n) (s2 : bij m),
    bij (n + m)
.
Arguments bij_comp {_}.
Arguments bij_plus {_ _}.

(* Equations Derive NoConfusion for nat. *)
(* Next Obligation. *)
(* Admitted. *)
(* Next Obligation. *)
(* Admitted. *)
(* Equations Derive NoConfusion NoConfusionHom for list. *)
(* Next Obligation. *)
(* Admitted. *)
(* Next Obligation. *)
(* Admitted. *)
(* Equations Derive Signature NoConfusion for bij. *)
(* Next Obligation. *)
(* Admitted. *)
(* Next Obligation. *)
(* Admitted. *)


Notation "'ι' [ n ]" := (bij_id n).
Notation "'σ' [ n ]" := (bij_swap n).
(* NOTE: [⨾] is a "fatsemi" not a regular semi and it is written as \fcmp *)
Notation "b1 ⨾ b2" := (bij_comp b1 b2) (at level 55, right associativity).
Infix  "⊍" := (bij_plus) (at level 60, right associativity).

Notation "f >>> g" := (compose g f) (at level 55, right associativity).

Definition size_bij (n:nat) (s:bij n) : nat :=
  match s with
  | bij_id n => n
  | bij_swap n => 2 + n
  | @bij_comp n _ _ => n
  | @bij_plus n m _ _ => n + m
  end.

Fixpoint bijection {n : nat} (b : bij n) : nat -> nat :=
  match b with
  | bij_id _ => fun (i:nat) => i
  | bij_swap _ => fun (i:nat) =>
                   match i with
                   | 0 => 1
                   | 1 => 0
                   | n => n
                   end
  | bij_comp b1 b2 =>
      fun i => (bijection b2 (bijection b1 i))
  | @bij_plus n _ b1 b2 =>
      fun i =>
        if Nat.ltb i n
        then (bijection b1) i
        else n + (bijection b2) (i - n)
  end.

Notation "⟦ b ⟧" := (@bijection _ b).

Definition bij_shift (n:nat) {m:nat} (b : bij m) : bij (n + m) :=
  ι[n] ⊍ b.

Notation "b >> [ n ]" := (bij_shift n b) (at level 35).

(* Assuming [f i < n] makes this into a PER, not an equivalence *)
Definition nat_fun_eq n (f : nat -> nat) (g : nat -> nat) : Prop :=
  forall i, i < n -> f i = g i /\ f i < n.

Infix "≈[ n ]" := (nat_fun_eq n) (at level 70, no associativity).

Definition bij_equiv (n:nat) : bij n -> bij n -> Prop :=
  fun b1 b2 => ⟦b1⟧ ≈[n] ⟦b2⟧.

Infix "≡[ n ]" := (bij_equiv n) (at level 70, no associativity).

(*
#[global] Instance refl_nat_fun_eq : forall n, Reflexive (nat_fun_eq n).
Proof.
  intros. repeat red.
  intros. reflexivity.
Qed.
 *)

#[global] Instance sym_nat_fun_eq : forall n, Symmetric (nat_fun_eq n).
Proof.
  intros. repeat red.
  intros. edestruct (H i) as [HE HLT]; auto.
  rewrite <- HE. auto.
Qed.

#[global] Instance trans_nat_fun_eq : forall n, Transitive (nat_fun_eq n).
Proof.
  intros. repeat red.
  intros.
  destruct (H i) as [HE1 HLT1]; auto.
  destruct (H0 i) as [HE2 HLT2]; auto.  
  rewrite <- HE2, <- HE1. auto.
Qed.

#[global]
  Instance Proper_comp: forall {n}, Proper (nat_fun_eq n ==> nat_fun_eq n ==> (nat_fun_eq n)) (compose).
Proof.
  repeat red.
  intros.
  unfold compose.  
  destruct (H0 i) as [HE2 HLT2]; auto.
  destruct (H (x0 i)) as [HE1 HLT1]; auto.
  rewrite <- HE2, <- HE1; auto. 
Qed.

#[global]
  Instance Proper_comp': forall {n}, Proper (nat_fun_eq n ==> nat_fun_eq n ==> flip (nat_fun_eq n)) (compose).
Proof.
  repeat red.
  intros.
  unfold compose.  
  destruct (H0 i) as [HE2 HLT2]; auto.
  destruct (H (x0 i)) as [HE1 HLT1]; auto.
  rewrite <- HE2, <- HE1; auto. 
Qed.

#[global] Instance bij_equiv_Symmetric : forall n, Symmetric (bij_equiv n).
Proof.
  intros.
  do 2 red. intros. symmetry. apply H.
Qed.

#[global] Instance bij_equiv_Transitive : forall n, Transitive (bij_equiv n).
Proof.
  intros.
  do 2 red. intros. eapply transitivity; eauto.
Qed.

#[global] Instance bijection_bij_equiv_Proper: forall n, Proper (bij_equiv n ==> nat_fun_eq n) (@bijection n).
Proof.
  do 2 red.
  intros. apply H.
Qed.  

Lemma bij_bounds : forall (n:nat) (b : bij n),
  forall i (LT : i < n), ⟦b⟧ i < n.
Proof.
  intros n b.
  induction b; intros; auto.
  - destruct i; simpl.
    + lia.
    + destruct i; lia.
  - simpl; auto.
  - simpl.
    destruct (Nat.ltb_spec0 i n).
    + apply IHb1 in l. lia.
    + assert (i - n < m). { lia.  }
      specialize (IHb2 (i -n)). apply IHb2 in H.
      lia.
Qed.      

#[global] Instance bij_equiv_Reflexive : forall n, Reflexive (bij_equiv n).
Proof.
  do 2 red. intros.
  split. reflexivity. apply bij_bounds. assumption.
Qed.  

Lemma bij_comp_assoc : forall (n:nat) (b1 b2 b3 : bij n),
    ⟦b1 ⨾ (b2 ⨾ b3) ⟧ ≈[n] ⟦(b1 ⨾ b2) ⨾ b3 ⟧.
Proof.
  intros.
  repeat red. intros.
  split.
  reflexivity.
  simpl. repeat apply bij_bounds. assumption.
Qed.  

Lemma bij_comp_comp : forall (n:nat) (b1 b2 : bij n),
    ⟦b1 ⨾ b2⟧  ≈[n]  ⟦b1⟧ >>> ⟦b2⟧.
Proof.
  repeat red; intros.
  split. reflexivity.
  repeat apply bij_bounds. assumption.
Qed.  

Lemma bij_comp_eq : forall n (b1 b2 : bij n) (x:nat),
    ⟦b2⟧ (⟦b1⟧ x) = ⟦b1 ⨾ b2⟧ x.
Proof.
  reflexivity.
Qed.

Lemma bij_comp_eq_parts1 : forall n (b11 b12 : bij n) (b21 b22 : bij n),
    ⟦b11⟧ ≈[n] ⟦b12⟧ ->
    ⟦b21⟧ ≈[n] ⟦b22⟧ ->
    ⟦b11⟧ >>> ⟦b21⟧ ≈[n] ⟦b12⟧ >>> ⟦b22⟧.
Proof.
  intros.
  apply Proper_comp; auto.
Qed.  

Lemma bij_comp_eq_parts : forall n (b11 b12 : bij n) (b21 b22 : bij n),
    ⟦b11⟧ ≈[n] ⟦b12⟧ ->
    ⟦b21⟧ ≈[n] ⟦b22⟧ ->
    ⟦b11 ⨾ b21⟧ ≈[n] ⟦b12 ⨾ b22⟧.
Proof.
  intros.
  simpl.
  intros x LT.
  split.
  destruct (H x) as [HE HLT]; auto.
  rewrite HE.
  destruct (H0 (⟦b12⟧ x)) as [HE2 HLT2]; auto.
  apply bij_bounds. assumption.
  repeat apply bij_bounds. assumption.
Qed.

#[global] Instance bij_comp_bij_equiv_Proper : forall (n:nat), Proper (bij_equiv n ==> bij_equiv n ==> bij_equiv n) (@bij_comp n).
Proof.
  intros.
  do 3 red. intros.
  apply bij_comp_eq_parts; auto.
Qed.  

Lemma bij_id_ident : forall (n i : nat),
    ⟦ι[n]⟧ i = i.
Proof.
  reflexivity.
Qed.  

Lemma bij_comp_plus : forall n m (b11 b12 : bij n) (b21 b22 : bij m),
    ⟦(b11 ⊍ b21) ⨾ (b12 ⊍ b22)⟧ ≈[n + m] ⟦(b11 ⨾ b12) ⊍ (b21 ⨾ b22)⟧.
Proof.
  intros.
  repeat red.
  intros.
  simpl.
  destruct (Nat.ltb_spec0 i n).
  - assert (⟦ b11 ⟧ i < n) by (apply bij_bounds; auto).
    destruct (Nat.ltb_spec0 (⟦ b11 ⟧ i) n).
    + split. reflexivity. specialize (bij_bounds _ b12 _ H0). intros. lia.
    + contradiction.
  - destruct (Nat.ltb_spec0 (n + ⟦ b21 ⟧ (i - n)) n).
    + lia.
    + assert ((n + ⟦ b21 ⟧ (i - n) - n) = ⟦ b21 ⟧ (i - n)). { lia. }
      rewrite H0.
      split. reflexivity. assert (⟦ b22 ⟧ (⟦ b21 ⟧ (i - n)) < m). { repeat apply bij_bounds. lia. }
           lia.
Qed.      

Lemma bij_comp_plus_equiv : forall n m (b11 b12 : bij n) (b21 b22 : bij m),
    (b11 ⊍ b21) ⨾ (b12 ⊍ b22) ≡[n + m] (b11 ⨾ b12) ⊍ (b21 ⨾ b22).
Proof.
  intros. apply bij_comp_plus.
Qed.  

Lemma bij_zero_plus : forall n (b: bij n), ⟦ι[0] ⊍ b⟧ ≈[n] ⟦b⟧.
Proof.
  intros.
  simpl.
  red. intros.
  rewrite Nat.sub_0_r.
  split. reflexivity.  apply bij_bounds. assumption.
Qed.

Lemma bij_zero_plus_equiv : forall n (b: bij n), ι[0] ⊍ b ≡[n] b.
Proof.
  intros. apply bij_zero_plus.
Qed.  

Lemma bij_plus_zero : forall n (b: bij n), ⟦b ⊍ ι[0]⟧ ≈[n] ⟦b⟧.
Proof.
  simpl.
  red. intros.
  assert (i <? n = true). { apply Nat.ltb_lt. assumption. } 
  rewrite H0.
  split. reflexivity. apply bij_bounds. assumption.
Qed.

(* Annoyingly, can't state this one because the type doesn' align *)
(*
Lemma bij_plus_zero_equiv : forall n (b: bij n), (b ⊎ ι[0]) ≡[n+0] b.
 *)

Lemma bij_swap_swap : forall n, ⟦σ[n] ⨾ σ[n]⟧ ≈[2+n] ⟦ι[2+n]⟧.
Proof.
  simpl. red.
  intros n i LT.
  destruct i.
  - split; [reflexivity | lia].
  - destruct i. split; [reflexivity | lia].
    split; [reflexivity | lia].
Qed.

Lemma bij_swap_swap_equiv : forall n, σ[n] ⨾ σ[n] ≡[2+n] ι[2+n].
Proof.
  apply bij_swap_swap.
Qed.

Lemma bij_id_plus_id : forall n m, ⟦ι[n] ⊍ ι[m]⟧ ≈[n+m] ⟦ι[n+m]⟧.
Proof.
  simpl. red.
  intros.
  specialize (Nat.ltb_lt i n) as LT.
  destruct (i <? n).
  split; [reflexivity | lia].
  lia.
Qed.

Lemma bij_id_plus_id_equiv : forall n m, (ι[n] ⊍ ι[m]) ≡[n+m] ι[n+m].
Proof.
  apply bij_id_plus_id.
Qed.  

Lemma bij_plus_eq_parts : forall n m (b11 b12 : bij n) (b21 b22 : bij m),
    ⟦b11⟧ ≈[n] ⟦b12⟧ ->
    ⟦b21⟧ ≈[m] ⟦b22⟧ ->
    ⟦b11 ⊍ b21⟧ ≈[n + m] ⟦b12 ⊍ b22⟧.
Proof.
  intros.
  simpl.
  red. intros.
  destruct (Nat.ltb_spec0 i n).
  - destruct (H i) as [HI HL].
    assumption. split. apply HI. lia.
  - assert (i - n < m) by lia.
    destruct (H0 (i-n)) as [HI HL].
    assumption.
    split.
    rewrite HI; auto.
    lia.
Qed.

#[global] Instance bij_plus_equiv_Proper : forall n m, Proper (bij_equiv n ==> bij_equiv m ==> bij_equiv (n+m)) (@bij_plus n m).
Proof.
  do 3 red.
  intros.
  apply bij_plus_eq_parts; auto.
Qed.


Lemma bij_id_comp_left : forall n (b : bij n),
    ⟦ ι[n] ⨾ b ⟧ ≈[n] ⟦ b ⟧.
Proof.
  intros.
  simpl.
  red.
  intros.
  split. reflexivity. apply bij_bounds. auto.
Qed.  

Lemma bij_id_comp_right : forall n (b : bij n),
    ⟦ b ⨾ ι[n] ⟧ ≈[n] ⟦ b ⟧.
Proof.
  intros.
  simpl.
  red.
  intros.
  split. reflexivity. apply bij_bounds. auto.
Qed.  

Lemma bij_id_comp_left_equiv : forall n (b : bij n),
    ι[n] ⨾ b  ≡[n] b.
Proof.
  apply bij_id_comp_left.
Qed.

Lemma bij_id_comp_right_equiv : forall n (b : bij n),
    b ⨾ ι[n]  ≡[n] b.
Proof.
  apply bij_id_comp_right.
Qed.  

Equations invert {n : nat} (b : bij n) : bij n :=
| ι[n] => ι[n]
| σ[n] => σ[n]
| b1 ⨾ b2 => (invert b2) ⨾ (invert b1)
| b1 ⊍ b2 => (invert b1) ⊍ (invert b2)
.

#[global]
  Transparent invert.

Lemma bij_invert : forall n (b : bij n),
    ⟦b ⨾ invert b⟧ ≈[n] ⟦ι[n]⟧.
Proof.
  intros n b.
  induction b.
  - split. reflexivity. simpl. assumption.
  - red. intros.
    destruct i; split; try reflexivity. simpl. lia.
    destruct i; split; try reflexivity. simpl.  destruct i; lia.
  - replace (invert (b1 ⨾ b2)) with ((invert b2) ⨾ (invert b1)) by reflexivity.
    rewrite <- bij_comp_assoc.
    rewrite bij_comp_comp.
    rewrite bij_comp_assoc.
    rewrite bij_comp_comp.
    rewrite IHb2.
    rewrite <- bij_comp_comp.
    rewrite bij_id_comp_left_equiv.
    apply IHb1.
  - replace (invert (b1 ⊍ b2)) with (invert b1 ⊍ invert b2) by reflexivity.
    rewrite bij_comp_plus.
    rewrite <- bij_id_plus_id.
    rewrite bij_plus_eq_parts; eauto.
    apply bij_equiv_Reflexive.    
Qed.

Lemma bij_invert_equiv : forall n (b : bij n),
    b ⨾ invert b ≡[n] ι[n].
Proof.
  apply bij_invert.
Qed.  

Lemma invert_bij : forall n (b : bij n),
    ⟦invert b ⨾ b⟧ ≈[n] ⟦ι[n]⟧.
Proof.
  intros n b.
  induction b.
  - split. reflexivity. assumption.
  - red. intros.
    destruct i; split; try reflexivity. simpl.  lia.
    destruct i; split; try reflexivity. simpl. destruct i; lia.
  - replace (invert (b1 ⨾ b2)) with ((invert b2) ⨾ (invert b1)) by reflexivity.
    rewrite <- bij_comp_assoc.
    rewrite bij_comp_comp.
    rewrite bij_comp_assoc.
    rewrite bij_comp_comp.
    rewrite IHb1.
    rewrite <- bij_comp_comp.
    rewrite bij_id_comp_left_equiv.
    apply IHb2.
  - replace (invert (b1 ⊍ b2)) with (invert b1 ⊍ invert b2) by reflexivity.
    rewrite bij_comp_plus.
    rewrite <- bij_id_plus_id.
    rewrite bij_plus_eq_parts; eauto.
    apply bij_equiv_Reflexive.
Qed.

Lemma invert_bij_equiv : forall n (b : bij n),
    invert b ⨾ b ≡[n] ι[n].
Proof.
  apply invert_bij.
Qed.  

Lemma invert_invert : forall n (b : bij n),
    ⟦ invert (invert b) ⟧ ≈[n] ⟦b⟧.
Proof.
  intros.
  induction b.
  - simpl. split. reflexivity. assumption.
  - simpl.  split. reflexivity. destruct i. lia. destruct i; lia.
  - simpl.
    red. intros.
    destruct (IHb1 i) as [IH1 LT1]; auto.
    destruct (IHb2 (⟦b1⟧ i)) as [IH2 LT2]; auto.
    apply bij_bounds. assumption.
    split.
    rewrite IH1. rewrite IH2. reflexivity.
    rewrite IH1. apply LT2.
  - simpl.
    red.
    intros.
    destruct (Nat.ltb_spec i n).
    split. apply IHb1. assumption. destruct (IHb1 i) as [_ HL]. assumption.
    lia.
    destruct (IHb2 (i -n)) as [HB HL]. lia.
    split.
    rewrite HB. reflexivity.
    lia.
Qed.    

Lemma invert_invert_equiv : forall n (b : bij n),
    invert (invert b) ≡[n] b.
Proof.
  apply invert_invert.
Qed.  

Lemma coerce_bij : forall n m, m = n -> bij n -> bij m.
Proof.
  intros. subst. assumption.
Defined.  

Lemma coerce_bijection : forall n m (EQ:m = n) (b:bij n) (i:nat),
    ⟦b⟧ i = ⟦coerce_bij n m EQ b⟧ i.
Proof.
  intros. subst. split.  
Qed.  

Lemma bij_inv : forall n (b : bij n),
  forall (i:nat) (LT : i < n), exists j, (j < n) /\ ⟦b⟧j = i.
Proof.
  intros.
  exists (⟦invert b⟧ i).
  split.
  - apply bij_bounds. assumption.
  - rewrite bij_comp_eq. specialize (invert_bij _ b i LT). intros H.
    destruct H as [H1 H2].
    rewrite H1. reflexivity.
Qed.    

  (** Connection to bFun and Bijections *)

  Lemma bFun_bij : forall (n:nat) (b : bij n), bFun n ⟦b⟧.
  Proof.
    intros.
    unfold bFun.
    apply bij_bounds.
  Defined.

  Definition bij_to_fin (n:nat) (b : bij n) : (Fin.t n -> Fin.t n) :=
    Fin2Restrict.restrict (bFun_bij n b).


  (** Missing from the library? *)
  Lemma Bijective_Injective : forall {A B} (f : A -> B), (Bijective f) -> Injective f.
  Proof.
    unfold Bijective, Injective.
    intros.
    destruct H as [g [HH1 HH2]].
    rewrite <- HH1. rewrite <- H0. rewrite HH1.
    reflexivity.
  Qed.

  Lemma Bijective_Surjective : forall {A B} (f : A -> B), (Bijective f) -> Surjective f.
  Proof.
    unfold Bijective, Surjective.
    intros.
    destruct H as [g [HH1 HH2]].
    exists (g y). apply HH2.
  Qed.


  (*
  0    1    2    3  ...   n


f(0) f(1) f(2) f(3) ... f(n)
  g    g    g    g       g

  0    1    2    3  ...   n


remove n  / f(n)

0 1 2 3 4

1 2 4 3 0

f 0 = 1
f 1 = 2
f 2 = 4
f 3 = 3
f 4 = 0

0 1 2 3

0 1 3 2


0 1 2 3 4

1 2 4 0 3

f(0) = 1
f(1) = 2
f(2) = 4
f(3) = 0
f(4) = 3

0 1 2 3

1 2 3 0 


0 1 2 3

2 0 3 1



i -> if f (i) < f(n) then f(i)
     else (f i) - 1

   *)

  (* Remove 0 -> f(0) from the (bijection) f by 
   0 1 2 ... ..... .. n


   0 1 2 ... (f 0) 

   *)
  Definition thin (f:nat -> nat) (n:nat) (i:nat) : nat :=
    if (f (S i)) <? (f 0) then (f (S i)) else (f (S i)) - 1.

  (* Extend bijection f with f 0 = j    (where j < S n)
   *)
  Definition thickx (f:nat -> nat) (n:nat) (j:nat) (i:nat) : nat :=
    if i =? 0 then j else
      if (f (i-1)) <? j then (f (i-1)) else 1 + (f (i-1)).

  Example f_ex (n:nat) :=
    match n with
    | 0 => 1
    | 1 => 2
    | 2 => 4
    | 3 => 0
    | 4 => 3
    | _ => n
    end.

  Example g_ex (n:nat) :=
    match n with
    | 0 => 1
    | 1 => 3
    | 2 => 0
    | 3 => 2
    | _ => n
    end.

  Example h_ex (n:nat) :=
    match n with
    | 0 => 2
    | 1 => 0
    | 2 => 1
    | 3 => 2
    | _ => n
    end.


  Lemma bFun_f_ex : bFun 5 f_ex.
  Proof.
    unfold bFun.
    induction x; intros.
    - simpl.  lia.
    - destruct x; simpl. lia. destruct x. lia. destruct x. lia. destruct x. lia.
      assumption.
  Qed.

  (*
Eval compute in (thin f_ex 5 0).
Eval compute in (thin f_ex 5 1).
Eval compute in (thin f_ex 5 2).
Eval compute in (thin f_ex 5 3).

Eval compute in (thin h_ex 4 0).
Eval compute in (thin h_ex 4 1).
Eval compute in (thin h_ex 4 2).

Eval compute in (thickx (thin h_ex 4) 4 2 0).
Eval compute in (thickx (thin h_ex 4) 4 2 1).
Eval compute in (thickx (thin h_ex 4) 4 2 2).
Eval compute in (thickx (thin h_ex 4) 4 2 3).

Definition g := (thin f_ex 5).

Eval compute in (thickx f_ex 5 3 0).
Eval compute in (thickx f_ex 5 3 1).
Eval compute in (thickx f_ex 5 3 2).
Eval compute in (thickx f_ex 5 3 3).
Eval compute in (thickx f_ex 5 3 4).
Eval compute in (thickx f_ex 5 3 5).

Eval compute in (thickx g 4 1 0).
Eval compute in (thickx g 4 1 1).
Eval compute in (thickx g 4 1 2).
Eval compute in (thickx g 4 1 3).
Eval compute in (thickx g 4 1 4).
   *)

  Lemma thin_bfun : forall (f:nat -> nat) (n:nat) (HF:bFun (S n) f),
      bFun n (thin f n).
  Proof.
    intros.
    unfold bFun in *.
    intros i LT.
    unfold thin.
    destruct (Nat.ltb_spec (f (S i)) (f 0)).
    - assert (f 0 < S n).
      apply HF. lia. lia.
    - assert (f (S i) < S n). apply HF. lia.
      lia.
  Qed.  

  Lemma thickx_bfun : forall (f:nat -> nat) (n:nat) (j:nat) (HJ:j < S n) (HF:bFun n f),
      bFun (S n) (thickx f n j).
  Proof.
    intros.
    unfold bFun in *.
    intros i LT.
    unfold thickx.
    destruct (Nat.eqb_spec i 0).
    - assumption.
    - destruct (Nat.ltb_spec (f (i-1)) j).
      + lia.
      + assert (f (i-1) < n). apply HF. lia. lia.
  Qed.




  (* 
This is only true if f doesn't map to contain f 0
   *)
  Lemma thin_thickx : forall (f:nat -> nat) (n:nat) (HF:bFun (S n) f)
                             (HUnique: forall k, f 0 <> f (S k)),
      thickx (thin f n) n (f 0) ≈[S n] f.
  Proof.
    intros f n HF HUnique.
    intros i LT.
    assert (bFun n (thin f n)) as HB2. apply thin_bfun. assumption.
    unfold bFun in HB2.
    assert (f 0 < S n). apply HF. lia.
    split.
    - unfold thickx in *.
      destruct (Nat.eqb_spec i 0).
      + subst.  reflexivity.
      + simpl.
        unfold thin in *.
        assert (S (i-1) = i) by lia.
        rewrite H0.
        destruct (Nat.ltb_spec (f i) (f 0)).
        * assert (f i <? f 0 = true). apply Nat.ltb_lt; auto.
          rewrite H2. reflexivity.
        * inversion H1.
          ** destruct i.  contradiction. apply HUnique in H3. inversion H3.
          ** assert (f 0 < f i) by lia. simpl.
             destruct (Nat.ltb_spec (m - 0) (f 0)); lia.
    - unfold thickx in *.
      destruct (Nat.eqb_spec i 0).
      + subst.  assumption.
      + simpl.
        unfold thin in *.
        assert (S (i-1) = i) by lia.
        rewrite H0.
        destruct (Nat.ltb_spec (f i) (f 0)).
        * assert (f i <? f 0 = true). apply Nat.ltb_lt; auto.
          rewrite H2. lia.
        * inversion H1.
          ** destruct i. contradiction. apply HUnique in H3. inversion H3.
          ** assert (f 0 < f i) by lia. simpl.
             destruct (Nat.ltb_spec (m - 0) (f 0)). lia.
             unfold bFun in HF.
             replace (S (m - 0)) with (S m) by lia.
             rewrite H2. apply HF. lia.
  Qed.

  Fixpoint up_to (n:nat) : list nat :=
    match n with
    | 0 => []
    | S n => 0::(List.map S (up_to n))
    end.


  (*
 Assuming j < n, yields a permutation that puts the element at index j 
 at index 0, leaving the other elements in the same order.

 Example:  to_front 2 4 [0; 1; 2; 3] ==> [2 ; 0 ; 1; 3]

 [to_front_0] characterizes the idea that [j] will be at the front 
 of the list.

 [to_front_lt] and [to_front_gt] say what happens to the indices
 permutated by the [to_front] operation.
   *)
  Program Fixpoint to_front (j:nat) (n:nat) : bij n :=
    match j with
    | 0 => bij_id n
    | S j =>
        match j with
        | 0 => match n with
               | 0 => bij_id 0
               | 1 => bij_id 1
               | S (S k) => (bij_swap k) 
               end
        | S j' => match n with
                  | 0 => bij_id 0
                  | 1 => bij_id 1
                  | S (S k) => bij_comp (bij_swap _) (coerce_bij _ (2 + k) _ (bij_plus (bij_id 1) (to_front j (S k))))
                  end
        end
    end.


  Example ex1 : nat -> nat := ⟦to_front 2 4⟧.
  (* Eval compute in List.map ex1 (up_to 4). *)

  (* These two helper functions re-compute the indices of the
   function [f] so that, once [f 0], has been pulled to the 
   front, [adjust f] still gives the same results as [f].

   See the lemma [to_front_adjust] below. 
   *)
  Definition adjust_index (v i :nat) :=
    if i <? v then i else i - 1.

  Definition adjust (f : nat -> nat) :=
    fun i => adjust_index (f 0) (f (i+1)).

  (* Builds a data structure that represents the bijection [f] by
   repeatedly pulling the next element to the head of the 
   permutation.  The tricky part is that each use of [to_front]
   re-indexes the tail of the permutation, so we have to 
   adjust the indices.
   *)
  Program Fixpoint build_bij (n:nat) (f : nat -> nat) : bij n :=
    match n with
    | 0 => bij_id 0
    | S m =>
        bij_comp (bij_plus (bij_id 1) (build_bij m (adjust f)))
          (to_front (f 0) (S m))
    end.

  Definition run n b := List.map ⟦build_bij n b⟧ (up_to n).

  Example hex (i:nat) : nat :=
    match i with
    | 0 => 2
    | 1 => 1
    | 2 => 3
    | 3 => 4
    | 4 => 0
    | _ => i
    end.

  (*
Eval compute in run 5 hex.
   *)

  Lemma bFun_adjust : forall n (f:nat -> nat), bFun (S n) f -> bFun n (adjust f).
  Proof.
    intros.
    unfold bFun in *.
    intros. unfold adjust, adjust_index.
    assert (f 0 < S n). apply H. lia.
    destruct (Nat.ltb_spec (f (x + 1)) (f 0)).
    - lia.
    - assert (f (x+1) < S n).
      apply H. lia. lia.
  Qed.

  Lemma to_front_0 : forall (j n : nat) (HLT: j < n),
      ⟦to_front j n⟧ 0 = j.
  Proof.
    induction j; intros; simpl.
    - reflexivity.
    - destruct j.
      + destruct n.
        * lia.
        * destruct n.
          -- lia.
          -- simpl. reflexivity.
      + destruct n.
        * lia.
        * destruct n.
          -- lia.
          -- rewrite <- bij_comp_eq.
             rewrite <- coerce_bijection.
             destruct n.
             ** lia.
             ** assert (((@bijection (S (S (S n))) (bij_swap (S n)) O)) = 1). { reflexivity. }
                rewrite H.
                cbn -[to_front].
                rewrite IHj. reflexivity. lia.
  Qed.

  Lemma to_front_lt : forall j n k
                             (HJ: j < S n)
                             (HLT: k < j),
      ⟦to_front j (S n)⟧ (S k) = k.
  Proof.
    induction j; intros.
    - lia.
    - simpl.
      destruct j.
      + destruct n.
        * lia.
        * assert (k = 0) by lia.
          subst. simpl. reflexivity.
      + destruct n.
        * lia.
        * rewrite <- bij_comp_eq.
          rewrite <- coerce_bijection.
          cbn -[to_front].
          destruct k.
          ** simpl. reflexivity.
          ** cbn -[to_front].
             rewrite IHj; auto. lia. lia.
  Qed.

  Lemma to_front_gt :
    forall j n k
           (HJ: j < S n)
           (HK: k < S n)                  
           (HLT: j < k),
      ⟦to_front j (S n)⟧ k = k.
  Proof.
    induction j; intros.
    - reflexivity.
    - simpl.
      destruct j.
      + destruct n.
        * lia.
        * simpl.
          destruct k. lia. destruct k. lia. reflexivity.
      + destruct n.
        * lia.
        * rewrite <- bij_comp_eq.
          rewrite <- coerce_bijection.
          cbn -[to_front].
          destruct k.
          ** lia.
          ** destruct k.
          -- lia.
          -- cbn -[to_front].
             rewrite IHj; lia.
  Qed.


  Lemma to_front_adjust :
    forall (i n:nat) (f : nat -> nat)
           (HB : bFun (S n) f)
           (HBij: bInjective (S n) f)
           (HLI : i < S n)
           (HNZ : 1 <= i),
      ⟦to_front (f 0) (S n)⟧ (S ((adjust f) (i-1))) = f i.
  Proof.
    intros.
    unfold adjust, adjust_index.
    assert (i - 1 + 1 = i) by lia.
    rewrite H.
    destruct (Nat.ltb_spec (f i) (f 0)).
    - apply to_front_lt; auto. apply HB. lia.
    - destruct (Nat.eqb_spec (f 0) (f i)).
      { assert (0 = i). apply HBij; lia. lia. }
      assert (f 0 < f i) by lia.
      assert (S (f i - 1) = f i) by lia.
      rewrite H2.
      apply to_front_gt.
      + apply HB. lia.
      + apply HB. assumption.
      + destruct (Nat.eqb_spec (f 0) (f i)).
        * unfold bInjective in HBij.
          apply HBij in e; lia.
        * lia.
  Qed.

  Lemma bInjective_lt :
    forall n m (f : nat -> nat)
           (HBij : bInjective n f)
           (HLT: m < n),
      bInjective m f.
  Proof.
    intros.
    unfold bInjective in *.
    intros.
    apply HBij; lia.
  Qed.
  

  Lemma bInjective_adjust :
    forall (n:nat) (f : nat -> nat)
           (HB: bFun (S n) f)
           (HBij : bInjective (S n) f),
      bInjective n (adjust f).
  Proof.
    intros.
    unfold bInjective in *.
    intros.
    unfold adjust, adjust_index in H1.
    unfold bFun in HB.
    destruct (Nat.ltb_spec (f (x+1)) (f 0)).
    - destruct (Nat.ltb_spec (f (y+1)) (f 0)).
      + assert (x + 1 = y + 1).
        apply HBij; lia. lia.
      + destruct (Nat.eqb_spec (f 0) (f (y + 1))).
        apply HBij in e; lia.
        lia.
    - destruct (Nat.ltb_spec (f (y+1)) (f 0)).
      + destruct (Nat.eqb_spec (f 0) (f (x + 1))).
        apply HBij in e; lia.
        lia.
      + destruct (Nat.eqb_spec (f 0) (f (x + 1))).
        apply HBij in e; lia.
        destruct (Nat.eqb_spec (f 0) (f (y + 1))).
        apply HBij in e; lia.
        assert (x + 1 = y + 1).
        apply HBij; lia.
        lia.
  Qed.

  Lemma build_bij_correct :
    forall (n:nat) (f : nat -> nat)
           (HB: bFun n f)
           (HBij: bInjective n f),
      ⟦build_bij n f⟧ ≈[n] f.
  Proof.
    induction n; intros.
    - simpl. intros i HI. lia.
    - simpl.
      red. intros. split.
      + destruct (Nat.ltb_spec i 1).
        * assert (i = 0) by lia. subst.
          apply to_front_0. apply HB. assumption.
        * assert (i - 1 < n) by lia.
          specialize (IHn (adjust f) (bFun_adjust n f HB) (bInjective_adjust n f HB HBij) (i-1) H1).
          destruct IHn.
          rewrite H2.
          apply to_front_adjust; auto.
      + destruct (Nat.ltb_spec i 1).
        * assert (i = 0) by lia. subst.
          rewrite to_front_0. apply HB. assumption. apply HB. assumption.
        * assert (i - 1 < n) by lia.
          specialize (IHn (adjust f) (bFun_adjust n f HB) (bInjective_adjust n f HB HBij) (i-1) H1).
          destruct IHn.
          rewrite H2.
          rewrite to_front_adjust; auto.
  Qed.

  Lemma bInjecive_comp : forall n (f : nat -> nat) (g : nat -> nat),
      bFun n f -> bInjective n f -> bInjective n g -> bInjective n (f >>> g).
  Proof.
    intros.
    unfold bInjective in *.
    intros. unfold compose in H4.
    apply H1 in H4. apply H0; auto. apply H; auto. apply H; auto.
  Qed.

  
  Lemma bInjective_bij : forall n (b : bij n), bInjective n ⟦b⟧.
  Proof.
    intros n b.
    induction b.
    - simpl. red; intros; tauto.
    - simpl. red; intros.
      destruct x; destruct y; auto.
      destruct y; auto. inversion H1.
      destruct x; auto. inversion H1.
      destruct x. destruct y. auto. inversion H1. destruct y. inversion H1. auto.
    - simpl. apply bInjecive_comp. apply bFun_bij. apply IHb1.
      apply IHb2.
    - simpl.
      red.  intros.
      destruct (Nat.ltb_spec x n).
      + destruct (Nat.ltb_spec y n).
        * apply IHb1; auto.
        * assert (bFun n ⟦b1⟧). apply bFun_bij.
          assert (⟦b1⟧ x < n). apply H4. assumption. lia.
      + destruct (Nat.ltb_spec y n).
        * assert (bFun n ⟦b1⟧). apply bFun_bij.
          assert (⟦b1⟧ (y) < n). apply H4.   lia.  lia.
        * assert (⟦ b2 ⟧ (x - n) = ⟦ b2 ⟧ (y - n)) by lia.
          apply IHb2 in H4; lia.
  Qed.
  
  Lemma build_bij_bij :
    forall n (b : bij n),
      (build_bij n ⟦b⟧) ≡[n] b.
  Proof.
    intros.
    apply build_bij_correct.
    apply bFun_bij.
    apply bInjective_bij.
  Qed.

  Lemma bij_bBijective : forall (n:nat) (b : bij n),
    exists (g : nat -> nat), bFun n g /\ forall x, x < n -> g (⟦b⟧ x) = x /\ ⟦b⟧ (g x) = x.
  Proof.
    intros.
    apply bSurjective_bBijective.
    - apply bFun_bij.
    - apply bInjective_bSurjective.
      apply bFun_bij.
      apply bInjective_bij.
  Qed.
