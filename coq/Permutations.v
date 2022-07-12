From Coq Require Import
     List
     Classes.RelationClasses
     Morphisms
     Arith.Arith
     Lia
     Logic.FinFun
     Program.Basics
.

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
Import MonadNotation.

Local Open Scope monad_scope.
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

Equations Derive NoConfusion for nat.
Equations Derive NoConfusion NoConfusionHom for list.
Equations Derive Signature NoConfusion for bij.


Notation "'ι' [ n ]" := (bij_id n).
Notation "'σ' [ n ]" := (bij_swap n).
(* NOTE: [⨾] is a "fatsemi" not a regular semi and it is written as \fcmp *)
Notation "b1 ⨾ b2" := (bij_comp b1 b2) (at level 55, right associativity).
Infix  "⊎" := (bij_plus) (at level 60, right associativity).

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
 ι[n] ⊎ b.

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
    ⟦(b11 ⊎ b21) ⨾ (b12 ⊎ b22)⟧ ≈[n + m] ⟦(b11 ⨾ b12) ⊎ (b21 ⨾ b22)⟧.
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
    (b11 ⊎ b21) ⨾ (b12 ⊎ b22) ≡[n + m] (b11 ⨾ b12) ⊎ (b21 ⨾ b22).
Proof.
  intros. apply bij_comp_plus.
Qed.  

Lemma bij_zero_plus : forall n (b: bij n), ⟦ι[0] ⊎ b⟧ ≈[n] ⟦b⟧.
Proof.
  intros.
  simpl.
  red. intros.
  rewrite Nat.sub_0_r.
  split. reflexivity.  apply bij_bounds. assumption.
Qed.

Lemma bij_zero_plus_equiv : forall n (b: bij n), ι[0] ⊎ b ≡[n] b.
Proof.
  intros. apply bij_zero_plus.
Qed.  

Lemma bij_plus_zero : forall n (b: bij n), ⟦b ⊎ ι[0]⟧ ≈[n] ⟦b⟧.
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
  
Lemma bij_id_plus_id : forall n m, ⟦ι[n] ⊎ ι[m]⟧ ≈[n+m] ⟦ι[n+m]⟧.
Proof.
  simpl. red.
  intros.
  specialize (Nat.ltb_lt i n) as LT.
  destruct (i <? n).
  split; [reflexivity | lia].
  lia.
Qed.

Lemma bij_id_plus_id_equiv : forall n m, (ι[n] ⊎ ι[m]) ≡[n+m] ι[n+m].
Proof.
  apply bij_id_plus_id.
Qed.  

Lemma bij_plus_eq_parts : forall n m (b11 b12 : bij n) (b21 b22 : bij m),
    ⟦b11⟧ ≈[n] ⟦b12⟧ ->
    ⟦b21⟧ ≈[m] ⟦b22⟧ ->
    ⟦b11 ⊎ b21⟧ ≈[n + m] ⟦b12 ⊎ b22⟧.
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
| b1 ⊎ b2 => (invert b1) ⊎ (invert b2)
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
  - replace (invert (b1 ⊎ b2)) with (invert b1 ⊎ invert b2) by reflexivity.
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
  - replace (invert (b1 ⊎ b2)) with (invert b1 ⊎ invert b2) by reflexivity.
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

  
Inductive Permutation {A:Type} : list A -> list A -> Type :=
| perm_id: forall l, Permutation l l
| perm_swap x y l : Permutation ([y] ++ [x] ++ l) ([x] ++ [y] ++ l)
| perm_comp l1 l2 l3 :
    Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3
| perm_plus l11 l12 l21 l22 :
  Permutation l11 l21 -> Permutation l12 l22 -> Permutation (l11 ++ l12) (l21 ++ l22).

Lemma Permutation_length : forall {A} (l1 l2 : list A) (HP : Permutation l1 l2),
    length l1 = length l2.
Proof.
  intros.
  induction HP; simpl; auto.
  rewrite IHHP1. rewrite IHHP2. reflexivity.
  do 2 rewrite app_length. rewrite IHHP1. rewrite IHHP2.
  reflexivity.
Qed.  

(* Not very useful *)
Definition Permutation_eq {A:Type} {l11 l12 l21 l22 : list A}
           (p1 : Permutation l11 l12)
           (p2 : Permutation l21 l22) :=
  l11 = l21 /\ l12 = l22.

Infix "≡" := (Permutation_eq) (at level 80).

Lemma Permutation_symmetric :
  forall {A:Type} (xs ys: list A)
    (H:Permutation xs ys), Permutation ys xs.
Proof.
  intros.
  induction H.
  - apply perm_id.
  - apply perm_swap.
  - eapply perm_comp; eauto.
  - apply perm_plus; eauto.
Qed.    

(** For working with setoid rewriting? *)
(** Propositional characterization *)
Definition Permutation_rel {A:Type} : relation (list A) :=
  fun l1 l2 => exists (p:Permutation l1 l2), True.

Lemma Permutation_rel_Reflexive : forall {A:Type}, Reflexive (@Permutation_rel A).
Proof.
  repeat red.
  intros. exists (perm_id x). auto.
Qed.

Lemma Permutation_rel_Symmetric : forall {A:Type}, Symmetric (@Permutation_rel A).
Proof.
  repeat red.
  intros. destruct H as [P _].
  exists (Permutation_symmetric x y P).  auto.
Qed.

Lemma Permutation_rel_Transitive : forall {A:Type}, Transitive (@Permutation_rel A).
Proof.
  repeat red.
  intros. destruct H as [P _]. destruct H0 as [Q _].
  exists (perm_comp x y z P Q).  auto.
Qed.

#[global]
Existing Instance Permutation_rel_Reflexive.

#[global]
Existing Instance Permutation_rel_Symmetric.

#[global]
Existing Instance Permutation_rel_Transitive.


Section PERM.

(** Thorsten Altenkirch's Characterization of Permutations - a more "canonical" form 
    that is built on insertion sort.
 *)

  Context {A : Type}.
  
Inductive Add : A -> list A -> list A -> Type :=
| zero : forall a aS, Add a aS (a :: aS)
| succ : forall a b aS bs, Add a aS bs -> Add a (b :: aS) (b :: bs).

Arguments zero {_ _}.
Arguments succ {_ _ _ _}.

Inductive Perm : list A -> list A -> Type :=
| perm_nil  : Perm [] []
| perm_cons : forall a aS bs cs, Perm aS cs -> Add a cs bs -> Perm (a :: aS) bs.

Arguments perm_cons {_ _ _ _}.

Fixpoint reflPerm (xs:list A) : Perm xs xs :=
  match xs with
  | [] => perm_nil
  | x::xs => perm_cons (reflPerm xs) zero
  end.

Lemma addLem : forall {a b aS bs cs} (P : Add a aS bs) (Q : Add b bs cs),
    {ds : list A & Add b aS ds * (Add a ds cs)}%type.
Proof.
  intros.
  revert b cs Q.
  induction P; intros.
  - inversion Q; subst.
    + exists (b :: aS). split.  apply zero. apply succ. apply zero.
    + eexists. split. apply X. apply zero.
  - inversion Q; subst.
    + eexists. split. apply zero. apply succ. apply succ. apply P.
    + specialize (IHP b0 bs0 X).
      destruct IHP as [ds [HP HQ]].
      eexists (b::ds). split. eapply succ. assumption. eapply succ. assumption.
Qed.      

Lemma transLem : forall {a bs cs bs'} (P : Perm bs cs) (H : Add a bs' bs),
    { cs' : list A & Perm bs' cs' * Add a cs' cs}%type.
Proof.
  intros.
  revert a bs' H.
  induction P; intros.
  - inversion H.
  - remember (a :: aS) as xs.
    revert a aS P a0 IHP Heqxs.
    inversion H; intros; inversion Heqxs; subst; clear Heqxs.
    + exists cs. split; auto.
    + destruct (IHP _ _ X) as [cs' [P' Q']].
      destruct (addLem Q' a2) as [ds [Y Z]].
      exists ds. split. eapply perm_cons; eauto. apply Z.
Qed.
      
Lemma transPerm : forall {aS bs cs} (P : Perm aS bs) (Q : Perm bs cs),
    Perm aS cs.
Proof.
  intros aS bs cs P Q.
  revert cs Q.
  induction P; intros.
  - assumption.
  - destruct (transLem Q a0) as [cs' [Q' Y]].
    apply (perm_cons (IHP cs' Q')).
    assumption.
Qed.    

Lemma symLem : forall {a aS bs cs} (P: Perm cs aS) (X : Add a cs bs),
    Perm bs (a :: aS).
Proof.
  intros a aS bs cs P X.
  revert aS P.
  induction X; intros.
  - eapply perm_cons. apply P. apply zero.
  - inversion P; subst.
    eapply perm_cons.
    apply (IHX _ X0). apply succ. assumption.
Qed.    

Lemma symPerm : forall {aS bs} (P : Perm aS bs),
    Perm bs aS.
Proof.
  intros.
  induction P.
  - apply perm_nil.
  - eapply symLem. apply IHP. assumption.
Qed.    

Lemma remPerm : forall {a aS bs} (P : Perm (a::aS) (a::bs)),
    Perm aS bs.
Proof.
  intros.
  inversion P; subst.
  inversion X0; subst.
  - assumption.
  - eapply transPerm. apply X.
    eapply perm_cons. apply reflPerm.
    assumption.
Qed.

Lemma swapPerm : forall {a b aS}, (Perm (a::b::aS) (b::a::aS)).
Proof.
  intros.
  eapply perm_cons.
  2: { eapply succ. eapply zero. }
  apply reflPerm.
Qed.

Lemma appendAdd : forall a aS bs cs,
    Add a aS bs -> Add a (aS ++ cs) (bs ++ cs).
Proof.
  intros a aS bs cs H.
  revert cs.
  induction H; intros.
  - apply zero.
  - simpl. apply succ. apply IHAdd.
Qed.    

Lemma appendPerm : forall aS bs cs ds,
    Perm aS bs -> Perm cs ds -> Perm (aS++cs) (bs++ds).
Proof.
  intros aS bs cs ds H.
  revert cs ds.
  induction H; intros.
  - simpl. assumption.
  - simpl. eapply perm_cons.
    apply IHPerm. apply X.
    apply appendAdd.
    assumption.
Qed.

Lemma Permutation_Perm : forall xs ys, Permutation xs ys -> Perm xs ys.
Proof.
  intros.
  induction X.
  - apply reflPerm.
  - apply swapPerm.
  - eapply transPerm. apply IHX1. apply IHX2.
  - apply appendPerm; auto.
Qed.

Lemma Permutation_AddLem : forall a cs bs,
    Add a cs bs -> Permutation (a::cs) bs.
Proof.
  intros.
  induction X.
  - apply perm_id.
  - eapply perm_comp.
    eapply perm_swap.
    replace (b :: bs) with ([b] ++ bs) by reflexivity.
    apply perm_plus. apply perm_id.
    apply IHX.
Qed.
    
Lemma Permutation_Add : forall a aS bs cs, 
    Permutation aS cs -> Add a cs bs -> Permutation (a :: aS) bs.
Proof.
  intros.
  revert a bs X0.
  induction X; intros.
  - apply Permutation_AddLem. assumption.
  - apply Permutation_AddLem in X0.
    replace (a :: [y] ++ [x] ++ l) with ([a] ++ (y::x::l)) by reflexivity.
    eapply perm_comp. eapply perm_plus. apply perm_id.
    eapply perm_swap. assumption.
  - apply IHX2 in X0.
    eapply perm_comp. eapply Permutation_symmetric.
    replace (a :: l1) with ([a] ++ l1) by reflexivity.
    apply perm_plus. apply perm_id.
    apply Permutation_symmetric. apply X1.
    apply X0.
  - apply Permutation_AddLem in X0.
    eapply perm_comp.
    2: { apply X0. }
    replace (a :: l11 ++ l12) with ([a] ++ (l11 ++ l12)) by reflexivity.
    replace (a :: l21 ++ l22) with ([a] ++ (l21 ++ l22)) by reflexivity.
    apply perm_plus. apply perm_id.
    apply perm_plus; assumption.
Qed.

Lemma Perm_Permutation : forall aS bs,
    Perm aS bs -> Permutation aS bs.
Proof.
  intros.
  induction X.
  - apply perm_id.
  - eapply Permutation_Add; eauto.
Qed.    

End PERM.


Set Equations Transparent.

Equations perm_bij {A:Type} (l1 l2 : list A) (p : Permutation l1 l2) : bij (length l1) :=
  perm_bij ?(l) ?(l) (perm_id l)

  := bij_id (length l)
  ;

  perm_bij ?([y] ++ [x] ++ l) ?([x] ++ [y] ++ l) (perm_swap x y l)

  := bij_swap (length l)
  ;

  perm_bij ?(l1) ?(l3) (perm_comp l1 l2 l3 q1 q2) with 
    perm_bij l1 l2 q1, perm_bij l2 l3 q2 => {
    | b1, b2 => bij_comp b1 (coerce_bij _ _ (Permutation_length l1 l2 q1) b2)
    }

  ;
  perm_bij ?(l11 ++ l12) ?(l21 ++ l22) (perm_plus l11 l12 l21 l22 q1 q2) 
    with
    perm_bij ?(l11) ?(l21) q1, perm_bij ?(l12) ?(l22) q2 => {
    | b1, b2 => (coerce_bij _ _ _ (bij_plus b1 b2))
    }
.
Next Obligation.
  apply app_length.
Defined.  

Arguments perm_bij {_ _ _}.

Fixpoint split {A:Type} (n m:nat) (l:list A) (L : length l = n + m) :
  { l1 & { l2 & length l1 = n /\ length l2 = m /\ l1 ++ l2 = l} }.
  revert m l L.
  induction n.
  - intros.
    exists []. exists l. do 2 split. apply L. reflexivity.
  - intros.
    assert ((S n + m) = S (n + m)) by lia.
    rewrite H in L.
    destruct l.
    + inversion L.
    + simpl in L.
      inversion L.
      specialize (IHn m l H1).
      destruct IHn as [l1 [l2 [L1 [L2 EQ]]]].
      exists (a::l1). exists l2. split.
      * simpl. rewrite L1. reflexivity.
      * split.
        -- assumption.
        -- simpl. rewrite EQ. reflexivity.
Defined.           

Lemma coerce_perm {A:Type} (l l1 l2 l3 : list A) (EQ: l1 ++ l2 = l) (p : Permutation (l1 ++ l2) l3) :
  Permutation l l3.
Proof.
  rewrite EQ in p. assumption.
Defined.  

Fixpoint split_option {A:Type} (n:nat) (l:list A) : option (list A * list A) :=
  match n with
  | 0 => Some ([], l)
  | S n => match l with
          | x::xs =>
              '(ys, zs) <- split_option n xs ;;
              ret (x::ys, zs)
          | _ => None
          end
  end.


Lemma split_option_correct {A:Type} (n:nat) (l:list A) (xs ys : list A) :
  split_option n l = Some (xs, ys) -> l = xs ++ ys /\ length xs = n /\ length ys = (length l - n).
Proof.
  revert l xs ys.
  induction n; intros.
  - simpl in H. inversion H. subst. split. reflexivity. split. reflexivity. lia.
  - simpl in H.
    destruct l eqn:HEQ; inversion H.
    subst.
    destruct (split_option n l0) eqn:HEQ2.
    + destruct p. inversion H; subst.
      apply IHn in HEQ2.
      destruct  HEQ2 as [Hys [Hlen HEQ]].
      subst. split. reflexivity. split.  reflexivity. simpl. rewrite HEQ. reflexivity.
    + inversion H.
Qed.

Lemma split_option_total {A:Type} (n:nat) (l:list A) (HL:length l >= n) :
  exists xs ys, split_option n l = Some (xs, ys).
Proof.
  revert l HL.
  induction n; intros.
  - exists []. exists l. reflexivity.
  - destruct l.
    + inversion HL.
    + simpl in HL. assert (length l >= n) by lia.
      destruct (IHn l H) as [xs [ys HEQ]].
      exists (a::xs). exists ys. simpl.
      rewrite HEQ. reflexivity.
Qed.      
      
Fixpoint bij_list {A:Type} {n : nat} (b : bij n) : list A -> option (list A) :=
  match b with
  | bij_id n =>
      fun l => if Nat.eqb (length l) n then ret l else None

  | bij_swap n =>
      fun l =>
        match l with
        | y::x::l => if Nat.eqb (length l) n then ret (x::y::l) else None
        | _ => None
        end

  | bij_comp b1 b2 =>
      fun l =>
        l1 <- bij_list b1 l;;
        bij_list b2 l1

  | @bij_plus n _ b1 b2 =>
      fun l =>
        '(xs, ys) <- split_option n l ;;
        xs' <- bij_list b1 xs ;;
        ys' <- bij_list b2 ys ;;
        ret (xs' ++ ys')
  end.

Lemma bij_list_len1 {A:Type} {n:nat} (b : bij n) (l1 l2 : list A) :
  bij_list b l1 = Some l2 -> n = length l1.
Proof.
  revert l1 l2.
  induction b; intros.
  - simpl in H. destruct (Nat.eqb_spec (length l1) n).
    + auto. + inversion H.
  - simpl in H. destruct l1; inversion H. destruct l1; inversion H.
    destruct (Nat.eqb_spec (length l1) n). simpl. rewrite e. reflexivity.
    inversion H.
  - simpl in H.
    destruct (bij_list b1 l1) eqn:HEQ.
    apply IHb1 in HEQ. assumption.
    inversion H.
  - simpl in H.
    destruct (split_option n l1) eqn:HEQ.
    destruct p.
    apply split_option_correct in HEQ.
    destruct HEQ as [Hl [Hlen _]].
    subst.
    destruct (bij_list b1 l) eqn:HEQ.
    destruct (bij_list b2 l0) eqn:HEQ2.
    apply IHb2 in HEQ2.
    subst. rewrite app_length. reflexivity.
    inversion H.
    inversion H.
    inversion H.
Qed.    

Lemma bij_list_len2 {A:Type} {n:nat} (b : bij n) (l1 l2 : list A) :
  bij_list b l1 = Some l2 -> n = length l2.
Proof.
  revert l1 l2.
  induction b; intros.
  - simpl in H. destruct (Nat.eqb_spec (length l1) n); inversion H.
    subst. reflexivity.
  - simpl in H. destruct l1; inversion H. destruct l1; inversion H.
    destruct (Nat.eqb_spec (length l1) n).
    inversion H. subst. reflexivity.
    inversion H.
  - simpl in H.
    destruct (bij_list b1 l1) eqn:HEQ.
    apply IHb1 in HEQ. 
    eapply IHb2. eauto. inversion H.
  - simpl in H.
    destruct (split_option n l1) eqn:HEQ.
    destruct p.
    apply split_option_correct in HEQ.
    destruct HEQ as [Hl [Hlen _]].
    subst.
    destruct (bij_list b1 l) eqn:HEQ.
    destruct (bij_list b2 l0) eqn:HEQ2.
    apply IHb2 in HEQ2.
    inversion H. subst.
    rewrite app_length.
    apply IHb1 in HEQ. rewrite HEQ. reflexivity.
    inversion H.
    inversion H.
    inversion H.
Qed.    

Lemma bij_list_total {A:Type} (n:nat) (b : bij n) (l1 : list A) (EQ:length l1 = n) :
  exists l2, bij_list b l1 = Some l2.
Proof.
  revert l1 EQ.
  induction b; intros.
  - exists l1. simpl.
    destruct (Nat.eqb_spec (length l1) n).
    + reflexivity.
    + contradiction.
  - destruct l1; try inversion EQ.
    destruct l1; try inversion EQ.
    exists (a0::a::l1). simpl.
    destruct (Nat.eqb (length l1) (length l1)) eqn:HEQ.
    + reflexivity.
    + rewrite Nat.eqb_refl in HEQ. inversion HEQ.
  - specialize (IHb1 l1 EQ).
    destruct IHb1 as [l2 HL2].
    assert (length l2 = n). { symmetry. eapply bij_list_len2. apply HL2. }
    specialize (IHb2 l2 H).
    destruct IHb2 as [l3 HL3].
    exists l3. simpl.
    rewrite HL2. assumption.
  - assert (length l1 >= n) by lia.
    apply split_option_total in H.
    destruct H as [xs [ys HEQ]].
    specialize (split_option_correct _ _ _ _ HEQ). intros.
    destruct H as [HEQ2 [HLX HLY]].
    assert (length ys = m) by lia.
    destruct (IHb1 xs HLX) as [xs2 HB1].
    destruct (IHb2 ys H) as [ys2 HB2].
    exists (xs2 ++ ys2). simpl.
    rewrite HEQ. rewrite HB1. rewrite HB2. reflexivity.
Qed.  

Lemma bij_list_correct {A:Type} (n:nat) (b : bij n) (l1 l2 : list A) (EQ:n = length l1)
  (H: bij_list b l1 = Some l2) :
  exists p : Permutation l1 l2,
    ⟦perm_bij p⟧ ≈[n] ⟦b⟧.
Proof.
  revert l1 l2 EQ H.
 induction b; intros.
  - simpl in H.
    assert (Nat.eqb (length l1) n = true). { subst. apply Nat.eqb_refl. }
    rewrite H0 in H.
    inversion H. subst.
    exists (perm_id l2). simpl. split. reflexivity. assumption.
  - simpl in H.
    destruct l1; inversion H.
    destruct l1; inversion H.
    simpl in EQ. inversion EQ.
    assert (Nat.eqb (length l1) n = true). { subst. apply Nat.eqb_refl. }
    rewrite H0 in H. inversion H.
    exists (perm_swap a0 a l1). split. reflexivity. simpl. destruct i. lia. destruct i; lia.
  - simpl in H.
    destruct (bij_list b1 l1) eqn:HL1.
    specialize (IHb1 l1 l EQ HL1).
    destruct IHb1 as [p1 EQP1].
    assert (n = length l2). { eapply bij_list_len2. apply H. }
    assert (n = length l). { eapply bij_list_len2. apply HL1. }    
    specialize (IHb2 l l2 H1 H).
    destruct IHb2 as [p2 EQP2].
    exists (perm_comp l1 l l2 p1 p2). simpl.
    subst.
    eapply bij_comp_eq_parts1.
    assumption.
    eapply transitivity.
    2: { apply EQP2. }
    symmetry. split. apply coerce_bijection. rewrite H1. apply bij_bounds. lia.
    inversion H.
  - simpl in H.
    destruct (split_option n l1) eqn:HS; try inversion H.
    destruct p.
    destruct (bij_list b1 l) eqn:HL; try inversion H.
    destruct (bij_list b2 l0) eqn:HL0; try inversion H.
    apply split_option_correct in HS.
    destruct HS as [HL1 [Hlen1 HEQ1]].
    rewrite HL1 in EQ, HEQ1.
    rewrite app_length in EQ, HEQ1.
    assert (m  = length l0)  by lia.
    symmetry in Hlen1.
    specialize (IHb1 l l3 Hlen1 HL).
    destruct IHb1 as [p1 EQP1].
    specialize (IHb2 l0 l4 H0 HL0).
    destruct IHb2 as [p2 EQP2].
    rewrite HL1.
    exists (perm_plus l l0 l3 l4 p1 p2).
    simpl.
    unfold perm_bij_clause_4, perm_bij_clause_4_clause_1.
    eapply transitivity.
    1: { symmetry. split. apply coerce_bijection. assert (i < length l + length l0) by lia. 
         simpl.
         destruct (Nat.ltb_spec i (length ?(l))).
         +  destruct (EQP1 i) as [HP HLT]. rewrite Hlen1. assumption. apply lt_plus_trans. assumption.
         + subst.
           destruct (EQP2 (i - length ?(l))). assert (?(l) = l) by reflexivity. rewrite H0. 
           rewrite H0 in H6. lia.
           assert (length ?(l) = length l) by reflexivity.
           rewrite H7. rewrite H7 in H3.
           apply plus_lt_compat_l. assumption.
    } 
    simpl.
    red. intros.
    destruct (Nat.ltb_spec i (length ?(l))).
    + destruct (EQP1 i). rewrite Hlen1. apply H5.
      destruct (Nat.ltb_spec i n).
      -- split. apply EQP1. assumption. apply lt_plus_trans. assumption.
      -- subst. assert (i < length l). apply H5. lia.
    +  destruct (Nat.ltb_spec i n).
       -- split. assert (n <= i). rewrite Hlen1. apply H5. lia.
          assert (n = length ?(l)). apply Hlen1. rewrite <- H7.
          apply plus_lt_compat_l. apply EQP2. lia.
       -- assert (n = length ?(l)). apply Hlen1. rewrite <- H7.
          split.
          ++ destruct (EQP2 (i -n)) as [HQ HL2].
             lia. rewrite <- HQ. reflexivity.
          ++ apply plus_lt_compat_l. rewrite H0. apply bij_bounds. lia.
Qed.             

Lemma bij_list_fun {A:Type} (n:nat) (b : bij n) (l1 : list A) (EQ:n = length l1) :
  exists l2, exists p : Permutation l1 l2,
    ⟦perm_bij p⟧ ≈[n] ⟦b⟧.
Proof.
  destruct (bij_list_total n b l1) as [l2 H]. symmetry. assumption.
  exists l2. apply bij_list_correct; auto.
Qed.

Lemma bij_list_coerce : forall (A:Type) (n m : nat) (H: m = n) (b : bij n) (l:list A),
    bij_list b l = bij_list (coerce_bij n m H b) l.
Proof.
  intros a n m H b.
  revert m H.
  induction b; intros; subst; auto.
Qed.

Lemma app_length_inversion : forall (A:Type) (xs1 xs2 ys1 ys2 : list A),
    xs1 ++ xs2 = ys1 ++ ys2 -> length xs1 = length ys1 -> xs1 = ys1 /\ xs2 = ys2.
Proof.
  induction xs1; intros; simpl in *.
  - destruct ys1.  split.  reflexivity. apply H.
    inversion H0.
  - destruct ys1. inversion H0.
    simpl in *.
    inversion H0.
    inversion H. subst.
    specialize (IHxs1 xs2 ys1 ys2 H4 H2).
    destruct IHxs1. subst. split; auto.
Qed.    
  

Lemma perm_bij_correct : forall (A:Type) (l1 l2 : list A) (p : Permutation l1 l2),
    bij_list (perm_bij p) l1 = Some l2.
Proof.
  intros.
  induction p; simpl.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite IHp1. rewrite <- bij_list_coerce. assumption.
  - unfold perm_bij_clause_4, perm_bij_clause_4_clause_1.
    unfold perm_bij_obligations_obligation_1.
    rewrite <- bij_list_coerce.
    simpl. 
    destruct (@split_option_total A (length (?(l11))) (l11 ++ l12)) as [l11' [l12' H]].
    { rewrite app_length. assert (length ?(l11) = length l11) by reflexivity. rewrite H. lia. }
    rewrite H.
    apply split_option_correct in H.
    destruct H as [HEq1 [HEq2 HEq3]].
    destruct (app_length_inversion _ l11 l12 l11' l12' HEq1). apply symmetry. apply HEq2.
    (* Annoying - the type indices don't line up so you can't just rewrite. *)
    subst. assert (l11' = ?(l11')) by reflexivity.
    assert (@bij_list A (@length A ?(l11')) (@perm_bij A ?(l11') ?(l21) p1) l11' = @Some (list A) l21).
    { eapply transitivity.  2: { apply IHp1. } reflexivity. }
    rewrite H0.
    assert (@bij_list A (@length A ?(l12')) (@perm_bij A ?(l12') ?(l22) p2) l12' = @Some (list A) l22).
    { eapply transitivity. 2: { apply IHp2. } reflexivity. }
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
  destruct H as [g [H1 H2]].
  rewrite <- H1. rewrite <- H0. rewrite H1.
  reflexivity.
Qed.

Lemma Bijective_Surjective : forall {A B} (f : A -> B), (Bijective f) -> Surjective f.
Proof.
  unfold Bijective, Surjective.
  intros.
  destruct H as [g [H1 H2]].
  exists (g y). apply H2.
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
