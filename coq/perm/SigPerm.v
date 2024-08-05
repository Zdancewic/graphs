(*** Permutation Library Signatures *)
(** This library contains six definitions of permutations and equivalence relationship. It turns out that ICPerm is the easiest one in establishing equivalence relation with other permutations. *)
From Coq Require Import
     List
     Classes.RelationClasses
     Morphisms
     Arith.Arith
     Lia
     Logic.FinFun
     Program.Basics
.

From stdpp Require Import gmultiset base.

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

Section Helpers.
  Variable A : Type.
  Section InHelpers.
    Lemma In_cons_iff : forall (a a0 : A) (l : list A),
        In a (a0 :: l) <-> a = a0 \/ In a l.
    Proof.
      intros; split; intros.
      - cbv in H. destruct H as [H | H]; auto.
      - destruct H; subst; auto.
        + apply in_eq.
        + apply in_cons; auto.
    Qed.

    Lemma In_app_exists : forall (a : A) (l : list A), In a l <-> exists l1 l2, l = l1 ++ a :: l2.
    Proof.
      intros; split; intros.
      - induction l.
        + apply in_nil in H; destruct H.
        + apply In_cons_iff in H.
          destruct H.
          ++ exists [], l. subst; auto.
          ++ apply IHl in H as (l1 & l2 & HL).
             exists (a0 :: l1), l2; subst; auto.
      - destruct H as (l1 & l2 & H).
        subst.
        apply in_app_iff; right.
        apply In_cons_iff; left; reflexivity.
    Qed.

    Lemma app_In_inj : forall (l l1 l2 : list A) (a : A), l = l1 ++ a :: l2 -> In a l.
    Proof.
      intros.
      assert (exists l1 l2, l = l1 ++ a :: l2).
      {
        exists l1. exists l2.
        auto.
      }
      apply In_app_exists in H0; auto.
    Qed.

    Lemma In_app_cons_or : forall (a a0: A) (l1 l2 : list A), In a (l1 ++ a0 :: l2) <-> a = a0 \/ In a (l1 ++ l2).
    Proof.
      intros; split; intros.
      - rewrite in_app_iff in *; rewrite In_cons_iff in *; repeat destruct H; auto.
      - rewrite in_app_iff in *; repeat destruct H; rewrite In_cons_iff; auto.
    Qed.

    Lemma list_eq_app_cons : forall (l11 l12 l21 l22 : list A) (a a0 : A)
                               (Happ: l11 ++ a :: l12 = l21 ++ a0 :: l22),
      exists l3 l4, a = a0 \/ l21 = l3 ++ a :: l4 \/ l22 = l3 ++ a :: l4.
    Proof.
      intros.
      symmetry in Happ.
      apply app_In_inj in Happ.
      apply In_app_cons_or in Happ.
      destruct Happ as [Happ | Happ].
      - exists []. exists []. auto.
      - apply in_app_iff in Happ.
        destruct Happ as [Happ | Happ].
        + apply In_app_exists in Happ. destruct Happ as (l1 & l2 & Happ).
          exists l1. exists l2. auto.
        + apply In_app_exists in Happ. destruct Happ as (l1 & l2 & Happ).
          exists l1. exists l2. auto.
    Qed.
  End InHelpers.

  Section TInHelpers.
    Fixpoint TIn (a : A) (l : list A) {struct l} : Type :=
      match l with
      | [] => False
      | b :: m => (a = b)%type + TIn a m
      end.

    Lemma TIn_eq : forall (a : A) (l : list A), TIn a (a :: l).
    Proof.
      intros.
      simpl.
      intuition.
    Qed.

    Lemma TIn_cons : forall (a b: A) (l : list A) (HI : TIn a l), TIn a (b :: l).
    Proof.
      intros.
      simpl.
      intuition.
    Qed.
    
    Lemma TIn_cons_inj : forall (a a0 : A) (l : list A) (HP: TIn a (a0 :: l)),
        ((a = a0)%type + (TIn a l)%type).
    Proof.
      intros.
      simpl in HP.
      destruct HP.
      - intuition.
      - intuition.
    Qed.

    Lemma TIn_cons_surj : forall (a a0 : A) (l : list A) (HI : (a = a0)%type + (TIn a l)), TIn a (a0 :: l).
    Proof.
      intros.
      simpl in *; auto.
    Qed.

    Lemma TIn_app_inj : forall (a : A) (l1 l2 : list A) (HI : TIn a (l1 ++ l2)),
        TIn a l1 + TIn a l2.
    Proof.
      intros a l1. revert a.
      induction l1; intros.
      - intuition.
      - apply TIn_cons_inj in HI. destruct HI; subst; simpl in *.
        + intuition. 
        + apply IHl1 in t.
          intuition.
    Qed.

    Lemma TIn_app_surj : forall (a : A) (l1 l2 : list A) (HI : TIn a l1 + TIn a l2),
        TIn a (l1 ++ l2).
    Proof.
    Admitted.
    (*   intros. *)
    (*   destruct HI. *)
    (* - induction l1; destruct t; simpl in *; intuition. *)
    (* - induction l2; destruct t. *)
    (*   +  *)


    Lemma TIn_app_exists_inj : forall (a : A) (l : list A) (HI : TIn a l),
        {l1 & {l2 & l = l1 ++ a :: l2}}.
    Proof.
      intros a l.
      revert a.
      - induction l; intros.
        + destruct HI. 
        + apply TIn_cons_inj in HI.
          destruct HI.
          ++ exists [], l. subst; auto.
          ++ apply IHl in t as (l1 & l2 & HL).
             exists (a :: l1), l2; subst; auto.
    Qed.

    Lemma TIn_app_exists_surj : forall (a : A) (l : list A) (HI : {l1 & {l2 & l = l1 ++ a :: l2}}),
        TIn a l.
    Proof.
      intros.
      destruct HI as (l1 & l2 & HI).
      subst.
      apply TIn_app_surj; right.
      apply TIn_cons_surj; intuition.
    Qed.

    Lemma app_TIn_inj : forall (l l1 l2 : list A) (a : A), (l = l1 ++ a :: l2)%type -> TIn a l.
    Proof.
      intros.
      assert ({l1 & {l2 & l = l1 ++ a :: l2}}).
      {
        exists l1. exists l2.
        auto.
      }
      apply TIn_app_exists_surj in X; auto.
    Qed.

    Lemma TIn_app_cons_or_inj : forall (a a0: A) (l1 l2 : list A), (TIn a (l1 ++ a0 :: l2))%type -> (a = a0)%type + TIn a (l1 ++ l2).
    Proof.
      intros.
      - apply TIn_app_inj in X. 
        destruct X.
        + right.
          apply TIn_app_surj; intuition.
        + apply TIn_cons_inj in t; destruct t; intuition.
          right.
          apply TIn_app_surj; intuition.
    Qed.

    Lemma TIn_app_cons_or_surj : forall (a a0 : A) (l1 l2 : list A), ((a = a0) + TIn a (l1 ++ l2)) -> TIn a (l1 ++ a0 :: l2).
    Proof.
      intros.
      apply TIn_app_surj.
      destruct X.
      - right.
        apply TIn_cons_surj; intuition.
      - apply TIn_app_inj in t.
        destruct t; intuition.
        right.
        apply TIn_cons_surj; intuition.
    Qed.

    Lemma list_eq_app_cons_type : forall (l11 l12 l21 l22 : list A) (a a0 : A)
                               (Happ: l11 ++ a :: l12 = l21 ++ a0 :: l22),
        (a = a0)%type + {l3 & {l4 & (l21 = l3 ++ a:: l4)%type}} + {l3 & {l4 & (l22 = l3 ++ a :: l4)%type}}.
    Proof.
      intros.
      symmetry in Happ.
      apply app_TIn_inj in Happ.
      apply TIn_app_cons_or_inj in Happ.
      destruct Happ as [Happ | Happ].
      - intuition.
      - apply TIn_app_inj in Happ.
        destruct Happ as [Happ | Happ]; apply TIn_app_exists_inj in Happ; destruct Happ as (l1 & l2 & Happ).
        + left; right.
          exists l1. exists l2. auto.
        + right.
          exists l1. exists l2. auto.
    Qed.

        (* apply (gmultiset_exists l2 _ a), *)
        (*   gmultiset_list_to_set_disj_inv *)
        (*   in H1. *)
    (* Lemma In_TIn_inj : forall (l : list A) (x : A), In x l -> TIn x l. *)
    (* Proof. *)
    (*   intros l. *)
    (*   induction l; intros. *)
    (*   - destruct H. *)
    (*   - destruct H. *)

    

  End TInHelpers.

  Section TMInHelpers.
    (* Search "elem_of". *)
    (* Print elem_of_multiset. *)
    (* Fixpoint TIn (a : A) (l : list A) {struct l} : Type := *)
    (*   match l with *)
    (*   | [] => False *)
    (*   | b :: m => (a = b)%type + TIn a m *)
    (*   end. *)
  End TMInHelpers.
End Helpers.

Section BIJ.
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
End BIJ.

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

Arguments Permutation_rel {_ _ _} _ {_}.
Arguments Permutation_inj_rel {_ _ _} _ {_}.

Class PermRelLaw {A : Type} P `{PermRel A P}
  := {
    PermRel_reflexive :> Reflexive (Permutation_rel P);
    PermRel_symmetric :> Symmetric (Permutation_rel P);
    PermRel_transitive :> Transitive (Permutation_rel P);
    PermRel_proper :>
      Proper
      (Permutation_rel P ==> Permutation_rel P ==> iff)
      (Permutation_rel P)
  }.


(* Class PermRelLaw {A : Type} `{Countable A} *)
(*   (Permutation : list A -> list A -> Type) `{PermRel _ Permutation} *)
(*   := { *)
(*     Permutation_reflexive :> Reflexive (Permutation_rel Permutation); *)
(*     Permutation_symmetric :> Symmetric (Permutation_rel Permutation); *)
(*     Permutation_transitive :> Transitive (Permutation_rel Permutation); *)
(*     Permutation_proper :> *)
(*       Proper *)
(*       (Permutation_rel Permutation ==> Permutation_rel Permutation ==> iff) *)
(*       (Permutation_rel Permutation) *)
(*   }. *)

Notation "l1 ≡[ P ] l2" := (Permutation_rel P l1 l2) (at level 70).

Ltac unfold_relH H :=
  unfold Permutation_rel, _Permutation_rel in H
.

Ltac unfold_destruct_relH H :=
  unfold_relH H; destruct H as (H & _).

Ltac unfold_rel :=
  unfold Permutation_rel, _Permutation_rel.

Section PromoteHelper.
  Context `{Countable A}.
  Context `{@PermRel A _ _ P1} `{@PermRel A _ _ P2}.
  Lemma promote_rel : (forall l1 l2, P1 l1 l2 -> P2 l1 l2) -> (forall l1 l2, Permutation_rel P1 l1 l2 -> Permutation_rel P2 l1 l2).
  Proof.
    intros.
    unfold_destruct_relH H2.
    apply X in H2.
    eexists; auto.
  Qed.
End PromoteHelper.
Print promote_rel.
Arguments promote_rel {_ _ _ _ _ _ _} _ {_ _} _.

Class PermEquiv {A} `{Countable A} (P1 P2 : list A -> list A -> Type) := {
    P1_P2_inj : forall l1 l2, P1 l1 l2 -> P2 l1 l2;
    P2_P1_inj : forall l1 l2, P2 l1 l2 -> P1 l1 l2;
  }.

Instance PermEquiv_inv {A} `{Countable A} (P1 P2 : list A -> list A -> Type) `{PermEquiv A P1 P2} : PermEquiv P2 P1.
Proof.
  destruct H1.
  split; auto.
Defined.

Arguments TIn {_}.
Section Permutation_Instances.
  Context `{Countable A}.
  Section OrderPerm.

    Inductive OrderPerm : list A -> list A -> Type :=
    | orderperm_id: forall l, OrderPerm l l
    | orderperm_swap x y l : OrderPerm ([y] ++ [x] ++ l) ([x] ++ [y] ++ l)
    | orderperm_comp l1 l2 l3 :
      OrderPerm l1 l2 -> OrderPerm l2 l3 -> OrderPerm l1 l3
    | orderperm_plus l11 l12 l21 l22 :
      OrderPerm l11 l21 -> OrderPerm l12 l22 -> OrderPerm (l11 ++ l12) (l21 ++ l22).
    Hint Constructors OrderPerm.

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
      Instance OrderPerm_rel_Reflexive : Reflexive (Permutation_rel OrderPerm).
      Proof.
        repeat red.
        intros. exists (orderperm_id x). auto.
      Qed.

      Instance OrderPerm_rel_Symmetric : Symmetric (Permutation_rel OrderPerm).
      Proof.
        repeat red.
        intros x y HP. destruct HP as [P].
        exists (OrderPerm_symmetric x y P). auto.
      Qed.

      Instance OrderPerm_rel_Transitive : Transitive (Permutation_rel OrderPerm).
      Proof.
        repeat red.
        intros x y z HP0 HP1. destruct HP0 as [P]. destruct HP1 as [Q].
        exists (orderperm_comp x y z P Q). auto.
      Qed.
      
      Instance OrderPerm_Proper : Proper ((Permutation_rel OrderPerm) ==> (Permutation_rel OrderPerm) ==> iff) (Permutation_rel OrderPerm). 
      Proof.
        repeat red.
        intros x0 y0 HP0 x1 y1 HP1.
        split; intros HP2.
        - apply symmetry.  eapply transitivity. 2:{ apply HP0. }  apply symmetry. eapply transitivity; eauto.
        - eapply transitivity. apply HP0. eapply transitivity. apply HP2. apply symmetry. auto.
      Qed.

      #[global]
        Instance PermRelLaw_OrderPerm : PermRelLaw OrderPerm := {
          PermRel_reflexive := reflexivity;
          PermRel_symmetric := symmetry;
          PermRel_transitive := transitivity;
          PermRel_proper := OrderPerm_Proper
        }.

    End OrderPermLaws.
  End OrderPerm.

  (** Inspired by Coq Standard Library *)
  Section SkipPerm.
    Inductive SkipPerm : list A -> list A -> Type :=
    | skipperm_nil : SkipPerm [] []
    | skipperm_swap : forall (x y : A) (l1 l2 : list A),
        SkipPerm l1 l2 ->
        SkipPerm (x :: y :: l1) (y :: x :: l2)
    | skipperm_skip : forall (x : A) (l1 l2 : list A),
        SkipPerm l1 l2 ->
        SkipPerm (x :: l1) (x :: l2)
    | skipperm_trans : forall (l1 l2 l3 : list A),
        SkipPerm l1 l2 ->
        SkipPerm l2 l3 ->
        SkipPerm l1 l3.
    Hint Constructors SkipPerm.

    #[global]
     Instance PermRel_SkipPerm : PermRel SkipPerm := {}.

    Lemma SkipPerm_nil_l_inj : forall (l : list A), SkipPerm [] l -> l = [].
    Proof.
      intros l HS.
      remember ([]) as l_nil.
      induction HS; auto; try discriminate.
      apply IHHS1 in Heql_nil as HR1; rewrite <- HR1.
      rewrite Heql_nil in HR1.
      auto.
    Qed.

    Lemma SkipPerm_nil_l_surj : forall (l : list A), l = [] -> SkipPerm [] l.
    Proof.
      intros; subst; auto.
    Qed.

    Lemma SkipPerm_nil_r_inj : forall (l : list A), SkipPerm l [] -> l = [].
    Proof.
      intros l HS.
      remember [] as l_nil.
      induction HS; auto; try discriminate.
      apply IHHS2 in Heql_nil as HR1; rewrite <- HR1.
      rewrite Heql_nil in HR1.
      auto.
    Qed.

    Lemma SkipPerm_head : forall (l11 l12 l2 : list A), SkipPerm l11 l12 -> SkipPerm (l11 ++ l2) (l12 ++ l2).
    Proof.
      intros l11 l12 l2 HS1. revert l2.
      induction HS1; intros; simpl; auto.
      - induction l2; auto.
      - eapply skipperm_trans; eauto.
    Qed.

    Lemma SkipPerm_tail : forall (l1 l21 l22 : list A), SkipPerm l21 l22 -> SkipPerm (l1 ++ l21) (l1 ++ l22).
    Proof.
      intros l1.
      induction l1; intros; simpl; auto.
    Qed.

    Lemma SkipPerm_comp : forall (l11 l12 l21 l22 : list A), SkipPerm l11 l12 -> SkipPerm l21 l22 -> SkipPerm (l11 ++ l21) (l12 ++ l22).
    Proof.
      intros l11 l12 l21 l22 HS1.
      revert l21 l22.
      induction HS1; intros; auto; repeat rewrite <- app_comm_cons.
      - apply skipperm_swap. auto.
      - apply skipperm_skip; auto.
      - apply skipperm_trans with (l2 := l2 ++ l22).
        {apply IHHS1_1. auto. }
        clear X.
        apply IHHS1_2. induction l22; auto.
    Qed.

    (* Equivalence of Order *)
    Theorem OrderPerm_SkipPerm_inj : forall (l1 l2 : list A), OrderPerm l1 l2 -> SkipPerm l1 l2.
    Proof.
      induction 1; try constructor; try (induction l; auto).
      - eapply skipperm_trans; eauto.
      - apply SkipPerm_comp; auto.
    Qed.

    Theorem SkipPerm_OrderPerm_inj : forall (l1 l2 : list A), SkipPerm l1 l2 -> OrderPerm l1 l2.
    Proof.
      induction 1; try constructor.
      - replace (x :: y :: l1) with ([x] ++ [y] ++ l1) by auto;
        replace (y :: x :: l2) with ([y] ++ [x] ++ l2) by auto.
        repeat rewrite app_assoc.
        apply orderperm_plus; auto.
        + apply orderperm_swap.
      - replace (x :: l1) with ([x] ++ l1) by auto;
        replace (x :: l2) with ([x] ++ l2) by auto.
        apply orderperm_plus; auto.
        + apply orderperm_id.
      - eapply orderperm_comp; eauto.
    Qed.

    Instance PermEquiv_OrderPerm_SkipPerm : PermEquiv OrderPerm SkipPerm := {
        P1_P2_inj := OrderPerm_SkipPerm_inj;
        P2_P1_inj := SkipPerm_OrderPerm_inj;
      }.

    Theorem OrderPermRel_SkipPermRel_bij : forall l1 l2, (Permutation_rel OrderPerm l1 l2) <-> (Permutation_rel SkipPerm l1 l2).
    Proof.
      intros; split.
      - apply (promote_rel OrderPerm_SkipPerm_inj).
      - apply (promote_rel SkipPerm_OrderPerm_inj).
    Qed.

    Section SkipPermLaws.

      Ltac SkipPerm_to_OrderPerm :=
        repeat (match goal with
        | [ H : Permutation_rel SkipPerm _ _ |- _ ] => apply OrderPermRel_SkipPermRel_bij in H
        | [ |- Permutation_rel SkipPerm _ _ ] => apply OrderPermRel_SkipPermRel_bij
        end).
      
      Instance SkipPerm_rel_Reflexive : Reflexive (Permutation_rel SkipPerm).
      Proof.
        unfold Reflexive.
        intros x.
        SkipPerm_to_OrderPerm.
        reflexivity.
      Qed.

      Instance SkipPerm_rel_Symmetric : Symmetric (Permutation_rel SkipPerm).
      Proof.
        unfold Symmetric.
        intros x y HR.
        SkipPerm_to_OrderPerm.
        symmetry; auto.
      Qed.

      Instance SkipPerm_rel_Transitive : Transitive (Permutation_rel SkipPerm).
      Proof.
        unfold Transitive.
        intros x y z HR1 HR2.
        SkipPerm_to_OrderPerm.
        eapply transitivity; eauto.
      Qed.
      

      Instance SkipPerm_Proper : Proper ((Permutation_rel SkipPerm) ==> (Permutation_rel SkipPerm) ==> iff) (Permutation_rel SkipPerm). 
      Proof.
        pose proof OrderPerm_Proper as HO.
        unfold Proper, respectful in *.
        intros x y HR1 x' y' HR2; split; intros HR3; SkipPerm_to_OrderPerm; specialize (HO x y HR1 x' y' HR2); apply HO; auto.
      Qed.

      #[global]
        Instance PermRelLaw_SkipPerm : PermRelLaw SkipPerm := {
          PermRel_reflexive := reflexivity;
          PermRel_symmetric := symmetry;
          PermRel_transitive := transitivity;
          PermRel_proper := SkipPerm_Proper
        }.

    End SkipPermLaws.

    Lemma SkipPerm_id : forall l, SkipPerm l l.
    Proof.
      induction l; auto.
    Qed.

    Lemma SkipPerm_In_weak : forall (l l1 l2 : list A) (a : A)
                               (Heq : l = l1 ++ l2),
        SkipPerm (a :: l) (l1 ++ a :: l2).
    Proof.
      intros.
      revert l l2 a Heq.
      induction l1; intros.
      - revert l Heq. induction l2; intros.
        + subst; repeat constructor.
        + destruct l; try discriminate.
          injection Heq; intros; subst.
          apply SkipPerm_id.
      - destruct l; try discriminate.
        + injection Heq; intros.
          rewrite H1 in *.
          pose proof IHl1 as IHl1'.
          specialize (IHl1 _ _ a0 H0).
          apply skipperm_trans with (l2 := a :: a0 :: l).
          ++ apply skipperm_swap. apply SkipPerm_id.
          ++ simpl. apply skipperm_skip; auto.
    Qed.

    (* HXC: Crucial for ICPerm -> SkipPerm *)
    Lemma SkipPerm_cancel : forall l1 l21 l22 a (HS: SkipPerm l1 (l21 ++ l22)), SkipPerm (a :: l1) (l21 ++ a :: l22).
    Proof.
      intros.
      remember (l21 ++ l22) as l2.
      revert a l21 l22 Heql2.
      induction HS; intros.
      - destruct l21, l22; try discriminate.
        simpl.
        do 2 constructor.
      - destruct l21.
        + simpl.
          destruct l22; try discriminate.
          destruct l22; try discriminate.
          injection Heql2; intros.
          rewrite H1, H2 in *.
          do 2 constructor.
          subst; auto.
        + destruct l21.
          ++
            injection Heql2; intros; subst.
            simpl.
            apply skipperm_trans with (a :: a0 :: x :: l1).
            {
              do 2 constructor; apply SkipPerm_id.
            }
            do 2 constructor; auto.
          ++ 
            injection Heql2; intros.
            specialize (IHHS a _ _ H0).
            rewrite H1, H2 in *; clear H1 H2.
            simpl.
            apply skipperm_trans with (a1 :: a :: a0 :: l1).
            {
              do 2 constructor; apply SkipPerm_id.
            }
            apply skipperm_trans with (a1 :: a0 :: a :: l1).
            {
              do 2 constructor; apply SkipPerm_id.
            }
            constructor.
            auto.
      - destruct l21; simpl in *.
        + subst.
          do 2 constructor; auto.
        + injection Heql2; intros.
          rewrite H1 in *; clear H1.
          apply skipperm_trans with (a0 :: a :: l1).
          {
            constructor; apply SkipPerm_id.
          }
          specialize (IHHS a _ _ H0).
          constructor; auto.
      - specialize (IHHS2 a _ _ Heql2).
        apply skipperm_trans with (a :: l2).
        {
          constructor; auto.
        }
        auto.
    Qed.

    Lemma SkipPermRel_cancel : forall l1 l21 l22 a (HS: Permutation_rel SkipPerm l1 (l21 ++ l22)),
        Permutation_rel SkipPerm (a :: l1) (l21 ++ a :: l22).
    Proof.
      intros.
      unfold_destruct_relH HS.
      eapply SkipPerm_cancel in HS.
      eexists; eauto.
    Qed.
    (*   intros. *)
    (*   remember (l21 ++ l22) as l2. *)
    (*   revert a l21 l22 Heql2. *)
    (*   unfold_destruct_relH HS. *)
    (*   induction HS. *)
    (*   - intros. *)
    (*     destruct l21, l22; try discriminate. *)
    (*     simpl. *)
    (*     assert (SkipPerm [a] [a]) by (do 2 constructor). *)
    (*     eexists; auto. *)
    (*   - intros. *)
    (*     destruct l21. *)
    (*     + simpl. *)
    (*       destruct l22; try discriminate. *)
    (*       destruct l22; try discriminate. *)
    (*       injection Heql2; intros. *)
    (*       rewrite H1, H2 in *. *)
    (*       do 3 constructor. *)
    (*       subst; auto. *)
    (*     + destruct l21. *)
    (*       ++   *)
    (*         injection Heql2; intros; subst. *)
    (*         simpl. *)
    (*         apply transitivity with (a :: a0 :: x :: l1). *)
    (*         { *)
    (*           assert (SkipPerm (a :: x :: a0 :: l1) (a :: a0 :: x :: l1)) by (do 2 constructor; apply SkipPerm_id). *)
    (*           eexists; auto. *)
    (*         }  *)
    (*         do 3 constructor. *)
    (*         auto. *)
    (*       ++ *)
    (*         injection Heql2; intros.  *)
    (*         specialize (IHHS a _ _ H0). *)
    (*         unfold_destruct_relH IHHS. *)
    (*          rewrite H1, H2 in *; clear H1 H2. *)
    (*          simpl. *)
    (*          apply transitivity with (a1 :: a :: a0 :: l1). *)
    (*          { *)
    (*            assert (SkipPerm (a :: a1 :: a0 :: l1) (a1 :: a :: a0 :: l1)) by (do 2 constructor; apply SkipPerm_id). *)
    (*            eexists; auto. *)
    (*          } *)
    (*          apply transitivity with (a1 :: a0 :: a :: l1). *)
    (*          { *)
    (*            assert (SkipPerm (a1 :: a :: a0 :: l1) (a1 :: a0 :: a :: l1)) by (do 2 constructor; apply SkipPerm_id). *)
    (*            eexists; auto. *)
    (*          } *)
    (*          assert (SkipPerm (a1 :: a0 :: a :: l1) (a0 :: a1 :: l21 ++ a :: l22)). *)
    (*          { *)
    (*            constructor. *)
    (*            auto. *)
    (*          } *)
    (*          eexists; auto. *)
    (*   - intros. *)
    (*     destruct l21. *)
    (*     + simpl. *)
    (*       destruct l22; try discriminate. *)
    (*       injection Heql2; intros. *)
    (*       rewrite H1 in *; clear H1. *)
    (*       assert (SkipPerm (a :: a0 :: l1) (a :: a0 :: l22)). *)
    (*       { *)
    (*         subst. *)
    (*         do 2 constructor; auto. *)
    (*       } *)
    (*       eexists; auto. *)
    (*     + injection Heql2; intros. *)
    (*       rewrite H1 in *; clear H1. *)
    (*       simpl. *)
    (*       apply transitivity with (y := (a0 :: a :: l1)). *)
    (*       {  *)
    (*         assert (SkipPerm (a :: a0 :: l1) (a0 :: a :: l1)) by (constructor; apply SkipPerm_id). *)
    (*         eexists; auto. *)
    (*       } *)
    (*       ++ specialize (IHHS a _ _ H0). *)
    (*          unfold_destruct_relH IHHS. *)
    (*          assert (SkipPerm (a0 :: a :: l1) (a0 :: l21 ++ a :: l22)) by (constructor; auto). *)
    (*          eexists; auto. *)
    (*   - intros. *)
    (*     specialize (IHHS2 a _ _ Heql2). *)
    (*     apply transitivity with (y := (a :: l2)). *)
    (*     + *)
    (*       assert (SkipPerm (a :: l1) (a :: l2)) by (constructor; auto). *)
    (*       eexists; auto. *)
    (*     + auto. *)
    (* Qed. *)
  End SkipPerm.

  Section ICPerm.
    Fixpoint occurrence (a : A) (l1 : list A) :=
      match l1 with
      | [] => 0
      | a' :: l1 =>
          let o := occurrence a l1 in
          match (decide_rel eq a a') with
          | left _ => 1 + o
          | right _ => o
          end
      end.

    Lemma occurrence_cons_neq : forall l a x, a <> x <-> occurrence a (x :: l) = occurrence a l.
    Proof.
      intros; split.
      - intros.
        cbn.
        destruct (decide_rel eq a x).
        + apply H0 in e; destruct e.
        + auto.
      - intros; cbn in H0.
        destruct (decide_rel eq a x) in H0.
        + lia.
        + auto.
    Qed.

    Lemma occurrence_cons_iff : forall l x a, occurrence a (x :: l) = if decide_rel eq a x then 1 + occurrence a l else occurrence a l.
    Proof.
      cbn; auto.
    Qed.

    Lemma occurrence_cons_eq : forall l x, occurrence x (x :: l) = S (occurrence x l).
    Proof.
      intros.
      cbn.
      destruct (decide_rel eq x x); auto.
      assert (x = x) by auto.
      apply n in H0; destruct H0.
    Qed.

    Corollary occurrence_cons_eq_neq_0 : forall l x, occurrence x (x :: l) <> 0.
    Proof.
      intros.
      rewrite occurrence_cons_eq.
      intros Hcontra; discriminate.
    Qed.
    
    Lemma occurrence_app_iff : forall l1 l2 a, occurrence a (l1 ++ l2) = occurrence a l1 + occurrence a l2.
    Proof.
      intros l1; induction l1.
      - intros; cbn; auto.
      - intros.
        simpl.
        rewrite IHl1.
        destruct (decide_rel eq a0 a); lia.
    Qed.

    Lemma occurrence_inv_In_non_empty : forall l x,
        occurrence x l <> 0 <-> In x l.
    Proof.
      intros; split.
      - 
        revert x.
        induction l.
        + intros.
          cbn in H0.
          lia.
        + intros.
          cbn in H0.
          destruct (decide_rel eq x a).
          ++ 
            subst.
            apply in_eq.
          ++
            specialize (IHl _ H0).
            apply in_cons; auto.
      - intros.
        apply In_app_exists in H0; destruct H0 as (l1 & l2 & H0).
        subst.
        rewrite occurrence_app_iff.
        rewrite occurrence_cons_eq.
        lia.
    Qed.

    Lemma occurrence_inv_TIn_non_empty_inj : forall l x,
        occurrence x l <> 0 -> TIn x l.
    Proof.
      induction l; intros; cbn in H0.
      - lia.
      - destruct (decide_rel eq x a).
        + 
          subst.
          apply TIn_eq.
        + 
          specialize (IHl _ H0).
          apply TIn_cons; auto.
    Qed.

    Lemma occurrence_inv_l : forall l1 l2 x
                               (HO : forall a, occurrence a (x :: l1) = occurrence a l2),
        In x l2.
    Proof.
      intros.
      pose proof (occurrence_cons_eq_neq_0 l1 x) as HO1.
      rewrite HO in HO1.
      apply occurrence_inv_In_non_empty in HO1; auto.
    Qed.

    Lemma occurrence_inv_TIn_non_empty_surj : forall l x,
        TIn x l -> occurrence x l <> 0.
    Proof.
      intros.
      apply TIn_app_exists_inj in X. destruct X as (l1 & l2 & X).
      subst.
      rewrite occurrence_app_iff.
      rewrite occurrence_cons_eq.
      lia.
    Qed.

    Lemma occurrence_inv_TIn_l : forall l1 l2 x
                               (HO : forall a, occurrence a (x :: l1) = occurrence a l2),
        TIn x l2.
    Proof.
      intros.
      pose proof (occurrence_cons_eq_neq_0 l1 x) as HO1.
      rewrite HO in HO1.
      apply occurrence_inv_TIn_non_empty_inj in HO1; auto.
    Qed.

    Definition ICPerm (l1 l2 : list A) : Type :=
      length l1 = length l2 /\ forall a, (occurrence a l1 = occurrence a l2).

    #[global]
      Instance PermRel_ICPerm : PermRel ICPerm := {}.

    Lemma ICPerm_cons : forall l1 l2 a
                          (HI : ICPerm l1 l2),
        ICPerm (a :: l1) (a :: l2).
    Proof.
      intros.
      unfold ICPerm in HI; destruct HI.
      assert (length (a :: l1) = length (a :: l2)) by (cbn; auto).
      assert (forall x, occurrence x (a :: l1) = occurrence x (a :: l2)).
      {
        intros.
        cbn.
        destruct (decide_rel eq x a); auto.
      }
      unfold ICPerm; auto.
    Qed.

    Lemma ICPerm_swap : forall l1 l2 a b
                          (HI : ICPerm l1 l2),
        (ICPerm (a :: b :: l1) (b :: a :: l2)).
    Proof.
      intros.
      unfold ICPerm in HI; destruct HI.
      assert (length (a :: b :: l1) = length (b :: a :: l2)) by (cbn; auto).
      assert (forall x, occurrence x (a :: b :: l1) = occurrence x (b :: a :: l2)).
      {
        intros.
        cbn.
        destruct (decide_rel eq x a), (decide_rel eq x b); auto.
      }
      unfold ICPerm; auto.
    Qed.

    Lemma ICPerm_trans : forall l1 l2 l3
                           (HI1 : ICPerm l1 l2) (HI2 : ICPerm l2 l3),
        (ICPerm l1 l3).
    Proof.
      intros.
      unfold ICPerm in *. destruct HI1, HI2.
      split.
      - rewrite H0, H2; auto.
      - intros.
        rewrite H1, H3; auto.
    Qed.

    Lemma ICPerm_nil : ICPerm [] [].
    Proof.
      unfold ICPerm; auto.
    Qed.

    Lemma ICPerm_inv_nil_l : forall l
                               (HI : ICPerm [] l), l = [].
    Proof.
      intros.
      unfold ICPerm in *. destruct HI as (HI & _).
      induction l; try discriminate; auto.
    Qed.

    Lemma ICPerm_symmetric : forall l1 l2
                               (HI : ICPerm l1 l2),
        ICPerm l2 l1.
    Proof.
      intros.
      unfold ICPerm in *. destruct HI.
      auto.
    Qed.

    Lemma In_ICPerm_in : forall l1 l2 a
                           (HIn: In a l1)
                           (HI : ICPerm l1 l2),
        In a l2.
    Proof.
      intros l1.
      destruct l1.
      - intros.
        apply in_nil in HIn; destruct HIn.
      - intros.
        apply occurrence_inv_In_non_empty in HIn.
        unfold ICPerm in HI; destruct HI.
        rewrite H1 in HIn.
        apply occurrence_inv_In_non_empty in HIn.
        auto.
    Qed.

    Lemma ICPerm_inv_cons_l : forall l1 l2 a
                                (HI : ICPerm (a :: l1) l2),
        In a l2.
    Proof.
      intros.
      assert (In a (a :: l1)) by apply in_eq.
      eapply In_ICPerm_in; eauto.
    Qed.

    Lemma TIn_ICPerm_in : forall l1 l2 a
                           (HIn: TIn a l1)
                           (HI : ICPerm l1 l2),
        TIn a l2.
    Proof.
      intros l1.
      destruct l1.
      - intros.
        destruct HIn.
      - intros.
        apply occurrence_inv_TIn_non_empty_surj in HIn.
        unfold ICPerm in HI; destruct HI.
        rewrite H1 in HIn.
        apply occurrence_inv_TIn_non_empty_inj in HIn.
        auto.
    Qed.

    Lemma ICPerm_inv_TIn_cons_l : forall l1 l2 a
                                (HI : ICPerm (a :: l1) l2),
        TIn a l2.
    Proof.
      intros.
      assert (TIn a (a :: l1)) by apply TIn_eq.
      eapply TIn_ICPerm_in; eauto.
    Qed.

    Lemma SkipPerm_ICPerm_inj : forall l1 l2 (HS: SkipPerm l1 l2),
        ICPerm l1 l2.
    Proof.
      intros.
      induction HS.
      - unfold ICPerm; intuition.
      - apply ICPerm_swap; intuition.
      - apply ICPerm_cons; intuition.
      - eapply ICPerm_trans; eauto.
    Qed.
    
    (* Lemma SkipPermRel_ICPermRel_inj : forall l1 l2 *)
    (*                                     (HS : Permutation_rel SkipPerm l1 l2), *)
    (*     Permutation_rel ICPerm l1 l2. *)
    (* Proof. *)
    (*   intros. *)
    (*   unfold_destruct_relH HS. *)
    (*   apply SkipPerm_ICPerm_inj in HS. *)
    (*   eexists; auto. *)
    (* Qed. *)
    (*   intros. *)
    (*   unfold_destruct_relH HS. *)
    (*   induction HS. *)
    (*   - pose proof ICPerm_nil. *)
    (*     eexists; auto. *)
    (*   - unfold_destruct_relH IHHS.  *)
    (*     assert (ICPerm (x :: y :: l1) (y :: x :: l2)) by (apply ICPerm_swap; auto). *)
    (*     eexists; auto. *)
    (*   - unfold_destruct_relH IHHS. *)
    (*     assert (ICPerm (x :: l1) (x :: l2)) by (apply ICPerm_cons; auto). *)
    (*     eexists; auto. *)
    (*   - unfold_destruct_relH IHHS1. unfold_destruct_relH IHHS2. *)
    (*     assert (ICPerm l1 l3) by (eapply ICPerm_trans; eauto). *)
    (*     eexists; auto. *)
    (* Qed. *)

    Lemma ICPerm_app_cons : forall l1 l21 l22 a
                              (HI: ICPerm l1 (l21 ++ l22)),
                              ICPerm (a :: l1) (l21 ++ a :: l22).
    Proof.
      intros.
      unfold ICPerm in *; destruct HI.
      split.
      - cbn.
        rewrite H0.
        do 2 rewrite app_length.
        cbn.
        lia.
      - intros.
        rewrite occurrence_app_iff.
        cbn.
        destruct (decide_rel eq a0 a); (rewrite H1; rewrite occurrence_app_iff; lia).
    Qed.

    Lemma ICPerm_app_cons_inv : forall l1 l21 l22 a
                                  (HI : ICPerm (a :: l1) (l21 ++ a :: l22)),
        ICPerm l1 (l21 ++ l22).
    Proof.
      intros.
      unfold ICPerm in *; destruct HI.
      split.
      - rewrite app_length in *. cbn in H0.
        rewrite Nat.add_succ_r in H0.
        injection H0; intros; auto.
      - intros.
        specialize (H1 a0).
        rewrite occurrence_app_iff in *.
        cbn in H1.
        destruct (decide_rel eq a0 a).
        + rewrite Nat.add_succ_r in H1.
          injection H1; auto.
        + auto.
    Qed.


    (* Lemma In_app_exists_type : forall l (a : A), In a l -> {l3 & {l4 & l = l3 ++ a :: l4}}%type. *)
    (* Proof. *)
    (*   intros l. *)
    (*   induction l; intros. *)
    (*   - destruct H0. *)
    (*   - apply In_cons_inj_type in H0. *)


    (* Admitted. *)
    

    (* Lemma ICPerm_cons_l_destruct : forall (a : A) (l1 l2 : list A) (HP : ICPerm (a :: l1) l2), *)
    (*     {l3 & {l4 & (l2 = l3 ++ a :: l4)}}%type. *)
    (* Proof. *)
    (*   intros. *)
    (*   apply ICPerm_inv_cons_l in HP. *)
    (*   apply TIn_app_exists_type in HP. *)
    (*   destruct HP as (l3 & l4 & HP). *)
      

  (* Lemma Permutation_destruct1 : *)
  (*   forall (a : A) (l1 l2 : list A) *)
  (*          (HP : P (l1 ++ [a]) l2), *)
  (*     { l2' & (P l2 (l2' ++ [a])) * (P l1 l2')}%type. *)
    Definition ICPerm_SkipPerm_inj : forall l1 l2 (HI : ICPerm l1 l2), SkipPerm l1 l2.
      intros l1; induction l1.
      - intros. apply ICPerm_inv_nil_l in HI; subst; constructor.
      - intros.
        pose proof HI as HI1.
        apply ICPerm_inv_TIn_cons_l, TIn_app_exists_inj in HI.
        destruct HI as (l3 & l4 & HI).
        rewrite HI in *.
        apply ICPerm_app_cons_inv in HI1.
        apply IHl1 in HI1.
        apply SkipPerm_cancel. auto.
    Qed.

    (* Lemma ICPermRel_SkipPermRel_inj : forall l1 l2 *)
    (*                                     (HI: Permutation_rel ICPerm l1 l2), *)
    (*     Permutation_rel SkipPerm l1 l2. *)
    (* Proof. *)
    (*   intros. *)
    (*   unfold_destruct_relH HI. *)
    (*   apply ICPerm_SkipPerm_inj in HI. *)
    (*   eexists; eauto. *)
    (* Qed. *)

    (*   intros l1. *)
    (*   induction l1. *)
    (*   - intros. *)
    (*     unfold_destruct_relH HI. *)
    (*     apply ICPerm_inv_nil_l in HI. *)
    (*     subst. *)
    (*     assert (SkipPerm [] []) by constructor. *)
    (*     eexists; auto. *)
    (*   - intros. *)
    (*     unfold_destruct_relH HI. *)
    (*     pose proof HI as HI1. *)
    (*     apply ICPerm_inv_cons_l, In_app_exists in HI; destruct HI as (l3 & l4 & HI). *)
    (*     rewrite HI in *. *)
    (*     apply ICPerm_app_cons_inv in HI1. *)
    (*     assert (Permutation_rel ICPerm l1 (l3 ++ l4)) by (eexists; auto). *)
    (*     specialize (IHl1 _ H0). *)
    (*     apply SkipPermRel_cancel; auto. *)
    (* Qed. *)

    Corollary SkipPermRel_ICPermRel_bij : forall l1 l2,
        Permutation_rel SkipPerm l1 l2 <-> Permutation_rel ICPerm l1 l2.
    Proof.
      intros; split.
      - apply (promote_rel SkipPerm_ICPerm_inj).
      - apply (promote_rel ICPerm_SkipPerm_inj).
    Qed.
                                                         

    Section ICPermLaws.

      Ltac ICPerm_to_SkipPerm :=
        repeat (match goal with
        | [ H : Permutation_rel ICPerm _ _ |- _ ] => apply SkipPermRel_ICPermRel_bij in H
        | [ |- Permutation_rel ICPerm _ _ ] => apply SkipPermRel_ICPermRel_bij
        end).
      
      Instance ICPerm_rel_Reflexive : Reflexive (Permutation_rel ICPerm).
      Proof.
        unfold Reflexive.
        intros x.
        ICPerm_to_SkipPerm.
        reflexivity.
      Qed.

      Instance ICPerm_rel_Symmetric : Symmetric (Permutation_rel ICPerm).
      Proof.
        unfold Symmetric.
        intros x y HR.
        ICPerm_to_SkipPerm.
        symmetry; auto.
      Qed.

      Instance ICPerm_rel_Transitive : Transitive (Permutation_rel ICPerm).
      Proof.
        unfold Transitive.
        intros x y z HR1 HR2.
        ICPerm_to_SkipPerm.
        eapply transitivity; eauto.
      Qed.

      Instance ICPerm_Proper : Proper ((Permutation_rel ICPerm) ==> (Permutation_rel ICPerm) ==> iff) (Permutation_rel ICPerm). 
      Proof.
        pose proof SkipPerm_Proper as HO.
        unfold Proper, respectful in *.
        intros x y HR1 x' y' HR2; split; intros HR3; ICPerm_to_SkipPerm; specialize (HO x y HR1 x' y' HR2); apply HO; auto.
      Qed.

      #[global]
        Instance PermRelLaw_ICPerm : PermRelLaw ICPerm := {
          PermRel_reflexive := reflexivity;
          PermRel_symmetric := symmetry;
          PermRel_transitive := transitivity;
          PermRel_proper := ICPerm_Proper
        }.
    End ICPermLaws.
  End ICPerm.

  Section MidPerm.
    Inductive MidPerm : list A -> list A -> Type :=
    | midperm_nil : MidPerm [] []
    | midperm_cons : forall a l11 l12 l21 l22, MidPerm (l11 ++ l12) (l21 ++ l22) -> MidPerm (l11 ++ a :: l12) (l21 ++ a :: l22).
    Hint Constructors MidPerm.

    #[global]
     Instance PermRel_MidPerm : PermRel MidPerm := {}.

    Lemma In_MidPerm_in : forall l1 l2 a,
        In a l1 -> MidPerm l1 l2 -> In a l2.
    Proof.
      intros l1 l2 a HIn HM.
      revert a HIn.
      induction HM.
      - intros.
        apply in_nil in HIn; destruct HIn.
      - intros.
        apply In_app_cons_or in HIn.
        apply In_app_cons_or.
        destruct HIn as [HIn | HIn].
        + subst; auto.
        + right. auto.
    Qed.
        
    Lemma MidPerm_cons_in : forall (l11 l12 l2 : list A) (a : A),
        MidPerm (l11 ++ a :: l12) l2 -> In a l2.
    Proof.
      intros l11 l12 l2 a HM.
      assert (HIn: In a (l11 ++ a :: l12)).
      {
        apply In_app_cons_or; auto.
      }
      eapply In_MidPerm_in; eauto.
    Qed.

    Lemma MidPerm_cons_in' : forall (a : A) (l12 l2 : list A),
        MidPerm (a :: l12) l2 -> In a l2.
    Proof.
      intros a l12 l2.
      replace (a :: l12) with ([] ++ a :: l12) by auto.
      apply MidPerm_cons_in.
    Qed.

    Lemma MidPerm_cons_in_separate : forall (a a0 : A) (l11 l12 l21 l22 : list A),
        MidPerm (l11 ++ a :: l12) (l21 ++ a0 :: l22) -> a = a0 \/ In a l21 \/ In a l22.
    Proof.
      intros a a0 l11 l12 l21 l22 HM.
      apply MidPerm_cons_in in HM. 
      apply in_app_iff in HM as [HM | HM]; auto.
      apply In_cons_iff in HM as [HM | HM]; auto.
    Qed.

    Lemma TIn_MidPerm_TIn : forall l1 l2 a,
        TIn a l1 -> MidPerm l1 l2 -> TIn a l2.
    Proof.
      intros l1 l2 a HIn HM.
      revert a HIn.
      induction HM.
      - intros.
        destruct HIn.
      - intros.
        apply TIn_app_cons_or_inj in HIn.
        apply TIn_app_cons_or_surj.
        destruct HIn as [HIn | HIn].
        + subst; auto.
        + right; auto.
    Qed.
        
    Lemma MidPerm_cons_TIn : forall (l11 l12 l2 : list A) (a : A),
        MidPerm (l11 ++ a :: l12) l2 -> TIn a l2.
    Proof.
      intros l11 l12 l2 a HM.
      assert (HIn: TIn a (l11 ++ a :: l12)).
      {
        apply TIn_app_cons_or_surj; auto.
      }
      eapply TIn_MidPerm_TIn; eauto.
    Qed.

    Lemma MidPerm_cons_TIn' : forall (a : A) (l12 l2 : list A),
        MidPerm (a :: l12) l2 -> TIn a l2.
    Proof.
      intros a l12 l2.
      replace (a :: l12) with ([] ++ a :: l12) by auto.
      apply MidPerm_cons_TIn.
    Qed.

    Lemma MidPerm_cons_TIn_separate : forall (a a0 : A) (l11 l12 l21 l22 : list A),
        MidPerm (l11 ++ a :: l12) (l21 ++ a0 :: l22) -> (a = a0)%type + TIn a l21 + TIn a l22.
    Proof.
      intros a a0 l11 l12 l21 l22 HM.
      apply MidPerm_cons_TIn in HM. 
      apply TIn_app_inj in HM as [HM | HM]; auto.
      apply TIn_cons_inj in HM as [HM | HM]; auto.
    Qed.

    Lemma MidPerm_ICPerm_inj : forall l1 l2 (HP : MidPerm l1 l2),
        ICPerm l1 l2.
    Proof.
      intros.
      induction HP.
      - apply SkipPerm_ICPerm_inj.
        constructor.
      - unfold ICPerm in *.
        destruct IHHP.
        split; intros.
        + repeat rewrite app_length; cbn.
          repeat rewrite Nat.add_succ_r.
          repeat rewrite <- app_length.
          lia.
        + repeat rewrite occurrence_app_iff.
          cbn.
          destruct (decide_rel eq a0 a).
          ++ repeat rewrite Nat.add_succ_r.
             repeat rewrite <- occurrence_app_iff.
             rewrite H1; lia.
          ++ repeat rewrite <- occurrence_app_iff.
             rewrite H1; lia.
    Qed.


    Corollary MidPermRel_ICPermRel_inj : forall l1 l2
                                         (HP:  Permutation_rel MidPerm l1 l2),
        Permutation_rel ICPerm l1 l2.
    Proof.
      apply promote_rel, MidPerm_ICPerm_inj.
    Qed.

    Lemma ICPerm_MidPerm_inj : forall l1 l2 (HP : ICPerm l1 l2),
        MidPerm l1 l2.
    Proof.
      intros l1.
      induction l1; intros.
      - apply ICPerm_inv_nil_l in HP; subst.
        constructor.
      - pose proof HP as HP'.
        apply ICPerm_inv_TIn_cons_l in HP.
        apply TIn_app_exists_inj in HP; destruct HP as (l21 & l22 & HP).
        subst.
        apply ICPerm_app_cons_inv in HP'.
        replace (a :: l1) with ([] ++ a :: l1) by auto.
        constructor.
        intuition.
    Qed.

    Theorem ICPermRel_MidPermRel_inj : forall l1 l2
                                         (HP : Permutation_rel ICPerm l1 l2),
        Permutation_rel MidPerm l1 l2.
    Proof.
      apply promote_rel, ICPerm_MidPerm_inj.
    Qed.
    (*   intros l1. *)
    (*   induction l1. *)
    (*   - intros. *)
    (*     unfold_destruct_relH HP. *)
    (*     apply ICPerm_inv_nil_l in HP; subst. *)
    (*     assert (MidPerm [] []) by constructor. *)
    (*     eexists; auto. *)
    (*   - intros. *)
    (*     pose proof HP as HP'. *)
    (*     unfold_destruct_relH HP. *)
    (*     apply ICPerm_inv_cons_l in HP. *)
    (*     apply In_app_exists in HP; destruct HP as (l21 & l22 & HP). *)
    (*     subst. *)
    (*     assert (HIR: Permutation_rel ICPerm l1 (l21 ++ l22)). *)
    (*     { *)
    (*       unfold_destruct_relH HP'. *)
    (*       apply ICPerm_app_cons_inv in HP'. *)
    (*       eexists; auto. *)
    (*     } *)
    (*     specialize (IHl1 _ HIR); unfold_destruct_relH IHl1. *)
    (*     assert (MidPerm (a :: l1) (l21 ++ a :: l22)). *)
    (*     { *)
    (*       replace (a :: l1) with ([] ++ a :: l1) by auto. *)
    (*       apply midperm_cons; simpl. *)
    (*       auto. *)
    (*     } *)
    (*     eexists; auto. *)
    (* Qed. *)

    Corollary MidPermRel_ICPermRel_bij : forall l1 l2, Permutation_rel MidPerm l1 l2 <-> Permutation_rel ICPerm l1 l2.
    Proof.
      intros; split.
      - apply MidPermRel_ICPermRel_inj.
      - apply ICPermRel_MidPermRel_inj.
    Qed.

    Section MidPermLaws.
      Ltac MidPerm_to_ICPerm :=
        repeat (match goal with
        | [ H : Permutation_rel MidPerm _ _ |- _ ] => apply MidPermRel_ICPermRel_bij in H
        | [ |- Permutation_rel MidPerm _ _ ] => apply MidPermRel_ICPermRel_bij
        end).
      
      Instance MidPerm_rel_Reflexive : Reflexive (Permutation_rel MidPerm).
      Proof.
        unfold Reflexive.
        intros x.
        MidPerm_to_ICPerm.
        reflexivity.
      Qed.

      Instance MidPerm_rel_Symmetric : Symmetric (Permutation_rel MidPerm).
      Proof.
        unfold Symmetric.
        intros x y HR.
        MidPerm_to_ICPerm.
        symmetry; auto.
      Qed.

      Instance MidPerm_rel_Transitive : Transitive (Permutation_rel MidPerm).
      Proof.
        unfold Transitive.
        intros x y z HR1 HR2.
        MidPerm_to_ICPerm.
        eapply transitivity; eauto.
      Qed.
      

      Instance MidPerm_Proper : Proper ((Permutation_rel MidPerm) ==> (Permutation_rel MidPerm) ==> iff) (Permutation_rel MidPerm). 
      Proof.
        pose proof ICPerm_Proper as HS.
        unfold Proper, respectful in *.
        intros x y HR1 x' y' HR2; split; intros HR3; MidPerm_to_ICPerm; specialize (HS x y HR1 x' y' HR2); apply HS; auto.
      Qed.

      #[global]
        Instance PermRelLaw_MidPerm : PermRelLaw MidPerm := {
          PermRel_reflexive := reflexivity;
          PermRel_symmetric := symmetry;
          PermRel_transitive := transitivity;
          PermRel_proper := MidPerm_Proper
        }.

    End MidPermLaws.

  End MidPerm.

  Section MFPerm.
    Inductive MFPerm : list A -> list A -> Type :=
    | mfperm_nil : MFPerm [] []
    | mfperm_cons : forall a l1 l21 l22, MFPerm l1 (l21 ++ l22) -> MFPerm (a :: l1) (l21 ++ a :: l22).
    Hint Constructors MFPerm.
    
    #[global]
     Instance PermRel_MFPerm : PermRel MFPerm := {}.

    Lemma MFPerm_MidPerm_inj : forall l1 l2, MFPerm l1 l2 -> MidPerm l1 l2.
    Proof.
      intros l1 l2 HP.
      induction HP.
      - constructor; auto.
      - replace (a :: l1) with ([] ++ a :: l1) by auto.
        apply midperm_cons; auto.
    Qed.

    Corollary MFPermRel_MidPermRel_inj : forall l1 l2, Permutation_rel MFPerm l1 l2 -> Permutation_rel MidPerm l1 l2.
    Proof.
      apply promote_rel, MFPerm_MidPerm_inj.
      (* unfold Permutation_rel, _Permutation_rel. *)
      (* intros l1 l2 HP; destruct HP as (HP & _). *)
      (* apply MFPerm_MidPerm_inj in HP. *)
      (* eexists; auto. *)
    Qed.

    Lemma MFPerm_ICPerm_inj : forall l1 l2 (HP : MFPerm l1 l2),
        ICPerm l1 l2.
    Proof.
      intros.
      induction HP.
      - apply ICPerm_nil.
      - apply ICPerm_app_cons; auto.
    Qed.

    Corollary MFPermRel_ICPermRel_inj : forall l1 l2
                                      (HP: Permutation_rel MFPerm l1 l2),
        Permutation_rel ICPerm l1 l2.
    Proof.
      apply promote_rel, MFPerm_ICPerm_inj.
    Qed.
    (*   intros. *)
    (*   unfold_destruct_relH HP. *)
    (*   induction HP. *)
    (*   - reflexivity. *)
    (*   - unfold_destruct_relH IHHP. *)
    (*     assert (ICPerm (a :: l1) (l21 ++ a :: l22)). *)
    (*     { *)
    (*       apply ICPerm_app_cons; auto. *)
    (*     } *)
    (*     eexists; auto. *)
    (* Qed. *)

    Lemma ICPerm_MFPerm_inj : forall l1 l2 (HI: ICPerm l1 l2),
        MFPerm l1 l2.
    Proof.
      intros l1. induction l1; intros.
      - apply ICPerm_inv_nil_l in HI; subst.
        constructor.
      - pose proof HI as HI'.
        apply ICPerm_inv_TIn_cons_l, TIn_app_exists_inj in HI as (l21 & l22 & HI); subst.
        apply ICPerm_app_cons_inv in HI'.
        constructor.
        intuition.
    Qed.

    Corollary ICPermRel_MFPermRel_inj : forall l1 l2
                                      (HI : Permutation_rel ICPerm l1 l2),
        Permutation_rel MFPerm l1 l2.
    Proof.
      apply promote_rel, ICPerm_MFPerm_inj.
    Qed.
    (*   intros l1. induction l1. *)
    (*   - intros. *)
    (*     unfold_destruct_relH HI. *)
    (*     apply ICPerm_inv_nil_l in HI; subst. *)
    (*     assert (MFPerm [] []) by auto. *)
    (*     eexists; auto. *)
    (*   - intros. *)
    (*     pose proof HI as HI'. *)
    (*     unfold_destruct_relH HI. *)
    (*     apply ICPerm_inv_cons_l, In_app_exists in HI as (l21 & l22 & HI); subst. *)
    (*     assert (HIR : Permutation_rel ICPerm l1 (l21 ++ l22)). *)
    (*     { *)
    (*       unfold_destruct_relH HI'. *)
    (*       apply ICPerm_app_cons_inv in HI'. *)
    (*       eexists; auto. *)
    (*     } *)
    (*     specialize (IHl1 _ HIR); unfold_destruct_relH IHl1. *)
    (*     assert (MFPerm (a :: l1) (l21 ++ a :: l22)) by (constructor; auto). *)
    (*     eexists; auto. *)
    (* Qed. *)

    Corollary MFPermRel_ICPermRel_bij : forall l1 l2,
        Permutation_rel MFPerm l1 l2 <-> Permutation_rel ICPerm l1 l2.
    Proof.
      intros; split.
      - apply MFPermRel_ICPermRel_inj.
      - apply ICPermRel_MFPermRel_inj.
    Qed.

    Section MFPermLaws.
      Ltac MFPerm_to_ICPerm :=
        repeat (match goal with
        | [ H : Permutation_rel MFPerm _ _ |- _ ] => apply MFPermRel_ICPermRel_bij in H
        | [ |- Permutation_rel MFPerm _ _ ] => apply MFPermRel_ICPermRel_bij
        end).

      Instance MFPerm_rel_Reflexive : Reflexive (Permutation_rel MFPerm).
      Proof.
        unfold Reflexive.
        intros x.
        MFPerm_to_ICPerm.
        reflexivity.
      Qed.

      Instance MFPerm_rel_Symmetric : Symmetric (Permutation_rel MFPerm).
      Proof.
        unfold Symmetric.
        intros x y HR.
        MFPerm_to_ICPerm.
        symmetry; auto.
      Qed.

      Instance MFPerm_rel_Transitive : Transitive (Permutation_rel MFPerm).
      Proof.
        unfold Transitive.
        intros x y z HR1 HR2.
        MFPerm_to_ICPerm.
        eapply transitivity; eauto.
      Qed.

      Instance MFPerm_Proper : Proper ((Permutation_rel MFPerm) ==> (Permutation_rel MFPerm) ==> iff) (Permutation_rel MFPerm). 
      Proof.
        pose proof ICPerm_Proper as HM.
        unfold Proper, respectful in *.
        intros x y HR1 x' y' HR2; split; intros HR3; MFPerm_to_ICPerm; specialize (HM x y HR1 x' y' HR2); apply HM; auto.
      Qed.

      #[global]
        Instance PermRelLaw_MFPerm : PermRelLaw MFPerm := {
          PermRel_reflexive := reflexivity;
          PermRel_symmetric := symmetry;
          PermRel_transitive := transitivity;
          PermRel_proper := MFPerm_Proper
        }.
    End MFPermLaws.
  End MFPerm.

  Section MultisetPerm.
    Definition MultisetPerm (l1 l2 : list A) : Type :=
      list_to_set_disj l1 =@{gmultiset A} list_to_set_disj l2.

    #[global]
      Instance PermRel_MultisetPerm : PermRel MultisetPerm := {}.

    (** Define a iff relationship between MultisetPerm and the rest of the permutations definition *)
    Theorem SkipPerm_MultisetPerm_inj : forall (l1 l2 : list A), SkipPerm l1 l2 -> MultisetPerm l1 l2.
    Proof.
      intros l1 l2 HO; unfold MultisetPerm.
      induction HO; auto; try multiset_solver.
    Qed.

    Corollary SkipPermRel_MultisetPermRel_inj : forall (l1 l2 : list A)
                                                  (HS : Permutation_rel SkipPerm l1 l2),
        Permutation_rel MultisetPerm l1 l2.
    Proof.
      apply promote_rel, SkipPerm_MultisetPerm_inj.
    Qed.

   Lemma list_to_set_disj_nil_iff : forall (l : list A), list_to_set_disj l =@{gmultiset A} ∅ <-> l = [].
    Proof.
      induction l; split; auto; intros.
      - simpl in *.
        multiset_solver.
      - discriminate.
    Qed.

    Lemma gmultiset_exists : forall (l : list A) (m : gmultiset A) (a : A)
                               (HM : {[+ a +]} ⊎ m = list_to_set_disj l),
        a ∈@{gmultiset A} (list_to_set_disj l).
    Proof.
      intros.
      multiset_solver.
    Qed.

    (* Lemma gmultiset_exists_TIn : forall (l : list A) (m : gmultiset A) (a : A) *)
    (*                            (HM : {[+ a +]} ⊎ m = list_to_set_disj l), *)
    (*     a ∈@{gmultiset A} (list_to_set_disj l). *)

    Lemma gmultiset_list_to_set_disj_inv : forall (l : list A) (a : A)
                                      (HM : a ∈@{gmultiset A} (list_to_set_disj l)),
        a ∈@{list A} l.
    Proof.
      intros l.
      induction l; intros.
      - simpl in HM. 
        apply gmultiset_not_elem_of_empty in HM.
        destruct HM.
      - simpl in HM. apply gmultiset_elem_of_disj_union in HM.
        destruct HM.
        + apply gmultiset_elem_of_singleton in H0; subst.
          apply elem_of_list_here.
        + apply IHl in H0.
          apply elem_of_list_further; auto.
    Qed.

    Lemma MultisetPerm_cons_inj : forall (l11 l12 l21 l22 : list A) (a : A),
        MultisetPerm (l11 ++ a :: l12) (l21 ++ a :: l22) ->
        MultisetPerm (l11 ++ l12) (l21 ++ l22).
    Proof.
      intros.
      assert (Hrewrite1: forall m1 m2, m1 ⊎ ({[+ a +]} ⊎ m2) =@{gmultiset A} {[+ a +]} ⊎ m1 ⊎ m2) by multiset_solver.
      unfold MultisetPerm in *.
      repeat rewrite list_to_set_disj_app, list_to_set_disj_cons, Hrewrite1 in *.
      multiset_solver.
    Qed.

    Lemma MultisetPermRel_cons : forall (l11 l12 l21 l22 : list A) (a : A),
        Permutation_rel MultisetPerm (l11 ++ a :: l12) (l21 ++ a :: l22) <->
        Permutation_rel MultisetPerm (l11 ++ l12) (l21 ++ l22).
    Proof.
      intros; split; intros HP.
      assert (Hrewrite1: forall m1 m2, m1 ⊎ ({[+ a +]} ⊎ m2) =@{gmultiset A} {[+ a +]} ⊎ m1 ⊎ m2) by multiset_solver.
      - unfold_destruct_relH HP.
        unfold MultisetPerm in HP.
        repeat rewrite list_to_set_disj_app in HP.
        repeat rewrite list_to_set_disj_cons in HP.
        repeat rewrite Hrewrite1 in HP.
        assert (list_to_set_disj l11 ⊎ list_to_set_disj l12 =@{gmultiset A} list_to_set_disj l21 ⊎ list_to_set_disj l22) by multiset_solver.
        unfold_rel.
        eexists; auto.
        unfold MultisetPerm; repeat rewrite list_to_set_disj_app; auto.
      - 
        unfold_destruct_relH HP.
        assert (MultisetPerm (l11 ++ a :: l12) (l21 ++ a :: l22)).
        {
          unfold MultisetPerm in *; repeat rewrite list_to_set_disj_app, list_to_set_disj_cons in *.
          multiset_solver.
        }
        eexists; auto.
    Qed.

(*     Lemma MultisetPerm_ICPerm_inj : forall (l1 l2 : list A), *)
(*         MultisetPerm l1 l2 -> ICPerm l1 l2. *)
(*     Proof. *)
(*       intros l1. *)
(*       induction l1. *)
(*       - admit. *)
(*       - intros. *)

(*     Lemma MultisetPerm_app_exists : forall (l1 l2 : list A) (a : A), *)
(*         MultisetPerm (a :: l1) l2 -> {l3 & {l4 & l2 = l3 ++ a :: l4}}. *)
(*     Proof. *)
(*       intros l1 l2 a. *)
(*       remember (a :: l1) as l. *)
(*       revert l1 l2 a Heql. *)
(*       induction l. *)
(*       - intros. *)
(*         admit. *)
(*       - intros. *)
(*         injection Heql; intros. *)
        


(*     (*   induction l1. *) *)
(*     (*   - admit. *) *)
(*     (*   -  *) *)





        
(*     (*   intros l1 l2. revert l1. *) *)
(*     (*   induction l2. *) *)
(*     (*   - intros. *) *)
(*     (*     admit. *) *)
(*     (*   - intros. *) *)

(*     (* Lemma test : forall (l : list A) (a : A), *) *)
(*     (*     (a ∈@{gmultiset A} list_to_set_disj l)%type -> TIn a l. *) *)
(*     (* Proof. *) *)
(*     (*   intros l. *) *)
(*     (*   induction l. *) *)
(*     (*   - intros. *) *)
(*     (*     admit. *) *)
(*     (*   - intros. *) *)
(*     (*     Search gmultiset. *) *)
(*     (*     unfold elem_of_list. *) *)
(*     (*     destruct H0. *) *)

    
(*     Lemma TIn_MultisetPerm_in : forall (l1 l2 : list A) (a : A), *)
(*         TIn a l1 -> MultisetPerm l1 l2 -> TIn a l2. *)
(*     Proof. *)
(*       intros l1. *)
(*       induction l1; intros. *)
(*       - destruct X. *)
(*       - destruct l2. *)
(*         + admit. *)
(*         + *)
(*           unfold MultisetPerm in X0. *)
(*           simpl in X0. *)
(* (* gmultiset_disj_union_inj_1: *) *)
(* (*   ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (X : gmultiset A), Inj eq eq (disj_union X) *) *)
        

(*     Lemma MultisetPerm_inv_TIn_cons_l : forall (l1 l2 : list A) (a : A), *)
(*         MultisetPerm (a :: l1) (l2) -> TIn a l2. *)
(*     Proof. *)
(*       intros. *)
(*       apply MultisetPerm_MFPerm_inj, *)
(*         MFPerm_ICPerm_inj, *)
(*         ICPerm_inv_TIn_cons_l *)
(*         in X. *)
(*       auto. *)
(*     Qed. *)

(*     Lemma MultisetPerm_MFPerm_inj : forall (l1 l2 : list A) (HP: MultisetPerm l1 l2), *)
(*         MFPerm l1 l2. *)
(*     Proof. *)
(*       intros l1. induction l1; intros. *)
(*       - unfold MultisetPerm in HP; simpl in HP; symmetry in HP. *)
(*         apply list_to_set_disj_nil_iff in HP; subst. *)
(*         constructor. *)
(*       - inversion HP. *)
(*         (* apply (gmultiset_exists l2 _ a), *) *)
(*         (*   gmultiset_list_to_set_disj_inv *) *)
(*         (*   in H1. *) *)
(*         Print elem_of_list_In. *)
(*     Admitted. *)


    (* Lemma TIn_MultisetPerm_TIn : forall (l1 l2 : list A) (a : A), *)
    (*     TIn a l1 -> MultisetPerm l1 l2 -> TIn a l2. *)
    (* Proof. *)
    (*   intros l1. *)
    (*   destruct l1. *)
    (*   - intros. *)
    (*     destruct X. *)
    (*   - intros. *)
        

      (* intros l1 l2. *)
      (* revert l1. *)
      (* induction l1 l2. *)
      (* - intros. *)
      (*   apply list_to_set_disj_nil_iff in H0; subst. *)
      (*   destruct X. *)
      (* - intros. *)
        
                


    (* Lemma MultisetPerm_cons_TIn : forall (l1 l2 : list A) (a : A), *)
    (*     {[+ a +]} ⊎ list_to_set_disj l1 =@{gmultiset A} list_to_set_disj l2 -> TIn a l2. *)
    (* Proof. *)
    (*   intros l1 l2. revert l1. *)
    (*   induction l2. *)
    (*   - intros. *)
    (*     multiset_solver. *)
    (*   - intros. *)
    (*     destruct (decide_rel eq a0 a). *)
    (*     + subst. *)
    (*       assert (list_to_set_disj l1 =@{gmultiset A} list_to_set_disj l2) by multiset_solver. *)
          

    Theorem MultisetPermRel_MFPermRel_inj : forall (l1 l2 : list A)
                                              (HP: Permutation_rel MultisetPerm l1 l2),
        Permutation_rel MFPerm l1 l2.
    Proof.
      intros l1.
      induction l1; intros.
      - unfold_destruct_relH HP.
        unfold MultisetPerm in HP; simpl in HP; symmetry in HP.
        apply list_to_set_disj_nil_iff in HP; subst.
        assert (MFPerm [] []) by constructor.
        eexists; auto.
      - unfold_destruct_relH HP.
        inversion HP.
        apply (gmultiset_exists l2 _ a) in H1.
        apply gmultiset_list_to_set_disj_inv in H1.
        apply elem_of_list_In in H1.
        apply In_app_exists in H1; destruct H1 as (l3 & l4 & H1).
        subst.
        assert (HP': MultisetPerm (l1) (l3 ++ l4)).
        {
          unfold MultisetPerm in HP.
          rewrite list_to_set_disj_app in HP.
          do 2 rewrite list_to_set_disj_cons in HP.
          assert (forall m1 m2, m1 ⊎ ({[+ a +]} ⊎ m2) =@{gmultiset A} {[+ a +]} ⊎ m1 ⊎ m2) by multiset_solver.
          rewrite H0 in HP.
          assert (list_to_set_disj l1 =@{gmultiset A} list_to_set_disj l3 ⊎ list_to_set_disj l4) by multiset_solver.
          unfold MultisetPerm. rewrite list_to_set_disj_app; auto.
        }
        assert (HPR : Permutation_rel MultisetPerm l1 (l3 ++ l4)) by (eexists; auto).
        apply IHl1 in HPR.
        replace (a :: l1) with ([] ++ a :: l1) by auto.
        unfold_destruct_relH HPR.
        assert (MFPerm (a :: l1) (l3 ++ a :: l4)) by (constructor; auto).
        eexists; auto.
    Qed.

    Corollary MultisetPermRel_SkipPermRel_inj : forall (l1 l2 : list A)
                                                  (HP: Permutation_rel MultisetPerm l1 l2),
        Permutation_rel SkipPerm l1 l2.
    Proof.
      intros.
      apply MultisetPermRel_MFPermRel_inj in HP.
      apply MFPermRel_ICPermRel_bij in HP.
      apply SkipPermRel_ICPermRel_bij. auto.
    Qed.
      
    Corollary SkipPermRel_MultisetPermRel_bij : forall l1 l2, (Permutation_rel SkipPerm l1 l2) <-> (Permutation_rel MultisetPerm l1 l2).
    Proof.
      intros; split.
      - apply SkipPermRel_MultisetPermRel_inj.
      - apply MultisetPermRel_SkipPermRel_inj.
    Qed.

    Section MultisetPermLaws.

      Ltac MultisetPerm_to_SkipPerm :=
        repeat (match goal with
        | [ H : Permutation_rel MultisetPerm _ _ |- _ ] => apply SkipPermRel_MultisetPermRel_bij in H
        | [ |- Permutation_rel MultisetPerm _ _ ] => apply SkipPermRel_MultisetPermRel_bij
        end).
      
      Instance MultisetPerm_rel_Reflexive : Reflexive (Permutation_rel SkipPerm).
      Proof.
        unfold Reflexive.
        intros x.
        MultisetPerm_to_SkipPerm.
        reflexivity.
      Qed.

      Instance MultisetPerm_rel_Symmetric : Symmetric (Permutation_rel SkipPerm).
      Proof.
        unfold Symmetric.
        intros x y HR.
        MultisetPerm_to_SkipPerm.
        symmetry; auto.
      Qed.

      Instance MultisetPerm_rel_Transitive : Transitive (Permutation_rel SkipPerm).
      Proof.
        unfold Transitive.
        intros x y z HR1 HR2.
        MultisetPerm_to_SkipPerm.
        eapply transitivity; eauto.
      Qed.
      

      Instance MultisetPerm_Proper : Proper ((Permutation_rel SkipPerm) ==> (Permutation_rel SkipPerm) ==> iff) (Permutation_rel SkipPerm). 
      Proof.
        pose proof SkipPerm_Proper as HO.
        unfold Proper, respectful in *.
        intros x y HR1 x' y' HR2; split; intros HR3; MultisetPerm_to_SkipPerm; specialize (HO x y HR1 x' y' HR2); apply HO; auto.
      Qed.

      #[global]
        Instance PermRelLaw_MultisetPerm : PermRelLaw SkipPerm := {
          PermRel_reflexive := reflexivity;
          PermRel_symmetric := symmetry;
          PermRel_transitive := transitivity;
          PermRel_proper := MultisetPerm_Proper
        }.

    End MultisetPermLaws.

    Section MultisetBijection.
      (* Already did SkipPermRel and MultisetPermRel *)
      Corollary OrderPermRel_MultisetPermRel_bij : forall l1 l2,
          Permutation_rel OrderPerm l1 l2 <-> Permutation_rel MultisetPerm l1 l2.
      Proof.
        intros; split; intros.
        - apply OrderPermRel_SkipPermRel_bij, SkipPermRel_MultisetPermRel_bij in H0.
          auto.
        - apply OrderPermRel_SkipPermRel_bij, SkipPermRel_MultisetPermRel_bij.
          auto.
      Qed.

      Corollary ICPermRel_MultisetPermRel_bij : forall l1 l2,
          Permutation_rel ICPerm l1 l2 <-> Permutation_rel MultisetPerm l1 l2.
      Proof.
        intros; split; intros.
        - apply SkipPermRel_ICPermRel_bij, SkipPermRel_MultisetPermRel_bij in H0.
          auto.
        - apply SkipPermRel_ICPermRel_bij, SkipPermRel_MultisetPermRel_bij.
          auto.
      Qed.

      Corollary MidPermRel_MultisetPermRel_bij : forall l1 l2,
          Permutation_rel MidPerm l1 l2 <-> Permutation_rel MultisetPerm l1 l2.
      Proof.
        intros; split; intros.
        - apply MidPermRel_ICPermRel_bij, ICPermRel_MultisetPermRel_bij in H0.
          auto.
        - apply MidPermRel_ICPermRel_bij, ICPermRel_MultisetPermRel_bij.
          auto.
      Qed.

      Corollary MFPermRel_MultisetPermRel_bij : forall l1 l2,
          Permutation_rel MFPerm l1 l2 <-> Permutation_rel MultisetPerm l1 l2.
      Proof.
        intros; split; intros.
        - apply MFPermRel_ICPermRel_bij, ICPermRel_MultisetPermRel_bij in H0.
          auto.
        - apply MFPermRel_ICPermRel_bij, ICPermRel_MultisetPermRel_bij.
          auto.
      Qed.
    End MultisetBijection.
  End MultisetPerm.

End Permutation_Instances.

(** Ltac for solving permutation  *)
Ltac transform_to_multisetpermrelH :=
  match goal with
  | [ H : Permutation_rel OrderPerm ?l1 ?l2 |- _ ] =>
      apply OrderPermRel_MultisetPermRel_bij in H
  | [ H : Permutation_rel ICPerm ?l1 ?l2 |- _ ] => 
      apply ICPermRel_MultisetPermRel_bij in H
  | [ H : Permutation_rel SkipPerm ?l1 ?l2 |- _ ] =>
      apply SkipPermRel_MultisetPermRel_bij in H
  | [ H : Permutation_rel MidPerm ?l1 ?l2 |- _ ] =>
      apply MidPermRel_MultisetPermRel_bij in H
  | [ H : Permutation_rel MFPerm ?l1 ?l2 |- _ ] =>
      apply MFPermRel_MultisetPermRel_bij in H
  end.

Ltac transform_to_multisetpermrel :=
  match goal with
  | [ |- Permutation_rel OrderPerm ?l1 ?l2 ] =>
      apply OrderPermRel_MultisetPermRel_bij
  | [ |- Permutation_rel ICPerm ?l1 ?l2 ] => 
      apply ICPermRel_MultisetPermRel_bij 
  | [ |- Permutation_rel SkipPerm ?l1 ?l2 ] =>
      apply SkipPermRel_MultisetPermRel_bij
  | [ |- Permutation_rel MidPerm ?l1 ?l2 ] =>
      apply MidPermRel_MultisetPermRel_bij
  | [ |- Permutation_rel MFPerm ?l1 ?l2 ] =>
      apply MFPermRel_MultisetPermRel_bij
  | [ |- Permutation_rel MultisetPerm ?l1 ?l2 ] =>
      idtac
  end.

Ltac normalize_auxH :=
  repeat (match goal with
  | [ H : Permutation_rel ?P ?l1 ?l2 |- _ ] =>
      unfold_destruct_relH H
  end).

Ltac normalize_list_to_set_disj :=
  repeat (match goal with 
          | [ |- context[list_to_set_disj (?l1 ++ ?l2)]] =>
              rewrite list_to_set_disj_app
          | [ H : context[list_to_set_disj (?l1 ++ ?l2)] |- _ ] =>
              rewrite list_to_set_disj_app in H
          | [ |- context[list_to_set_disj (?a :: ?l)]] =>
              rewrite list_to_set_disj_cons
          | [ H : context[list_to_set_disj (?a :: ?l)] |- _ ] =>
              rewrite list_to_set_disj_cons in H
          end).

Ltac multiset_solver_plus :=
  match goal with
  | [ |- Permutation_rel MultisetPerm ?l1 ?l2 ] =>
      let HP := fresh "HP" in
      assert (HP: MultisetPerm l1 l2) by (unfold MultisetPerm in *; normalize_list_to_set_disj; multiset_solver); exists HP; auto
  | [ |- _ ] =>
      unfold MultisetPerm in *; normalize_list_to_set_disj; multiset_solver
  end.

Ltac permutation_solver' :=
  repeat transform_to_multisetpermrelH;
  normalize_auxH;
  try transform_to_multisetpermrel
.

Ltac permutation_solver :=
  permutation_solver'; multiset_solver_plus.

Section Examples.

  Example test0 : list_to_set_disj [1; 2] =@{gmultiset nat} {[+ 1; 2 +]}.
  Proof.
    intros. multiset_solver.
  Qed.


  Example test1 : forall (l1 l2 : list nat),
      Permutation_rel SkipPerm l2 l1 ->
      Permutation_rel OrderPerm l1 l2.
  Proof.
    intros.
    permutation_solver.
  Qed.

  Example test2 : forall X Y Z,
      Permutation_rel SkipPerm X [1] ->
      Permutation_rel SkipPerm Y [2] ->
      Permutation_rel SkipPerm Z [3] ->
      Permutation_rel SkipPerm (X ++ Y ++ Z) [1; 2; 3].
  intros.
  permutation_solver.
  Qed.

  Example test3 : forall X,
      Permutation_rel SkipPerm X [1] ->
      Permutation_rel SkipPerm X [2] ->
      False.
  Proof.
    intros.
    permutation_solver.
  Qed.

  Example test4 : forall (X Y Z : list nat),
      Permutation_rel SkipPerm (X ++ Y) [1; 2] ->
      Permutation_rel SkipPerm (Y ++ Z) [2; 3] ->
      Permutation_rel SkipPerm (X ++ Z) [1; 3] ->
      Permutation_rel SkipPerm (X ++ Y ++ Z) [1; 2 ; 3].
  Proof.
    intros.
    permutation_solver.
  Qed.

  Example test5 : forall (X Y Z : list nat),
      Permutation_rel OrderPerm (X ++ Y) [3; 1] ->
      Permutation_rel ICPerm (Y ++ Z) [2; 3] ->
      Permutation_rel MFPerm (X ++ Z) [1; 3] ->
      Permutation_rel MidPerm (X ++ Y ++ Z) [3; 1; 2].
  Proof.
    intros.
    permutation_solver.
  Qed.

End Examples.

(* TODO: Build another structure / type class that is named TOPermRel. Basically this permutation relation has to be able to convert into one other permutation relation among the six above.
If it does, all the theories can be solved by simply converting to an easier one and solve it.
 *)
 (* _Permutation_inj_rel *)
(* Section TOPERMREL. *)
(*   Context `{Countable A}. *)
(*   Structure perm_convertible := { *)
(*       perm : list A -> list A -> Type; *)
(*       permrel : PermRel perm; *)
(*       permrel_OrderPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[OrderPerm] l2; *)
(*       permrel_SkipPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[SkipPerm] l2; *)
(*       permrel_ICPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[ICPerm] l2; *)
(*       permrel_MultisetPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[MultisetPerm] l2; *)
(*       permrel_MidPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[MidPerm] l2; *)
(*       permrel_MFPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[MFPerm] l2 *)
(*     }. *)
(* End TOPERMREL. *)

(* Arguments perm_convertible A {_ _}. *)
(* Arguments perm {_ _ _}. *)
(* Arguments permrel {_ _ _}. *)
(* Arguments permrel_OrderPermRel_bij {_ _ _}. *)
(* Arguments permrel_SkipPermRel_bij {_ _ _}. *)
(* Arguments permrel_ICPermRel_bij {_ _ _}. *)
(* Arguments permrel_MultisetPermRel_bij {_ _ _}. *)
(* Arguments permrel_MidPermRel_bij {_ _ _}. *)
(* Arguments permrel_MFPermRel_bij {_ _ _}. *)

(* Section TOPERMREL. *)
(*   Context `{Countable A}. *)
(*   Structure perm_convertible := { *)
(*       perm : list A -> list A -> Type; *)
(*       permrel : PermRel perm; *)
(*       permrel_OrderPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[OrderPerm] l2; *)
(*       permrel_SkipPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[SkipPerm] l2; *)
(*       permrel_ICPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[ICPerm] l2; *)
(*       permrel_MultisetPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[MultisetPerm] l2; *)
(*       permrel_MidPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[MidPerm] l2; *)
(*       permrel_MFPermRel_bij : forall l1 l2, l1 ≡[perm] l2 <-> l1 ≡[MFPerm] l2 *)
(*     }. *)
(* End TOPERMREL. *)

(* Arguments perm_convertible A {_ _}. *)
(* Arguments perm {_ _ _}. *)
(* Arguments permrel {_ _ _}. *)
(* Arguments permrel_OrderPermRel_bij {_ _ _}. *)
(* Arguments permrel_SkipPermRel_bij {_ _ _}. *)
(* Arguments permrel_ICPermRel_bij {_ _ _}. *)
(* Arguments permrel_MultisetPermRel_bij {_ _ _}. *)
(* Arguments permrel_MidPermRel_bij {_ _ _}. *)
(* Arguments permrel_MFPermRel_bij {_ _ _}. *)

Class PermConvertible {A : Type} P `{PermRel A P} := {
    Perm_OrderPerm_inj : forall l1 l2, P l1 l2 -> OrderPerm l1 l2;
    Perm_OrderPerm_surj : forall l1 l2, OrderPerm l1 l2 -> P l1 l2;
    Perm_SkipPerm_inj : forall l1 l2, P l1 l2 -> SkipPerm l1 l2;
    Perm_SkipPerm_surj : forall l1 l2, SkipPerm l1 l2 -> P l1 l2;
    Perm_ICPerm_inj : forall l1 l2, P l1 l2 -> ICPerm l1 l2;
    Perm_ICPerm_surj : forall l1 l2, ICPerm l1 l2 -> P l1 l2;
    Perm_MidPerm_inj : forall l1 l2, P l1 l2 -> MidPerm l1 l2;
    Perm_MidPerm_surj : forall l1 l2, MidPerm l1 l2 -> P l1 l2;
    Perm_MFPerm_inj : forall l1 l2, P l1 l2 -> MFPerm l1 l2;
    Perm_MFPerm_surj : forall l1 l2, MFPerm l1 l2 -> P l1 l2;
    (* Perm_MultisetPerm_inj : forall l1 l2, P l1 l2 -> MultisetPerm l1 l2; *)
    (* MultisetPerm_PermRel_inj : forall l1 l2, MultisetPerm l1 l2 -> P l1 l2; *)
    (* PermRel_OrderPermRel_bij : forall l1 l2, l1 ≡[P] l2 <-> l1 ≡[OrderPerm] l2; *)
    (*   PermRel_SkipPermRel_bij : forall l1 l2, l1 ≡[P] l2 <-> l1 ≡[SkipPerm] l2; *)
    (*   PermRel_ICPermRel_bij : forall l1 l2, l1 ≡[P] l2 <-> l1 ≡[ICPerm] l2; *)
      PermRel_MultisetPermRel_bij : forall l1 l2, l1 ≡[P] l2 <-> l1 ≡[MultisetPerm] l2;
    (*   PermRel_MidPermRel_bij : forall l1 l2, l1 ≡[P] l2 <-> l1 ≡[MidPerm] l2; *)
    (*   PermRel_MFPermRel_bij : forall l1 l2, l1 ≡[P] l2 <-> l1 ≡[MFPerm] l2 *)
  }.

Section Theory.
  Variable A : Type.
  Context `{PermConvertible A P}.
  Ltac convert_order :=
    repeat (match goal with
            | [ H : P ?l1 ?l2 |- _ ] => apply Perm_OrderPerm_inj in H
            | [ |- P ?l1 ?l2 ] => apply Perm_OrderPerm_surj
    end).

  (* Example test : forall l1 l2, l1 ≡[P] l2. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply (promote_rel Perm_OrderPerm_surj). *)
  (*   apply promote_rel, Perm_OrderPerm_surj. *)
  (*   apply (promote_rel Perm_OrderPerm_inj). *)
  (*   apply (promote_rel Perm_OrderPerm_inj) in H2. *)
  (*   unfold_destruct_relH H2. *)


  Ltac convert_skip :=
    repeat (match goal with
            | [ H : P ?l1 ?l2 |- _ ] => apply Perm_SkipPerm_inj in H
            | [ |- P ?l1 ?l2 ] => apply Perm_SkipPerm_surj
    (* | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply PermRel_SkipPermRel_bij in H *)
    (* | [ H : P ?l1 ?l2 |- _ ] => *)
    (*     let H' := fresh H in *)
    (*     assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H *)
    (* | [ |- ?l1 ≡[P] ?l2 ] => apply PermRel_SkipPermRel_bij *)
    end).

  Ltac convert_ic :=
    repeat (match goal with
            | [ H : P ?l1 ?l2 |- _ ] => apply Perm_ICPerm_inj in H
            | [ |- P ?l1 ?l2 ] => apply Perm_ICPerm_surj
    (* | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply PermRel_ICPermRel_bij in H *)
    (* | [ H : P ?l1 ?l2 |- _ ] => *)
    (*     let H' := fresh H in *)
    (*     assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H *)
    (* | [ |- ?l1 ≡[P] ?l2 ] => apply PermRel_ICPermRel_bij *)
    end).

  Ltac convert_multiset :=
    repeat (match goal with
            (* | [ H : P ?l1 ?l2 |- _ ] => apply Perm_MultisetPerm_inj in H *)
            (* | [ |- P ?l1 ?l2 ] => apply SkipPerm_MultisetPerm_surj *)
    | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply PermRel_MultisetPermRel_bij in H
    | [ H : P ?l1 ?l2 |- _ ] =>
        let H' := fresh H in
        assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H
    | [ |- ?l1 ≡[P] ?l2 ] => apply PermRel_MultisetPermRel_bij
    end).

  Ltac convert_mf :=
    repeat (match goal with
            | [ H : P ?l1 ?l2 |- _ ] => apply Perm_MFPerm_inj in H
            | [ |- P ?l1 ?l2 ] => apply Perm_MFPerm_surj
    (* | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply PermRel_MFPermRel_bij in H *)
    (* | [ H : P ?l1 ?l2 |- _ ] => *)
    (*     let H' := fresh H in *)
    (*     assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H *)
    (* | [ |- ?l1 ≡[P] ?l2 ] => apply PermRel_MFPermRel_bij *)
    end).

  Ltac convert_mid :=
    repeat (match goal with
            | [ H : P ?l1 ?l2 |- _ ] => apply Perm_MidPerm_inj in H
            | [ |- P ?l1 ?l2 ] => apply Perm_MidPerm_surj
    (* | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply PermRel_MidPermRel_bij in H *)
    (* | [ H : P ?l1 ?l2 |- _ ] => *)
    (*     let H' := fresh H in *)
    (*     assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H *)
    (* | [ |- ?l1 ≡[P] ?l2 ] => apply PermRel_MidPermRel_bij *)
    end).

  Ltac convert_orderperm :=
    repeat (match goal with
              | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply (promote_rel Perm_OrderPerm_inj) in H
              | [ H : P ?l1 ?l2 |- _ ] =>
                  let H' := fresh H in
                  assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H
              | [ |- ?l1 ≡[P] ?l2 ] => apply (promote_rel Perm_OrderPerm_surj)
            end
      ).

  Ltac convert_skipperm :=
    repeat (match goal with
              | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply (promote_rel Perm_SkipPerm_inj) in H
              | [ H : P ?l1 ?l2 |- _ ] =>
                  let H' := fresh H in
                  assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H
              | [ |- ?l1 ≡[P] ?l2 ] => apply (promote_rel Perm_SkipPerm_surj)
            end
      ).

  Ltac convert_icperm :=
    repeat (match goal with
              | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply (promote_rel Perm_ICPerm_inj) in H
              | [ H : P ?l1 ?l2 |- _ ] =>
                  let H' := fresh H in
                  assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H
              | [ |- ?l1 ≡[P] ?l2 ] => apply (promote_rel Perm_ICPerm_surj)
            end
      ).

  Ltac convert_midperm :=
    repeat (match goal with
              | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply (promote_rel Perm_MidPerm_inj) in H
              | [ H : P ?l1 ?l2 |- _ ] =>
                  let H' := fresh H in
                  assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H
              | [ |- ?l1 ≡[P] ?l2 ] => apply (promote_rel Perm_MidPerm_surj)
            end
      ).

  Ltac convert_mfperm :=
    repeat (match goal with
              | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply (promote_rel Perm_MFPerm_inj) in H
              | [ H : P ?l1 ?l2 |- _ ] =>
                  let H' := fresh H in
                  assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H
              | [ |- ?l1 ≡[P] ?l2 ] => apply (promote_rel Perm_MFPerm_surj)
            end
      ).

  (* Ltac convert_orderperm := *)
  (*   repeat (match goal with *)
  (*             | [ H : ?l1 ≡[P] ?l2 |- _ ] => apply (promote_rel Perm_OrderPerm_inj) in H *)
  (*             | [ H : P ?l1 ?l2 |- _ ] => *)
  (*                 let H' := fresh H in *)
  (*                 assert (H': l1 ≡[P] l2) by (eexists; auto); clear H; rename H' into H *)
  (*             | [ |- ?l1 ≡[P] ?l2 ] => apply (promote_rel Perm_OrderPerm_surj) *)
  (*           end *)
  (*     ). *)

  Lemma Permutation_length : forall l1 l2 (HP : P l1 l2), length l1 = length l2.
  Proof.
    intros.
    convert_ic.
    unfold ICPerm; destruct HP; auto.
  Qed.
  (* HXC: Seems quite clunky. Is there a way to write an Ltac that does some sort of proof search? *)

  Lemma Permutation_reflexive : forall l, P l l.
  Proof.
    intros.
    convert_order.
    constructor.
  Qed.

  Lemma Permutation_symmetric :
    forall (l1 l2: list A)
      (HP : P l1 l2), P l2 l1.
  Proof.
    intros.
    convert_order.
    apply OrderPerm_symmetric; auto.
  Qed.    

  Lemma Permutation_transitive : forall l1 l2 l3 (HP1 : P l1 l2) (HP2 : P l2 l3), P l1 l3.
  Proof.
    intros.
    convert_order.
    eapply orderperm_comp; eauto.
  Qed.

  Lemma Permutation_rel_Reflexive : Reflexive (Permutation_rel P).
  Proof.
    intros.
    unfold Reflexive; intros.
    convert_orderperm.
    apply reflexivity.
  Qed.

  Lemma Permutation_rel_Symmetric : Symmetric (Permutation_rel P).
  Proof.
    intros; unfold Symmetric; intros.
    convert_orderperm.
    apply symmetry; auto.
  Qed.

  Lemma Permutation_rel_Transitive : Transitive (Permutation_rel P).
  Proof.
    intros; unfold Transitive; intros.
    convert_orderperm.
    eapply transitivity; eauto.
  Qed.

  #[local]
    Existing Instance Permutation_rel_Reflexive.

  #[local]
    Existing Instance Permutation_rel_Symmetric.

  #[local]
    Existing Instance Permutation_rel_Transitive.

  Lemma Permuation_Proper : Proper (Permutation_rel P ==> Permutation_rel P ==> iff) (Permutation_rel P).
  Proof.
    repeat red; intros.
    split; intros.
    - apply Permutation_rel_Symmetric in H2.
      apply Permutation_rel_Transitive with x; auto.
      apply Permutation_rel_Transitive with x0; auto.
    - apply Permutation_rel_Symmetric in H3.
      apply Permutation_rel_Transitive with y; auto.
      apply Permutation_rel_Transitive with y0; auto.
  Qed.

  Lemma Permutation_In :
    forall (l1 l2 : list A) (x:A)
      (HP : P l1 l2),
      In x l1 <-> In x l2.
  Proof.  
    intros. 
    convert_order.
    induction HP; split; intros; simpl in *; intuition.
    - apply in_app_or in H2.
      apply in_or_app. intuition.
    - apply in_app_or in H2.
      apply in_or_app. intuition.
  Qed.    

  Lemma Permutation_TIn_inj :
    forall (l1 l2 : list A) (x:A)
      (HP : P l1 l2),
      TIn x l1 -> TIn x l2.
  Proof.  
    intros. 
    convert_order.
    induction HP; simpl in *; intuition.
    apply TIn_app_inj in X. 
    apply TIn_app_surj. intuition.
  Qed.    

  Lemma Permutation_TIn_surj :
    forall (l1 l2 : list A) (x : A)
      (HP : P l1 l2),
      TIn x l2 -> TIn x l1.
  Proof.
    intros.
    apply Permutation_symmetric in HP.
    eapply Permutation_TIn_inj; eauto.
  Qed.

  Lemma Permutation_rel_In :
    forall (l1 l2 : list A) (x:A)
      (HP : l1 ≡[P] l2),
      In x l1 <-> In x l2.
  Proof.
    intros. destruct HP as [HP _].
    apply Permutation_In.
    assumption.
  Qed.

  Lemma Permutation_rel_swap :
    forall x y (l : list A),
      ([y] ++ [x] ++ l) ≡[P] ([x] ++ [y] ++ l).
  Proof.
    intros.
    convert_orderperm.
    constructor; auto. apply orderperm_swap.
  Qed.

  Lemma Permutation_rel_plus :
    forall (l11 l21 l12 l22 : list A),
      (l11 ≡[P] l21) -> (l12 ≡[P] l22) -> (l11 ++ l12) ≡[P] (l21 ++ l22).
  Proof.
    intros.
    convert_orderperm.
    inversion H2. inversion H3.
    constructor; auto. apply orderperm_plus; auto.
  Qed.


  Lemma Permutation_hoist :
    forall (l : list A) (a:A),
      P (l ++ [a])([a] ++ l).
  Proof.
    intros. convert_order. revert a.
    induction l; intros; simpl.
    - apply orderperm_id.
    - eapply orderperm_comp.
      replace (a :: l ++ [a0]) with ([a] ++ (l ++ [a0])) by auto.
      apply orderperm_plus. apply orderperm_id. apply IHl.
      apply orderperm_swap.
  Qed.

  Lemma Permutation_rel_hoist :
    forall (l : list A) (a:A),
      (l ++ [a]) ≡[P] ([a] ++ l).
  Proof.
    intros.
    convert_multiset.
    eexists; permutation_solver.
  Qed.

  Lemma Permutation_exchange :
    forall (l1 l2 : list A),
      P (l1 ++ l2) (l2 ++ l1).
  Proof.
    intros.
    convert_order.
    revert l2.
    induction l1; intros; simpl.
    - rewrite app_nil_r.
      apply orderperm_id.
    - eapply orderperm_comp.
      replace (a:: l1 ++ l2) with ([a] ++ (l1 ++ l2)) by auto.
      apply orderperm_plus. apply orderperm_id. apply IHl1.
      eapply orderperm_comp.
      2: { replace (l2 ++ a :: l1) with ((l2 ++ [a]) ++ l1).
           apply orderperm_plus. apply Perm_OrderPerm_inj. apply Permutation_symmetric. apply Permutation_hoist. apply orderperm_id.
           rewrite <- app_assoc. reflexivity. }
      rewrite <- app_assoc. apply orderperm_id.
  Qed.

  Lemma Permutation_rel_exchange :
    forall (l1 l2 : list A),
      (l1 ++ l2) ≡[P] (l2 ++ l1).
  Proof.
    intros; convert_multiset.
    eexists; permutation_solver.
  Qed.

  Lemma Permutation_nil_inv :
    forall (l : list A),
      P l [] -> l = [].
  Proof.
    intros l HP.
    convert_ic.
    normalize_auxH.
    unfold ICPerm in *. destruct HP.
    destruct l; try discriminate; auto.
  Qed.
  (* HXC: Proof is small now!! *)
    (* convert_order. *)
    (* normalize_auxH. *)
    (* remember [] as s. *)
    (* revert Heqs. *)
    (* induction HP. *)
    (* - intros. reflexivity. *)

    (* - intros. inversion Heqs. *)
    (* - intros. subst. specialize (IHHP2 eq_refl). *)
    (*   subst. apply IHHP1. reflexivity. *)
    (* - intros. apply app_eq_nil in Heqs. *)
    (*   destruct Heqs. *)
    (*   rewrite IHHP1; auto. *)
    (*   rewrite IHHP2; auto. *)

  Lemma Permutation_rel_nil_inv :
    forall (l : list A)
      (HP: l ≡[P] []),
      l = [].
  Proof.
    intros.
    normalize_auxH.
    apply Permutation_nil_inv in HP; auto.
  Qed.

  Lemma Permutation_singleton :
    forall (l : list A) (a :A),
      P l [a] -> l = [a].
  Proof.
    intros l a HP.
    convert_mfperm. symmetry in HP; normalize_auxH.
    inversion HP.
    inversion X.
    destruct l21, l22; try discriminate.
    auto.
  Qed.
  (* HXC: Certainly much shorter than earlier proof *)
    (* remember [a] as s. *)
    (* revert a Heqs. *)
    (* induction HP; intros. *)
    (* - reflexivity. *)
    (* - inversion Heqs. *)
    (* - subst. *)
    (*   rewrite (IHHP2 a eq_refl) in IHHP1. *)
    (*   apply (IHHP1 a eq_refl). *)
    (* - apply app_eq_unit in Heqs. *)
    (*   destruct Heqs as [[H2 H3] | [H2 H3]]. *)
    (*   + subst. rewrite (IHHP2 a eq_refl). *)
    (*     apply Permutation_nil_inv in HP2. rewrite HP2. *)
    (*     reflexivity. *)
    (*   + subst. rewrite (IHHP1 a eq_refl). *)
    (*     apply Permutation_nil_inv in HP3. rewrite HP3. *)
    (*     reflexivity. *)

  Lemma Permutation_rel_singleton :
    forall (l : list A) (a :A)
      (HP: l ≡[P] [a]), l = [a].
  Proof.
    intros l a HP.
    destruct HP as [HP _].
    apply Permutation_singleton in HP.
    assumption.
  Qed.      

  Lemma Permutation_doubleton :
    forall (l : list A) (a1 a2 : A)
      (HP: P l ([a1] ++ [a2])), (l = [a1] ++ [a2]) \/ (l = [a2] ++ [a1]).
  Proof.
    intros.
    convert_mfperm. symmetry in HP. normalize_auxH.
    inversion HP.
    assert (HP2: [a2] ≡[P] (l21 ++ l22)) by (apply (promote_rel Perm_MFPerm_surj); eexists; auto).
    apply Permutation_rel_Symmetric in HP2.
    apply Permutation_rel_singleton in HP2.
    destruct l21.
    - destruct l22; try discriminate.
      destruct l22; try discriminate.
      injection HP2; intros ->.
      intuition.
    - destruct l21; try discriminate.
      destruct l22; try discriminate.
      injection HP2; intros ->.
      intuition.
  Qed.
      

  (*   apply Permutation_singleton in X. *)

  (*   inversion HP; subst. *)
  (*   inversion X. *)



  (*   intros A l a1 a2 HP. *)
  (*   remember ([a1] ++ [a2]) as s. *)
  (*   revert a1 a2 Heqs. *)
  (*   induction HP; intros. *)
  (*   - left. reflexivity. *)
  (*   - inversion Heqs. *)
  (*     subst. *)
  (*     right. reflexivity. *)
  (*   - subst. *)
  (*     destruct (IHHP2 a1 a2 eq_refl). *)
  (*     + destruct (IHHP1 a1 a2 e). *)
  (*       * subst. left. reflexivity. *)
  (*       * subst. right. reflexivity. *)
  (*     + destruct (IHHP1 a2 a1 e). *)
  (*       * subst. right. reflexivity. *)
  (*       * subst. left.  reflexivity. *)
  (*   - destruct l21. *)
  (*     + apply Permutation_nil_inv in HP1. subst. *)
  (*       destruct (IHHP2 _ _ Heqs). *)
  (*       * subst. left. reflexivity. *)
  (*       * subst. right. reflexivity. *)
  (*     + destruct l21. *)
  (*       * inversion Heqs; subst. *)
  (*         apply Permutation_singleton in HP2. *)
  (*         subst. *)
  (*         apply Permutation_singleton in HP1. *)
  (*         subst. *)
  (*         left. reflexivity. *)
  (*       * destruct l21; destruct l22; inversion Heqs; subst. *)
  (*         apply Permutation_nil_inv in HP2. subst. *)
  (*         destruct (IHHP1 _ _ eq_refl); subst. *)
  (*         ++ left. reflexivity. *)
  (*         ++ right. reflexivity. *)
  (* Qed.            *)


  Lemma Permutation_rel_doubleton :
    forall (l : list A) (a1 a2 : A),
      l ≡[P] ([a1] ++ [a2]) -> (l = [a1] ++ [a2]) \/ (l = [a2] ++ [a1]).
  Proof.
    intros l a1 a2 HP.
    destruct HP as [HP _].
    apply Permutation_doubleton in HP.
    destruct HP; intuition.
  Qed.  

  Lemma Permutation_singleton_inv :
    forall (a1 a2 : A)
           (HP : P [a1] [a2]),
      a1 = a2.
  Proof.
    intros.
    apply Permutation_singleton in HP.
    inversion HP.
    reflexivity.
  Qed.  

  Lemma Permutation_rel_singleton_inv :
    forall (a1 a2 : A)
           (HP : [a1] ≡[P] [a2]),
      a1 = a2.
  Proof.
    intros.
    apply Permutation_rel_singleton in HP.
    inversion HP.
    reflexivity.
  Qed.  
  
  Section TAPerm.

    (** Thorsten Altenkirch's Characterization of Permutations - a more "canonical" form 
    that is built on insertion sort.
     *)

    Inductive Add : A -> list A -> list A -> Type :=
    | zero : forall a aS, Add a aS (a :: aS)
    | succ : forall a b aS bs, Add a aS bs -> Add a (b :: aS) (b :: bs).

    Arguments zero {_ _}.
    Arguments succ {_ _ _ _}.

    Lemma Add_app : forall l1 l2 a, Add a (l1 ++ l2) (l1 ++ a :: l2).
    Proof.
      intros l1.
      induction l1; intros.
      - apply zero.
      - simpl. apply succ; auto.
    Qed.

    Lemma Add_app_exists l1 l2 a (HP : Add a l1 l2): exists l11 l12, l1 = l11 ++ l12 /\ l2 = l11 ++ a :: l12.
    Proof.
      intros.
      induction HP.
      - exists [], aS; intuition.
      - destruct IHHP as (l11 & l12 & IHHP1 & IHHP2).
        exists (b :: l11), (l12). subst; intuition.
    Qed.

    Inductive TAPerm : list A -> list A -> Type :=
    | taperm_nil  : TAPerm [] []
    | taperm_cons : forall a aS bs cs, TAPerm aS cs -> Add a cs bs -> TAPerm (a :: aS) bs.

    (* Arguments taperm_cons {_ _ _ _}. *)
    
    #[global]
     Instance PermRel_TAPerm : PermRel TAPerm := {}.

    (* Proof of its equivalence with MFPerm *)

    Lemma MFPerm_TAPerm_inj : forall l1 l2, MFPerm l1 l2 -> TAPerm l1 l2.
    Proof.
      intros.
      induction X.
      - apply taperm_nil.
      - apply taperm_cons with (cs := (l21 ++ l22)); auto.
        apply Add_app.
    Qed.

    Lemma MFPerm_id : forall (l : list A), MFPerm l l.
    Proof.
      intros.
      induction l.
      - apply mfperm_nil.
      - apply mfperm_cons with (l21 := []).
        auto.
    Qed.

    Lemma MFPerm_AddLem : forall a cs bs, Add a cs bs -> MFPerm (a :: cs) bs.
    Proof.
      intros.
      induction X.
      - apply mfperm_cons with (l21 := []).
        apply MFPerm_id.
      - inversion IHX.
        replace (b :: l21 ++ a :: l22) with ((b :: l21) ++ a :: l22) by reflexivity.
        apply mfperm_cons; simpl.
        apply mfperm_cons with (l21 := []).
        auto.
    Qed.

    Lemma TAPermRel_MFPermRel_bij : forall l1 l2, l1 ≡[TAPerm] l2 <-> l1 ≡[MFPerm] l2.
    Proof.
      intros; split; intros.
      - normalize_auxH.
        induction H2.
        + eexists; auto. apply mfperm_nil.
        + apply Add_app_exists in a0.
          destruct a0 as (l11 & l12 & Hcs & Hbs).
          subst.
          normalize_auxH.
          eexists; auto.
          apply mfperm_cons; auto.
      - normalize_auxH.
        apply MFPerm_TAPerm_inj in H2; eexists; auto.
    Qed.

    (* TODO: Declare Canonical Structure here *)
    Fixpoint reflPerm (xs:list A) : TAPerm xs xs :=
      match xs with
      | [] => taperm_nil
      | x::xs => taperm_cons _ _ _ _ (reflPerm xs) zero
      end.

    Lemma addLem : forall {a b aS bs cs} (HA1 : Add a aS bs) (HA2 : Add b bs cs),
        {ds : list A & Add b aS ds * (Add a ds cs)}%type.
    Proof.
      intros.
      revert b cs HA2.
      induction HA1; intros; inversion HA2; subst.
      - exists (b :: aS). split.  apply zero. apply succ. apply zero.
      - eexists. split. apply X. apply zero.
      - eexists. split. apply zero. apply succ. apply succ. apply HA1.
      - specialize (IHHA1 b0 bs0 X).
        destruct IHHA1 as [ds [HP HQ]].
        eexists (b::ds). split. eapply succ. assumption. eapply succ. assumption.
    Qed.      

    Lemma transLem : forall {a bs cs bs'} (HA1 : TAPerm bs cs) (HA2 : Add a bs' bs),
        { cs' : list A & TAPerm bs' cs' * Add a cs' cs}%type.
    Proof.
      intros.
      revert a bs' HA2.
      induction HA1; intros.
      - inversion HA2.
      - remember (a :: aS) as xs.
        revert a aS HA1 a0 IHHA1 Heqxs.
        inversion HA2; intros; inversion Heqxs; subst; clear Heqxs.
        + exists cs. split; auto.
        + destruct (IHHA1 _ _ X) as [cs' [P' Q']].
          destruct (addLem Q' a2) as [ds [Y Z]].
          exists ds. split. eapply taperm_cons; eauto. apply Z.
    Qed.
    
    Lemma transPerm : forall {aS bs cs} (HA1 : TAPerm aS bs) (HA2 : TAPerm bs cs),
        TAPerm aS cs.
    Proof.
      intros aS bs cs HA1 HA2.
      revert cs HA2.
      induction HA1; intros.
      - assumption.
      - destruct (transLem HA2 a0) as [cs' [Q' Y]].
        apply (taperm_cons _ _ _ _ (IHHA1 cs' Q')).
        assumption.
    Qed.    

    Lemma symLem : forall {a aS bs cs} (HA1: TAPerm cs aS) (HA2 : Add a cs bs),
        TAPerm bs (a :: aS).
    Proof.
      intros a aS bs cs HA1 HA2.
      revert aS HA1.
      induction HA2; intros.
      - eapply taperm_cons. apply HA1. apply zero.
      - inversion HA1; subst.
        eapply taperm_cons.
        apply (IHHA2 _ X). apply succ. assumption.
    Qed.    

    Lemma symPerm : forall {aS bs} (HA1 : TAPerm aS bs),
        TAPerm bs aS.
    Proof.
      intros.
      induction HA1.
      - apply taperm_nil.
      - eapply symLem. apply IHHA1. assumption.
    Qed.    

    Lemma remPerm : forall {a aS bs} (HA1 : TAPerm (a::aS) (a::bs)),
        TAPerm aS bs.
    Proof.
      intros.
      inversion HA1; subst.
      inversion X0; subst.
      - assumption.
      - eapply transPerm. apply X.
        eapply taperm_cons. apply reflPerm.
        assumption.
    Qed.

    Lemma swapPerm : forall {a b aS}, (TAPerm (a::b::aS) (b::a::aS)).
    Proof.
      intros.
      eapply taperm_cons.
      2: { eapply succ. eapply zero. }
      apply reflPerm.
    Qed.

    Lemma appendAdd : forall a aS bs cs,
        Add a aS bs -> Add a (aS ++ cs) (bs ++ cs).
    Proof.
      intros a aS bs cs HA.
      revert cs.
      induction HA; intros.
      - apply zero.
      - simpl. apply succ. auto.
    Qed.
    Lemma appendPerm : forall aS bs cs ds,
        TAPerm aS bs -> TAPerm cs ds -> TAPerm (aS++cs) (bs++ds).
    Proof.
      intros aS bs cs ds HA.
      revert cs ds.
      induction HA; intros.
      - simpl. assumption.
      - simpl. eapply taperm_cons.
        apply IHHA. apply X.
        apply appendAdd.
        assumption.
    Qed.

    Lemma OrderPerm_TAPerm_inj : forall xs ys, OrderPerm xs ys -> TAPerm xs ys.
    Proof.
      intros.
      induction X.
      - apply reflPerm.
      - apply swapPerm.
      - eapply transPerm. apply IHX1. apply IHX2.
      - apply appendPerm; auto.
    Qed.

    Lemma OrderPerm_AddLem : forall a cs bs,
        Add a cs bs -> OrderPerm (a::cs) bs.
    Proof.
      intros.
      induction X.
      - apply orderperm_id.
      - eapply orderperm_comp.
        eapply orderperm_swap.
        replace (b :: bs) with ([b] ++ bs) by reflexivity.
        apply orderperm_plus. apply orderperm_id.
        apply IHX.
    Qed.
    
    Lemma OrderPerm_Add : forall a aS bs cs, 
        OrderPerm aS cs -> Add a cs bs -> OrderPerm (a :: aS) bs.
    Proof.
      intros.
      revert a bs X0.
      induction X; intros.
      - apply OrderPerm_AddLem. assumption.
      - apply OrderPerm_AddLem in X0.
        replace (a :: [y] ++ [x] ++ l) with ([a] ++ (y::x::l)) by reflexivity.
        eapply orderperm_comp. eapply orderperm_plus. apply orderperm_id.
        eapply orderperm_swap. assumption.
      - apply IHX2 in X0.
        eapply orderperm_comp. eapply OrderPerm_symmetric.
        replace (a :: l1) with ([a] ++ l1) by reflexivity.
        apply orderperm_plus. apply orderperm_id.
        apply OrderPerm_symmetric. apply X1.
        apply X0.
      - apply OrderPerm_AddLem in X0.
        eapply orderperm_comp.
        2: { apply X0. }
        replace (a :: l11 ++ l12) with ([a] ++ (l11 ++ l12)) by reflexivity.
        replace (a :: l21 ++ l22) with ([a] ++ (l21 ++ l22)) by reflexivity.
        apply orderperm_plus. apply orderperm_id.
        apply orderperm_plus; assumption.
    Qed.


    Lemma TAPerm_OrderPerm_inj : forall aS bs,
        TAPerm aS bs -> OrderPerm aS bs.
    Proof.
      intros.
      induction X.
      - apply orderperm_id.
      - eapply OrderPerm_Add; eauto.
    Qed.    

    Corollary TAPermRel_OrderPermRel_bij : forall aS bs, Permutation_rel TAPerm aS bs <-> Permutation_rel OrderPerm aS bs.
    Proof.
      intros; split; apply promote_rel.
      - apply TAPerm_OrderPerm_inj.
      - apply OrderPerm_TAPerm_inj.
    Qed.

    Ltac try_perm_defs' :=
      (match goal with
      | [ H : OrderPerm ?l1 ?l2 |- _ ] => apply OrderPerm_SkipPerm_inj in H
      | [ H : SkipPerm ?l1 ?l2 |- _ ] => apply SkipPerm_ICPerm_inj in H
      | [ H : ICPerm ?l1 ?l2 |- _ ] => apply ICPerm_MFPerm_inj in H
      | [ H : MFPerm ?l1 ?l2 |- _ ] => apply MFPerm_MidPerm_inj in H
      | [ H : MidPerm ?l1 ?l2 |- _ ] => apply MidPerm_ICPerm_inj, ICPerm_SkipPerm_inj, SkipPerm_OrderPerm_inj in H 
      end); auto.

    Ltac try_perm_defs :=
      do 5 (try try_perm_defs').
    
    #[global]
      Instance PermConvertible_TAPerm : PermConvertible TAPerm.
    Proof.
      split; try apply TAPerm_OrderPerm_inj; try apply OrderPerm_TAPerm_inj; intros; try apply TAPerm_OrderPerm_inj in X; try apply OrderPerm_TAPerm_inj; try_perm_defs; split; intros.
      - apply TAPermRel_OrderPermRel_bij in H2. permutation_solver.
      - apply TAPermRel_OrderPermRel_bij. permutation_solver.
    Defined.
  End TAPerm.

  Lemma Permutation_split :
    forall (a1 a2 : A) (l1 l2 : list A)
           (HP : P ([a1] ++ l1) ([a2] ++ l2)),
      ((a1 = a2) * P l1 l2) +
        { l1' & { l2' &
                    P l1 ([a2] ++ l1') *
                      P l2 ([a1] ++ l2') *
                      P l1' l2'}}%type.
  Proof.
    intros a1 a2 l1. revert a1 a2.
    induction l1.
    - intros. destruct l2.
      + simpl in HP.
        apply Permutation_singleton in HP.
        left. split.
        ++ injection HP; auto.
        ++ apply Perm_OrderPerm_surj. apply orderperm_id.
      + apply Permutation_length in HP.
        simpl in HP. inversion HP.
    - intros.
      apply Perm_OrderPerm_inj in HP.
      apply OrderPerm_TAPerm_inj in HP.
      inversion HP.
      subst.
      inversion X0.
      + subst.
        left. split. reflexivity.
        apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj.
        assumption.
      + subst.
        apply TAPerm_OrderPerm_inj, (@Perm_OrderPerm_surj _ P _ _ _ _) in X, HP.
        (* apply (@Perm_OrderPerm_surj _ P _ _ _) in X. *)

        specialize (IHl1 a a2 aS X).
        destruct IHl1 as [[HEQ HPS] | [l1' [l2' [[HP1 HP2] HP3]]]].
        * subst.
          right.
          exists l1. exists aS.
          split; [split |].
          -- apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj. apply reflPerm.
          -- apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj. apply symPerm. eapply taperm_cons. apply reflPerm. apply X1.
          -- apply HPS.
        * right.
          exists aS. eexists.
          split; [split | ].
          -- apply X.
          -- apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj. apply symPerm. eapply taperm_cons. 2: { apply X1. } apply reflPerm.
          -- apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj. apply reflPerm.
  Qed.
  
  Lemma OrderPerm_split :
    forall (a1 a2 : A) (l1 l2 : list A)
           (HP : OrderPerm ([a1] ++ l1) ([a2] ++ l2)),
      ((a1 = a2) * (OrderPerm l1 l2))%type +
        { l1' & { l2' &
                    (OrderPerm l1 ([a2] ++ l1')) *
                      (OrderPerm l2 ([a1] ++ l2')) *
                      (OrderPerm l1' l2')}}%type.
  Proof.
    intros.
    apply (@Perm_OrderPerm_surj _ P _ _ _ _) in HP.
    apply Permutation_split in HP.
    destruct HP as [[HEQ HPS] | [l1' [l2' [[HP1 HP2] HP3]]]].
    - left. split; auto. apply Perm_OrderPerm_inj in HPS. assumption.
    - right. exists l1'. exists l2'.
      split; [split |]; apply (@Perm_OrderPerm_inj _ P _ _ _ _); assumption.
  Qed.

  Lemma Permutation_split_rel :
    forall (a1 a2 : A) (l1 l2 : list A)
           (HP : ([a1] ++ l1) ≡[P] ([a2] ++ l2)),
      ((a1 = a2) /\ (l1 ≡[P] l2))%type \/
        exists l1'  l2',
          (l1 ≡[P] ([a2] ++ l1')) /\
            (l2 ≡[P] ([a1] ++ l2')) /\
            (l1' ≡[P] l2').
  Proof.
    intros.
    destruct HP as [HP _].
    apply Permutation_split in HP.
    destruct HP as [[EQ HP] | [l1' [l2' [[HP1 HP2] HP3]]]].
    - left. split; auto. econstructor; eauto.
    - right. exists l1', l2'. repeat split; auto.
  Qed.

  Lemma OrderPerm_split_rel :
    forall (a1 a2 : A) (l1 l2 : list A)
           (HP : ([a1] ++ l1) ≡[OrderPerm] ([a2] ++ l2)),
      ((a1 = a2) /\ (l1 ≡[OrderPerm] l2))%type \/
        exists l1'  l2',
          (l1 ≡[OrderPerm] ([a2] ++ l1')) /\
            (l2 ≡[OrderPerm] ([a1] ++ l2')) /\
            (l1' ≡[OrderPerm] l2').
  Proof.
    intros.
    destruct HP as [HP _].
    apply OrderPerm_split in HP.
    destruct HP as [[EQ HP] | [l1' [l2' [[HP1 HP2] HP3]]]].
    - left. split; auto. econstructor; eauto.
    - right. exists l1', l2'. repeat split; auto.
  Qed.

  Lemma Add_inv1:
    forall (a : A) (l1 l2 : list A),
      Add a l1 ([a] ++ l2) -> P l1 l2.
  Proof.
    intros a l1 l2 HA.
    destruct l1.
    - inversion HA. subst. apply Perm_OrderPerm_surj. econstructor.
    - inversion HA; subst.
      + apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj. apply reflPerm.
      + destruct l2.
        * inversion X.
        * apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj. econstructor.
          apply reflPerm.
          apply X.
  Qed.                    



  Lemma AddPermutation :
    forall a (l1 l2 : list A),
      Add a l1 l2 -> P (a::l1) l2.
  Proof.
    intros.
    induction X; subst.
    - apply Permutation_reflexive.
    - eapply Permutation_transitive. convert_order. apply TAPerm_OrderPerm_inj. apply OrderPerm_TAPerm_inj in IHX. apply swapPerm. convert_skip. constructor; assumption.
  Qed.    

  Lemma Permutation_inv1 :
    forall a (l1 l2 : list A)
           (HP: P ([a] ++ l1) ([a] ++ l2)),
      P l1 l2.
  Proof.
    intros a l1 l2 HP.
    apply Perm_OrderPerm_inj, OrderPerm_TAPerm_inj in HP.
    apply Perm_OrderPerm_surj, TAPerm_OrderPerm_inj.
    inversion HP.
    subst.
    apply Add_inv1 in X0.
    apply Perm_OrderPerm_inj, OrderPerm_TAPerm_inj in X0.
    eapply transPerm; eauto.
  Qed.

  Lemma Permutation_destruct1 :
    forall (a : A) (l1 l2 : list A)
           (HP : P (l1 ++ [a]) l2),
      { l2' & (P l2 (l2' ++ [a])) * (P l1 l2')}%type.
  Proof.
    intros.
    apply Perm_OrderPerm_inj in HP.
    assert (OrderPerm ([a] ++ l1) l2).
    { eapply orderperm_comp. apply (@Perm_OrderPerm_surj _ P _ _ _ _) in HP. apply (@Perm_OrderPerm_inj _ P _ _ _ _). apply Permutation_symmetric. eapply Permutation_hoist. assumption. }
    destruct l2.
    - apply (@Perm_OrderPerm_surj _ P _ _ _ _) in X. apply Permutation_nil_inv in X. inversion X.
    - apply (@Perm_OrderPerm_surj _ P _ _ _ _) in HP, X. apply Permutation_split in X.
      destruct X as [[HEQ HP'] | [l11 [l22 [[HP1 HP2] HP3]]]].
      + subst.
        exists l2. split.
        * apply Permutation_symmetric. apply Permutation_hoist.
        * assumption.
      + exists l1. split.
        * apply Permutation_symmetric. assumption.
        * apply Permutation_reflexive.
  Qed. 

  Lemma Permutation_destruct1_rel :
    forall (a : A) (l1 l2 : list A)
           (HP : (l1 ++ [a]) ≡[P] l2),
    exists l2', (l2 ≡[P] (l2' ++ [a])) /\ (l1 ≡[P] l2').
  Proof.
    intros.
    destruct HP as [HP _].
    apply Permutation_destruct1 in HP.
    destruct HP as [l2' [HP1 HP2]].
    exists l2'. split; eexists; auto. 
  Qed.  

  #[global]
    Instance Permuation_Proper_app : Proper (Permutation_rel P ==> Permutation_rel P ==> Permutation_rel P) (app).
  Proof.
    repeat red.
    intros.
    destruct H2 as [H2 _].
    destruct H3 as [H3 _].
    eexists; auto.
    apply Perm_OrderPerm_surj.
    apply Perm_OrderPerm_inj in H2, H3.
    apply orderperm_plus; auto.
  Qed.

  Lemma Permutation_append : ∀ aS bs cs ds : list A, P aS bs → P cs ds → P (aS ++ cs) (bs ++ ds).
  Proof.
    intros.
    convert_order.
    apply orderperm_plus; assumption.
  Qed.

  Lemma Perm_strengthen :
    forall (a : A) (l1 l21 l22 : list A)
           (HP : P ([a] ++ l1) (l21 ++ [a] ++ l22)),
      (P l1 (l21 ++ l22)).
  Proof.
    intros a l1 l21 l22 HP.
    apply (Permutation_inv1 a).
    eapply Permutation_transitive.
    apply HP.
    do 2 rewrite app_assoc.
    apply Permutation_append.
    apply Permutation_hoist.
    apply Permutation_reflexive.
  Qed.  

  Ltac p_inversion :=
    repeat
      match goal with
      | [ H : P ?X ?Y |- _] => is_var X; is_var Y; fail
      | [ H : P ?X ?Y |- _] => is_var X; apply Permutation_symmetric in H
      end.

  Lemma Permutation_destruct2 :
    forall (a1 a2: A) (l1 l2 : list A)
           (HP : P (l1 ++ [a1] ++ [a2]) l2),
      { l2' & (P l2 (l2' ++ [a1] ++ [a2])) * (P l1 l2')}%type.
  Proof.
    intros.
    rewrite app_assoc in HP.
    apply Permutation_destruct1 in HP.
    destruct HP as [l2' [HP1 HP2]].
    apply Permutation_destruct1 in HP2.
    destruct HP2 as [l2'' [HP3 HP4]].
    exists l2''. split.
    rewrite app_assoc.
    - eapply Permutation_transitive. apply HP1. apply Permutation_append. apply HP3.
      apply Permutation_reflexive.
    - assumption.
  Qed.

  Lemma Permutation_destruct2_rel :
    forall (a1 a2: A) (l1 l2 : list A)
           (HP : (l1 ++ [a1] ++ [a2]) ≡[P] l2),
    exists l2' , (l2 ≡[P] (l2' ++ [a1] ++ [a2])) /\ (l1 ≡[P] l2').
  Proof.
    intros.
    destruct HP as [HP _].
    apply Permutation_destruct2 in HP.
    destruct HP as [l2' [HP1 HP2]].
    exists l2'. split; econstructor; eauto.
  Qed.

  Lemma Permutation_cons : forall l1 l2 a, P l1 l2 -> P (a :: l1) (a :: l2).
  Proof.
    intros.
    convert_skip.
    constructor; auto.
  Qed.

  Lemma Permutation_split2 :
    forall (l1 l2 l3 : list A) a
      (HP : P (l1 ++ l2) (l3 ++ [a])),
      {l1' &  P l1 (l1' ++ [a]) * P (l1' ++ l2) l3}%type +
        {l2' & P l2 (l2' ++ [a]) * P (l1 ++ l2') l3}%type.
  Proof.
    intros l1 l2 l3 a.
    revert l2 l3.
    induction l1; intros; simpl in *.
    - right.
      exists l3. split; auto. apply Permutation_reflexive.
    - apply (Permutation_transitive (a0 :: l1 ++ l2) (l3 ++ [a]) ([a] ++ l3)) in HP.
      2: {
        apply Permutation_exchange.
      }
      replace (a0 :: l1 ++ l2) with ([a0] ++ (l1 ++ l2)) in HP by reflexivity.
      apply Permutation_split in HP.
      destruct HP as [[EQ HP] | [l1' [l2' [HP]]]].
      (* destruct HP as [[EQ HP] | [l1' [l2' [HP1 [HP2 HP3]]]]]. *)
      + subst. left. exists l1. split. replace (a :: l1) with ([a] ++ l1) by auto. apply Permutation_exchange. assumption.
      + destruct HP as (HP1 & HP2).
        assert (HP3: P (l1 ++ l2) (l1' ++ [a])).
        { eapply Permutation_transitive.
          - apply HP1.
          - apply Permutation_exchange.
        }
        clear HP1.
        apply IHl1 in HP3.
        replace (a0 :: l1) with ([a0] ++ l1) by reflexivity.
        destruct HP3 as [[l1'' [HPP1 HPP2]] | [l2'' [HPP1 HPP2]]].
        * left.

          (* setoid_rewrite HPP1. *)
          exists ([a0] ++ l1'').
          split.
          -- simpl.
             apply Permutation_cons; assumption.
          -- apply Permutation_symmetric in HP2.
             eapply Permutation_transitive.
             2: {
               apply HP2.
             }
             simpl.
             apply Permutation_cons.
             eapply Permutation_transitive; eassumption.
        * right.
          exists l2''; split; auto.
          apply Permutation_symmetric in HP2.
          eapply Permutation_transitive.
          2: {
            apply HP2.
          }
          simpl.
          apply Permutation_cons.
          eapply Permutation_transitive; eassumption.
  Qed.        
  
  Lemma Permutation_rel_split:
    forall (l1 l2 l3 : list A) a,
      l1 ++ l2 ≡[P] l3 ++ [a] ->
      (exists l1', l1 ≡[P] l1' ++ [a] /\ l1' ++ l2 ≡[P] l3) \/
        (exists l2', l2 ≡[P] l2' ++ [a] /\ l1 ++ l2' ≡[P] l3).
  Proof.
    intros l1 l2 l3 a.
    revert l2 l3.
    induction l1; intros; simpl in *.
    - right.
      exists l3. split.  assumption. reflexivity.
    - rewrite (Permutation_rel_exchange l3 [a]) in H2.
      replace (a0 :: l1 ++ l2) with ([a0] ++ (l1 ++ l2)) in H2 by reflexivity.
      apply Permutation_split_rel in H2.
      destruct H2 as [[EQ HP] | [l1' [l2' [HP1 [HP2 HP3]]]]].
      + subst. left. exists l1. split. rewrite Permutation_rel_exchange. reflexivity.
        apply HP.
      + assert (l1 ++ l2 ≡[P] l1' ++ [a]).
        { rewrite HP1. rewrite Permutation_rel_exchange. reflexivity. }
        clear HP1.
        apply IHl1 in H2.
        replace (a0 :: l1) with ([a0] ++ l1) by reflexivity.
        destruct H2 as [[l1'' [HPP1 HPP2]] | [l2'' [HPP1 HPP2]]].
        * left.
          exists ([a0] ++ l1'').
          split.
          -- rewrite HPP1. reflexivity.
          -- rewrite HP2. rewrite <- HP3.
             rewrite <- app_assoc.
             rewrite <- HPP2. reflexivity.
        * right.
          exists l2''.  split; try assumption.
          rewrite HP2.
          rewrite <- HP3.
          rewrite <- HPP2. reflexivity.
  Qed.        

  Lemma Permutation_strengthen :
    forall (a : A) (l1 l21 l22 : list A)
           (HP : P ([a] ++ l1) (l21 ++ [a] ++ l22)),
      (P l1 (l21 ++ l22)).
  Proof.
    intros a l1 l21 l22 HP.
    eapply Perm_strengthen.
    apply HP.
  Qed.  

  Lemma Permutation_strengthen_rel :
    forall (a : A) (l1 l21 l22 : list A)
           (HP : ([a] ++ l1) ≡[P] (l21 ++ [a] ++ l22)),
      (l1 ≡[P] (l21 ++ l22)).
  Proof.
    intros a l1 l21 l22 HP.
    destruct HP as [HP _].
    econstructor.  eapply Permutation_strengthen.
    apply HP.
    auto.
  Qed.  

  Definition Permutation_remove_ll := Permutation_inv1.

  Lemma Permutation_remove_rel_ll :
    forall (a : A) (l1  l2 : list A)
           (HP : ([a] ++ l1) ≡[P] ([a] ++ l2)),
      (l1 ≡[P] l2).
  Proof.
    intros a l1 l2 HP.
    replace l2 with ([] ++ l2) by reflexivity.
    replace ([a] ++ l2) with ([] ++ [a] ++ l2) in HP by reflexivity.
    eapply Permutation_strengthen_rel.
    apply HP.
  Qed.  

  Lemma Permutation_remove_rr :
    forall (a : A) (l1 l2 : list A)
      (HP : P (l1 ++ [a]) (l2 ++ [a])),
      P l1 l2.
  Proof.
    intros a l1 l2 HP.
    assert (P (l1 ++ [a]) ([a] ++ l2)).
    {
      eapply Permutation_transitive.
      - apply HP.
      - apply Permutation_exchange.
    }
    assert (P ([a] ++ l1) ([a] ++ l2)).
    {
      apply Permutation_symmetric in X.
      apply Permutation_symmetric.
      eapply Permutation_transitive.
      - apply X.
      - apply Permutation_exchange.
    }
    eapply Permutation_remove_ll; eassumption.
  Qed.

  Lemma Permutation_remove_rel_rr :
    forall (a : A) (l1  l2 : list A)
           (HP : (l1 ++ [a]) ≡[P] (l2 ++ [a])),
      (l1 ≡[P] l2).
  Proof.
    intros a l1 l2 HP.
    rewrite (Permutation_rel_exchange l1 [a]) in HP.
    rewrite (Permutation_rel_exchange l2 [a]) in HP.
    eapply Permutation_remove_rel_ll; eauto.
  Qed.  

  Set Equations Transparent.

  Lemma OrderPerm_length : forall (l1 l2 : list A), OrderPerm l1 l2 -> length l1 = length l2.
  Proof.
    intros.
    apply (@Perm_OrderPerm_surj _ P _ _ _ _) in X.
    apply Permutation_length; auto.
  Qed.

  Equations perm_bij (l1 l2 : list A) (p : OrderPerm l1 l2) : bij (length l1) :=
    perm_bij ?(l) ?(l) (orderperm_id l)

    := bij_id (length l)
    ;

    perm_bij ?([y] ++ [x] ++ l) ?([x] ++ [y] ++ l) (orderperm_swap x y l)

    := bij_swap (length l)
    ;

    perm_bij ?(l1) ?(l3) (orderperm_comp l1 l2 l3 q1 q2) with 
      perm_bij l1 l2 q1, perm_bij l2 l3 q2 => {
      | b1, b2 => bij_comp _ b1 (coerce_bij _ _ (OrderPerm_length l1 l2 q1) b2)
      }

    ;
    perm_bij ?(l11 ++ l12) ?(l21 ++ l22) (orderperm_plus l11 l12 l21 l22 q1 q2) 
      with
      perm_bij ?(l11) ?(l21) q1, perm_bij ?(l12) ?(l22) q2 => {
      | b1, b2 => (coerce_bij _ _ _ (bij_plus _ _ b1 b2))
      }
  .
  Next Obligation.
    apply app_length.
  Defined.  

  Arguments perm_bij {_ _ _}.

  Fixpoint split (n m:nat) (l:list A) (L : length l = n + m) :
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

  Lemma coerce_perm {A:Type} (l l1 l2 l3 : list A) (EQ: l1 ++ l2 = l) (p : (l1 ++ l2) ≡ l3) :
    l ≡ l3.
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
           +  destruct (EQP1 i) as [HP HLT]. rewrite Hlen1. assumption.
              eapply Nat.lt_le_trans. eassumption. apply Nat.le_add_r.
           + subst.
             destruct (EQP2 (i - length ?(l))). assert (?(l) = l) by reflexivity. rewrite H0. 
             rewrite H0 in H6. lia.
             assert (length ?(l) = length l) by reflexivity.
             rewrite H7. rewrite H7 in H3.
             apply Nat.add_lt_mono_l. assumption.
      } 
      simpl.
      red. intros.
      destruct (Nat.ltb_spec i (length ?(l))).
      + destruct (EQP1 i). rewrite Hlen1. apply H5.
        destruct (Nat.ltb_spec i n).
        -- split. apply EQP1. assumption. eapply Nat.lt_le_trans.
           apply H7. lia.
        -- subst. assert (i < length l). apply H5. lia.
      +  destruct (Nat.ltb_spec i n).
         -- split. assert (n <= i). rewrite Hlen1. apply H5. lia.
            assert (n = length ?(l)). apply Hlen1. rewrite <- H7.
            apply Nat.add_lt_mono_l.
            apply EQP2. lia.
         -- assert (n = length ?(l)). apply Hlen1. rewrite <- H7.
            split.
            ++ destruct (EQP2 (i -n)) as [HQ HL2].
               lia. rewrite <- HQ. reflexivity.
            ++ apply Nat.add_lt_mono_l. rewrite H0. apply bij_bounds. lia.
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
End Properties.
