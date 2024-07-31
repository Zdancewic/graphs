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

Section Helpers.
  Variable A : Type.
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
End Helpers.

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

Class PermRelLaw {A : Type} `{Countable A}
  (Permutation : list A -> list A -> Type) `{PermRel _ Permutation}
  := {
    Permutation_reflexive :> Reflexive (Permutation_rel Permutation);
    Permutation_symmetric :> Symmetric (Permutation_rel Permutation);
    Permutation_transitive :> Transitive (Permutation_rel Permutation);
    Permutation_proper :>
      Proper
      (Permutation_rel Permutation ==> Permutation_rel Permutation ==> iff)
      (Permutation_rel Permutation)
  }.

Ltac unfold_relH H :=
  unfold Permutation_rel, _Permutation_rel in H
.

Ltac unfold_destruct_relH H :=
  unfold_relH H; destruct H as (H & _).

Ltac unfold_rel :=
  unfold Permutation_rel, _Permutation_rel.

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
          Permutation_reflexive := reflexivity;
          Permutation_symmetric := symmetry;
          Permutation_transitive := transitivity
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

    Theorem OrderPermRel_SkipPermRel_bij : forall l1 l2, (Permutation_rel OrderPerm l1 l2) <-> (Permutation_rel SkipPerm l1 l2).
    Proof.
      intros. split; intros HR; unfold Permutation_rel, _Permutation_rel in *; destruct HR; eexists; auto.
      - apply OrderPerm_SkipPerm_inj; auto.
      - apply SkipPerm_OrderPerm_inj; auto.
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
          Permutation_reflexive := reflexivity;
          Permutation_symmetric := symmetry;
          Permutation_transitive := transitivity
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
    Lemma SkipPermRel_cancel : forall l1 l21 l22 a (HS: Permutation_rel SkipPerm l1 (l21 ++ l22)),
        Permutation_rel SkipPerm (a :: l1) (l21 ++ a :: l22).
    Proof.
      intros.
      remember (l21 ++ l22) as l2.
      revert a l21 l22 Heql2.
      unfold_destruct_relH HS.
      induction HS.
      - intros.
        destruct l21, l22; try discriminate.
        simpl.
        assert (SkipPerm [a] [a]) by (do 2 constructor).
        eexists; auto.
      - intros.
        destruct l21.
        + simpl.
          destruct l22; try discriminate.
          destruct l22; try discriminate.
          injection Heql2; intros.
          rewrite H1, H2 in *.
          do 3 constructor.
          subst; auto.
        + destruct l21.
          ++  
            injection Heql2; intros; subst.
            simpl.
            apply transitivity with (a :: a0 :: x :: l1).
            {
              assert (SkipPerm (a :: x :: a0 :: l1) (a :: a0 :: x :: l1)) by (do 2 constructor; apply SkipPerm_id).
              eexists; auto.
            } 
            do 3 constructor.
            auto.
          ++
            injection Heql2; intros. 
            specialize (IHHS a _ _ H0).
            unfold_destruct_relH IHHS.
             rewrite H1, H2 in *; clear H1 H2.
             simpl.
             apply transitivity with (a1 :: a :: a0 :: l1).
             {
               assert (SkipPerm (a :: a1 :: a0 :: l1) (a1 :: a :: a0 :: l1)) by (do 2 constructor; apply SkipPerm_id).
               eexists; auto.
             }
             apply transitivity with (a1 :: a0 :: a :: l1).
             {
               assert (SkipPerm (a1 :: a :: a0 :: l1) (a1 :: a0 :: a :: l1)) by (do 2 constructor; apply SkipPerm_id).
               eexists; auto.
             }
             assert (SkipPerm (a1 :: a0 :: a :: l1) (a0 :: a1 :: l21 ++ a :: l22)).
             {
               constructor.
               auto.
             }
             eexists; auto.
      - intros.
        destruct l21.
        + simpl.
          destruct l22; try discriminate.
          injection Heql2; intros.
          rewrite H1 in *; clear H1.
          assert (SkipPerm (a :: a0 :: l1) (a :: a0 :: l22)).
          {
            subst.
            do 2 constructor; auto.
          }
          eexists; auto.
        + injection Heql2; intros.
          rewrite H1 in *; clear H1.
          simpl.
          apply transitivity with (y := (a0 :: a :: l1)).
          { 
            assert (SkipPerm (a :: a0 :: l1) (a0 :: a :: l1)) by (constructor; apply SkipPerm_id).
            eexists; auto.
          }
          ++ specialize (IHHS a _ _ H0).
             unfold_destruct_relH IHHS.
             assert (SkipPerm (a0 :: a :: l1) (a0 :: l21 ++ a :: l22)) by (constructor; auto).
             eexists; auto.
      - intros.
        specialize (IHHS2 a _ _ Heql2).
        apply transitivity with (y := (a :: l2)).
        +
          assert (SkipPerm (a :: l1) (a :: l2)) by (constructor; auto).
          eexists; auto.
        + auto.
    Qed.
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

    Lemma occurrence_inv_l : forall l1 l2 x
                               (HO : forall a, occurrence a (x :: l1) = occurrence a l2),
        In x l2.
    Proof.
      intros.
      pose proof (occurrence_cons_eq_neq_0 l1 x) as HO1.
      rewrite HO in HO1.
      apply occurrence_inv_In_non_empty in HO1; auto.
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
    
    Lemma SkipPermRel_ICPermRel_inj : forall l1 l2
                                        (HS : Permutation_rel SkipPerm l1 l2),
        Permutation_rel ICPerm l1 l2.
    Proof.
      intros.
      unfold_destruct_relH HS.
      induction HS.
      - pose proof ICPerm_nil.
        eexists; auto.
      - unfold_destruct_relH IHHS. 
        assert (ICPerm (x :: y :: l1) (y :: x :: l2)) by (apply ICPerm_swap; auto).
        eexists; auto.
      - unfold_destruct_relH IHHS.
        assert (ICPerm (x :: l1) (x :: l2)) by (apply ICPerm_cons; auto).
        eexists; auto.
      - unfold_destruct_relH IHHS1. unfold_destruct_relH IHHS2.
        assert (ICPerm l1 l3) by (eapply ICPerm_trans; eauto).
        eexists; auto.
    Qed.

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


    Lemma ICPermRel_SkipPermRel_inj : forall l1 l2
                                        (HI: Permutation_rel ICPerm l1 l2),
        Permutation_rel SkipPerm l1 l2.
    Proof.
      intros l1.
      induction l1.
      - intros.
        unfold_destruct_relH HI.
        apply ICPerm_inv_nil_l in HI.
        subst.
        assert (SkipPerm [] []) by constructor.
        eexists; auto.
      - intros.
        unfold_destruct_relH HI.
        pose proof HI as HI1.
        apply ICPerm_inv_cons_l, In_app_exists in HI; destruct HI as (l3 & l4 & HI).
        rewrite HI in *.
        apply ICPerm_app_cons_inv in HI1.
        assert (Permutation_rel ICPerm l1 (l3 ++ l4)) by (eexists; auto).
        specialize (IHl1 _ H0).
        apply SkipPermRel_cancel; auto.
    Qed.

    Corollary SkipPermRel_ICPermRel_bij : forall l1 l2,
        Permutation_rel SkipPerm l1 l2 <-> Permutation_rel ICPerm l1 l2.
    Proof.
      intros; split.
      - apply SkipPermRel_ICPermRel_inj.
      - apply ICPermRel_SkipPermRel_inj.
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
          Permutation_reflexive := reflexivity;
          Permutation_symmetric := symmetry;
          Permutation_transitive := transitivity
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

    Theorem MidPermRel_ICPermRel_inj : forall l1 l2
                                         (HP:  Permutation_rel MidPerm l1 l2),
        Permutation_rel ICPerm l1 l2.
    Proof.
      intros.
      unfold_destruct_relH HP.
      induction HP.
      - apply SkipPermRel_ICPermRel_bij.
        pose proof (SkipPerm_id []); eexists; auto.
      - unfold_destruct_relH IHHP.
        unfold ICPerm in IHHP.
        destruct IHHP.
        assert (ICPerm (l11 ++ a :: l12) (l21 ++ a :: l22)).
        {
          unfold ICPerm.
          split.
          - repeat rewrite app_length; cbn.
            repeat rewrite Nat.add_succ_r.
            repeat rewrite <- app_length.
            lia.
          - intros.
            repeat rewrite occurrence_app_iff.
            cbn.
            destruct (decide_rel eq a0 a).
            + repeat rewrite Nat.add_succ_r.
              repeat rewrite <- occurrence_app_iff.
              rewrite H1; lia.
            + repeat rewrite <- occurrence_app_iff.
              rewrite H1; lia.
        }
        eexists; auto.
    Qed.

    Theorem ICPermRel_MidPermRel_inj : forall l1 l2
                                         (HP : Permutation_rel ICPerm l1 l2),
        Permutation_rel MidPerm l1 l2.
    Proof.
      intros l1.
      induction l1.
      - intros.
        unfold_destruct_relH HP.
        apply ICPerm_inv_nil_l in HP; subst.
        assert (MidPerm [] []) by constructor.
        eexists; auto.
      - intros.
        pose proof HP as HP'.
        unfold_destruct_relH HP.
        apply ICPerm_inv_cons_l in HP.
        apply In_app_exists in HP; destruct HP as (l21 & l22 & HP).
        subst.
        assert (HIR: Permutation_rel ICPerm l1 (l21 ++ l22)).
        {
          unfold_destruct_relH HP'.
          apply ICPerm_app_cons_inv in HP'.
          eexists; auto.
        }
        specialize (IHl1 _ HIR); unfold_destruct_relH IHl1.
        assert (MidPerm (a :: l1) (l21 ++ a :: l22)).
        {
          replace (a :: l1) with ([] ++ a :: l1) by auto.
          apply midperm_cons; simpl.
          auto.
        }
        eexists; auto.
    Qed.

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
          Permutation_reflexive := reflexivity;
          Permutation_symmetric := symmetry;
          Permutation_transitive := transitivity
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


    Theorem MFPermRel_MidPermRel_inj : forall l1 l2, Permutation_rel MFPerm l1 l2 -> Permutation_rel MidPerm l1 l2.
      unfold Permutation_rel, _Permutation_rel.
      intros l1 l2 HP; destruct HP as (HP & _).
      apply MFPerm_MidPerm_inj in HP.
      eexists; auto.
    Qed.

    Lemma MFPermRel_ICPermRel_inj : forall l1 l2
                                      (HP: Permutation_rel MFPerm l1 l2),
        Permutation_rel ICPerm l1 l2.
    Proof.
      intros.
      unfold_destruct_relH HP.
      induction HP.
      - reflexivity.
      - unfold_destruct_relH IHHP.
        assert (ICPerm (a :: l1) (l21 ++ a :: l22)).
        {
          apply ICPerm_app_cons; auto.
        }
        eexists; auto.
    Qed.

    Lemma ICPermRel_MFPermRel_inj : forall l1 l2
                                      (HI : Permutation_rel ICPerm l1 l2),
        Permutation_rel MFPerm l1 l2.
    Proof.
      intros l1. induction l1.
      - intros.
        unfold_destruct_relH HI.
        apply ICPerm_inv_nil_l in HI; subst.
        assert (MFPerm [] []) by auto.
        eexists; auto.
      - intros.
        pose proof HI as HI'.
        unfold_destruct_relH HI.
        apply ICPerm_inv_cons_l, In_app_exists in HI as (l21 & l22 & HI); subst.
        assert (HIR : Permutation_rel ICPerm l1 (l21 ++ l22)).
        {
          unfold_destruct_relH HI'.
          apply ICPerm_app_cons_inv in HI'.
          eexists; auto.
        }
        specialize (IHl1 _ HIR); unfold_destruct_relH IHl1.
        assert (MFPerm (a :: l1) (l21 ++ a :: l22)) by (constructor; auto).
        eexists; auto.
    Qed.

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
          Permutation_reflexive := reflexivity;
          Permutation_symmetric := symmetry;
          Permutation_transitive := transitivity
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
      intros.
      unfold_destruct_relH HS.
      apply SkipPerm_MultisetPerm_inj in HS.
      eexists; auto.
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
          Permutation_reflexive := reflexivity;
          Permutation_symmetric := symmetry;
          Permutation_transitive := transitivity
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
  match goal with
  | [ H : Permutation_rel ?P ?l1 ?l2 |- _ ] =>
      unfold_destruct_relH H
  end.

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
  repeat normalize_auxH;
  try transform_to_multisetpermrel
.

Ltac permutation_solver :=
  permutation_solver'; multiset_solver_plus.

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
