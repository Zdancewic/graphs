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
      (* Lemma Permutation_rel_Reflexive : forall {A : Type}, Reflexive (@Permutation_rel). *)
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

    (* Lemma SkipPerm_head : forall (l11 l12 l2 : list A), SkipPerm l11 l12 -> SkipPerm (l11 ++ l2) (l12 ++ l2). *)
    (* Proof. *)
    (*   intros l11 l12 l2 HS1. revert l2. *)
    (*   induction HS1; intros; simpl; auto. *)
    (*   - induction l2; auto. *)
    (*   - eapply sp_trans; eauto. *)
    (* Qed. *)

    (* Lemma SkipPerm_tail : forall (l1 l21 l22 : list A), SkipPerm l21 l22 -> SkipPerm (l1 ++ l21) (l1 ++ l22). *)
    (* Proof. *)
    (*   intros l1. *)
    (*   induction l1; intros; simpl; auto. *)
    (* Qed. *)

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
      (* Lemma Permutation_rel_Reflexive : forall {A : Type}, Reflexive (@Permutation_rel). *)

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
  End SkipPerm.

  Section MidPerm.
    Inductive MidPerm : list A -> list A -> Type :=
    | midperm_nil : MidPerm [] []
    | midperm_cons : forall a l11 l12 l21 l22, MidPerm (l11 ++ l21) (l12 ++ l22) -> MidPerm (l11 ++ a :: l21) (l12 ++ a :: l22).
    Hint Constructors MidPerm.

    #[global]
     Instance PermRel_MidPerm : PermRel MidPerm := {}.



    Lemma In_cons_iff : forall (a a0 : A) (l : list A),
        In a (a0 :: l) <-> a = a0 \/ In a l.
    Proof.
      intros; split; intros.
      - cbv in H0. destruct H0 as [H0 | H0]; auto.
      - destruct H0; subst; auto.
        + apply in_eq.
        + apply in_cons; auto.
    Qed.

    Lemma In_app_exists : forall (a : A) (l : list A), In a l <-> exists l1 l2, l = l1 ++ a :: l2.
    Proof.
      intros; split; intros.
      - induction l.
        + apply in_nil in H0; destruct H0.
        + apply In_cons_iff in H0.
          destruct H0.
          ++ exists [], l. subst; auto.
          ++ apply IHl in H0 as (l1 & l2 & HL).
             exists (a0 :: l1), l2; subst; auto.
      - destruct H0 as (l1 & l2 & H0).
        subst.
        apply in_app_iff; right.
        apply In_cons_iff; left; reflexivity.
    Qed.

    Lemma In_app_cons_or : forall (a a0: A) (l1 l2 : list A), In a (l1 ++ a0 :: l2) <-> a = a0 \/ In a (l1 ++ l2).
    Proof.
      intros; split; intros.
      - rewrite in_app_iff in *; rewrite In_cons_iff in *; repeat destruct H0; auto.
      - rewrite in_app_iff in *; repeat destruct H0; rewrite In_cons_iff; auto.
    Qed.

    Lemma app_cons_inj : forall a (l11 l12 l21 l22 : list A),
        l11 ++ a :: l12 = l21 ++ a :: l22 -> l11 ++ l12 = l21 ++ l22.
    Proof.
    Admitted.

    Lemma list_eq_app_cons : forall (a a0 : A) (l11 l12 l21 l22 : list A),
        l11 ++ a :: l12 = l21 ++ a0 :: l22 -> exists l3 l4, a = a0 \/ l21 = l3 ++ a :: l4 \/ l22 = l3 ++ a :: l4.
    Admitted.

    Lemma MidPerm_cons_in : forall (a : A) (l11 l12 l2 : list A),
        MidPerm (l11 ++ a :: l12) l2 -> In a l2.
    Proof.
      intros a l11 l12 l2 HM.
      remember (l11 ++ a :: l12) as l1.
      revert l11 l12 a Heql1.
      induction HM.
      - induction l11; discriminate.
      - intros.
        rewrite In_app_cons_or.
        pose proof Heql1 as HL.
        apply list_eq_app_cons in Heql1.
        destruct Heql1 as (l3 & l4 & Heql1).
        destruct Heql1.
        {
          destruct (decide_rel eq a a0); auto.
        }
        right.
        destruct H0; rewrite H0 in HL. 
        + rewrite <- app_assoc in HL.
          replace ((a :: l4) ++ a0 :: l1) with (a :: (l4 ++ a0 :: l1)) in HL by auto.
          apply app_cons_inj in HL.
          apply (IHHM (l3 ++ l4) l1 a0).
          rewrite <- app_assoc; auto.
        + replace (l0 ++ a0 :: l3 ++ a :: l4) with ((l0 ++ a0 :: l3) ++ a :: l4) in HL.
          ++ apply (app_cons_inj a l11 l21 (l0 ++ a0 :: l3) l4) in HL.
             rewrite <- app_assoc in HL.
             replace ((a0 :: l3) ++ l4) with (a0 :: (l3 ++ l4)) in HL by auto.
             apply (IHHM l0 (l3 ++ l4)); auto.
          ++ rewrite <- app_assoc.
             replace ((a0 :: l3) ++ a :: l4) with (a0 :: (l3 ++ a :: l4)) by auto.
             auto.
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

    Lemma MidPermRel_inv : forall (l11 l12 l21 l22 : list A) (a : A), Permutation_rel MidPerm (l11 ++ a :: l12) (l21 ++ a :: l22) -> Permutation_rel MidPerm (l11 ++ l12) (l21 ++ l22).
    Proof.
      intros.
      remember (l11 ++ a :: l12) as l1.
      remember (l21 ++ a :: l22) as l2.
      revert a l11 l12 l21 l22 Heql1 Heql2.
      unfold_destruct_relH H0.
      induction H0.
      - intros.
        induction l11; discriminate.
      - intros.
        pose proof Heql1 as HL1.
        apply list_eq_app_cons in HL1; destruct HL1 as (l31 & l32 & HL1). destruct HL1 as [HL1 | [HL1 | HL1]].
        (* This looks really painful. 8 cases for three of the little ones *)
        + rewrite HL1 in *. apply app_cons_inj in Heql1, Heql2.
          destruct l0, l1.
          ++ destruct l2, l3; try (rewrite Heql1, Heql2 in H0; inversion H0; induction l0; discriminate).
             assert (MidPerm ([] ++ []) ([] ++ [])) by auto.
             eexists; auto.
          ++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             +++
               induction l2; discriminate.
             +++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l0 l4 l2 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a3 :: l4) (l2 ++ a3 :: l5)) by auto.
               eexists; eauto.
             +++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l0 l4 l3 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a3 :: l4) (l3 ++ a3 :: l5)) by auto.
               eexists; eauto.
             +++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l0 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
          ++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             +++ induction l2; discriminate.
             +++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l1 l4 l2 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a3 :: l4) (l2 ++ a3 :: l5)) by auto.
               eexists; eauto.
             +++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l1 l4 l3 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a3 :: l4) (l3 ++ a3 :: l5)) by auto.
               eexists; eauto.
             +++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l1 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
          ++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             +++ induction l3; discriminate.
             +++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l2 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l2 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
             +++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l3 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l3 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
             +++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a5 l4 l6 l5 l7 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l4 ++ a5 :: l6) (l5 ++ a5 :: l7)) by auto.
               eexists; eauto.
        + pose proof Heql2 as HL2.
          apply list_eq_app_cons in HL2; destruct HL2 as (l41 & l42 & HL2). destruct HL2 as [HL2 | [HL2 | HL2]].
          ++ 
            rewrite HL2 in *. apply app_cons_inj in Heql1, Heql2.
            destruct l0, l1.
            +++ destruct l2, l3; try (rewrite Heql1, Heql2 in H0; inversion H0; induction l0; discriminate).
             assert (MidPerm ([] ++ []) ([] ++ [])) by auto.
             eexists; auto.
            +++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             ++++
               induction l2; discriminate.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l0 l4 l2 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a3 :: l4) (l2 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l0 l4 l3 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a3 :: l4) (l3 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l0 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
          +++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             ++++ induction l2; discriminate.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l1 l4 l2 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a3 :: l4) (l2 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l1 l4 l3 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a3 :: l4) (l3 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l1 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
          +++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             ++++ induction l3; discriminate.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l2 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l2 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
             ++++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l3 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l3 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a5 l4 l6 l5 l7 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l4 ++ a5 :: l6) (l5 ++ a5 :: l7)) by auto.
               eexists; eauto.
          ++ subst.
             assert (HRE1 : forall l, (l31 ++ a :: l32) ++ l = l31 ++ a :: (l32 ++ l)) by (intros; rewrite <- app_assoc; auto).
             assert (HRE2 : forall l, (l41 ++ a :: l42) ++ l = l41 ++ a :: (l42 ++ l)) by (intros; rewrite <- app_assoc; auto).
             rewrite HRE1, HRE2 in *; clear HRE1 HRE2.
             apply app_cons_inj in Heql1, Heql2.
             assert (HRE1 : forall l, (l31 ++ l32 ++ l) = (l31 ++ l32) ++ l) by (intros; rewrite <- app_assoc; auto).
             assert (HRE2 : forall l, (l41 ++ l42 ++ l) = (l41 ++ l42) ++ l) by (intros; rewrite <- app_assoc; auto).
             rewrite HRE1, HRE2 in *.
             specialize (IHMidPerm a0 (l31 ++ l32) l1 (l41 ++ l42) l3 Heql1 Heql2); unfold_destruct_relH IHMidPerm.
             rewrite <- HRE1, <- HRE2 in *.
             assert (MidPerm (l31 ++ a :: l32 ++ l1) (l41 ++ a :: l42 ++ l3)) by auto.
             eexists; auto.
          ++ subst.
             assert (HRE1 : forall l, (l31 ++ a :: l32) ++ l = l31 ++ a :: (l32 ++ l)) by (intros; rewrite <- app_assoc; auto).
             assert (HRE2 : forall l, l2 ++ a0 :: l ++ a :: l42 = (l2 ++ a0 :: l) ++ a :: l42) by (intros; rewrite <- app_assoc; auto).
             rewrite HRE1, HRE2 in *; clear HRE1 HRE2.
             apply app_cons_inj in Heql1, Heql2.
             assert (HRE1 : forall l, l31 ++ l32 ++ l = (l31 ++ l32) ++ l) by (intros; rewrite <- app_assoc; auto).
             assert (HRE2 : forall l, (l2 ++ l) ++ l42 = l2 ++ l ++ l42) by (intros; rewrite <- app_assoc; auto).
             rewrite HRE1, HRE2 in *; simpl in *.
             specialize (IHMidPerm a0 _ _ _ _ Heql1 Heql2); unfold_destruct_relH IHMidPerm.
             rewrite <- HRE1, <- HRE2 in *.
             assert (MidPerm (l31 ++ a :: l32 ++ l1) (l2 ++ l41 ++ a :: l42)).
             {
               replace (l2 ++ l41 ++ a :: l42) with ((l2 ++ l41) ++ a :: l42) by (rewrite app_assoc; auto).
               auto.
             }
             eexists; auto.
        + pose proof Heql2 as HL2.
          apply list_eq_app_cons in HL2; destruct HL2 as (l41 & l42 & HL2). destruct HL2 as [HL2 | [HL2 | HL2]].
          ++
            rewrite HL2 in *. apply app_cons_inj in Heql1, Heql2.
            destruct l0, l1.
            +++ destruct l2, l3; try (rewrite Heql1, Heql2 in H0; inversion H0; induction l0; discriminate).
             assert (MidPerm ([] ++ []) ([] ++ [])) by auto.
             eexists; auto.
            +++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             ++++
               induction l2; discriminate.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l0 l4 l2 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a3 :: l4) (l2 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l0 l4 l3 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a3 :: l4) (l3 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l0 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l0 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
          +++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             ++++ induction l2; discriminate.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l1 l4 l2 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a3 :: l4) (l2 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a3 l1 l4 l3 l5 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a3 :: l4) (l3 ++ a3 :: l5)) by auto.
               eexists; eauto.
             ++++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l1 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l1 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
          +++ destruct l2, l3; rewrite Heql1, Heql2 in *; simpl in *; inversion H0.
             ++++ induction l3; discriminate.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l2 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l2 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
             ++++ 
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a4 l3 l5 l4 l6 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l3 ++ a4 :: l5) (l4 ++ a4 :: l6)) by auto.
               eexists; eauto.
             ++++
               symmetry in H2; symmetry in H3.
               specialize (IHMidPerm a5 l4 l6 l5 l7 H2 H3).
               unfold_destruct_relH IHMidPerm.
               assert (MidPerm (l4 ++ a5 :: l6) (l5 ++ a5 :: l7)) by auto.
               eexists; eauto.
          ++ subst.
             assert (HRE1 : forall l, l0 ++ a0 :: l ++ a :: l32 = (l0 ++ a0 :: l) ++ a :: l32) by (intros; rewrite <- app_assoc; auto).
             assert (HRE2 : forall l, (l41 ++ a :: l42) ++ l = l41 ++ a :: (l42 ++ l)) by (intros; rewrite <- app_assoc; auto).
             rewrite HRE1, HRE2 in *; clear HRE1 HRE2.
             apply app_cons_inj in Heql1, Heql2.
             assert (HRE2 : forall l, l41 ++ l42 ++ l = (l41 ++ l42) ++ l) by (intros; rewrite <- app_assoc; auto).
             assert (HRE1 : forall l, (l0 ++ l) ++ l32 = l0 ++ l ++ l32) by (intros; rewrite <- app_assoc; auto).
             rewrite HRE1, HRE2 in *; simpl in *.
             specialize (IHMidPerm a0 _ _ _ _ Heql1 Heql2); unfold_destruct_relH IHMidPerm.
             rewrite <- HRE1, <- HRE2 in *.
             assert (MidPerm (l0 ++ l31 ++ a :: l32) (l41 ++ a :: l42 ++ l3)).
             {
               replace (l0 ++ l31 ++ a :: l32) with ((l0 ++ l31) ++ a :: l32) by (rewrite app_assoc; auto).
               auto.
             }
             eexists; auto.
          ++ subst.
             assert (HRE : forall l1 l2 l3, l1 ++ a0 :: l2 ++ a :: l3 = (l1 ++ a0 :: l2) ++ a :: l3) by (intros; rewrite <- app_assoc; auto).
             rewrite HRE in *; clear HRE.
             apply app_cons_inj in Heql1, Heql2.
             rewrite <- app_assoc in Heql1, Heql2; simpl in *.
             specialize (IHMidPerm a0 _ _ _ _ Heql1 Heql2); unfold_destruct_relH IHMidPerm.
             assert (MidPerm (l0 ++ l31 ++ a :: l32) (l2 ++ l41 ++ a :: l42)).
             {
             replace (l0 ++ l31 ++ a :: l32) with ((l0 ++ l31) ++ a :: l32) by (rewrite <- app_assoc; auto).
             replace (l2 ++ l41 ++ a :: l42) with ((l2 ++ l41) ++ a :: l42) by (rewrite <- app_assoc; auto).
             apply midperm_cons.
             do 2 rewrite <- app_assoc; auto.
             }
             eexists; auto.
    Qed.

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
      - auto.
      - replace (a :: l1) with ([] ++ a :: l1) by auto.
        apply midperm_cons; auto.
    Qed.

    Theorem MFPermRel_MidPermRel_inj : forall l1 l2, Permutation_rel MFPerm l1 l2 -> Permutation_rel MidPerm l1 l2.
      unfold Permutation_rel, _Permutation_rel.
      intros l1 l2 HP; destruct HP as (HP & _).
      apply MFPerm_MidPerm_inj in HP.
      eexists; auto.
    Qed.


    Lemma MidPermRel_MFPermRel_inj : forall l1 l2, Permutation_rel MidPerm l1 l2 -> Permutation_rel MFPerm l1 l2.
    Proof.
      intros l1. induction l1.
      - intros.
        unfold_destruct_relH H0.
        inversion H0.
        ++ subst.
           assert (MFPerm [] []) by auto; eexists; auto.
        ++ induction l11; discriminate.
      - intros.
        pose proof H0 as X.
        unfold_destruct_relH H0.
        apply MidPerm_cons_in' in H0.
        apply In_app_exists in H0. destruct H0 as (l3 & l4 & H0).
        subst.
        unfold_destruct_relH X.
        replace (a :: l1) with ([] ++ a :: l1) in X by auto.
        assert (HP : Permutation_rel MidPerm ([] ++ a :: l1) (l3 ++ a :: l4)) by (eexists; auto).
        apply MidPermRel_inv in HP; simpl in HP.
        specialize (IHl1 _ HP); unfold_destruct_relH IHl1.
        assert (MFPerm (a :: l1) (l3 ++ a :: l4)) by auto.
        eexists; auto.
    Qed.

    Theorem MidPermRel_MFPermRel_bij : forall l1 l2, Permutation_rel MidPerm l1 l2 <-> Permutation_rel MFPerm l1 l2.
    Proof.
      intros; split.
      - apply MidPermRel_MFPermRel_inj.
      - apply MFPermRel_MidPermRel_inj.
    Qed.

    Lemma MFPermRel_trans : forall (l1 l2 l3 : list A)
                              (HP1: Permutation_rel MFPerm l1 l2)
                              (HP2: Permutation_rel MFPerm l2 l3), Permutation_rel MFPerm l1 l3.
    Proof.
      intros l1.
      induction l1.
      - intros.
        unfold_destruct_relH HP1; inversion HP1; subst.
        unfold_destruct_relH HP2; inversion HP2; subst.
        eexists; auto.
      - intros.
        unfold_destruct_relH HP1.
        inversion HP1; subst.
        pose proof HP2 as HP2'.
        apply MidPermRel_MFPermRel_bij in HP2.
        unfold_destruct_relH HP2.
        apply MidPerm_cons_in in HP2.
        apply In_app_exists in HP2; destruct HP2 as (l4 & l5 & HP2); subst.
        apply MidPermRel_MFPermRel_bij in HP2'.
        apply MidPermRel_inv in HP2'.
        apply MidPermRel_MFPermRel_bij in HP2'.
        assert (HP1' : Permutation_rel MFPerm l1 (l21 ++ l22)) by (eexists; auto).
        specialize (IHl1 _ _ HP1' HP2'); unfold_destruct_relH IHl1.
        assert (MFPerm (a :: l1) (l4 ++ a :: l5)) by auto.
        eexists; auto.
    Qed.

    (* HXC: Another proof for transitivity, though it is easier to prove transitivity by doing a bijection on MFPerm *)
    Lemma MidPermRel_trans : forall (l1 l2 l3 : list A), Permutation_rel MidPerm l1 l2 -> Permutation_rel MidPerm l2 l3 -> Permutation_rel MidPerm l1 l3.
    Proof.
      intros l1.
      unfold Permutation_rel, _Permutation_rel.
      induction l1.
      - intros. destruct H0 as (H0 & _); destruct H1 as (H1 & _).
        inversion H0; subst; inversion H1; subst.
        + assert (MidPerm [] []) by auto; eexists; auto.
        + induction l11; discriminate.
        + induction l12; discriminate.
        + induction l11; discriminate.
      - intros. destruct H0 as (H0 & _); destruct H1 as (H1 & _).
        pose proof H0 as HL1.
        apply MidPerm_cons_in' in HL1.
        apply In_app_exists in HL1. destruct HL1 as (l4 & l5 & HL1).
        subst.
        pose proof H1 as HL2.
        apply MidPerm_cons_in in HL2.
        apply In_app_exists in HL2. destruct HL2 as (l6 & l7 & HL2).
        subst.
        assert (HP2: Permutation_rel MidPerm (l4 ++ a :: l5) (l6 ++ a :: l7)).
        {
          unfold Permutation_rel, _Permutation_rel; eexists; auto.
        }
        replace (a :: l1) with ([] ++ a :: l1) in H0 by auto.
        assert (HP1 : Permutation_rel MidPerm ([] ++ a :: l1) (l4 ++ a :: l5)).
        {
          unfold Permutation_rel, _Permutation_rel; eexists; auto.
        }
        apply MidPermRel_inv in HP1; simpl in HP1.
        apply MidPermRel_inv in HP2.
        specialize (IHl1 _ _ HP1 HP2).
        destruct IHl1 as (IHl1 & _).
        assert (MidPerm (a :: l1) (l6 ++ a :: l7)).
        {
          replace (a :: l1) with ([] ++ a :: l1) by auto.
          apply midperm_cons; auto.
        }
        eexists; auto.
    Qed.
    
    Theorem SkipPermRel_MidPermRel_inj : forall (l1 l2 : list A), Permutation_rel SkipPerm l1 l2 -> Permutation_rel MidPerm l1 l2.
      intros. unfold Permutation_rel, _Permutation_rel in *.
      destruct H0 as (H0 & _).
      induction H0; auto.
      - eexists; auto.
      - destruct IHSkipPerm as (IHSkipPerm & _).
        assert (MidPerm (x :: y :: l1) (y :: x :: l2)).
        {
        replace (x :: y :: l1) with ([] ++ x :: (y :: l1)) by auto.
        replace (y :: x :: l2) with ([y] ++ x :: l2) by auto.
        apply midperm_cons.
        replace ([y] ++ l2) with ([] ++ y :: l2) by auto.
        apply midperm_cons; auto.
        }
        exists X; auto.
      - destruct IHSkipPerm as (IHSkipPerm & _).
        assert (MidPerm (x :: l1) (x :: l2)).
        {
         replace (x :: l1) with ([] ++ x :: l1) by auto.
         replace (x :: l2) with ([] ++ x :: l2) by auto.
         apply midperm_cons; auto.
        }
        exists X; auto.
      - eapply MidPermRel_trans; eauto.
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

    Theorem MidPermRel_SkipPermRel_inj : forall (l1 l2 : list A)
                                       (HP : Permutation_rel MidPerm l1 l2),
        Permutation_rel SkipPerm l1 l2.
    Proof.
      intros l1; induction l1.
      - intros.
        unfold_destruct_relH HP.
        inversion HP; subst.
        + assert (SkipPerm [] []) by constructor.
          eexists; auto.
        + induction l11; discriminate.
      - intros.
        pose proof HP as HP'.
        unfold_destruct_relH HP.
        apply MidPerm_cons_in' in HP.
        apply In_app_exists in HP; destruct HP as (l3 & l4 & HP); rewrite HP in HP'.
        replace (a :: l1) with ([] ++ a :: l1) in HP' by auto.
        apply MidPermRel_inv  in HP'; simpl in HP'.
        specialize (IHl1 _ HP'); unfold_destruct_relH IHl1.
        assert (HS : SkipPerm (a :: l1) (l2)).
        {
          
          assert (HS1 : SkipPerm (a :: l1) (a :: l3 ++ l4)).
          {
            apply skipperm_skip. auto.
          }
          apply (skipperm_trans _ _ _ HS1).
          subst. apply SkipPerm_In_weak; auto.
        }
        eexists; auto.
    Qed.

    Theorem MidPermRel_SkipPermRel_bij : forall (l1 l2 : list A), Permutation_rel MidPerm l1 l2 <-> Permutation_rel SkipPerm l1 l2.
    Proof.
      intros; split.
      - apply MidPermRel_SkipPermRel_inj.
      - apply SkipPermRel_MidPermRel_inj.
    Qed.

    

  End MidPerm.
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
      
    (* Theorem OrderPerm_MultisetPerm_inj : forall (l1 l2 : list A), OrderPerm l1 l2 -> MultisetPerm l1 l2. *)
    (* Proof. *)
    (*   intros l1 l2 HO. *)
    (*   induction HO; unfold MultisetPerm in *; auto; try multiset_solver. *)
    (*   do 2 rewrite list_to_set_disj_app. *)
    (*   rewrite IHHO1, IHHO2; reflexivity. *)
    (* Qed. *)

   Lemma list_to_set_disj_nil_iff : forall (l : list A), list_to_set_disj l =@{gmultiset A} ∅ <-> l = [].
    Proof.
      induction l; split; auto; intros.
      - simpl in *.
        multiset_solver.
      - discriminate.
    Qed.

    Theorem MultisetPerm_SkipPerm_inj : forall (l1 l2 : list A), MultisetPerm l1 l2 -> SkipPerm l1 l2.
    Proof.
      unfold MultisetPerm.
      intros l1.
      assert (HE : list_to_set_disj [] =@{gmultiset A} ∅) by auto.
      induction l1; intros l2 HM.
      - destruct l2; try constructor; unfold MultisetPerm in *.
        rewrite HE in HM; clear HE.
        symmetry in HM; apply list_to_set_disj_nil_iff in HM. discriminate.
      - destruct l2; try constructor; unfold MultisetPerm in *.
        {rewrite HE in HM; clear HE.
          apply list_to_set_disj_nil_iff in HM; discriminate. }
        destruct (decide_rel eq a a0).
        {subst.
          apply skipperm_skip.
          simpl in HM.
          eapply (@inj _ _ eq) in HM; auto.
          apply gmultiset_disj_union_inj_1. }
        clear HE.
        revert a a0 n l2 HM IHl1.
        induction l1; intros; destruct l2; simpl in *.
        + do 2 rewrite right_id in HM; try (unfold RightId; intros; symmetry; apply gmultiset_disj_union_right_id).
          apply gmultiset_singleton_inj in HM; tauto.
        + admit.
        + admit.
        + 
    Admitted.

    Theorem SkipPermRel_MultisetPermRel_bij : forall l1 l2, (Permutation_rel SkipPerm l1 l2) <-> (Permutation_rel MultisetPerm l1 l2).
    Proof.
      intros. split; intros HR; unfold Permutation_rel, _Permutation_rel in *; destruct HR; eexists; auto.
      - apply SkipPerm_MultisetPerm_inj; auto.
      - apply MultisetPerm_SkipPerm_inj; auto.
    Qed.

    Section MultisetPermLaws.
      (* Lemma Permutation_rel_Reflexive : forall {A : Type}, Reflexive (@Permutation_rel). *)

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
  End MultisetPerm.
  
End Permutation_Instances.
