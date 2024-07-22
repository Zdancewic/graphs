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
  End SkipPerm.

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
        destruct l1, l2; simpl in *.
        + do 2 rewrite right_id in HM; try (unfold RightId; intros; symmetry; apply gmultiset_disj_union_right_id).
          apply gmultiset_singleton_inj in HM; tauto.
        + rewrite right_id in HM; try (unfold RightId; intros; symmetry; apply gmultiset_disj_union_right_id).
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

    

    

  (*   Theorem OrderPerm_MultisetPerm_surj : forall (l1 l2 : list A), MultisetPerm l1 l2 -> OrderPerm l1 l2. *)
  (*   Proof. *)
  (*     intros l1. *)
  (*     assert (HE : list_to_set_disj [] =@{gmultiset A} ∅) by auto. *)
  (*     induction l1; intros l2 HM. *)
  (*     - destruct l2; try constructor; unfold MultisetPerm in *. *)
  (*       rewrite HE in HM; clear HE. *)
  (*       symmetry in HM; apply list_to_set_disj_nil_iff in HM. discriminate. *)
  (*     - destruct l2; try constructor; unfold MultisetPerm in *. *)
  (*       + rewrite HE in HM; clear HE. *)
  (*         apply list_to_set_disj_nil_iff in HM; discriminate. *)
  (*       + destruct (decide_rel eq a a0). *)
  (*         ++ subst. *)
  (*            replace (a0 :: l1) with ([a0] ++ l1) by auto; replace (a0 :: l2) with ([a0] ++ l2) by auto. *)
  (*            apply orderperm_plus; try constructor. *)
  (*            apply IHl1. *)
  (*   Admitted. *)

  (*   Section MultisetPermLaws. *)
  (*     (* Lemma Permutation_rel_Reflexive : forall {A : Type}, Reflexive (@Permutation_rel). *) *)
  (*     Instance MultisetPerm_rel_Reflexive : Reflexive (Permutation_rel MultisetPerm). *)
  (*     Proof. *)
  (*       repeat red. *)
  (*       intros. unfold MultisetPerm. *)
  (*       eexists; auto. *)
  (*     Qed. *)

  (*     Instance MultisetPerm_rel_Symmetric : Symmetric (Permutation_rel MultisetPerm). *)
  (*     Proof. *)
  (*       repeat red. *)
  (*       intros x y HP. destruct HP as [P]. *)
  (*       exists (OrderPerm_symmetric x y P). auto. *)
  (*     Qed. *)

  (*     Instance MultisetPerm_rel_Transitive : Transitive (Permutation_rel MultisetPerm). *)
  (*     Proof. *)
  (*       repeat red. *)
  (*       intros x y z HP0 HP1. destruct HP0 as [P]. destruct HP1 as [Q]. *)
  (*       exists (orderperm_comp x y z P Q). auto. *)
  (*     Qed. *)
      
  (*     Instance MultisetPerm_Proper : Proper ((Permutation_rel MultisetPerm) ==> (Permutation_rel MultisetPerm) ==> iff) (Permutation_rel MultisetPerm).  *)
  (*     Proof. *)
  (*       repeat red. *)
  (*       intros x0 y0 HP0 x1 y1 HP1. *)
  (*       split; intros HP2. *)
  (*       - apply symmetry.  eapply transitivity. 2:{ apply HP0. }  apply symmetry. eapply transitivity; eauto. *)
  (*       - eapply transitivity. apply HP0. eapply transitivity. apply HP2. apply symmetry. auto. *)
  (*     Qed. *)

  (*     #[global] *)
  (*       Instance PermRelLaw_OrderPerm : PermRelLaw OrderPerm := { *)
  (*         Permutation_reflexive := reflexivity; *)
  (*         Permutation_symmetric := symmetry; *)
  (*         Permutation_transitive := transitivity *)
  (*       }. *)

  (*   End OrderPermLaws. *)



  (* End MultisetPerm. *)

(* End OrderPerm. *)

(* Section OrderPerm. *)
(*   Context `{Countable A}. *)

(*   Inductive OrderPerm : list A -> list A -> Type := *)
(*   | perm_id: forall l, OrderPerm l l *)
(*   | perm_swap x y l : OrderPerm ([y] ++ [x] ++ l) ([x] ++ [y] ++ l) *)
(*   | perm_comp l1 l2 l3 : *)
(*     OrderPerm l1 l2 -> OrderPerm l2 l3 -> OrderPerm l1 l3 *)
(*   | perm_plus l11 l12 l21 l22 : *)
(*     OrderPerm l11 l21 -> OrderPerm l12 l22 -> OrderPerm (l11 ++ l12) (l21 ++ l22). *)

(*   Definition OrderPerm_Permutation_rel : relation (list A) := *)
(*     fun l1 l2 => exists (p : OrderlPerm l1 l2), True. *)

(*   Program Definition OrderPerm_Permutation_inj_rel {l1 l2 : list A} (p : Permutation l1 l2) : *)
(*     Permutation_rel l1 l2 := *)
(*     _. *)
(*   Next Obligation. *)
(*     red. exists p. auto. *)
(*   Defined. *)
  
(* End OrderPerm. *)

(* Module Type PermutationSig. *)
(*   Context `{Countable A}. *)
(*   Parameter Permutation : list A -> list A -> Type. *)

(*   Parameter Permutation_rel : relation (list A). *)

(*   Parameter Permutation_inj_rel : forall (l1 l2: list A), Permutation l1 l2 -> Permutation_rel l1 l2. *)

(*   Parameter Permutation_rel_Reflexive : Reflexive Permutation_rel. *)

(*   Parameter Permutation_rel_Symmetric : Symmetric Permutation_rel. *)

(*   Parameter Permutation_rel_Transitive : Transitive Permutation_rel. *)

(*   Parameter Permutation_Proper : Proper (Permutation_rel ==> Permutation_rel ==> iff) Permutation_rel. *)

(* End PermutationSig. *)


(* Module OrderPerm <: PermutationSig. *)
(*   Context `{Countable A}. *)

(*   Inductive _Permutation : list A -> list A -> Type := *)
(*   | perm_id: forall l, _Permutation l l *)
(*   | perm_swap x y l : _Permutation ([y] ++ [x] ++ l) ([x] ++ [y] ++ l) *)
(*   | perm_comp l1 l2 l3 : *)
(*     _Permutation l1 l2 -> _Permutation l2 l3 -> _Permutation l1 l3 *)
(*   | perm_plus l11 l12 l21 l22 : *)
(*     _Permutation l11 l21 -> _Permutation l12 l22 -> _Permutation (l11 ++ l12) (l21 ++ l22). *)

(*   Definition Permutation : list A -> list A -> Type := *)
(*     _Permutation. *)

(*   (* Inductive Permutation : list A -> list A -> Type := *) *)
(*   (* | perm_id: forall l, Permutation l l *) *)
(*   (* | perm_swap x y l : Permutation ([y] ++ [x] ++ l) ([x] ++ [y] ++ l) *) *)
(*   (* | perm_comp l1 l2 l3 : *) *)
(*   (*   Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3 *) *)
(*   (* | perm_plus l11 l12 l21 l22 : *) *)
(*   (*   Permutation l11 l21 -> Permutation l12 l22 -> Permutation (l11 ++ l12) (l21 ++ l22). *) *)

(*   Definition Permutation_rel : relation (list A) := *)
(*     fun l1 l2 => exists (p : Permutation l1 l2), True. *)

(*   Lemma Permutation_symmetric : *)
(*     forall (xs ys: list A) *)
(*       (HP : Permutation xs ys), Permutation ys xs. *)
(*   Proof. *)
(*     intros. *)
(*     induction HP. *)
(*     - apply perm_id. *)
(*     - apply perm_swap. *)
(*     - eapply perm_comp; eauto. *)
(*     - apply perm_plus; eauto. *)
(*   Qed.     *)
  
(*   Program Definition Permutation_inj_rel {l1 l2 : list A} (p : Permutation l1 l2) : *)
(*     Permutation_rel l1 l2 := *)
(*     _. *)
(*   Next Obligation. *)
(*     red. exists p. auto. *)
(*   Defined. *)

(*   (* Lemma Permutation_rel_Reflexive : forall {A : Type}, Reflexive (@Permutation_rel). *) *)
(*   Instance Permutation_rel_Reflexive : Reflexive Permutation_rel. *)
(*   Proof. *)
(*     repeat red. *)
(*     intros. exists (perm_id x). auto. *)
(*   Qed. *)

(*   Instance Permutation_rel_Symmetric : Symmetric Permutation_rel. *)
(*   Proof. *)
(*     repeat red. *)
(*     intros x y HP. destruct HP as [P]. *)
(*     exists (Permutation_symmetric x y P). auto. *)
(*   Qed. *)

(*   Instance Permutation_rel_Transitive : Transitive Permutation_rel. *)
(*   Proof. *)
(*     repeat red. *)
(*     intros x y z HP0 HP1. destruct HP0 as [P]. destruct HP1 as [Q]. *)
(*     exists (perm_comp x y z P Q). auto. *)
(*   Qed. *)
  
(*   Instance Permutation_Proper : Proper (Permutation_rel ==> Permutation_rel ==> iff) Permutation_rel. *)
(*   Proof. *)
(*     repeat red. *)
(*     intros x0 y0 HP0 x1 y1 HP1. *)
(*     split; intros HP2. *)
(*     - apply symmetry.  eapply transitivity. 2:{ apply HP0. }  apply symmetry. eapply transitivity; eauto. *)
(*     - eapply transitivity. apply HP0. eapply transitivity. apply HP2. apply symmetry. auto. *)
(*   Qed. *)
  
(* End OrderPerm. *)

(* Module MultisetPerm <: PermutationSig. *)
(*   Context `{Countable A}. *)
(*   Definition Permutation (l1 l2 : list A) : Prop := *)
(*     list_to_set_disj l1 =@{gmultiset A} list_to_set_disj l2. *)

(*   Import OrderPerm. *)

(*   Theorem OrderPerm_MultisetPerm_Equivalence : forall (l1 l2 : list A), Permutation l1 l2 <-> OrderPerm.Permutation l1 l2. *)
