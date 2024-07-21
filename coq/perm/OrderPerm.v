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


Lemma Permutation_symmetric :
  forall {A:Type} (xs ys: list A)
    (H : Permutation xs ys), Permutation ys xs.
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

Notation "x ≡ y" := (Permutation_rel x y) (at level 70, right associativity).

Program Definition Permutation_inj_rel {A : Type} {l1 l2 : list A} (p : Permutation l1 l2) :
  Permutation_rel l1 l2 :=
  _.
Next Obligation.
  red. exists p. auto.
Defined.
Coercion Permutation_inj_rel : Sortclass >-> Funclass.

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

#[global]
 Instance Permuation_Proper {A} : Proper (Permutation_rel ==> Permutation_rel ==> iff) (@Permutation_rel A).
Proof.
  repeat red.
  intros.
  split; intros.
  - apply symmetry.  eapply transitivity. 2:{ apply H. }  apply symmetry. eapply transitivity; eauto.
  - eapply transitivity. apply H. eapply transitivity. apply H1. apply symmetry. auto.
Qed.

Lemma Permutation_In :
  forall A (l1 l2 : list A) (x:A)
    (HP : Permutation l1 l2),
    In x l1 <-> In x l2.
Proof.  
  intros. 
  induction HP; split; intros; intuition.
  - simpl. simpl in H. intuition.
  - simpl. simpl in H. intuition.
  - apply in_app_or in H.
    apply in_or_app. intuition.
  - apply in_app_or in H.
    apply in_or_app. intuition.
Qed.    


Lemma Permutation_rel_In :
  forall A (l1 l2 : list A) (x:A)
    (HP : l1 ≡ l2),
    In x l1 <-> In x l2.
Proof.  
  intros. destruct HP as [HP _].
  apply Permutation_In.
  assumption.
Qed.    

Lemma Permutation_rel_swap :
  forall A x y (l : list A),
  ([y] ++ [x] ++ l) ≡ ([x] ++ [y] ++ l).
Proof.
  intros.
  constructor; auto. apply perm_swap.
Qed.

Lemma Permutation_rel_plus :
  forall A (l11 l21 l12 l22 : list A),
    (l11 ≡ l21) -> (l12 ≡ l22) -> (l11 ++ l12) ≡ (l21 ++ l22).
Proof.
  intros.
  inversion H. inversion H0.
  constructor; auto. apply perm_plus; auto.
Qed.


Lemma Permutation_hoist :
  forall A (l : list A) (a:A),
    Permutation (l ++ [a])([a] ++ l).
Proof.
  induction l; intros; simpl.
  - apply perm_id.
  - eapply perm_comp.
    replace (a :: l ++ [a0]) with ([a] ++ (l ++ [a0])) by auto.
    apply perm_plus. apply perm_id. apply IHl.
    apply perm_swap.
Qed.


Lemma Permutation_rel_hoist :
  forall A (l : list A) (a:A),
    (l ++ [a]) ≡ ([a] ++ l).
Proof.
  intros.
  eexists; auto. apply Permutation_hoist.
Qed.

Lemma Permutation_exchange :
  forall A (l1 l2 : list A),
    Permutation (l1 ++ l2) (l2 ++ l1).
Proof.
  induction l1; intros; simpl.
  - rewrite app_nil_r.
    apply perm_id.
  - eapply perm_comp.
    replace (a:: l1 ++ l2) with ([a] ++ (l1 ++ l2)) by auto.
    apply perm_plus. apply perm_id. apply IHl1.
    eapply perm_comp.
    2: { replace (l2 ++ a :: l1) with ((l2 ++ [a]) ++ l1).
         apply perm_plus. apply Permutation_symmetric. apply Permutation_hoist. apply perm_id.
         rewrite <- app_assoc. reflexivity. }
    rewrite <- app_assoc. apply perm_id.
Qed.    

Lemma Permutation_rel_exchange :
  forall A (l1 l2 : list A),
    (l1 ++ l2) ≡ (l2 ++ l1).
Proof.
  intros.
  eexists; auto. apply Permutation_exchange.
Qed.

Lemma Permutation_nil_inv :
  forall A (l : list A),
    Permutation l [] -> l = [].
Proof.
  intros A l HP.
  remember [] as s.
  revert Heqs.
  induction HP.
  - intros. reflexivity.

  - intros. inversion Heqs.
  - intros. subst. specialize (IHHP2 eq_refl).
    subst. apply IHHP1. reflexivity.
  - intros. apply app_eq_nil in Heqs.
    destruct Heqs.
    rewrite IHHP1; auto.
    rewrite IHHP2; auto.
Qed.

Lemma Permutation_rel_nil_inv :
  forall A (l : list A),
    l ≡ [] -> l = [].
Proof.
  intros A l HP.
  destruct HP as [HP _].
  apply Permutation_nil_inv in HP.
  assumption.
Qed.

Lemma Permutation_singleton :
  forall A (l : list A) (a :A),
    Permutation l [a] -> l = [a].
Proof.
  intros A l a HP.
  remember [a] as s.
  revert a Heqs.
  induction HP; intros.
  - reflexivity.
  - inversion Heqs.
  - subst.
    rewrite (IHHP2 a eq_refl) in IHHP1.
    apply (IHHP1 a eq_refl).
  - apply app_eq_unit in Heqs.
    destruct Heqs as [[H1 H2] | [H1 H2]].
    + subst. rewrite (IHHP2 a eq_refl).
      apply Permutation_nil_inv in HP1. rewrite HP1.
      reflexivity.
    + subst. rewrite (IHHP1 a eq_refl).
      apply Permutation_nil_inv in HP2. rewrite HP2.
      reflexivity.
Qed.      

Lemma Permutation_rel_singleton :
  forall A (l : list A) (a :A),
    l ≡ [a] -> l = [a].
Proof.
  intros A l a HP.
  destruct HP as [HP _].
  apply Permutation_singleton in HP.
  assumption.
Qed.      

Lemma Permutation_doubleton :
  forall A (l : list A) (a1 a2 : A),
    Permutation l ([a1] ++ [a2]) -> (l = [a1] ++ [a2]) + (l = [a2] ++ [a1]).
Proof.
  intros A l a1 a2 HP.
  remember ([a1] ++ [a2]) as s.
  revert a1 a2 Heqs.
  induction HP; intros.
  - left. reflexivity.
  - inversion Heqs.
    subst.
    right. reflexivity.
  - subst.
    destruct (IHHP2 a1 a2 eq_refl).
    + destruct (IHHP1 a1 a2 e).
      * subst. left. reflexivity.
      * subst. right. reflexivity.
    + destruct (IHHP1 a2 a1 e).
      * subst. right. reflexivity.
      * subst. left.  reflexivity.
  - destruct l21.
    + apply Permutation_nil_inv in HP1. subst.
      destruct (IHHP2 _ _ Heqs).
      * subst. left. reflexivity.
      * subst. right. reflexivity.
    + destruct l21.
      * inversion Heqs; subst.
        apply Permutation_singleton in HP2.
        subst.
        apply Permutation_singleton in HP1.
        subst.
        left. reflexivity.
      * destruct l21; destruct l22; inversion Heqs; subst.
           apply Permutation_nil_inv in HP2. subst.
           destruct (IHHP1 _ _ eq_refl); subst.
           ++ left. reflexivity.
           ++ right. reflexivity.
Qed.           


Lemma Permutation_rel_doubleton :
  forall A (l : list A) (a1 a2 : A),
    l ≡ ([a1] ++ [a2]) -> (l = [a1] ++ [a2]) \/ (l = [a2] ++ [a1]).
Proof.
  intros A l a1 a2 HP.
  destruct HP as [HP _].
  apply Permutation_doubleton in HP.
  destruct HP; intuition.
Qed.  

Lemma Permutation_singleton_inv :
  forall A (a1 a2 : A)
    (HP : Permutation [a1] [a2]),
    a1 = a2.
Proof.
  intros.
  apply Permutation_singleton in HP.
  inversion HP.
  reflexivity.
Qed.  

Lemma Permutation_rel_singleton_inv :
  forall A (a1 a2 : A)
    (HP : [a1] ≡ [a2]),
    a1 = a2.
Proof.
  intros.
  apply Permutation_rel_singleton in HP.
  inversion HP.
  reflexivity.
Qed.  
