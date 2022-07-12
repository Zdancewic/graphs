From Coq Require Import List.

Import ListNotations.
Local Open Scope list_scope.
Open Scope type_scope.

Section PERM.

  Context {A : Type}.

(** Steve's version *)
  
Inductive Permutation  : list A -> list A -> Type :=
| perm_id: forall l, Permutation l l
| perm_swap x y l : Permutation ([y] ++ [x] ++ l) ([x] ++ [y] ++ l)
| perm_comp l1 l2 l3 :
    Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3
| perm_plus l11 l12 l21 l22 :
  Permutation l11 l21 -> Permutation l12 l22 -> Permutation (l11 ++ l12) (l21 ++ l22).

Lemma PermutationSymmetric : forall (xs ys: list A),
    Permutation xs ys -> Permutation ys xs.
Proof.
  intros.
  induction X.
  - apply perm_id.
  - apply perm_swap.
  - eapply perm_comp; eauto.
  - apply perm_plus; eauto.
Qed.    


(** Thorsten's Version *)

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
    {ds : list A & Add b aS ds * (Add a ds cs)}.
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
    { cs' : list A & Perm bs' cs' * Add a cs' cs}.
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
    eapply perm_comp. eapply PermutationSymmetric.
    replace (a :: l1) with ([a] ++ l1) by reflexivity.
    apply perm_plus. apply perm_id.
    apply PermutationSymmetric. apply X1.
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
