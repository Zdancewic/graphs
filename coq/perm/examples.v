From stdpp Require Import gmultiset sets.
From Coq Require List Permutation.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.

Section test_multiset_solver.
  Context `{Countable A}.
  Lemma solver_test_0 : forall (x y: A) (X : gmultiset A),
      {[+ x; y +]} ⊎ X = {[+ y; x +]} ⊎ X.
  Proof. multiset_solver. Qed.

  (* Take some time to solve *)
  Lemma solver_test_1 : forall (a b c : A) (X Y Z : gmultiset A),
      X ⊎ Y = {[+ a; b +]} ->
      Y ⊎ Z = {[+ b; c+]} ->
      X ⊎ Z = {[+ a; c+]} ->
      X ⊎ Y ⊎ Z = {[+a ; b; c+]}.
  Proof. multiset_solver. Qed.


  Lemma solver_test_2 : forall (a b : A) (X Y Z : gmultiset A),
      X ⊎ Y = {[+ b; b +]} ->
      Y ⊎ Z = {[+ b; b +]} ->
      X ⊎ Z = {[+ b; b +]} ->
      X ⊎ Y ⊎ Z = {[+ b; b; b+]}.
  Proof. multiset_solver. Qed.

  (* Seems to run into infinite loop *)
  Lemma solver_test_3 : forall (a b : A) (X Y Z : gmultiset A),
      X ⊎ Y = {[+ a; b; b +]} ->
      Y ⊎ Z = {[+ b; b +]} ->
      X ⊎ Y ⊎ Z = {[+ a; b; b; b +]}.
  Proof. (* multiset_solver *) Abort.

  Lemma solver_test_4 : forall (a b : A) (X Y : gmultiset A),
      X ⊎ Y = {[+ a; b; b; a +]} ->
      Y ⊎ X = {[+ a; a; b; b +]}.
  Proof. multiset_solver. Qed.

  (* Seems to run into infinite loop *)
  (* This should be true *)
  Lemma solver_test_5 : forall (a b : A) (X Y Z : gmultiset A),
     X ⊎ Y = {[+ a; b; b +]}  ->
     Y = ∅ ->
     Y ⊎ Z = {[+ b; b +]} ->
     X ⊎ Y ⊎ Z = {[+ a; b; b; b; b+]}.
  Proof. multiset_solver. Qed.

  (* Seems to run into infinite loop *)
  (* The hypothesis has a contradiction *)
  Lemma solver_test_6 : forall (a b c : A) (X Y Z : gmultiset A),
      X ⊎ Z = {[+ a; b; b +]} ->
      Y ⊎ Z = {[+ b; c+]} ->
      X = {[+ a +]} ->
      X ⊎ Y ⊎ Z = {[+ c +]}.
  Proof. (* multiset_solver. Qed. *) Abort.

  (* Seems to have some ability in getting contradiction. *)
  Lemma solver_test_7 : forall (a : A) (X : gmultiset A),
      X = {[+ a +]} ->
      X = {[+ a; a +]} ->
      False.
  Proof. multiset_solver. Qed.

  Lemma solver_test_13 : forall (a b : A) (X Y : gmultiset A),
      X ⊎ Y = {[+ a; b +]} ->
      X ⊎ Y ⊎ X ⊎ Y = {[+ a; a; b; b+]}.
  Proof. multiset_solver. Qed.

  Lemma solver_test_8 : forall (a b : A) (X Y B C : gmultiset A),
      X ⊎ Y = B ⊎ C ⊎ {[+ a; b +]} ->
      X = B ⊎ {[+ a +]} ->
      Y = C ⊎ {[+ b +]}.
  Proof. multiset_solver. Qed.

  (** Bogus Test Cases *)
  (* Instantly solved *)
  Lemma solver_test_9 : forall (a b : A) (X Z : gmultiset A),
      X = {[+ a +]} ->
      Z = {[+ b +]}.
  Proof. Fail multiset_solver. Abort.

  Lemma solver_test_10 : forall (a b : A) (X Z : gmultiset A),
      X ⊎ Z = {[+ a; b+]} ->
      X = {[+ a +]}.
  Proof. Fail multiset_solver. Abort.

  Section test_in_aac.
    Lemma solver_test_11 : forall (X Y : gmultiset A),
        X ⊎ Y = Y ⊎ X.
    Proof. multiset_solver. Qed.

    Lemma solver_test_12 : forall (B C D E : gmultiset A),
        C ⊎ B ⊎ D ⊎ E = C ⊎ B ⊎ E ⊎ D.
    Proof. multiset_solver. Qed.
  End test_in_aac.
  Lemma solver_test_14 : forall (a b : A) (X Y Z : gmultiset A),
      X ⊎ Z = Y ⊎ {[+ a +]} ->
      Y ⊎ X = {[+ b +]} ->
      Z = {[+ a; b +]}.
  Proof. Fail multiset_solver. Abort.
  (* TODO: Manual Proof *)
End test_multiset_solver.


Section test_aac_tactics.
  Import List Permutation.
  Import Instances.Lists.
  Variable A : Type.
  Lemma aac_test_0 : forall (X Y : list A),
      Permutation (X ++ Y) (Y ++ X).
  Proof. intros. aac_reflexivity. Qed.

  Lemma aac_test_0_0 : forall (x y : A) (X : list A), Permutation ([x] ++ [y] ++ X) ([y] ++ [x] ++ X).
  Proof. intros. aac_reflexivity. Qed.

  (* Fail test cases *)
  Lemma aac_test_0_1 : forall (x y: A) (X : list A), Permutation ([x; y] ++ X) ([y; x] ++ X).
  Proof.
    intros.
    (* Fail to be discharged *)
    Fail aac_reflexivity.
    apply perm_swap.
  Qed.

  (* Not provable by simply using aac-tactics *)
  (* Not entirely obvious how to solve these by aac-tactics *)
  Lemma aac_test_1 : forall (a b c : A) (X Y Z : list A),
      Permutation (X ++ Y) ([a; b]) ->
      Permutation (Y ++ Z) ([b; c]) ->
      Permutation (X ++ Z) ([a; c]) ->
      Permutation (X ++ Y ++ Z) ([a; b; c]).
  Proof.
    intros.
    aac_normalise in *.
    (* This seems to give hints only to the goal *)
    (* This does not really help unifying the three equations *)
    aac_instances H.
  Abort.

  Lemma aac_test_1 : forall (a b c : A) (X Y Z : list A),
      Permutation (X ++ Y) ([a] ++ [b]) ->
      Permutation (Y ++ Z) ([b] ++ [c]) ->
      Permutation (X ++ Z) ([a] ++ [c]) ->
      Permutation (X ++ Y ++ Z) ([a] ++ [b] ++ [c]).
  Proof.
    intros.
    aac_normalise in *.
    aac_rewrite H. 
    aac_normalise.
  Abort.

  Lemma aac_test_2 : forall (a b : A) (X Y Z : list A),
      Permutation (X ++ Y) ([b; b]) ->
      Permutation (Y ++ Z) ([b; b]) ->
      Permutation (X ++ Z) ([b; b]) ->
      Permutation (X ++ Y ++ Z) ([b; b; b]).
  Proof.
    intros. 
    Abort.

  Lemma aac_test_3 : forall (a b : A) (X Y Z : list A),
      Permutation (X ++ Y) [a; b; b] ->
      Permutation (Y ++ Z) [b; b] ->
      Permutation (X ++ Y ++ Z) [a; b; b; b].
  Proof. intros. Fail aac_reflexivity. Abort.

  Lemma aac_test_4 : forall (a b : A) (X Y : list A),
      Permutation (X ++ Y) [a; a; b; b] ->
      Permutation (Y ++ X) [a; a; b; b].
  Proof. intros. aac_rewrite H. aac_reflexivity. Qed.

  Lemma aac_test_4_0 : forall (a b : A) (X Y : list A),
      Permutation (X ++ Y) [a; a; b; b] ->
      Permutation (Y ++ X) [a; b; b; a].
  Proof. intros. aac_rewrite H. aac_normalise. Fail aac_reflexivity. Abort.
  (* Permutation l1 l2 <-> mset_of_list l1 ≡ mset_of_list l2 *)
End test_aac_tactics.
