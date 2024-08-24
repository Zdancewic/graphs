(* Polymorphic Multiplicative Exponential Linear Logic *)

From Coq Require Import
  PeanoNat
  Lia
  List
  Classes.RelationClasses
  Morphisms
  Wellfounded
  Program
  Program.Wf
.
  

(* From Graph Require Import Permutations. *)

From Graph Require Import SigPerm.

From stdpp Require Import gmultiset base countable.

Import ListNotations.

Local Open Scope positive.

Variant base_type :=
  | b_unit
  | b_other (n:nat).

(* Lemma Decision_base_type : forall (b1 b2 : base_type), Decision (b1 = b2). *)

#[global]
  Instance EqDecision_base_type : EqDecision base_type.
Proof. solve_decision. Defined.

Definition encode_base_type : base_type -> positive :=
  fun b => 
    match b with
    | b_unit => 1%positive
    | b_other n => Pos.succ (encode n)
    end.

Definition decode_base_type : positive -> option base_type :=
  fun p =>
    if decide (p = 1)%positive then Some b_unit else 
    (* match p with *)
    (* | 1%positive => Some b_unit *)
    (* | _ =>  *)
        b_other <$> decode (Pos.pred p)
    (* end. *)
.

#[global]
  Program Instance Countable_base_type : Countable base_type :=
  {|
    encode := encode_base_type;
    decode := decode_base_type
  |}.
Next Obligation.
  intros.
  destruct x.
  - auto.
  - simpl.
    unfold decode_base_type.
    case_decide.
    + auto with lia.
    + by rewrite Pos.pred_succ, decode_encode.
Qed.

(* TODO: Seems redundant now *)
Lemma base_type_eq_dec : forall (b1 b2:base_type), {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Qed.  

Inductive typ :=
| t_base (p:bool) (b:base_type)  (* p is the "polarity" *)
| t_var (p:bool) (x:nat)    (* de Bruijn indices *) (* p is the "polarity" *)
| t_tensor (t1 t2 : typ)
| t_par (t1 t2 : typ)
| t_bang (t : typ)
| t_ques (t : typ)
| t_forall (t:typ) (* de Bruijn binder *)
| t_exists (t:typ) (* de Bruijn binder *)
.


Module PMELLBasicNotations.
Notation "[1]" := (t_base true b_unit) : pmell_scope.   (* Unit for [⊗] *)
Notation "[⊥]" := (t_base false b_unit) : pmell_scope.  (* Unit for [∥] *)

Notation "'B' n" := (t_base true (b_other n)) (at level 20) : pemll_scope.
Notation "'B⟂' n" := (t_base false (b_other n)) (at level 20) : pmell_scope.
Infix "⊗" := t_tensor (at level 80) : pmell_scope.
Infix "∥" := t_par (at level 90) : pmell_scope.
Notation "[!] t" := (t_bang t) (at level 30) : pmell_scope.
Notation "[?] t" := (t_ques t) (at level 30) : pmell_scope.
Notation "[forall] t" := (t_forall t) (at level 30) : pmell_scope.
Notation "[exists] t" := (t_exists t) (at level 30) : pmell_scope.
End PMELLBasicNotations.

Import PMELLBasicNotations.
Delimit Scope pmell_scope with pmell.
Open Scope pmell_scope.

(* TODO: Define Countable. Require change in Permutation *)

Lemma typ_eq_dec : forall (t u:typ), {t = u} + {t <> u}.
Proof.
  intros.
  decide equality.
  - apply base_type_eq_dec.
  - apply Bool.bool_dec.
  - apply Nat.eq_dec.
  - apply Bool.bool_dec.
Qed.

#[global]
  Instance EqDecision_typ : EqDecision typ.
Proof. solve_decision. Defined.

(*
t_base:         000
t_var:          001
t_tensor:       010
t_par:          011
t_bang:         100
t_ques:         101
t_forall:       110
t_exists:       111
 *)

Fixpoint encode_typ (t : typ) {struct t}:  positive :=
    match t with
    | t_base p b =>
        let pos_b := encode b in
        if p then pos_b~1~0~0~0
        else pos_b~0~0~0~0
    | t_var p x =>
        let pos_x := encode x in
        if p then pos_x~1~0~0~1
        else pos_x~0~0~0~1
    | t_tensor t1 t2 =>
        (encode (encode_typ t1, encode_typ t2))~0~1~0
    | t_par t1 t2 =>
        (encode (encode_typ t1, encode_typ t2))~0~1~1
    | t_bang t => (encode_typ t)~1~0~0
    | t_ques t => (encode_typ t)~1~0~1
    | t_forall t => (encode_typ t)~1~1~0
    | t_exists t => (encode_typ t)~1~1~1
    end.

From ExtLib Require Import
  Structures.Monads
.
Import Monads.
From Graph Require Import MonadNotation.

Import MonadNotation.MonadNotation.
Local Open Scope monad_scope.

Require Import Recdef.

(* Fixpoint prod_decode_fst (p : positive) : option positive. *)
(*   destruct p. *)
(*   -  *)

(* Function prod_decode_fst (p : positive) {wf Pos.lt p}: option positive := *)
(*   match p with *)
(*   | p~0~0 => (~0) <$> prod_decode_fst p *)
(*   | p~0~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end *)
(*   | p~1~0 => (~0) <$> prod_decode_fst p *)
(*   | p~1~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end *)
(*   | 1~0 => None *)
(*   | 1~1 => Some 1 *)
(*   | 1 => Some 1 *)
(*   end. *)
(* Admitted. *)
Lemma prod_decode_fst_decreasing : forall p q, prod_decode_fst p = Some q -> q <= p.
Proof.
Admitted.

Lemma prod_decode_snd_decreasing : forall p q, prod_decode_snd p = Some q -> q <= p.
Proof.
Admitted.

(* (* Lemma WF_lt : well_founded Pos.lt. *) *)
(* (* Proof. *) *)
(* (*   auto. *) *)
(* (*   unfold well_founded. *) *)
(* (*   intros. *) *)
(* (*   Search Acc. *) *)


(* Function decode_typ (p : positive) {measure Pos.to_nat p} : option typ := *)
(*   match p with *)
(*   | p1~0~0~0 => *)
(*       match p1 with *)
(*       | p2~0 => *)
(*           t_base false <$> (decode p2) *)
(*       | p2~1 => *)
(*           t_base true <$> (decode p2) *)
(*       | _ => None *)
(*       end *)
(*   | p1~0~0~1 => *)
(*       match p1 with *)
(*       | p2~0 => *)
(*           t_var false <$> (decode p2) *)
(*       | p2~1 => *)
(*           t_var true <$> (decode p2) *)
(*       | _ => None *)
(*       end *)
(*   | p1~0~1~0 => *)
(*       match prod_decode_fst p1 with *)
(*       | Some x => *)
(*           match prod_decode_snd p1 with *)
(*           | Some y => *)
(*               match decode_typ x with *)
(*               | Some t1 => *)
(*                   match decode_typ y with *)
(*                   | Some t2 => *)
(*                       Some (t_tensor t1 t2) *)
(*                   | None => None *)
(*                   end *)
(*               | None => None *)
(*               end *)
(*           | None => None *)
(*           end *)
(*       | None => None *)
(*       end *)
(*   | p1~0~1~1 => *)
(*       match prod_decode_fst p1 with *)
(*       | Some x => *)
(*           match prod_decode_snd p1 with *)
(*           | Some y => *)
(*               match decode_typ x with *)
(*               | Some t1 => *)
(*                   match decode_typ y with *)
(*                   | Some t2 => *)
(*                       Some (t_par t1 t2) *)
(*                   | None => None *)
(*                   end *)
(*               | None => None *)
(*               end *)
(*           | None => None *)
(*           end *)
(*       | None => None *)
(*       end *)
(*       (* x <- prod_decode_fst p1;; *) *)
(*       (* match Pos.lt_dec x p with *) *)
(*       (* | left _ => t1 <- decode_typ x;; *) *)
(*       (*   ret (t_tensor t1 (t_var true 0)) *) *)
(*       (* | _ => None *) *)
(*       (* end *) *)
(*       (* x <- prod_decode_fst p1;; *) *)
(*       (* y <- prod_decode_snd p1;; *) *)
(*       (* match Pos.le_dec x p1, Pos.le_dec y p1 with *) *)
(*       (* | left _, left _ => *) *)
(*       (*     t1 <- decode_typ x;; *) *)
(*       (*     t2 <- decode_typ y;; *) *)
(*       (*     ret (t_tensor t1 t2) *) *)
(*       (* | _, _ => None *) *)
(*       (* end *) *)
(*   (* | p1~0~1~1 => *) *)
(*   (*     x <- prod_decode_fst p1;; *) *)
(*   (*     y <- prod_decode_snd p1;; *) *)
(*   (*     match Pos.lt_dec x p, Pos.lt_dec y p with *) *)
(*   (*     | left _, left _ => *) *)
(*   (*         t1 <- decode_typ x;; *) *)
(*   (*         t2 <- decode_typ y;; *) *)
(*   (*         ret (t_par t1 t2) *) *)
(*   (*     | _, _ => None *) *)
(*   (*     end *) *)
(*   | p1~1~0~0 => *)
(*       t_bang <$> (decode_typ p1) *)
(*   | p1~1~0~1 => t_ques <$> (decode_typ p1) *)
(*   | p1~1~1~0 => t_forall <$> (decode_typ p1) *)
(*   | p1~1~1~1 => t_exists <$> (decode_typ p1) *)
(*   | _ => None *)
(*   end. *)
(* Proof. *)
(*   - intros. *)
(*     lia. *)
(*   - intros. *)
(*     apply prod_decode_snd_decreasing in teq3. *)
(*     lia. *)
(*   - intros. *)
(*     apply prod_decode_fst_decreasing in teq2. *)
(*     lia. *)
(*   - lia. *)
(*   - lia. *)
(*   - intros. *)
(*     apply prod_decode_snd_decreasing in teq3. *)
(*     lia. *)
(*   - intros. *)
(*     apply prod_decode_fst_decreasing in teq2. *)
(*     lia. *)
(*   - intros. *)
(*     lia. *)
(* Qed. *)

Program Fixpoint decode_typ (p : positive) {measure (Pos.to_nat p)} : option typ :=
  match p with
  | p1~0~0~0 =>
      match p1 with
      | p2~0 =>
          t_base false <$> (decode p2)
      | p2~1 =>
          t_base true <$> (decode p2)
      | _ => None
      end
  | p1~0~0~1 =>
      match p1 with
      | p2~0 =>
          t_var false <$> (decode p2)
      | p2~1 =>
          t_var true <$> (decode p2)
      | _ => None
      end
  | p1~0~1~0 =>
      x <- prod_decode_fst p1;;
      y <- prod_decode_snd p1;;
      match Pos.lt_dec x p, Pos.lt_dec y p with
      | left _, left _ =>
      t1 <- decode_typ x;;
      t2 <- decode_typ y;;
      ret (t_tensor t1 t2)
      | _, _ => None
      end
  | p1~0~1~1 =>
      x <- prod_decode_fst p1;;
      y <- prod_decode_snd p1;;
      match Pos.lt_dec x p, Pos.lt_dec y p with
      | left _, left _ =>
      t1 <- decode_typ x;;
      t2 <- decode_typ y;;
      ret (t_par t1 t2)
      | _, _ => None
      end
  | p1~1~0~0 =>
      t_bang <$> (decode_typ p1)
  | p1~1~0~1 => t_ques <$> (decode_typ p1)
  | p1~1~1~0 => t_forall <$> (decode_typ p1)
  | p1~1~1~1 => t_exists <$> (decode_typ p1)
  | _ => None
  end.
Solve Obligations with (intros; try apply Pos2Nat.inj_lt; try lia; auto).
Next Obligation.
  intros; repeat split; intros; lia.
Defined.
Next Obligation.
  intros; repeat split; intros; lia.
Defined.
Next Obligation.
  intros; repeat split; intros; lia.
Defined.
Next Obligation.
  intros; repeat split; intros; lia.
Defined.
Next Obligation.
  intros; repeat split; intros; lia.
Defined.
Next Obligation.
  intros; repeat split; intros; lia.
Defined.
Next Obligation.
  intros; repeat split; intros; lia.
Defined.
Next Obligation.
  apply measure_wf, lt_wf.
Defined.
  (* | p'~0~0~1 *)
  (* | p'~0~1~0 *)
  (* | p~0~1~1 *)
  (* | p~1~0~0 *)
  (* | p~1~0~1 *)
  (* | p~1~1~0 *)
  (* | p~1~1~1 *)

(* Lemma countable_base : forall , decode_typ (encode_typ (t_base p b)) = Some (t_base p b). *)
(* Proof. *)

(* Admitted. *)

#[global]
  Program Instance Countable_typ : Countable typ :=
  {|
    encode := encode_typ;
    decode := decode_typ
  |}.
Next Obligation.
  intros.
  induction x.
  - simpl.
    destruct p.
    + unfold decode_typ.
Admitted.

(*   intros. *)
(*   induction x. *)
(*   (* - simpl. *) *)
(*   (*   remember (encode b) as p'. *) *)
(*   (*   destruct p. *) *)
(*   (*   + unfold decode_typ. *) *)
(*   (*     simpl. *) *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - simpl. *)
(*     unfold decode_typ. *)
      

(*   - simpl. *)
(*     unfold decode_base_type. *)
(*     case_decide. *)
(*     + auto with lia. *)
(*     + by rewrite Pos.pred_succ, decode_encode. *)
(* Qed. *)

Fixpoint dual (t:typ) : typ :=
  match t with
  | t_base p b => t_base (negb p) b
  | t_var p x => t_var (negb p) x
  | t1 ⊗ t2 => (dual t1) ∥ (dual t2)
  | t1 ∥ t2 => (dual t1) ⊗ (dual t2)
  | [!]t => [?](dual t)
  | [?]t => [!](dual t)
  | [forall]t => [exists](dual t)
  | [exists]t => [forall](dual t)
  end.

Lemma dual_involutive : forall t, dual (dual t) = t.
Proof.
  induction t; simpl; try (rewrite IHt; reflexivity).
  - destruct p; reflexivity.
  - destruct p; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma negb_eq_inj : forall b1 b2, negb b1 = negb b2 -> b1 = b2.
Proof.
  intros b1 b2. destruct b1, b2; simpl in *; try discriminate; reflexivity.
Qed.

Lemma negb_eq_iff : forall b1 b2, b1 = b2 <-> negb b1 = negb b2.
Proof.
  intros; split; intros.
  - rewrite H; reflexivity.
  - apply negb_eq_inj; auto.
Qed.

Lemma dual_eq_inj : forall t1 t2, dual t1 = dual t2 -> t1 = t2.
Proof.
  intros t1. induction t1; intros; (destruct t2; simpl in H; try discriminate).
  - injection H; intros -> H1. apply negb_eq_iff in H1 as ->.
    reflexivity.
  - injection H; intros -> H1. apply negb_eq_iff in H1 as ->.
    reflexivity.
  - injection H. intros H1 H2.
    apply IHt1_1 in H2. apply IHt1_2 in H1.
    subst; reflexivity.
  - injection H. intros H1 H2.
    apply IHt1_1 in H2. apply IHt1_2 in H1.
    subst; reflexivity.
  - injection H; intros H1.
    apply IHt1 in H1.
    subst; reflexivity.
  - injection H; intros H1.
    apply IHt1 in H1.
    subst; reflexivity.
  - injection H; intros H1.
    apply IHt1 in H1.
    subst; reflexivity.
  - injection H; intros H1.
    apply IHt1 in H1.
    subst; reflexivity.
Qed.

Lemma dual_eq_iff : forall t1 t2, t1 = t2 <-> dual t1 = dual t2.
Proof.
  intros; split; intros.
  - rewrite H. auto.
  -  apply dual_eq_inj; auto.
Qed.

Lemma dual_swap_iff : forall t1 t2, t1 = dual t2 <-> dual t1 = t2.
Proof.
  intros; split; intros; apply dual_eq_iff in H; rewrite dual_involutive in H; auto.
Qed.

Close Scope positive_scope.

Inductive wf_typ  : nat -> typ -> Prop :=
| wf_t_base : forall c p (bt:base_type), wf_typ c (t_base p bt)
| wf_t_var : forall c p (x:nat) (LT:x < c), wf_typ c (t_var p x)
| wf_t_tensor : forall (c:nat) (t1 t2 : typ), wf_typ c t1 -> wf_typ c t2 -> wf_typ c (t1 ⊗ t2)
| wf_t_par : forall c (t1 t2 : typ), wf_typ c t1 -> wf_typ c t2 -> wf_typ c (t1 ∥ t2)
| wf_t_bang : forall c t, wf_typ c t -> wf_typ c ([!]t)
| wf_t_ques : forall c t, wf_typ c t -> wf_typ c ([?]t)
| wf_t_forall : forall c t, wf_typ (1 + c) t -> wf_typ c ([forall] t)
| wf_t_exists : forall c t, wf_typ (1 + c) t -> wf_typ c ([exists] t)
.                                               

#[global]
Hint Constructors wf_typ : core.

Notation "c '⊢' t 'wf'" := (wf_typ c t) (at level 70).

Lemma wf_typ_dual : forall c t (HWF: c ⊢ t wf), c ⊢ (dual t) wf.
Proof.
  intros.
  induction HWF; simpl; auto.
Qed.  

Corollary wf_typ_dual_inv : forall c t, c ⊢ (dual t) wf -> c ⊢ t wf.
Proof.
  intros.
  rewrite <- dual_involutive.
  apply wf_typ_dual; auto.
Qed.


(*
[ b_b ... b_1 ⊢ t wf]  ==> [ c_c ... c_1 b_b ... b_1 ⊢ t wf]
*)
Lemma wf_typ_weaken : forall (b c:nat) (t:typ) (HWF: b ⊢ t wf),
    (c + b) ⊢ t wf.
Proof.
  intros.
  induction HWF; intros; auto.
  - constructor. lia.
  - constructor. replace (1 + (c + c0)) with (c + (1 + c0)) by lia. apply IHHWF.
  - constructor. replace (1 + (c + c0)) with (c + (1 + c0)) by lia. apply IHHWF.
Qed.    

(*
[ a_a ... a_1  b_b ... b_1 ⊢ t wf]   ==> [ a_a ... a_1 c_c ... c_1 b_b .. b_1 |- t fw]
*)
Fixpoint shift_typ b c (t:typ) :=
  match t with
  | t_base p n => t_base p n
  | t_var p x => if Nat.ltb x b then t_var p x else t_var p (c + x)
  | t1 ⊗ t2 => (shift_typ b c t1) ⊗ (shift_typ b c t2)
  | t1 ∥ t2 => (shift_typ b c t1) ∥ (shift_typ b c t2)
  | [!]t => [!](shift_typ b c t)
  | [?]t => [?](shift_typ b c t)              
  | [forall]t => [forall](shift_typ (b + 1) c t)
  | [exists]t => [exists](shift_typ (b + 1) c t)              
  end.

Lemma shift_typ_one_id : forall b c, shift_typ b c [1] = [1].
Proof.
  intros.
  reflexivity.
Qed.  

Lemma shift_typ_bot_id : forall b c, shift_typ b c [⊥] = [⊥].
Proof.
  intros.
  reflexivity.
Qed.  

Lemma wf_typ_shift : forall (a b c :nat) (t:typ) (HWF : a + b ⊢ t wf),
    (a + c + b ⊢ (shift_typ b c t) wf).
Proof.
  intros.
  remember (a + b) as bound.
  revert a b Heqbound.
  induction HWF; intros; simpl; auto.
  - destruct (Nat.ltb_spec x b).
    * constructor. lia.
    * constructor. lia.
  - constructor. replace (1 + (a + c + b)) with (a + c + (b + 1)) by lia.
    apply IHHWF. lia.
  - constructor. replace (1 + (a + c + b)) with (a + c + (b + 1)) by lia.
    apply IHHWF. lia.
Qed.    

Corollary wf_typ_shift0 : forall b c t, c ⊢ t wf -> c + b ⊢ (shift_typ c b t) wf.
Proof.
  intros. replace (c + b) with (0 + b + c) by lia.
  apply wf_typ_shift. auto.
Qed.

Lemma wf_typ_shift_strengthen :
  forall (a b c : nat) (t:typ)
    (HWF : a + c + b ⊢ (shift_typ b c t) wf),
    a + b ⊢ t wf.
Proof.
  intros a b c t.
  revert a b c.
  induction t; intros; simpl in *.
  - constructor.
  - constructor. destruct (Nat.ltb_spec x b).
    + lia.
    + inversion HWF. subst. lia.
  - inversion HWF.
    subst.
    constructor; eauto.
  - inversion HWF.
    subst.
    constructor; eauto.
  - inversion HWF.
    subst.
    constructor.
    eauto.
  - inversion HWF.
    subst.
    constructor.
    eauto.
  - inversion HWF.
    subst.
    constructor.
    replace (1 + (a + b)) with (a + (b + 1)) by lia.
    eapply IHt with (c:=c).
    replace (a + c + (b + 1)) with (1 + (a + c + b)) by lia.
    assumption.
  - inversion HWF.
    subst.
    constructor.
    replace (1 + (a + b)) with (a + (b + 1)) by lia.
    eapply IHt with (c:=c).
    replace (a + c + (b + 1)) with (1 + (a + c + b)) by lia.
    assumption.
Qed.    

Lemma dual_shift_typ_comm : forall t b c, shift_typ b c (dual t) = dual (shift_typ b c t).
Proof.
  intros t. induction t; intros; simpl; auto.
  - destruct (x <? b); auto.
  - rewrite IHt1, IHt2. auto.
  - rewrite IHt1, IHt2. auto.
  - rewrite IHt. auto.
  - rewrite IHt. auto.
  - rewrite IHt. auto.
  - rewrite IHt. auto.
Qed.
    
(*
[ a_a ... a_1   b_b ... b_1 |- u wf ]
[ a_a ... a_1 x b_b ... b_1 |- t wf]
[ a_a ... a_1   b_b ... b_1 |- t { u / x } wf ]
 *)
(* NOTE:
   Substituting for a negative type variable dualizes [u].
*)
Fixpoint typ_subst (b:nat) (u:typ) (t:typ) : typ :=
  match t with
  | t_base p n => t_base p n
  | t_var p x =>
      if Nat.ltb x b then t_var p x
      else if Nat.eqb x b then
             if p then u else (dual u)
           else t_var p (pred x)
  | t1 ⊗ t2 => (typ_subst b u t1) ⊗ (typ_subst b u t2)
  | t1 ∥ t2 => (typ_subst b u t1) ∥ (typ_subst b u t2)
  | [!]t => [!](typ_subst b u t)
  | [?]t => [?](typ_subst b u t)              
  | [forall]t => [forall](typ_subst (b + 1) (shift_typ 0 1 u) t)
  | [exists]t => [exists](typ_subst (b + 1) (shift_typ 0 1 u) t)              
  end.

Lemma typ_subst_dual : forall b u t,
    (dual (typ_subst b u t)) = (typ_subst b u (dual t)).
Proof.
  intros. revert b u.
  induction t; intros; simpl; eauto.
  - destruct (Nat.ltb_spec x b).
    + reflexivity.
    + destruct (Nat.eqb_spec x b).
      destruct p; simpl; try reflexivity.
      apply dual_involutive.
      reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
Qed.    

Lemma typ_subst_wf :
  forall (b:nat) (u t:typ) (WFU : b ⊢ u wf) (WFT : b + 1 ⊢ t wf),
    b ⊢ (typ_subst b u t) wf.
Proof.
  intros.
  remember (b + 1) as a.
  revert u b WFU Heqa.
  induction WFT; intros; simpl; auto.
  - destruct (Nat.ltb_spec x b).
    + constructor. assumption.
    + destruct (Nat.eqb_spec x b).
      * subst. destruct p. assumption. apply wf_typ_dual. assumption.
      * destruct x. lia. simpl. constructor. lia.
  - constructor.
    replace (1 + b) with (b + 1) by lia.
    apply IHWFT. replace (b + 1) with (b + 1 + 0) by lia. apply wf_typ_shift.
    replace (b + 0) with b by lia. assumption.
    lia.
- constructor.
    replace (1 + b) with (b + 1) by lia.
    apply IHWFT. replace (b + 1) with (b + 1 + 0) by lia. apply wf_typ_shift.
    replace (b + 0) with b by lia. assumption.
    lia.    
Qed.

Lemma typ_subst_wf_inversion :
  forall (b:nat) (u t : typ) (WFT : b ⊢ (typ_subst b u t) wf),
    b + 1 ⊢ t wf.
Proof.
  intros b u t.
  revert b u.
  induction t; intros c u HWF.
  - constructor.
  - constructor.
    simpl in HWF.
    destruct (Nat.ltb_spec x c).
    + lia.
    + destruct (Nat.eqb_spec x c).
      * lia.
      * destruct x.
        lia. inversion HWF. subst. lia.
  - inversion HWF.
    subst.
    constructor; eauto.
  - inversion HWF.
    subst.
    constructor; eauto.
  - inversion HWF.
    subst.
    constructor. eauto.
  - inversion HWF.
    subst.
    constructor. eauto.
  - inversion HWF.
    subst.
    constructor.
    replace (1 + (c + 1)) with ((1 + c) + 1) by lia.
    eapply IHt. replace (c + 1) with (1 + c) in H1 by lia.
    apply H1.
  - inversion HWF.
    subst.
    constructor.
    replace (1 + (c + 1)) with ((1 + c) + 1) by lia.
    eapply IHt. replace (c + 1) with (1 + c) in H1 by lia.
    apply H1.
Qed.    

Definition ctx := list typ.

Definition shift_ctx (b c:nat) := List.map (shift_typ b c).

Definition wf_ctx (c:nat) (G : ctx) :=
  
  forall u, In u G -> c ⊢ u wf.

Lemma wf_ctx_app :
  forall c G1 G2,
    (wf_ctx c G1 /\ wf_ctx c G2) <-> wf_ctx c (G1 ++ G2).
Proof.
  intros.
  split; intros.
  - unfold wf_ctx in *. intros.
    apply in_app_or in H0.
    destruct H, H0; auto.
  - split.
    + unfold wf_ctx in *.
      intros. apply H. apply in_or_app. auto.
    + unfold wf_ctx in *.
      intros. apply H. apply in_or_app. auto.
Qed.

Lemma wf_ctx_empty :
  forall c, wf_ctx c [].
Proof.
  unfold wf_ctx. intros. inversion H.
Qed.

Lemma wf_ctx_single :
  forall c t, c ⊢ t wf <-> wf_ctx c [t].
Proof.
  unfold wf_ctx. intros.
  split; intros.
  - inversion H0.
    + subst; auto.
    + inversion H1.
  - apply H. simpl. left. reflexivity.
Qed.    

Import convertTactics.
Import ConvertibleTactics.
Definition P : list typ -> list typ -> Type := OrderPerm.

#[global]
 Instance PermConvertible_P : PermConvertible typ P.
Proof.
  apply PermConvertible_OrderPerm.
Qed.

Lemma Permutation_assoc_swap : forall l1 l2 l3, P ((l1 ++ l2) ++ l3) ((l1 ++ l3) ++ l2).
Proof.
  intros.
  convertTactics.convert_multiset. permutation_solver.
Qed.

Lemma Permutation_rel_assoc_swap : forall l1 l2 l3, (l1 ++ l2) ++ l3 ≡[P] (l1 ++ l3) ++ l2.
Proof.
  intros. eexists; auto. apply Permutation_assoc_swap.
Qed.

Lemma Permutation_singleton_app : forall a l21 l22, P [a] (l21 ++ l22) -> (l21 = [a]) * (l22 = []) + (l21 = []) * (l22 = [a]).
Proof.
  intros.
  apply Permutation_symmetric in X.
  apply Permutation_singleton in X.
  destruct l21.
  - intuition.
  - destruct l21; try discriminate. 
    destruct l22; try discriminate.
    intuition.
Qed.

Lemma Permutation_rel_singleton_app : forall a l21 l22, [a] ≡[P] l21 ++ l22 -> (l21 = [a] /\ l22 = []) \/ (l21 = [] /\ l22 = [a]).
Proof.
  intros.
  normalize_auxH.
  apply Permutation_singleton_app in H.
  destruct H as [[HP1 HP2] | [HP1 HP2]]; intuition.
Qed.

Lemma In_singleton : forall {A : Type} (a b : A), In a [b] -> a = b.
Proof.
  intros.
  apply In_cons_iff in H. destruct H; auto.
  apply in_nil in H. destruct H.
Qed.

Lemma wf_ctx_Permutation_inj :
  forall c G1 G2
    (HP : P G1 G2)
    (HWF : wf_ctx c G1),
    wf_ctx c G2.
Proof.
  unfold wf_ctx in *.
  intros.
  apply HWF.
  eapply Permutation_In in HP.
  apply HP. assumption.
Qed.  

Lemma wf_ctx_Permutation_surj :
  forall c G1 G2
    (HP : P G1 G2)
    (HWF : wf_ctx c G2),
    wf_ctx c G1.
Proof.
  intros.
  apply Permutation_symmetric in HP.
  eapply wf_ctx_Permutation_inj; eauto.
Qed.

Lemma shift_ctx_strengthen :
  forall (b c:nat) G
    (HWF : wf_ctx (c + b) (shift_ctx b c G)),
    wf_ctx b G.
Proof.
  unfold wf_ctx.
  intros.
  replace b with (0 + b) by lia.
  eapply wf_typ_shift_strengthen.
  simpl.
  apply HWF.
  apply in_map. assumption.
Qed.

Lemma wf_shift_ctx :
  forall b c G  (HWF: wf_ctx c G),
    wf_ctx (b + c) (shift_ctx c b G).
Proof.
  unfold wf_ctx.
  intros.
  unfold shift_ctx in H.
  apply in_map_iff in H.
  destruct H as [u' [HEQ HIN]].
  subst.
  replace (b + c) with (0 + b + c) by lia.
  apply wf_typ_shift.
  apply HWF.
  assumption.
Qed.

Lemma wf_shift_ctx' : forall b c G, wf_ctx c G -> wf_ctx (c + b) (shift_ctx c b G).
Proof.
  intros. replace (c + b) with (b + c) by lia.
  apply wf_shift_ctx; auto.
Qed.

Lemma shift_ctx_app :
  forall b c G1 G2,
    shift_ctx c b (G1 ++ G2) = (shift_ctx c b G1) ++ (shift_ctx c b G2).
Proof.
  intros b c G1 G2.
  unfold shift_ctx.
  rewrite map_app.
  reflexivity.
Qed.

Lemma Permutation_shift_ctx:
  forall (b c:nat) G1 G2
    (HP: P G1 G2),
    P (shift_ctx c b G1)  (shift_ctx c b G2).
Proof.
  intros b c G1 G2 HP.
  induction HP.
  - apply orderperm_id.
  - apply orderperm_swap.
  - eapply orderperm_comp; eauto.
  - do 2 rewrite shift_ctx_app.
    apply orderperm_plus; auto.
Qed.  

(* TODO: Can we prove the surjective rule *)

Lemma Permutation_rel_shift_ctx :
  forall (b c:nat) G1 G2
    (HP: G1 ≡[P] G2),
    shift_ctx c b G1 ≡[P] shift_ctx c b G2.
Proof.
  intros b c G1 G2 HP.
  destruct HP as [HP _].
  constructor; auto.
  apply Permutation_shift_ctx.
  assumption.
Qed.

#[local]
  Instance Proper_shift_ctxt : Proper (eq ==> eq ==> (Permutation_rel OrderPerm) ==> (Permutation_rel OrderPerm)) shift_ctx.
Proof.
  do 4 red.
  intros.
  subst.
  eapply Permutation_rel_shift_ctx.
  assumption.
Qed.

Lemma wf_ctx_perm_inj : forall {G G' c} (HG: G ≡[P] G') (HW: wf_ctx c G), wf_ctx c G'.
Proof.
  intros.
  unfold wf_ctx in *.
  intros.
  pose proof (@Permutation_rel_In _ _ _ P _ _).
  symmetry in HG.
  specialize (H0 _ _ u HG).
  apply H0 in H.
  apply HW; auto.
Qed.

Lemma wf_ctx_perm_iff : forall {G G' c} (HG: G ≡[P] G'), wf_ctx c G <-> wf_ctx c G'.
Proof.
  intros; split; apply wf_ctx_perm_inj; auto.
  symmetry. auto.
Qed.

Corollary wf_ctx_app_perm_iff : forall {G G1 G2 c} (HG : G ≡[P] G1 ++ G2), wf_ctx c G <-> wf_ctx c G1 /\ wf_ctx c G2.
Proof.
  intros; split; intros.
  - apply (wf_ctx_perm_inj HG) in H.
    apply wf_ctx_app in H; auto.
  - apply (wf_ctx_perm_iff HG).
    apply wf_ctx_app; auto.
Qed.

(*  We define a _family_ of logics, parameterized by two things:

    [PID : typ -> Prop] : used to regulate which types are allowed by the [pf_id] rule.
    and
    [PCUT : typ -> Prop] : used to regulate which types are allowed by the [pf_cut] rule.

    When [PID = fun t => True], the logic allows any variables (and so does not require
    eta expansion).  When [PID = fun t => atomic t], the logic requires variables to 
    be atomic (i.e. of base_other or type variables.)

    When [PCUT = fun t => True], the logc allows all cuts.  When [PCUT = fun t => False], the 
    logic does not permit any cuts.
 *)

Ltac PInvert :=
  repeat
    match goal with
    | [ H : ?X = ?X |- _] => clear H
                                 
    | [ H : ?D1 ≡[P] ?D2 |- _ ] => destruct H as [H _]
                                              
    | [ H : P [] ?YS |- _ ] =>
        apply Permutation_symmetric in H
                                              
    | [ H : P ?XS [] |- _] =>
        apply Permutation_nil_inv in H; inversion H; subst

    | [ H : P [?x] [?y] |- _] =>
        apply Permutation_singleton_inv in H; inversion H; clear H

    | [ H : P ?XS ([?y] ++ []) |- _] =>
        replace ([y] ++ []) with [y] in H by reflexivity 
                                                                 
    | [ H : P [?x] ([?y] ++ ?YS) |- _] =>
          destruct YS; [| apply Permutation_length in H; inversion H
          ]

    | [ H : P [?x] ?YS |- _] =>
        apply Permutation_symmetric in H
                         
    | [ H : P ?XS [?y] |- _] =>
        apply Permutation_singleton in H; inversion H; clear H
                         
    | [ H : P ([?x] ++ ?XS) ([?y] ++ ?YS) |- _] =>
        let EQ := fresh "EQ" in
        let HP := fresh H in
        let l1 := fresh  in
        let l2 := fresh  in
        let HI := fresh H in
        let HJ := fresh H in
        let HK := fresh H in
        apply Permutation_split in H;
        destruct H as [[EQ HP] | [l1 [l2 [[HI HJ] HK]]] ]; [subst | ]

    | [ H : P ([?x] ++ ?XS) (?YS ++ [?y]) |- _] =>
        let HH := fresh H in
        assert (P ([x] ++ XS) ([y] ++ YS)) as HH by
        (eapply Permutation_transitive; [apply H | apply Permutation_exchange]);
        clear H

      (* Only apply the following rule when the list is used in the goal *)
    | [ H : P ([?x] ++ ?XS) (?YS) |- context[?XS] ] =>
        is_var(YS);
        let HH := fresh H in
        let XS' := fresh XS in
        let HA := fresh H in
        assert (P (XS ++ [x]) YS) as HH by (eapply Permutation_transitive; [eapply Permutation_exchange |  apply H]); clear H; apply Permutation_destruct1 in HH; destruct HH as [XS' [HH HA]]

              
    | [ H : P ?XS (?YS ++ [?y]) |- _] =>
        let HH := fresh H in
        assert (P ([y] ++ YS) XS) as HH by
            (apply Permutation_symmetric; (eapply Permutation_transitive; [apply H | apply Permutation_exchange])); clear H
              
    end.

Lemma list_app_inv_tl :
  forall A l1 l2 (x y : A)
    (H : (l1 ++ [x] = l2 ++ [y])),
    l1 = l2 /\ x = y.
Proof.
  induction l1; induction l2; intros.
  - inversion H. split; auto.
  - inversion H. subst. destruct l2; inversion H2.
  - inversion H. subst. destruct l1; inversion H2.
  - inversion H. subst.
    apply IHl1 in H2.
    destruct H2; subst.
    split; reflexivity.
Qed.    

Ltac LInvert :=
  repeat
    match goal with
    | [ H : ?X = ?X |- _] => clear H

    | [ H : [?x] = [?y] |- _] => inversion H; subst; clear H

    | [ H : ?XS ++ [?x] = ?YS ++ [?y] |- _] =>
        let H' := fresh H in
        apply list_app_inv_tl in H; destruct H as [H H']; subst
                                                         
    | [ H : ?L ++ [?a] = [] |- _ ] =>
        destruct L; inversion H
                                                         
    | [ H : ?L ++ [?a] = [?b] |- _ ] =>
        replace [b] with ([] ++ [b]) in H by reflexivity

    | [ H : [?a] = ?L ++ [?b] |- _] =>
        symmetry in H
                                               
    | [ H : (?x::?y::[]) = ?L |- _ ] =>
        replace (x::y::[]) with ([x] ++ [y]) in H by reflexivity
    end.

(* #[local] Hint Resolve Permutation_reflexive : core. *)

Ltac head t :=
    match t with
  | ?t' _ => head t'
  | _ => t
  end.

Ltac head_constructor t :=
  let t' := head t in is_constructor t'.

Ltac solve_dual :=
  repeat match goal with
    |  [ H : dual ?X = ?t |- _] =>
         let H' := fresh H in
         is_var(X); head_constructor t;
         assert ((dual (dual X) = dual t)) as H' by (rewrite H; reflexivity);
         clear H; rewrite dual_involutive in H'; simpl in H'
    |  [ H : ?t = dual ?X |- _ ] =>
         symmetry in H
    end.


Ltac contradict_perm_rel H :=
  PInvert; LInvert; inversion H.

Inductive vacuous : typ -> Prop :=
| vacuous_one : vacuous [1]
| vacuous_tensor: forall t1 t2, vacuous t1 -> vacuous t2 -> vacuous (t1 ⊗ t2)
| vacuous_par : forall t1 t2, vacuous t1 -> vacuous t2 -> vacuous (t1 ∥ t2)
| vacuous_bang: forall t, vacuous ([!]t) (* Can simply move this to persistent *)
(* | vacuous_ques : forall t, vacuous t -> vacuous ([?]t) *)
(* Vacuous  *)
(* | vacuous_forall : forall t, vacuous t -> vacuous ([forall] t) *)
(* | vacuous_exists : forall t, vacuous t -> vacuous ([∃] t) *)
.

Definition vacuous_ephem (D : ctx) :=
  forall t, In t D -> vacuous t.

Lemma vacuous_ephem_empty : vacuous_ephem [].
Proof.
  unfold vacuous_ephem; intros.
  inversion H.
Qed.
Hint Resolve vacuous_ephem_empty : core.

Lemma vacuous_ephem_cons_surj : forall D a, vacuous a -> vacuous_ephem D -> vacuous_ephem (a :: D).
Proof.
  intros.
  unfold vacuous_ephem.
  intros.
  apply In_cons_iff in H1. destruct H1.
  - subst; auto.
  - auto.
Qed.

Lemma vacuous_ephem_cons_inj : forall D a, vacuous_ephem (a :: D) -> vacuous a /\ vacuous_ephem D.
Proof.
  intros.
  unfold vacuous_ephem in *. split.
  - assert (In a (a :: D)) by apply in_eq.
    apply H in H0. auto.
  - intros.
    assert (In t (a :: D)).
    {apply In_cons_iff. intuition. }
    apply H in H1; auto.
Qed.

Lemma vacuous_ephem_cons_iff : forall D a, vacuous_ephem (a :: D) <-> vacuous a /\ vacuous_ephem D.
Proof.
  intros; split.
  - apply vacuous_ephem_cons_inj.
  - intros. destruct H.
    apply vacuous_ephem_cons_surj; auto.
Qed.

Lemma vacuous_ephem_app_inj : forall D1 D2, vacuous_ephem (D1 ++ D2) -> vacuous_ephem D1 /\ vacuous_ephem D2.
Proof.
  intros D1. induction D1; intros.
  - split; auto.
  - simpl in H.
    apply vacuous_ephem_cons_iff in H as (H1 & H2).
    apply IHD1 in H2.
    split; intuition.
    apply vacuous_ephem_cons_iff; intuition.
Qed.

Lemma vacuous_ephem_app_surj : forall D1 D2, vacuous_ephem D1 -> vacuous_ephem D2 -> vacuous_ephem (D1 ++ D2).
Proof.
  intros D1. induction D1.
  - intros; auto.
  - intros.
    apply vacuous_ephem_cons_iff in H as (H1 & H2).
    simpl. apply vacuous_ephem_cons_iff; auto.
Qed.

Lemma vacuous_ephem_app_iff : forall D1 D2, vacuous_ephem (D1 ++ D2) <-> vacuous_ephem D1 /\ vacuous_ephem D2.
Proof.
  intros; split.
  - apply vacuous_ephem_app_inj.
  - intros; destruct H.
    apply vacuous_ephem_app_surj; auto.
Qed.

Lemma Permutation_vacuous_ephem_inj : forall D D', P D D' -> vacuous_ephem D -> vacuous_ephem D'.
Proof.
  intros D D' HP. apply Perm_OrderPerm_inj in HP.
  induction HP; intros.
  - auto.
  - apply vacuous_ephem_app_iff in H as (H1 & H2). apply vacuous_ephem_app_iff in H2 as (H2 & H3).
    repeat apply vacuous_ephem_app_surj; intuition.
  - auto.
  - apply vacuous_ephem_app_iff in H as (H1 & H2).
    apply vacuous_ephem_app_iff; split; auto.
Qed.

Corollary Permutation_vacuous_ephem_surj : forall D D', P D D' -> vacuous_ephem D' -> vacuous_ephem D.
Proof.
  intros.
  apply Permutation_symmetric in X.
  eapply Permutation_vacuous_ephem_inj; eauto.
Qed.

Corollary Permutation_rel_vacuous_ephem_iff : forall D D', D ≡[P] D' -> vacuous_ephem D <-> vacuous_ephem D'.
Proof.
  intros. normalize_auxH. split.
  - apply Permutation_vacuous_ephem_inj. auto.
  - apply Permutation_vacuous_ephem_surj. auto.
Qed.

Instance Proper_vacuous_ephem: Proper (Permutation_rel P ==> flip impl) vacuous_ephem.
Proof.
  unfold Proper, "==>".
  intros.
  unfold flip.
  unfold impl.
  intros.
  apply (Permutation_rel_vacuous_ephem_iff _ _ H). auto.
Defined.

Corollary vacuous_ephem_one: vacuous_ephem [[1]].
Proof.
  unfold vacuous_ephem; intros.
  apply In_singleton in H. subst.
  constructor. 
Qed.

Corollary vacuous_ephem_tensor: forall t u, vacuous t -> vacuous u -> vacuous_ephem [t ⊗ u].
Proof.
  unfold vacuous_ephem; intros.
  apply In_singleton in H1; subst.
  constructor; auto.
Qed.

Corollary vacuous_ephem_par : forall t u, vacuous t -> vacuous u -> vacuous_ephem [t_par t u].
Proof.
  unfold vacuous_ephem; intros.
  apply In_singleton in H1; subst.
  constructor; auto.
Qed.

Corollary vacuous_ephem_bang : forall t, vacuous t -> vacuous_ephem [[!] t].
Proof.
  unfold vacuous_ephem; intros.
  apply In_singleton in H0; subst.
  constructor; auto.
Qed.

Lemma vacuous_ephem_singleton : forall t, vacuous t <-> vacuous_ephem [t].
Proof.
  intros; split; intros.
  - unfold vacuous_ephem. intros.
    apply In_singleton in H0; subst. auto.
  - unfold vacuous_ephem in H.
    assert (In t [t]). {apply In_cons_iff. intuition. }
    apply H in H0; auto.
Qed.

Inductive vac_ephem : ctx -> Prop :=
| vac_empty : vac_ephem []
| vac_one : forall D D',
    D ≡[P] D' ++ [[1]] ->
    vac_ephem D' -> vac_ephem D
| vac_cut : forall D D1 D2 u,
    vac_ephem (D1 ++ [u]) ->
    vac_ephem (D2 ++ [dual u]) ->
    D ≡[P] D1 ++ D2 ->
    vac_ephem D
| vac_tensor : forall D D' t1 t2,
    vac_ephem (D' ++ [t1] ++ [t2]) ->
    D ≡[P] D' ++ [t1 ⊗ t2] ->
    vac_ephem D
| vac_par : forall D D1 D2 t1 t2,
    vac_ephem (D1 ++ [t1]) ->
    vac_ephem (D2 ++ [t2]) ->
    D ≡[P] D1 ++ D2 ++ [t_par t1 t2] ->
    vac_ephem D
| vac_bang : forall D t,
    vac_ephem D ->
    vac_ephem (D ++ [[!]t])
(* | vac_ques : forall D D' t, *)
(*     D ≡[P] D' ++ [t] -> *)
(*     vac_ephem D -> *)
(*     vac_ephem (D' ++ [[?]t]) *)
| vac_comp : forall D1 D2,
    vac_ephem D1 ->
    vac_ephem D2 ->
    vac_ephem (D1 ++ D2)
| vac_perm : forall D1 D2,
    D1 ≡[P] D2 -> 
    vac_ephem  D1 ->
    vac_ephem D2
.

Instance Proper_vac_ephem : Proper (Permutation_rel P ==> flip (impl)) vac_ephem.
Proof.
  intros. unfold Proper, "==>".
  intros.
  unfold flip, impl.
  apply vac_perm. symmetry. auto.
Qed.

  (* PID, PCUT : typ → Prop *)
  (* PID_dual : ∀ u : typ, PID u ↔ PID (dual u) *)
  (* D, D1, D2 : list typ *)
  (* t1, t2 : typ *)
  (* H : vac_ephem (D1 ++ [t1]) *)
  (* H0 : vac_ephem (D2 ++ [t2]) *)
  (* H1 : D ≡[ P] D1 ++ D2 ++ [t1 ∥ t2] *)
  (* IHvac_ephem1 : ∀ D2 D3 : list typ, D2 ++ D3 ≡[ P] D1 ++ [t1] → vac_ephem D2 ∧ vac_ephem D3 *)
  (* IHvac_ephem2 : ∀ D1 D3 : list typ, D1 ++ D3 ≡[ P] D2 ++ [t2] → vac_ephem D1 ∧ vac_ephem D3 *)
  (* D0, D3, l1' : list typ *)
  (* HP1 : D0 ≡[ P] l1' ++ [t1 ∥ t2] *)
  (* HP2 : l1' ++ D3 ≡[ P] D1 ++ D2 *)
  (* ============================ *)
  (* vac_ephem D0 ∧ vac_ephem D3 *)

Lemma Permutation_rel_split4 : forall l11 l12 l21 l22, l11 ++ l12 ≡[P] l21 ++ l22 -> exists l211 l212 l221 l222, l21 ≡[P] l211 ++ l212 /\ l22 ≡[P] l221 ++ l222 /\ l11 ≡[P] l211 ++ l221 /\ l12 ≡[P] l212 ++ l222.
Proof.
  Admitted.

Lemma vac_ephem_app : forall D1 D2, vac_ephem (D1 ++ D2) -> vac_ephem D1 /\ vac_ephem D2.
Proof.
  intros. assert (exists D, D1 ++ D2≡[P] D). {exists (D1 ++ D2). reflexivity. }
  destruct H0.
  apply (vac_perm _ _ H0) in H.
  revert D1 D2 H0.
  induction H; intros.
  - apply Permutation_rel_length in H0.
    destruct D1; try discriminate.
    destruct D2; try discriminate.
    split; constructor.
  - rewrite H in H1. apply Permutation_rel_split2 in H1.
    destruct H1 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + apply IHvac_ephem in HP2 as (HPP1 & HPP2).
      split; auto.
      rewrite HP1. apply vac_comp; auto.
      eapply vac_one. 2: {apply vac_empty. } reflexivity.
    + apply IHvac_ephem in HP2 as (HPP1 & HPP2).
      split; auto.
      rewrite HP1. apply vac_comp; auto.
      eapply vac_one. 2: {apply vac_empty. } reflexivity.
  - rewrite H1 in H2. apply Permutation_rel_split4 in H2.
    destruct H2 as (l211 & l212 & l221 & l222 & HP'1 & HP'2 & HP'3 & HP'4).
    split.
    + rewrite HP'3.
      assert (l211 ++ (l212 ++ [u]) ≡[P] D1 ++ [u]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem1 in H2; destruct H2.
      assert (l221 ++ (l222 ++ [dual u]) ≡[P] D2 ++ [dual u]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem2 in H4; destruct H4.
      eapply vac_comp; auto.
    + rewrite HP'4.
      assert ((l211 ++ [u]) ++ l212 ≡[P] D1 ++ [u]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem1 in H2; destruct H2.
      assert ((l221 ++ [dual u]) ++ l222 ≡[P] D2 ++ [dual u]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem2 in H4; destruct H4.
      eapply vac_comp; auto.
  - rewrite H0 in H1. apply Permutation_rel_split2 in H1.
    destruct H1 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + assert ((l1' ++ [t1] ++ [t2]) ++ D2 ≡[P] D' ++ [t1] ++ [t2]).
      {convertTactics.convert_multisetperm. permutation_solver. }
      apply IHvac_ephem in H1. destruct H1.
      split; auto.
      rewrite HP1.
      eapply vac_tensor; eauto. reflexivity.
    + assert (D1 ++ (l2' ++ [t1] ++ [t2]) ≡[P] D' ++ [t1] ++ [t2]).
      {convertTactics.convert_multisetperm. permutation_solver. }
      apply IHvac_ephem in H1. destruct H1.
      split; auto.
      rewrite HP1.
      eapply vac_tensor; eauto. reflexivity.
  - rewrite H1 in H2. rewrite app_assoc in H2. apply Permutation_rel_split2 in H2.
    destruct H2 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + apply Permutation_rel_split4 in HP2. destruct HP2 as (l211 & l212 & l221 & l222 & HP'1 & HP'2 & HP'3 & HP'4).
      assert ((l211 ++ [t1]) ++ l212 ≡[P] D1 ++ [t1]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem1 in H2. destruct H2.
      assert (l222 ++ (l221 ++ [t2]) ≡[P] D2 ++ [t2]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem2 in H4. destruct H4.
      split.
      ++ rewrite HP1, HP'3, <- app_assoc. eapply vac_par.
         3: {reflexivity. }
         +++ assumption.
         +++ assumption.
      ++ rewrite HP'4. eapply vac_comp; auto.
    + apply Permutation_rel_split4 in HP2. destruct HP2 as (l211 & l212 & l221 & l222 & HP'1 & HP'2 & HP'3 & HP'4).
      assert (l211 ++ (l212 ++ [t1]) ≡[P] D1 ++ [t1]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem1 in H2. destruct H2.
      assert (l221 ++ (l222 ++ [t2]) ≡[P] D2 ++ [t2]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem2 in H4. destruct H4.
      split.
      ++ rewrite HP'3. eapply vac_comp; auto.
      ++ rewrite HP1, HP'4, <- app_assoc. eapply vac_par.
         3: {reflexivity. }
         +++ assumption.
         +++ assumption.
  - apply Permutation_rel_split2 in H0.
    destruct H0 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + apply IHvac_ephem in HP2. destruct HP2. split; intuition.
      rewrite HP1. apply vac_bang. auto.
    + apply IHvac_ephem in HP2. destruct HP2. split;  intuition.
      rewrite HP1. apply vac_bang. auto.
  (* - apply Permutation_rel_split2 in H1. *)
  (*   destruct H1 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]]. *)
  (*   + assert ((l1' ++ [t]) ++ D2 ≡[P] D). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem in H1. destruct H1. *)
  (*     split; intuition. *)
  (*     rewrite HP1. eapply vac_ques; try reflexivity; eauto. *)
  (*   + assert (D1 ++ (l2' ++ [t]) ≡[P] D). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac_ephem in H1. destruct H1. *)
  (*     split; intuition. *)
  (*     rewrite HP1. eapply vac_ques; try reflexivity; eauto. *)
  - apply Permutation_rel_split4 in H1. destruct H1 as (l211 & l212 & l221 & l222 & HP'1 & HP'2 & HP'3 & HP'4).
    symmetry in HP'1. apply IHvac_ephem1 in HP'1. destruct HP'1.
    symmetry in HP'2. apply IHvac_ephem2 in HP'2. destruct HP'2.
    split;  try rewrite HP'3; try rewrite HP'4; apply vac_comp; auto.
  - rewrite <- H in H1. apply IHvac_ephem in H1. auto.
Qed.

Lemma vac_ephem_vacuous_ephem_inj : forall D, vac_ephem D -> vacuous_ephem D.
Proof.
  intros D HV. induction HV.
  - apply vacuous_ephem_empty.
  - rewrite H. apply vacuous_ephem_app_iff; intuition.
    apply vacuous_ephem_one.
  - apply vacuous_ephem_app_iff in IHHV1, IHHV2.
    rewrite H.
    apply vacuous_ephem_app_iff. intuition.
  - rewrite H. apply vacuous_ephem_app_iff in IHHV as (HV1 & HV2). apply vacuous_ephem_app_iff in HV2 as (HV2 & HV3). apply vacuous_ephem_app_iff; split; intuition.
    apply vacuous_ephem_singleton. apply vacuous_ephem_singleton in HV2, HV3. constructor; auto.
  - rewrite H. apply vacuous_ephem_app_iff in IHHV1, IHHV2. destruct IHHV1, IHHV2.
    repeat (apply vacuous_ephem_app_iff; split); auto.
    apply vacuous_ephem_singleton. apply vacuous_ephem_singleton in H1, H3. constructor; auto.
  - apply vacuous_ephem_app_iff; intuition.
    apply vacuous_ephem_singleton. constructor.
  (* - rewrite H in IHHV. apply vacuous_ephem_app_iff in IHHV. destruct IHHV. *)
  (*   apply vacuous_ephem_app_iff; intuition. *)
    (* apply vacuous_ephem_singleton. apply vacuous_ephem_singleton in H1. constructor; auto. *)
  - apply vacuous_ephem_app_iff; intuition.
  - rewrite <- H; auto.
Qed.

Lemma vacuous_ephem_vac_ephem_inj : forall D, vacuous_ephem D -> vac_ephem D.
Proof.
  intros D.
  induction D; intros.
  - constructor.
  - apply vacuous_ephem_cons_iff in H. destruct H.
    replace (a :: D) with ([a] ++ D) by auto.
    constructor; auto.
    clear IHD H0.
    induction H.
    + eapply vac_one.
      2: {apply vac_empty. }
      reflexivity.
    + eapply vac_tensor.
      2: {assert ([t1 ⊗ t2] ≡[P] [] ++ [t1 ⊗ t2]). reflexivity. eassumption. }
      repeat apply vac_comp; try constructor; auto.
    + eapply vac_par.
      3: {assert ([t_par t1 t2] ≡[P] [] ++ [] ++ [t_par t1 t2]). reflexivity. eassumption. }
      ++ auto.
      ++ auto.
    + eapply vac_perm.
      assert ([] ++ [[!] t] ≡[P] [[!]t]) by reflexivity. eassumption.
      eapply vac_bang.
      eapply vac_empty.
    (* + eapply vac_perm. *)
    (*   assert ([] ++ [[?] t] ≡[P] [[?] t]) by reflexivity. eassumption. *)
    (*   eapply vac_ques. *)
    (*   reflexivity. *)
    (*   auto. *)
Qed.

Corollary vacuous_ephem_vac_ephem_iff : forall D, vacuous_ephem D <-> vac_ephem D.
Proof.
  intros; split; try apply vacuous_ephem_vac_ephem_inj; try apply vac_ephem_vacuous_ephem_inj.
Qed.

Section PF.

  Context (PID : typ -> Prop).
  Context (PCUT : typ -> Prop).

  Reserved Notation " c , G , D '⊢pf' " (at level 101, D at level 100, G at level 100).

  Inductive pf : nat -> ctx -> ctx -> Prop :=
  | pf_id : forall c G (u:typ),
      PID u ->
      c ⊢ u wf ->
      wf_ctx c G ->
      c , G , [u] ++ [dual u] ⊢pf

(* absorbtion *)                
| pf_absorb : forall c G G' t D,
    wf_ctx c (G ++ [t]) ->
    G' ≡[P] (G ++ [t]) ->
    c , G' , D ++ [t] ⊢pf ->
             c , G' , D ⊢pf       
                        
| pf_cut : forall c G D1 D2 D u,
    PCUT u ->
    c ⊢ u wf ->
    c , G , D1 ++ [u] ⊢pf ->
            c , G , D2 ++ [dual u] ⊢pf ->
                    D ≡[P] (D1 ++ D2) ->                    
                    c , G , D ⊢pf         
                              
| pf_bot : forall c G,
    wf_ctx c G ->    
    c , G , [ [⊥] ] ⊢pf

| pf_one : forall c G D D',
    c , G , D' ⊢pf ->
            D ≡[P] (D' ++ [ [1] ]) ->        
            c , G , D ⊢pf
                      
| pf_tensor : forall c G D D' t u,
    c , G , D' ++ [t] ++ [u] ⊢pf ->
            D ≡[P] (D' ++ [ t ⊗ u ]) ->
            c , G , D ⊢pf

| pf_par : forall c G D1 D2 D t u,
    c , G , D1 ++ [t] ⊢pf ->
            c , G , D2 ++ [u] ⊢pf ->
                    D ≡[P] (D1 ++ D2 ++ [ t ∥ u ]) ->
                    c , G , D ⊢pf

| pf_bang : forall c G D1 D t,
    c , G ++ [t] , D1 ⊢pf ->
                   D ≡[P] D1 ++ [ [!]t ] ->               
                   c , G , D ⊢pf

| pf_ques : forall c G t,
    c , G , [t] ⊢pf ->
            c , G , [ [?]t ] ⊢pf

| pf_forall : forall c G D1 D u t,
    c ⊢ u wf ->
    c , G , D1 ++ [typ_subst c u t] ⊢pf ->
            D ≡[P] D1 ++ [ [forall] t ] ->
            c , G , D  ⊢pf           

| pf_exists : forall c G D1 D u,
    (1 + c) , (shift_ctx c 1 G) , (shift_ctx c 1 D1) ++ [u] ⊢pf ->
                                  D ≡[P] D1 ++ [ [exists] u ] ->
                                  c , G , D ⊢pf 

  (*
| pf_mix : forall c G D1 D2,
   c ; G ; D1 ⊢ok ->
   c ; G ; D2 ⊢ok ->
   c ; G ; D1 ++ D2 ⊢ok

             
               
| pf_perm : forall c G1 G2 D1 D2,
    Permutation_rel G1 G2 ->
    Permutation_rel D1 D2 ->
    c ; G1 ; D1 ⊢ok ->
    c ; G2 ; D2 ⊢ok
   *)               
  where
  "c , G , D '⊢pf'" := (pf c G D).

Context (PID_dual : forall u, PID u <-> PID (dual u)).

(* pf_ind: *)
(*   ∀ P0 : nat → ctx → ctx → Prop, *)
(*     (∀ (c : nat) (G : ctx) (u : typ), PID u → c ⊢ u wf → wf_ctx c G → P0 c G ([u] ++ [dual u])) *)
(*     → (∀ (c : nat) (G G' : list typ) (t : typ) (D : list typ), wf_ctx c (G ++ [t]) → G' ≡[ P] G ++ [t] → (c, G', D ++ [t] ⊢pf) → P0 c G' (D ++ [t]) → P0 c G' D) *)
(*       → (∀ (c : nat) (G : ctx) (D1 D2 D : list typ) (u : typ), *)
(*            PCUT u → c ⊢ u wf → (c, G, D1 ++ [u] ⊢pf) → P0 c G (D1 ++ [u]) → (c, G, D2 ++ [dual u] ⊢pf) → P0 c G (D2 ++ [dual u]) → D ≡[ P] D1 ++ D2 → P0 c G D) *)
(*         → (∀ (c : nat) (G : ctx), wf_ctx c G → P0 c G [[⊥]]) *)
(*           → (∀ (c : nat) (G : ctx) (D : list typ) (D' : ctx), (c, G, D' ⊢pf) → P0 c G D' → D ≡[ P] D' ++ [[1]] → P0 c G D) *)
(*             → (∀ (c : nat) (G : ctx) (D D' : list typ) (t u : typ), (c, G, D' ++ [t] ++ [u] ⊢pf) → P0 c G (D' ++ [t] ++ [u]) → D ≡[ P] D' ++ [t ⊗ u] → P0 c G D) *)
(*               → (∀ (c : nat) (G : ctx) (D1 D2 D : list typ) (t u : typ), *)
(*                    (c, G, D1 ++ [t] ⊢pf) → P0 c G (D1 ++ [t]) → (c, G, D2 ++ [u] ⊢pf) → P0 c G (D2 ++ [u]) → D ≡[ P] D1 ++ D2 ++ [t ∥ u] → P0 c G D) *)
(*                 → (∀ (c : nat) (G : list typ) (D1 : ctx) (D : list typ) (t : typ), (c, G ++ [t], D1 ⊢pf) → P0 c (G ++ [t]) D1 → D ≡[ P] D1 ++ [[!] t] → P0 c G D) *)
(*                   → (∀ (c : nat) (G : ctx) (t : typ), (c, G, [t] ⊢pf) → P0 c G [t] → P0 c G [[?] t]) *)
(*                     → (∀ (c : nat) (G : ctx) (D1 D : list typ) (u t : typ), *)
(*                          c ⊢ u wf → (c, G, D1 ++ [typ_subst c u t] ⊢pf) → P0 c G (D1 ++ [typ_subst c u t]) → D ≡[ P] D1 ++ [[forall] t] → P0 c G D) *)
(*                       → (∀ (c : nat) (G D1 D : list typ) (u : typ), *)
(*                            (1 + c, shift_ctx c 1 G, shift_ctx c 1 D1 ++ [u] ⊢pf) → P0 (1 + c) (shift_ctx c 1 G) (shift_ctx c 1 D1 ++ [u]) → D ≡[ P] D1 ++ [[exists] u] → P0 c G D) *)
(*                         → ∀ (n : nat) (c c0 : ctx), (n, c, c0 ⊢pf) → P0 n c c0 *)

Lemma pf_perm : forall c G1 G2 D1 D2
    (HPG: P G1 G2) 
    (HPD: P D1 D2)
    (HWF: c , G1 , D1 ⊢pf),
    c , G2 , D2 ⊢pf.
  Proof.
    intros. revert G2 D2 HPG HPD.
    induction HWF; intros.
    - apply Permutation_symmetric in HPD.
      apply Permutation_doubleton in HPD.
      destruct HPD; subst.
      + apply pf_id; auto. eapply wf_ctx_Permutation_inj; eauto.
      + rewrite <- (dual_involutive u) at 2.
        apply pf_id. rewrite <- PID_dual. assumption.
        apply wf_typ_dual. assumption. eapply wf_ctx_Permutation_inj; eauto.
    - specialize (IHHWF G2 (D2 ++ [t]) HPG).
      destruct H0.
      eapply pf_absorb.
      3: { apply IHHWF. eapply Permutation_append. apply HPD.  apply Permutation_reflexive. }
      apply H. eexists; auto. eapply Permutation_transitive. eapply Permutation_symmetric. apply HPG. apply x. 
    - destruct H1.
      specialize (IHHWF1 G2 (D1 ++ [u]) HPG).
      specialize (IHHWF2 G2 (D2 ++ [dual u]) HPG).
      assert (P (D1 ++ D2) D0).
      { convert_multiset. permutation_solver. (* eapply Permutation_transitive. eapply Permutation_symmetric. apply x. assumption.  *)}
      eapply pf_cut; eauto.
      apply IHHWF1.
      apply Permutation_reflexive.
      apply IHHWF2.
      apply Permutation_reflexive.
      convert_multisetperm; permutation_solver.
      (* eexists. apply Permutation_symmetric. assumption. auto. *)
    - apply Permutation_symmetric in HPD. apply Permutation_singleton in HPD. subst.
      apply pf_bot. eapply wf_ctx_Permutation_inj. apply HPG; auto. assumption.
    - destruct H as [H _].
      apply Permutation_symmetric in H. apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pf_one. eapply IHHWF; eassumption. (* assumption. apply HPD2. *)
      convert_multisetperm; permutation_solver.
      (* eexists. eapply perm_comp. eapply Permutation_symmetric. apply HPD. apply HPD1. auto. *)
    - destruct H as [H _].
      apply Permutation_symmetric in H. apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pf_tensor. eapply IHHWF. assumption.
      eapply Permutation_append. apply HPD2. apply Permutation_reflexive.
      convert_multisetperm; permutation_solver.
      (* eexists. eapply perm_comp. eapply Permutation_symmetric. apply HPD. apply HPD1. auto. *)
    - destruct H as [H _].
      apply Permutation_symmetric in H. rewrite app_assoc in H.
      apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pf_par. apply IHHWF1. assumption. apply Permutation_reflexive.
      apply IHHWF2; auto. apply Permutation_reflexive. 
      convert_multisetperm. permutation_solver.
      (* eexists; [|auto]. eapply Permutation_transitve. eapply Permutation_symmetric. apply HPD. *)
      (* rewrite app_assoc. eapply perm_comp. apply HPD1. *)
      (* eapply perm_plus. apply Permutation_symmetric. assumption. apply perm_id. *)
    - eapply pf_bang.
      eapply IHHWF.
      eapply Permutation_append. assumption. apply Permutation_reflexive.
      apply Permutation_reflexive.
      convert_multisetperm; permutation_solver.

      (* 2: { destruct H as [H _]. econstructor; auto. *)
      (*      eapply perm_comp. apply Permutation_symmetric. apply HPD. apply H. } *)
      (* apply perm_id. *)
    - apply Permutation_symmetric in HPD. apply Permutation_singleton in HPD.
      subst.
      apply pf_ques. apply IHHWF. assumption. apply Permutation_reflexive.
    - eapply pf_forall.
      + apply H.
      + eapply IHHWF. assumption.
        apply Permutation_reflexive.
      + convert_multisetperm; permutation_solver.
        (* destruct H0 as [H0 _]. *)
        (* constructor; auto. *)
        (* eapply perm_comp. apply Permutation_symmetric. apply HPD. *)
        (* apply H0. *)
    - eapply pf_exists.
      eapply IHHWF.
      + apply Permutation_shift_ctx. assumption.
      + apply Permutation_reflexive.
      + convert_multisetperm; permutation_solver.
        (* destruct H as [H _]. *)
        (* constructor; auto. *)
        (* eapply perm_comp. apply Permutation_symmetric. apply HPD. *)
        (* apply H. *)
Qed.      

  Corollary pf_perm_rel : forall c G1 G2 D1 D2
    (HPG: G1 ≡[P] G2) 
    (HPD: D1 ≡[P] D2)
    (HWF: c , G1 , D1 ⊢pf),
    c , G2 , D2 ⊢pf.
  Proof.
    intros.
    normalize_auxH.
    eapply pf_perm; eauto.
  Qed.

Lemma pf_exchange : forall c G D1 D2,
    pf c G (D1 ++ D2) ->
    pf c G (D2 ++ D1).
Proof.
  intros.
  eapply pf_perm; eauto.
  - constructor; auto. 
  - apply Permutation_exchange.
Qed.


Ltac WF_CTX :=
  repeat
    match goal with
    | H : ?C ≡[P] ?D |- _ => destruct H as [H _]
    | H : P ?C ?D |- wf_ctx ?A ?C =>
        apply Permutation_symmetric in H; apply (wf_ctx_Permutation_inj _ _ _ H); clear H
    | H : wf_ctx ?C (?D ++ ?E) |- _ => apply wf_ctx_app in H; destruct H
    | _ : _ |- wf_ctx ?C (?D ++ ?E) => apply wf_ctx_app; split
    | H : wf_ctx ?C [?U] |- _ => apply wf_ctx_single in H
    | _ : _ |- wf_ctx ?C [?U] => apply wf_ctx_single
    | H : wf_ctx (1 + ?C) (shift_ctx ?C 1 ?D) |- _ => apply shift_ctx_strengthen in H
    end.  


Lemma pf_wf_typ : forall c G D,
    pf c G D -> (wf_ctx c G /\ wf_ctx c D).
Proof.
  intros c G D HP.
  induction HP; intuition; WF_CTX; intuition.
  - apply wf_typ_dual. auto.
  - constructor.
    replace (1 + c) with (c + 1) by lia.
    eapply typ_subst_wf_inversion.
    eauto.
Qed.    

Lemma pf_weakening : forall D G G1 G2 c, G ≡[P] G1 ++ G2 -> wf_ctx c G2 -> pf c G1 D -> pf c G D.
Proof.
  intros D G G1 G2 c HG HW HP.
  revert G G2 HG HW.
  induction HP; intros.
  - apply pf_id; auto.
    eapply wf_ctx_app_perm_iff in HG.
    apply HG; intuition.
  - 
    assert ((G ++ [t]) ++ G2 ≡[P] (G ++ G2) ++ [t]).
    {convertTactics.convert_multisetperm. permutation_solver. }
    eapply pf_absorb.
    + assert (wf_ctx c ((G ++ G2) ++ [t])).
      {
        apply (wf_ctx_perm_iff H1).
        apply wf_ctx_app; intuition.
      }
      apply H2.
    + rewrite H0 in HG.
      eapply transitivity; eauto.
    + eapply IHHP; eauto.
  - eapply pf_cut; try eapply IHHP1; try eapply IHHP2; eassumption.
  - apply pf_bot.
    apply (wf_ctx_app_perm_iff HG). intuition.
  - eapply pf_one; eauto.
  - eapply pf_tensor; eauto.
  - eapply pf_par.
    + eapply IHHP1.
      ++ eauto.
      ++ eauto.
    + eapply IHHP2.
      ++ eauto.
      ++ eauto.
    + eauto.
  - eapply pf_bang.
    + eapply IHHP.
      ++ assert (G0 ++ [t] ≡[P] (G ++ [t]) ++ G2).
         {
           convertTactics.convert_multisetperm. permutation_solver.
         }
         eassumption.
      ++ eassumption.
    + assumption.
  - eapply pf_ques; eauto.
  - eapply pf_forall; try eassumption.
    eapply IHHP; eassumption.
  - eapply pf_exists.
    + apply IHHP with (G2 := shift_ctx c 1 G2).
      ++ 
        apply (Permutation_rel_shift_ctx 1 c) in HG.
        rewrite shift_ctx_app in HG.
        assumption.
      ++ apply wf_shift_ctx; assumption.
    + assumption.
Qed.

Lemma pf_absorb_append : forall D D1 D2 G c, wf_ctx c (G ++ D2) -> D ≡[P] D1 ++ D2 -> pf c (G ++ D2) D -> pf c (G ++ D2) D1.
Proof.
  intros D D1 D2 G c HW HP HG.
  normalize_auxH.
  revert D D1 G c HW HP HG.
  induction D2.
  - intros.
    rewrite app_nil_r in *.
    eapply pf_perm.
    + apply Permutation_reflexive.
    + apply HP.
    + apply HG.
  - intros.
    assert (P ((G ++ [a]) ++ D2) (G ++ a :: D2)).
    {
      convertTactics.convert_multiset. permutation_solver.
    }
    apply (wf_ctx_Permutation_surj _ _ _ X) in HW.
    assert (P D ((D1 ++ [a]) ++ D2)).
    {
      convertTactics.convert_multiset. permutation_solver.
    }
    assert ((c, (G ++ [a]) ++ D2, D ⊢pf)).
    {
      eapply pf_perm.
      - apply Permutation_symmetric. eassumption.
      - apply Permutation_reflexive.
      - assumption.
    }
    specialize (IHD2 _ _ _ _ HW X0 H).
    eapply pf_absorb.
    + apply wf_ctx_app in HW; destruct HW as (HW1 & HW2).
      apply wf_ctx_app in HW1; destruct HW1 as (HW1 & HW3).
      assert (wf_ctx c (G ++ D2)) by (apply wf_ctx_app; auto).
      apply wf_ctx_app; split.
      ++ apply H0.
      ++ apply HW3.
    + convertTactics.convert_multisetperm. permutation_solver.
    + eapply pf_perm.
      ++ eassumption.
      ++ apply Permutation_reflexive.
      ++ eassumption.
Qed.

Corollary pf_promote_append : forall D D1 D2 G c, D ≡[P] D1 ++ D2 -> wf_ctx c D2 -> pf c G D -> pf c (G ++ D2) D1.
Proof.
  intros.
  eapply pf_absorb_append.
  - apply pf_wf_typ in H1 as (H1 & _).
    apply wf_ctx_app; intuition.
  - eassumption.
  - eapply pf_weakening.
    + reflexivity.
    + assumption.
    + assumption.
Qed.

Corollary pf_promote_cons : forall D D' G c t, D ≡[P] D' ++ [t] -> c ⊢ t wf -> pf c G D -> pf c (G ++ [t]) D'.
Proof.
  intros.
  eapply pf_promote_append.
  - eassumption.
  - apply pf_wf_typ in H1. destruct H1 as (_ & H1).
    apply (wf_ctx_perm_iff H), wf_ctx_app in H1.
    intuition.
  - assumption.
Qed.

Corollary wf_ctx_contract : forall c G t, wf_ctx c (G ++ [t] ++ [t]) -> wf_ctx c (G ++ [t]).
Proof.
  intros.
  apply wf_ctx_app.
  apply wf_ctx_app in H. destruct H.
  apply wf_ctx_app in H0. destruct H0.
  intuition.
Qed.

(* Lemma pf_contract : forall D G' c t, pf c (G' ++ [t] ++ [t]) D -> pf c (G' ++ [t]) D. *)
(* Proof. *)
(*   intros D G' c t HG. *)
(*   pose proof HG as HG'. *)
(*   apply pf_wf_typ in HG'; destruct HG' as (HG'1 & HG'2). *)
  

(* Corollary Permutation_rel_length : forall l1 l2, l1 ≡[P] l2 ->  length l1 = length l2. *)
(* Proof. *)
(*   intros. *)
(*   normalize_auxH. *)
(*   apply (@SigPerm.Permutation_length _ _ _ P _ _). *)
(*   auto. *)
(* Qed. *)

(* Arguments Permutation_rel_split2 {_ _ _ _ _ _}. *)
(* Arguments Permutation_rel_singleton {_ _ _ _ _ _}. *)

(* Corollary Permutation_singleton_nil : forall l a b, P (l ++ [a]) [b] -> (l = [])%type * (a = b)%type. *)
(* Proof. *)
(*   intros. *)
(*   apply SigPerm.Permutation_singleton in X. *)
(*   destruct l. *)
(*   - injection X; intros ->. *)
(*     intuition. *)
(*   - destruct l; discriminate. *)
(* Qed. *)

(* Corollary Permutation_rel_singleton_nil : forall l a b, l ++ [a] ≡[P] [b] -> l = [] /\ a = b. *)
(* Proof. *)
(*   intros. *)
(*   normalize_auxH. *)
(*   apply Permutation_singleton_nil in H as (H1 & H2). *)
(*   intuition. *)
(* Qed. *)

Ltac normalize_wf_ctxH :=
  repeat (match goal with
  | [ H : wf_ctx ?c (?l1 ++ ?l2) |- _ ] => apply wf_ctx_app in H; destruct H
  end).

Lemma pf_contract_perm_rel : forall D G G' c t, G ≡[P] G' ++ [t] ++ [t] -> pf c G D -> pf c (G' ++ [t]) D.
Proof.
  intros D G G' c t HP HG. 
  revert G' t HP.
  induction HG; intros.
  - apply pf_id; try assumption.
    apply (wf_ctx_perm_iff HP) in H1.
    apply wf_ctx_contract in H1.
    assumption.
  - rewrite HP in H0.
    replace (G'0 ++ [t0] ++ [t0]) with ((G'0 ++ [t0]) ++ [t0]) in H0 by (rewrite <- app_assoc; auto).
    apply Permutation_rel_split2 in H0.
    destruct H0 as [[l1 [HP1 HP2]] | [l2 [HP1 HP2]]].
    + apply Permutation_rel_split2 in HP1.
      destruct HP1 as [[l3 [HP3 HP4]] | [l4 [HP3 HP4]]].
      ++ rewrite HP3 in HP.
         specialize (IHHG _ _ HP).
         eapply pf_perm_rel.
         {rewrite HP3.
          reflexivity. }
         {reflexivity. }
         eapply pf_absorb.
         +++ 
           assert (wf_ctx c ((l3 ++ [t0]) ++ [t])).
           {
             normalize_wf_ctxH.
             apply (wf_ctx_perm_iff HP2) in H; normalize_wf_ctxH.
             apply (wf_ctx_perm_iff HP4) in H; normalize_wf_ctxH.
             do 2 (try (apply wf_ctx_app; split)); assumption.
           }
           apply H0.
         +++ 
           convertTactics.convert_multisetperm. permutation_solver.
         +++ 
           assumption.
      ++ symmetry in HP3. apply Permutation_rel_singleton_nil in HP3 as [HP3 HP5]. subst.
         eapply pf_absorb.
         2: {reflexivity. }
         +++ normalize_wf_ctxH.
             apply (wf_ctx_perm_iff HP2) in H. normalize_wf_ctxH.
             apply (wf_ctx_perm_iff HP4) in H. normalize_wf_ctxH.
             apply wf_ctx_app; intuition.
         +++ apply IHHG; auto.
    + symmetry in HP1.
      apply Permutation_rel_singleton_nil in HP1 as (-> & ->).
      eapply pf_absorb.
      ++ normalize_wf_ctxH.
         apply (wf_ctx_perm_iff HP2) in H.
         normalize_wf_ctxH.
         apply wf_ctx_app; split.
         +++
           apply H.
         +++ 
           apply H2.
      ++ reflexivity.
      ++ apply IHHG; auto.
  - eapply pf_cut.
    + apply H.
    + assumption.
    + auto.
    + auto.
    + assumption.
  - apply pf_bot.
    apply (wf_ctx_perm_iff HP) in H. normalize_wf_ctxH.
    apply wf_ctx_app. intuition.
  - eapply pf_one; auto.
  - eapply pf_tensor; auto.
  - eapply pf_par.
    + apply IHHG1; auto.
    + apply IHHG2; auto.
    + assumption.
  - eapply pf_bang.
    2 : {eassumption. }
    eapply pf_perm_rel.
    + assert ((G' ++ [t]) ++ [t0] ≡[P] (G' ++ [t0]) ++ [t]).
      {
        convertTactics.convert_multisetperm. permutation_solver.
      }
      apply H0.
    + reflexivity.
    + apply IHHG.
      convertTactics.convert_multisetperm. permutation_solver.
  - eapply pf_ques; auto.
  - eapply pf_forall; eauto.
  - eapply pf_exists.
    2: { eassumption. }
    rewrite shift_ctx_app.
    simpl.
    apply IHHG.
    assert (shift_ctx c 1 G' ++ [shift_typ c 1 t] ++ [shift_typ c 1 t] = shift_ctx c 1 (G' ++ [t] ++ [t])).
    {
      do 2 rewrite shift_ctx_app; auto.
    }
    rewrite H0.
    apply Permutation_rel_shift_ctx.
    assumption.
Qed.

(* Lemma pf_contract : forall D G G' c t, G ≡[P] G' ++ [t] ++ [t] -> pf c G D -> pf c (G' ++ [t]) D. *)
Corollary pf_contract : forall D G c t, pf c (G ++ [t] ++ [t]) D -> pf c (G ++ [t]) D.
Proof.
  intros.
  eapply pf_contract_perm_rel.
  - reflexivity.
  - assumption.
Qed.

Corollary pf_bang_D : forall D G c t, pf c G (D ++ [t]) -> pf c G (D ++ [[!]t]).
Proof.
  intros.
  eapply pf_bang.
  2: {reflexivity. }
  eapply pf_promote_cons.
  - reflexivity.
  - apply pf_wf_typ in H as (_ & H).
    normalize_wf_ctxH.
    unfold wf_ctx in H0.
    apply H0.
    unfold In; intuition.
  - assumption.
Qed.

Lemma wf_ctx_bang_typ : forall c t, wf_ctx c [[!]t] <-> c ⊢ t wf.
Proof.
  intros; split; intros.
  - assert (In ([!]t) [[!]t]) by apply in_eq.
    apply H in H0.
    inversion H0; auto.
  - unfold wf_ctx.
    intros.
    apply In_cons_iff in H0. destruct H0.
    + subst.
      constructor; auto.
    + inversion H0.
Qed.

Lemma wf_ctx_ques_typ : forall c t, wf_ctx c [[?]t] <-> c ⊢ t wf.
Proof.
  intros; split; intros.
  - assert (In ([?]t) [[?]t]) by apply in_eq.
    apply H in H0.
    inversion H0; auto.
  - unfold wf_ctx.
    intros.
    apply In_cons_iff in H0. destruct H0.
    + subst.
      constructor; auto.
    + inversion H0.
Qed.

(*
(G ++ [t] ++ [!t] ++ [!!t]); D
(G ++ [t] ++ [!t]); D ++ [!!t]
------------------------------
(G ++ [t]); D ++ [!t] ⊢
-----------------------?
(G ++ [t]); D ⊢
------------------
G; (D ++ [t]) ⊢
------------------
G; (D ++ [!t]) ⊢
----------------------
 *)

Lemma pf_absorb_bang : forall D G G' c t, G ≡[P] G' ++ [t] -> pf c G D -> pf c G (D ++ [[!]t]).
Proof.
  intros.
  eapply pf_bang.
  2: {reflexivity. }
  eapply pf_perm_rel.
  - rewrite H.
    reflexivity.
  - reflexivity.
  - pose proof pf_perm_rel.
    assert (D ≡[P] D) by reflexivity.
    specialize (H1 _ _ _ _ _ H H2 H0).
    eapply pf_weakening.
    + reflexivity.
    + apply pf_wf_typ in H1 as (H1 & _).
      normalize_wf_ctxH; auto.
    + assumption.
Qed.

Lemma pf_bang_inv : forall D D' G c t, D ≡[P] D' ++ [[!]t] -> pf c (G ++ [t]) D -> pf c (G ++ [t]) D'.
Proof.
  (* intros D D' G c t HP HG. *)
  (* revert D' HP. *)
  (* induction HG; intros. *)
  (* --  *)
Abort.


Lemma pf_cf_bang_promote: forall D G G' c t, G ≡[P] G' ++ [[!]t] -> pf c G D -> pf c (G' ++ [t]) D.
Proof.
  (* intros. *)
  (* assert (D ≡[P] D) by reflexivity. *)
  (* apply (pf_perm_rel _ _ _ _ _ H H1) in H0. *)
  (* eapply pf_bang_inv. *)
  (* reflexivity. *)
  (* eapply pf_weakening. *)
  
  (* eapply pf_absorb. *)
  (*   +  *)
  (*   apply pf_wf_typ in H0 as (H0 & _). *)
  (*   normalize_wf_ctxH. *)
  (*   apply wf_ctx_bang_typ; auto. *)
  (* -  *)








  
  (* intros D G G' c t HP HG. *)
  (* revert G' t HP. *)
  (* induction HG; intros. *)
  (* - eapply pf_id; try assumption. *)
  (*   normalize_wf_ctxH. apply (wf_ctx_perm_iff HP) in H1. *)
  (*   normalize_wf_ctxH. *)
  (*   apply wf_ctx_app. intuition. *)
  (*   unfold wf_ctx in *. *)
  (*   assert (In ([!]t) [[!]t]) by (apply in_eq). *)
  (*   apply H2 in H3. *)
  (*   inversion H3. *)
  (*   intros. *)
  (*   apply In_cons_iff in H7. destruct H7; subst; auto. *)
  (*   inversion H7. *)
  (* - eapply pf_absorb. *)
   



  (* intros. *)
  (* eapply pf_promote_cons. *)
  (* - auto. *)
  (* - reflexivity. *)
  (* - admit. *)
  (* - *)
Abort.

#[local] Hint Constructors pf : core.

Ltac normalize_wf_ctxH' :=
  repeat (match goal with
  | [ H: wf_ctx ?C1 ?D /\ wf_ctx ?C2 ?E |- _ ] => destruct H
  | [ H: wf_ctx ?C1 (?D ++ ?E) |- _ ] => apply wf_ctx_app in H
  | [ H: wf_ctx ?C1 (?a :: ?D) |- _ ] => replace (a :: D) with ([a] ++ [D]) in H by auto
  | [ H: wf_ctx ?C1 [?a] |- _ ] => apply wf_ctx_single in H
  | [ H: wf_typ ?C1 (dual ?a) |- _ ] => apply wf_typ_dual_inv in H
  | [ H: wf_typ ?C1 ([!] ?a) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 ([?] ?a) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 (?a ⊗ ?b) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 (t_par ?a ?b) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 ([forall] ?t) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 ([exists] ?t) |- _ ] => inversion H; clear H; subst
  end).

Ltac normalize_wf_ctx :=
  repeat
    (match goal with
     | [ |- wf_ctx ?C1 ?D /\ wf_ctx ?C2 ?E ] => split
     | [ |- wf_ctx ?C1 (?D ++ ?E) ] => apply wf_ctx_app
     | [ |- wf_ctx ?C1 (?a :: ?D) ] => replace (a :: D) with ([a] ++ [D]) by auto
     | [ |- wf_ctx ?C1 [?a] ] => apply wf_ctx_single
     | [ |- wf_typ ?C1 (dual ?a) ] => apply wf_typ_dual
     | [ |- wf_typ ?C1 ([!] ?a) ] => constructor 
     | [ |- wf_typ ?C1 ([?] ?a) ] => constructor
     | [ |- wf_typ ?C1 (?a ⊗ ?b) ] => constructor
     | [ |- wf_typ ?C1 (t_par ?a ?b) ] => constructor
     | [ |- wf_typ ?C1 ([forall] ?t) ] => constructor
     | [ |- wf_typ ?C1 ([exists] ?t) ] => constructor
     end
    ; eauto).

Ltac normalize_wf_ctx_more :=
  repeat (match goal with
  | [ H: pf ?PID ?PCUT ?c ?G ?D |- _ ] => apply pf_wf_typ in H
  end).

Ltac wf_ctx_solver :=
  normalize_wf_ctx_more; normalize_wf_ctxH'; normalize_wf_ctx; auto.

Section BOTINV.
  Context (PID_bot : PID ([⊥])).
  Lemma pf_bottom_inv : forall c G D D',
      D ≡[P] D' ++ [[⊥]] ->
      pf c G D ->
      vac_ephem D'.
  Proof.
    intros c G D D' HP HG.
    revert D' HP.
    induction HG; intros.
    - apply Permutation_rel_split2 in HP.
      destruct HP as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
      + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1).
        rewrite <- HP1 in *.
        rewrite <- HP2. simpl.
        eapply vac_one.
        2: {apply vac_empty. }
        reflexivity.
      + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1).
        rewrite dual_swap_iff in HP1. subst.
        rewrite <- HP2. simpl.
        eapply vac_one.
        2: {apply vac_empty. }
        reflexivity.
    - assert (D ++ [t] ≡[P] (D' ++ [t]) ++ [[⊥]]). {convertTactics.convert_multisetperm. permutation_solver. }
      apply IHHG in H1.
      apply vac_ephem_app in H1; intuition.
    - rewrite H1 in HP. apply Permutation_rel_split2 in HP.
      admit.                    (* I don't think it is possible for this one *)
    - symmetry in HP. apply Permutation_rel_singleton_nil in HP as (-> & _).
      apply vac_empty.
    - rewrite H in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      apply IHHG in HP1. rewrite HP2. apply vac_comp.
      + rewrite <- HP3. auto.
      + eapply vac_one. rewrite app_nil_l. reflexivity. apply vac_empty.
    - rewrite H in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      assert (D' ++ [t] ++ [u] ≡[P] (l2' ++ [t] ++ [u]) ++ [[⊥]]). {convertTactics.convert_multisetperm. permutation_solver. }
      apply IHHG in H0. apply vac_ephem_app in H0 as (HV1 & HV2). apply vac_ephem_app in HV2 as (HV2 & HV3).
      rewrite HP2. apply vac_comp; auto.
      eapply vac_tensor. 2: {rewrite app_nil_l. reflexivity. } repeat apply vac_comp; auto. apply vac_empty.
    - rewrite H in HP. rewrite app_assoc in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      rewrite HP2.
      apply Permutation_rel_split2 in HP1.
      destruct HP1 as [[l3' [HP1' HP2']] | l4' [HP1' HP2']].
      + admit.
      + admit.
  Abort.
End BOTINV.

Lemma pf_unit_inv :
  forall c G D D'
    (HP: D' ≡[P] (D ++ [[1]])) 
    (H: pf c G D') ,
    pf c G D.
Proof.
  intros c G D D' HP H.
  revert D HP.
  induction H; intros D'' HP.
  - PInvert.
    + simpl. auto.
    + subst.
    solve_dual.
    subst. PInvert.
    auto.
  - eapply pf_absorb. apply H.
    + assumption.
    + apply IHpf.
      rewrite HP.
      do 2 rewrite <- app_assoc.
      convertTactics.convert_multisetperm; permutation_solver.
      (* assert ([[1]] ++ [t] ≡[P] [t] ++ [[1]]). { econstructor; eauto. apply perm_swap. } *)
      (* rewrite H2. reflexivity. *)
  - rewrite H3 in HP.
    apply Permutation_rel_split2 in HP.
    destruct HP as [[D1' [EQ1 EQ2]] | [D2' [EQ1 EQ2]]].
    + assert ( D1 ++ [u] ≡[P] (D1' ++ [u]) ++ [[1]] ).
      { convertTactics.convert_multisetperm. permutation_solver.
        (* rewrite EQ1. do 2 rewrite <- app_assoc. *)
        (* rewrite (Permutation_rel_exchange _ [[1]] [u]). *)
        (* reflexivity. } *)
      }
      apply IHpf1 in H4.
      eapply pf_cut. apply H. apply H0. apply H4. apply H2.
      convertTactics.convert_multisetperm. permutation_solver.
      (* rewrite EQ2. reflexivity. *)
    + assert ( D2 ++ [dual u] ≡[P] (D2' ++ [dual u]) ++ [[1]] ).
      { convertTactics.convert_multisetperm. permutation_solver.
        (* rewrite EQ1. do 2 rewrite <- app_assoc. *)
        (* rewrite (Permutation_rel_exchange _ [[1]] [dual u]). *)
        (* reflexivity. } *)
      }
      apply IHpf2 in H4.
      eapply pf_cut. apply H. apply H0. apply H1. apply H4.
      convertTactics.convert_multisetperm. permutation_solver.
      (* rewrite EQ2. reflexivity. *)
   - contradict_perm_rel H0.
   - rewrite H0 in HP.
     apply Permutation_rel_remove_rr in HP.
     destruct HP as [HP _].     
     eapply pf_perm.
     (* apply PID_dual. *)
     apply Permutation_reflexive.
     apply HP.
     apply H.
   - rewrite H0 in HP.
     apply Permutation_rel_split2 in HP.
    destruct HP as [[D1' [EQ1 EQ2]] | [D2' [EQ1 EQ2]]].
     + assert (D' ++ [t] ++ [u] ≡[P] ((D1' ++ [t] ++ [u]) ++ [[1]])).
       { 
         convertTactics.convert_multisetperm. permutation_solver.
         (* rewrite EQ1. *)
         (* do 2 rewrite <- app_assoc. *)
         (* rewrite (Permutation_rel_exchange _ [[1]] ([t] ++ [u])). *)
         (* rewrite <- app_assoc. *)
         (* reflexivity. *)
       }
       apply IHpf in H1.
       eapply pf_tensor.
       apply H1.
       rewrite <- EQ2.
       reflexivity.
     + contradict_perm_rel H0.
   -                            (* Par case *)
     rewrite H1 in HP.
     apply Permutation_rel_split2 in HP.
     destruct HP as [[D1' [EQ1 EQ2]] | [D2' [EQ1 EQ2]]].
     + assert (D1 ++ [t] ≡[P] ((D1' ++ [t]) ++ [[1]])).
       { convertTactics.convert_multisetperm. permutation_solver.
         (* rewrite EQ1. *)
         (* do 2 rewrite <- app_assoc. *)
         (* rewrite (Permutation_rel_exchange _ [[1]] [t]). *)
         (* reflexivity. *)
       }
       apply IHpf1 in H2.
       eapply pf_par.
       apply H2.
       apply H0.
       rewrite <- EQ2. reflexivity.
     + apply Permutation_rel_split2 in EQ1.
       destruct EQ1 as [[D2'' [EQ21 EQ22]] | [D2'' [EQ21 EQ22]]].
       * assert (D2 ++ [u] ≡[P] (D2'' ++ [u]) ++ [[1]]).
         {
           convertTactics.convert_multisetperm. permutation_solver.
           (* rewrite EQ21. *)
           (* do 2 rewrite <- app_assoc. *)
           (* rewrite (Permutation_rel_exchange _ [[1]] [u]). *)
           (* reflexivity. *)
         }
         apply IHpf2 in H2.
         eapply pf_par.
         apply H.
         apply H2.
         rewrite <- EQ2. rewrite <- EQ22. reflexivity.
       * contradict_perm_rel H2.
   - rewrite H0 in HP.
     apply Permutation_rel_split2 in HP.
     destruct HP as [[D1' [EQ1 EQ2]] | [D2' [EQ1 EQ2]]].
     + apply IHpf in EQ1.
       eapply pf_bang.
       apply EQ1.
       rewrite EQ2. reflexivity.
     + PInvert. LInvert. inversion H0.
   - PInvert. LInvert. inversion H0.
   - rewrite H1 in HP.
     apply Permutation_rel_split2 in HP.     
     destruct HP as [[D1' [EQ1 EQ2]] | [D2' [EQ1 EQ2]]].
     + assert (D1 ++ [typ_subst c u t] ≡[P] (D1' ++ [typ_subst c u t]) ++ [[1]]).
       {
         convertTactics.convert_multisetperm. permutation_solver.
         (* rewrite EQ1. *)
         (* do 2 rewrite <- app_assoc. *)
         (* rewrite (Permutation_rel_exchange _ [[1]] [typ_subst c u t]). *)
         (* reflexivity. *)
       }
       apply IHpf in H2.
       eapply pf_forall.
       apply H.
       apply H2.
       rewrite EQ2. reflexivity.
     + PInvert. LInvert. inversion H1.
   - rewrite H0 in HP.
     apply Permutation_rel_split2 in HP.     
     destruct HP as [[D1' [EQ1 EQ2]] | [D2' [EQ1 EQ2]]].
     + assert (shift_ctx c 1 D1 ++ [u] ≡[P] (shift_ctx c 1 D1' ++ [u]) ++ [[1]]).
       { rewrite EQ1.
         rewrite shift_ctx_app.
         convertTactics.convert_multisetperm. permutation_solver.
         (* simpl. *)
         (* do 2 rewrite <- app_assoc. *)
         (* rewrite (Permutation_rel_exchange _ [[1]] [u]). *)
         (* reflexivity. *)
       }
       apply IHpf in H1.
       eapply pf_exists.
       apply H1.
       rewrite EQ2.
       reflexivity.
     + PInvert. LInvert. inversion H0.
Qed. 


Section TENSORINV.
  Context (PID_tensor : forall t u, PID (t ⊗ u) <-> PID t /\ PID u).
  (* Context (PID_par : forall t u, PID (t_par t u) <-> PID t /\ PID u). *)
  Lemma pf_tensor_inv : forall c G D D' t u,
      pf c G D ->
      D ≡[P] (D' ++ [t ⊗ u]) ->
      pf c G (D' ++ [t] ++ [u]).
  Proof.
    intros c G D D' t u HG HP.
    revert D' t u HP.
    induction HG; intros.
    - apply Permutation_rel_split2 in HP.
      destruct HP as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
      + symmetry in HP1. eapply Permutation_rel_singleton_nil in HP1 as (-> & HP1).
        rewrite <- HP1 in *. replace ([] ++ [dual (t ⊗ u)]) with [dual (t ⊗ u)] by auto.
        eapply pf_perm_rel. reflexivity. rewrite <- HP2.
        assert ([dual (t ⊗ u0)] ++ [t] ++ [u0] ≡[P] [t] ++ [u0] ++ [dual (t ⊗ u0)]). {convertTactics.convert_multisetperm. permutation_solver. } symmetry in H2. apply H2.
        inversion H0.
        eapply (pf_par _ _ [t] [u0]).
        ++ eapply pf_id; auto. apply PID_tensor in H; intuition.
        ++ eapply pf_id; auto. apply PID_tensor in H; intuition.
        ++ simpl. reflexivity.
      + symmetry in HP1. eapply Permutation_rel_singleton_nil in HP1 as (-> & HP1).
        apply dual_eq_iff in HP1. rewrite dual_involutive in HP1. rewrite <- HP1 in *.
        replace ([dual (t ⊗ u0)] ++ []) with ([dual (t ⊗ u0)]) in HP2 by auto.
        eapply pf_perm_rel. reflexivity. rewrite <- HP2. assert ([t] ++ [u0] ++ [dual (t ⊗ u0)] ≡[P] [dual (t ⊗ u0)] ++ [t] ++ [u0]). {convertTactics.convert_multisetperm. permutation_solver. } apply H2.
        inversion H0.
        apply wf_typ_dual_inv in H5, H6.
        eapply (pf_par _ _ [t] [u0]).
        ++ eapply pf_id; auto. apply PID_dual in H. apply PID_tensor in H; intuition.
        ++ eapply pf_id; auto. apply PID_dual in H. apply PID_tensor in H; intuition. 
        ++ simpl. reflexivity.
    - eapply pf_absorb; try eassumption.
      eapply pf_perm_rel. reflexivity. assert (((D' ++ [t]) ++ [t0] ++ [u]) ≡[P]((D' ++ [t0] ++ [u]) ++ [t])). {convertTactics.convert_multisetperm. permutation_solver. } apply H1.
      eapply IHHG. convertTactics.convert_multisetperm. permutation_solver.
    - rewrite H1 in HP. apply Permutation_rel_split2 in HP.
      destruct HP as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
      + eapply pf_cut. apply H. apply H0. 
        3: {assert (D' ++ [t] ++ [u0] ≡[P] (l1' ++ [t] ++ [u0]) ++ D2). {convertTactics.convert_multisetperm. permutation_solver. } eassumption. }
        ++ eapply pf_perm_rel. reflexivity. assert ((l1' ++ [u]) ++ [t] ++ [u0] ≡[P] (l1' ++ [t] ++ [u0]) ++ [u]) by (convertTactics.convert_multisetperm; permutation_solver). eassumption.
           apply IHHG1. convertTactics.convert_multisetperm. permutation_solver.
        ++ assumption.
      + eapply pf_cut. apply H. apply H0.
        3: {assert (D' ++ [t] ++ [u0] ≡[P] D1 ++ (l2' ++ [t] ++ [u0])) by (convertTactics.convert_multisetperm; permutation_solver). eassumption. }
        ++ assumption.
        ++ eapply pf_perm_rel. reflexivity. assert ((l2' ++ [dual u]) ++ [t] ++ [u0] ≡[P] (l2' ++ [t] ++ [u0]) ++ [dual u]) by (convertTactics.convert_multisetperm; permutation_solver). eassumption.
           eapply IHHG2. convertTactics.convert_multisetperm. permutation_solver.
    - symmetry in HP. eapply Permutation_rel_singleton_nil in HP as (_ & HContra).
      discriminate.
    - rewrite H in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      eapply pf_one.
      2: {
        assert (D'0 ++ [t] ++ [u] ≡[P] (l1' ++ [t] ++ [u]) ++ [[1]]).
        {convertTactics.convert_multisetperm. permutation_solver. }
        apply H0.
      }
      apply IHHG. assumption.
    - rewrite H in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]].
      + injection HP1; intros; subst.
        eapply pf_perm_rel. reflexivity. rewrite <- HP2. reflexivity.
        auto.
      + eapply pf_tensor.
        2: {
          assert (D'0 ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [t ⊗ u]).
          {
            convertTactics.convert_multisetperm. permutation_solver.
          }
          apply H0. }
        eapply pf_perm_rel. reflexivity. assert ((l1' ++ [t] ++[u]) ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [t] ++ [u]).
        {convertTactics.convert_multisetperm. permutation_solver. }
        apply H0.
        apply IHHG. convertTactics.convert_multisetperm. permutation_solver.
    - rewrite H in HP. rewrite app_assoc in HP. eapply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      apply Permutation_rel_split2 in HP1.
      destruct HP1 as [[l3' [HP'1 HP'2]] | [l4' [HP'1 HP'2]]].
      + eapply pf_par.
        3: {
          assert (D' ++ [t0] ++ [u0] ≡[P] ((l3' ++ [t0] ++ [u0]) ++ D2 ++ [t_par t u])).
          { convertTactics.convert_multisetperm. permutation_solver. }
          apply H0.
        }
        ++ 
          eapply pf_perm_rel. reflexivity.
          assert ((l3' ++ [t]) ++ [t0] ++ [u0] ≡[P] (l3' ++ [t0] ++ [u0]) ++ [t]).
          {convertTactics.convert_multisetperm. permutation_solver. }
          apply H0.
          apply IHHG1. convertTactics.convert_multisetperm. permutation_solver.
        ++ assumption.
      + eapply pf_par.
        3: {
          assert (D' ++ [t0] ++ [u0] ≡[P] D1 ++ (l4' ++ [t0] ++ [u0]) ++ [t_par t u]).
          { convertTactics.convert_multisetperm. permutation_solver. }
          eassumption.
        }
        ++ assumption.
        ++ eapply pf_perm_rel. reflexivity.
           assert ((l4' ++ [u]) ++ [t0] ++ [u0] ≡[P] (l4' ++ [t0] ++ [u0]) ++ [u]).
           {convertTactics.convert_multisetperm. permutation_solver. }
           eassumption.
           apply IHHG2. convertTactics.convert_multisetperm. permutation_solver.
    - rewrite H in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      eapply pf_bang.
      2: {
        assert (D' ++ [t0] ++ [u] ≡[P] (l1' ++ [t0] ++ [u]) ++ [[!]t]).
        { convertTactics.convert_multisetperm. permutation_solver. }
        eassumption.
      }
      apply IHHG. assumption.
    - symmetry in HP. eapply Permutation_rel_singleton_nil in HP as (_ & HP).
      discriminate.
    - rewrite H0 in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      eapply pf_forall. eassumption.
      2: {
        assert (D' ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [[forall]t]).
        { convertTactics.convert_multisetperm. permutation_solver. }
        eassumption.
      }
      eapply pf_perm_rel. reflexivity.
      assert ((l1' ++ [typ_subst c u t]) ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [typ_subst c u t]).
      {convertTactics.convert_multisetperm. permutation_solver. }
      eassumption.
      apply IHHG. convertTactics.convert_multisetperm. permutation_solver.
    - rewrite H in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
      eapply pf_exists.
      2: {
        assert (D' ++ [t] ++ [u0] ≡[P] (l1' ++ [t] ++ [u0]) ++ [[exists]u]).
        {convertTactics.convert_multisetperm. permutation_solver. }
        eassumption.
      }
      repeat rewrite shift_ctx_app.
      eapply pf_perm_rel. reflexivity.
      assert ((shift_ctx c 1 l1' ++ [u]) ++ (shift_ctx c 1 [t]) ++ (shift_ctx c 1 [u0]) ≡[P] (shift_ctx c 1 l1' ++ shift_ctx c 1 [t] ++ shift_ctx c 1 [u0]) ++ [u]).
      {convertTactics.convert_multisetperm. permutation_solver. }
      eassumption.
      eapply IHHG.
      rewrite HP1. rewrite shift_ctx_app. simpl.
      convertTactics.convert_multisetperm. permutation_solver.
  Qed.
End TENSORINV.

(* Ltac WF_CTX := *)
(*   repeat *)
(*     match goal with *)
(*     | H : ?C ≡[P] ?D |- _ => destruct H as [H _] *)
(*     | H : P ?C ?D |- wf_ctx ?A ?C => *)
(*         apply Permutation_symmetric in H; apply (wf_ctx_Permutation_inj _ _ _ H); clear H *)
(*     | H : wf_ctx ?C (?D ++ ?E) |- _ => apply wf_ctx_app in H; destruct H *)
(*     | _ : _ |- wf_ctx ?C (?D ++ ?E) => apply wf_ctx_app; split *)
(*     | H : wf_ctx ?C [?U] |- _ => apply wf_ctx_single in H *)
(*     | _ : _ |- wf_ctx ?C [?U] => apply wf_ctx_single *)
(*     | H : wf_ctx (1 + ?C) (shift_ctx ?C 1 ?D) |- _ => apply shift_ctx_strengthen in H *)
(*     end.   *)

Section BANGINV.
  Context (PID_bang : forall t, PID ([!]t) <-> PID t).
  (* Context (PID_ques : forall t, PID ([?]t) <-> PID t). *)
Lemma pf_bang_inv : forall c G G1 D1 D t,
    pf c G1 D ->
    D ≡[P] D1 ++ [[!] t] ->
    G ≡[P] G1 ++ [t] ->
    pf c G D1.
Proof.
  intros c G G1 D1 D t HG HPD HPG.
  revert G D1 t HPD HPG.
  induction HG; intros.
  - apply Permutation_rel_split2 in HPD.
    destruct HPD as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1. destruct HP1 as (-> & <-).
      eapply pf_perm_rel. reflexivity. rewrite <- HP2. simpl. reflexivity. 
      apply pf_ques.
      eapply pf_absorb with (t := t).
      ++ wf_ctx_solver.
         (* apply wf_ctx_app; split; try eassumption. *)
         (* unfold wf_ctx. intros. *)
         (* apply In_singleton in H2. *)
         (* rewrite H2; inversion H0; auto. *)
      ++ auto.
      ++ eapply pf_perm_rel. reflexivity. apply Permutation_rel_exchange.
         eapply pf_id; inversion H0; auto. apply PID_bang; auto.
         apply (wf_ctx_perm_iff HPG).
         wf_ctx_solver.
         (* apply wf_ctx_app. intuition. *)
         (*      unfold wf_ctx. intros. apply In_singleton in H5. *)
         (*      subst; auto. *)
    + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1. destruct HP1 as (-> & HP1).
      apply dual_swap_iff in HP1. rewrite <- HP1 in *.
      inversion H0.
      eapply pf_perm_rel. reflexivity. simpl in HP2. rewrite <- HP2. reflexivity.
      eapply pf_ques.
      eapply pf_absorb with (t := t).
      ++ wf_ctx_solver.
        (* apply wf_ctx_app; split; eauto. *)
        (*  unfold wf_ctx; intros. *)
        (*  apply In_singleton in H5; subst. *)
        (*  apply wf_typ_dual_inv in H4; auto. *)
      ++ auto.
      ++ eapply pf_perm_rel. reflexivity. apply Permutation_rel_exchange. 
         eapply pf_id; auto. 
         +++ apply PID_dual in H. apply PID_bang. auto.
         +++ wf_ctx_solver.
           (* apply wf_typ_dual_inv in H4; auto. *)
         +++ apply (wf_ctx_perm_iff HPG).
             wf_ctx_solver.
             (* apply wf_ctx_app; split; auto. *)
             (* unfold wf_ctx; intros. apply In_singleton in H5; subst. *)
             (* apply wf_typ_dual_inv in H4; auto. *)
  - rewrite H0, <- app_assoc in HPG.
    assert (pf c (G ++ [t]) (D1 ++ [[!] t0] ++ [t])).
    {
      eapply pf_perm_rel. apply H0. assert (D ++ [t] ≡[P] D1 ++ [[!] t0] ++ [t]). {convertTactics.convert_multisetperm. permutation_solver. }
      apply H1.
      assumption.
    }
    eapply pf_absorb. 
    2: {
      rewrite HPG, app_assoc. apply Permutation_rel_assoc_swap.
      (* assert (G0 ≡[P] (G ++ [t0]) ++ [t]). *)
      (* {convertTactics.convert_multisetperm. permutation_solver. } *)
      (* eassumption. *)
    }
    {wf_ctx_solver. apply pf_wf_typ in HG as (HG1 & HG2). apply wf_ctx_app in HG2 as (HG2 & HG3). eapply (wf_ctx_perm_iff HPD) in HG2. wf_ctx_solver. }
    eapply IHHG.
    2: { rewrite H0, HPG, <- app_assoc. reflexivity. }
    convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H1 in HPD. apply Permutation_rel_split2 in HPD.
    destruct HPD as [[l1' [HPD1 HPD2]] | [l2' [HPD1 HPD2]]].
    + eapply pf_cut; try eassumption. 
      3: {rewrite <- HPD2. reflexivity. }
      ++ eapply IHHG1. 
         +++ rewrite HPD1. apply Permutation_rel_assoc_swap.
         +++ assumption.
      ++ eapply pf_weakening. eassumption. apply pf_wf_typ in HG1 as (_ & HG1). apply wf_ctx_app in HG1 as (HG1 & _). apply (wf_ctx_perm_iff HPD1) in HG1. wf_ctx_solver.
         assumption.
    + eapply pf_cut; try eassumption.
      3: {rewrite <- HPD2. reflexivity. }
      ++ eapply pf_weakening. eassumption. apply pf_wf_typ in HG2 as (_ & HG2). apply wf_ctx_app in HG2 as (HG2 & _). apply (wf_ctx_perm_iff HPD1) in HG2. wf_ctx_solver.
         assumption.
      ++ eapply IHHG2.
         +++ rewrite HPD1. apply Permutation_rel_assoc_swap.
         +++ assumption.
  - symmetry in HPD. apply Permutation_rel_singleton_nil in HPD as (_ & HPD). discriminate.
  - rewrite H in HPD. apply Permutation_rel_split_last in HPD.
    destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate.
    eapply pf_one.
    2: {eassumption. }
    eapply IHHG.
    + rewrite <- HPD3. eassumption.
    + assumption.
  - rewrite H in HPD. apply Permutation_rel_split_last in HPD.
    destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate.
    eapply pf_tensor.
    2: { rewrite HPD2, <- HPD3. reflexivity. }
    eapply IHHG.
    2: { eassumption. }
    convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H in HPD. rewrite app_assoc in HPD. apply Permutation_rel_split_last in HPD.
    destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate.
    apply Permutation_rel_split2 in HPD1.
    destruct HPD1 as [[l3' [HPD'1 HPD'2]] | [l4' [HPD'1 HPD'2]]].
    + eapply pf_par.
      3: {
        assert (D0 ≡[P] l3' ++ D2 ++ [t_par t u]).
        { convertTactics.convert_multisetperm. permutation_solver. }
        eassumption.
      }
      ++ eapply IHHG1.
         2: {eassumption. }
         convertTactics.convert_multisetperm. permutation_solver.
      ++ eapply pf_weakening. eassumption.
         assert (pf c G ((l3' ++ [[!] t0]) ++ [t])).
         {eapply pf_perm_rel. reflexivity. rewrite <- HPD'1. reflexivity. assumption. }
         wf_ctx_solver.
         apply pf_wf_typ in H0 as (_ & H0). wf_ctx_solver.
         assumption.
    + eapply pf_par.
      3: {
        assert (D0 ≡[P] D1 ++ l4' ++ [t_par t u]).
        {convertTactics.convert_multisetperm. permutation_solver. }
        eassumption.
      }
      ++ eapply pf_weakening. eassumption.
         assert (pf c G ((l4' ++ [[!] t0]) ++ [u])).
         {eapply pf_perm_rel. reflexivity. rewrite <- HPD'1. reflexivity. assumption. }
         wf_ctx_solver.
         apply pf_wf_typ in H0. wf_ctx_solver.
         assumption.
      ++ eapply IHHG2.
         2: {eassumption. }
         convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H in HPD. apply Permutation_rel_split_last in HPD.
    destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]].
    + inversion HPD1; subst.
      eapply pf_perm_rel.
      ++ symmetry in HPG. apply HPG.
      ++ apply HPD2.
      ++ assumption.
    + eapply pf_bang.
      2: { rewrite HPD2. rewrite <- HPD3. reflexivity. }
      eapply IHHG.
      ++ rewrite HPD1. reflexivity.
      ++ convertTactics.convert_multisetperm. permutation_solver.
  - symmetry in HPD. apply Permutation_rel_singleton_nil in HPD.
    destruct HPD as (_ & HPD). discriminate.
  - rewrite H0 in HPD. apply Permutation_rel_split_last in HPD.
    destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate.
    eapply pf_forall. eassumption.
    2: { rewrite HPD2, <- HPD3. reflexivity. }
    eapply IHHG.
    2: { eassumption. }
    convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H in HPD. apply Permutation_rel_split_last in HPD.
    destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate.
    eapply pf_exists.
    2: { rewrite HPD2, <- HPD3. reflexivity. }
    eapply IHHG.
    2: { rewrite HPG. rewrite shift_ctx_app. simpl. reflexivity. }
    rewrite HPD1, shift_ctx_app.
    simpl. convertTactics.convert_multisetperm. permutation_solver.
Qed.
End BANGINV.

Section QUESINV.
  Context (PID_ques : forall t, PID ([?] t) <-> PID t).
Lemma pf_ques_inv : forall c G D D' t,
    D ≡[P] D' ++ [[?]t] ->
    pf c G D ->
    pf c G (D' ++ [t]).
Proof.
  intros c G D D' t HP HG.
  revert D' t HP.
  induction HG; intros.
  - apply Permutation_rel_split2 in HP.
    destruct HP as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & <-). 
      eapply pf_perm_rel. reflexivity. simpl in HP2. rewrite <- HP2. apply Permutation_rel_exchange.
      eapply pf_bang.
      2: {reflexivity. }
      eapply pf_absorb.
      2: {reflexivity. }
      wf_ctx_solver.
      apply pf_id; wf_ctx_solver. apply PID_ques; auto.
    + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1).
      apply dual_swap_iff in HP1 as <-.
      eapply pf_perm_rel. reflexivity. simpl in HP2. rewrite <- HP2. apply Permutation_rel_exchange.
      eapply pf_bang.
      2: {reflexivity. }
      eapply pf_absorb.
      2: {reflexivity. }
      wf_ctx_solver.
      apply pf_id; wf_ctx_solver. apply PID_dual in H. apply PID_ques; auto.
  - eapply pf_absorb; try eassumption.
    eapply pf_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. 
    apply IHHG. convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H1 in HP. apply Permutation_rel_split2 in HP.
    destruct HP as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + eapply pf_cut. eassumption. eassumption.
      3: { rewrite <- HP2. apply Permutation_rel_assoc_swap. }
      ++ eapply pf_perm_rel. reflexivity. apply Permutation_rel_assoc_swap.
         eapply IHHG1. rewrite HP1. apply Permutation_rel_assoc_swap.
      ++ assumption.
    + eapply pf_cut. eassumption. eassumption.
      3: {rewrite <- HP2. rewrite <- app_assoc. reflexivity. }
      ++ assumption.
      ++ eapply pf_perm_rel. reflexivity. apply Permutation_rel_assoc_swap.
         eapply IHHG2. rewrite HP1. apply Permutation_rel_assoc_swap.
  - symmetry in HP. apply Permutation_rel_singleton_nil in HP as (_ & HP). discriminate.
  - rewrite H in HP. apply Permutation_rel_split_last in HP.
    destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
    eapply pf_one. 2: {rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. }
    eapply IHHG. assumption. 
  - rewrite H in HP. apply Permutation_rel_split_last in HP.
    destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
    eapply pf_tensor.
    2: { rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. }
    eapply pf_perm_rel. reflexivity. assert ((l1' ++ [t] ++ [u]) ++ [t0] ≡[P] (l1' ++ [t0]) ++ [t] ++ [u]). {convertTactics.convert_multisetperm. permutation_solver. } eassumption.
    eapply IHHG. convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H in HP. rewrite app_assoc in HP. apply Permutation_rel_split_last in HP.
    destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
    apply Permutation_rel_split2 in HP1.
    destruct HP1 as [[l3' [HP'1 HP'2]] | [l4' [HP'1 HP'2]]].
    + eapply pf_par.
      3: {
        assert (D' ++ [t0] ≡[P] (l3' ++ [t0]) ++ D2 ++ [t_par t u]).
        {convertTactics.convert_multisetperm. permutation_solver. }
        eassumption.
      }
      ++ eapply pf_perm_rel. reflexivity. apply Permutation_rel_assoc_swap.          apply IHHG1. convertTactics.convert_multisetperm. permutation_solver.
      ++ assumption.
    + eapply pf_par.
      3: {
        assert (D' ++ [t0] ≡[P] D1 ++ (l4' ++ [t0]) ++ [t_par t u]).
        {convertTactics.convert_multisetperm. permutation_solver. }
        eassumption.
      }
      ++ assumption.
      ++ eapply pf_perm_rel. reflexivity. apply Permutation_rel_assoc_swap.
         apply IHHG2. convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H in HP. apply Permutation_rel_split_last in HP.
    destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
    eapply pf_bang.
    2: {
      rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap.
    }
    apply IHHG. eassumption.
  - symmetry in HP. apply Permutation_rel_singleton_nil in HP as (-> & HP).
    injection HP. intros ->. simpl; assumption.
  - rewrite H0 in HP. apply Permutation_rel_split_last in HP.
    destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
    eapply pf_forall.
    3: { rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. }
    eassumption.
    eapply pf_perm_rel. reflexivity. apply Permutation_rel_assoc_swap.
    apply IHHG. convertTactics.convert_multisetperm. permutation_solver.
  - rewrite H in HP. apply Permutation_rel_split_last in HP.
    destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate.
    eapply pf_exists.
    2: {rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. }
    repeat rewrite shift_ctx_app.
    eapply pf_perm_rel. reflexivity. apply Permutation_rel_assoc_swap.
    eapply IHHG. rewrite HP1. repeat rewrite shift_ctx_app. simpl.
    convertTactics.convert_multisetperm. permutation_solver.
Qed.
End QUESINV.
End PF.

Ltac normalize_wf_ctxH :=
  repeat (match goal with
  | [ H : wf_ctx ?c (?l1 ++ ?l2) |- _ ] => apply wf_ctx_app in H; destruct H
  end).

Definition atomic (t:typ) : Prop :=
  match t with
  | t_base p (b_other n) => True
  | t_var p x => True
  | _ => False
  end.
Definition any : typ -> Prop := fun t => True.
Definition no_cut : typ -> Prop := fun t => False.

Module PMELLNotations.
  Export PMELLBasicNotations.
  Notation "'⦃' c ';' G ';' D '⊢ok' '⦄'" := (pf any any c G D) (at level 101, D at level 0, G at level 0) : pmell_scope.
  Notation "'⦃' c ';' G ';' D '⊢prim' '⦄'" := (pf atomic any c G D) (at level 101, D at level 0, G at level 0) : pmell_scope.
  Notation "'⦃' c ';' G ';' D '⊢cf' '⦄'" := (pf any no_cut c G D) (at level 101, D at level 0, G at level 0) : pmell_scope.
  Notation "'⦃' c ; G ; D '⊢norm' '⦄'" := (pf atomic no_cut c G D) (at level 101, D at level 0, G at level 0) : pmell_scope.
End PMELLNotations.
Import PMELLNotations.

Lemma atomic_dual : forall u : typ, atomic u <-> atomic (dual u).
Proof.
  intros u.
  split; intros.
  - destruct u; try contradiction; auto.
  - destruct u; try contradiction; auto.
Qed.


Definition pf_exchange' {PCUT} := @pf_exchange _ PCUT atomic_dual.

Lemma any_dual : forall u : typ, any u <-> any (dual u).
Proof.
  intros u. unfold any. tauto.
Qed.

#[local] Hint Resolve any_dual : core.


Open Scope list_scope.
Check ([1; 2; 3; 4]%list).

Lemma shift_ctx_singleton : forall b c t, shift_ctx c b [t] = [shift_typ c b t].
Proof.
  intros.
  reflexivity.
Qed.

  (* c : nat *)
  (* G : ctx *)
  (* D1, D : list typ *)
  (* u, t : typ *)
  (* H : c ⊢ u wf *)
  (* H0 : ⦃ c; G; (D1 ++ [typ_subst c u t]) ⊢cf ⦄ *)
  (* H1 : D ≡[ P] D1 ++ [[forall] t] *)
  (* IHpf : ∀ b : nat, ⦃ c + b; (shift_ctx c b G); (shift_ctx c b (D1 ++ [typ_subst c u t])) ⊢cf ⦄ *)
  (* b : nat *)
  (* ============================ *)
  (* ⦃ c + b; (shift_ctx c b G); (shift_ctx c b D1 ++ [typ_subst (c + b) (shift_typ c b u) (shift_typ c b t)]) ⊢cf ⦄ *)

Ltac lia' := try apply Nat.ltb_lt; try apply Nat.ltb_nlt; try apply Nat.eqb_eq; try apply Nat.eqb_neq; lia.

Lemma nlt_eq_ngt : forall a b, a = b -> a <? b = false /\ a =? b = true /\ b <? a = false .
Proof.
  intros; subst; repeat split; lia'.
Qed.

Lemma lt_neq_ngt : forall a b, a < b -> a <? b = true /\ a =? b = false /\ b <? a = false.
Proof.
  intros; subst; repeat split; lia'.
Qed.

Lemma nlt_neq_gt : forall a b, b < a -> a <? b = false /\ a =? b = false /\ b <? a = true.
Proof.
  intros; subst; repeat split; lia'.
Qed.

  (* [forall] typ_subst (c + b + 1) (shift_typ 0 1 (shift_typ c b u)) (shift_typ (c + 1) b t) = *)
  (* [forall] typ_subst (c + 1 + b) (shift_typ (c + 1) b (shift_typ 0 1 u)) (shift_typ (c + 1) b t) *)

Lemma shift_typ_le_swap : forall t c1 c2 b1 b2, c2 <= c1 -> shift_typ c2 b2 (shift_typ c1 b1 t) = (shift_typ (c1 + b2) b1 (shift_typ c2 b2 t)).
Proof.
  intros t.
  induction t; intros; simpl; auto.
  - 
    destruct (Nat.ltb_spec x c1); simpl.
    + destruct (Nat.ltb_spec x c2); simpl.
      ++ assert (x <? c1 + b2 = true) by lia'.
         rewrite H2. auto.
      ++ assert (b2 + x <? c1 + b2 = true) by lia'.
         rewrite H2. auto.
    + destruct (Nat.ltb_spec x c2); simpl.
      ++ lia.
      ++ assert (b1 + x <? c2 = false) by lia'. rewrite H2.
         assert (b2 + x <? c1 + b2 = false) by lia'. rewrite H3.
         replace (b2 + (b1 + x)) with (b1 + (b2 + x)) by lia.
         auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt.
    + replace (c1 + 1 + b2) with (c1 + b2 + 1) by lia; auto.
    + lia.
  - rewrite IHt.
    + replace (c1 + 1 + b2) with (c1 + b2 + 1) by lia; auto.
    + lia.
Qed.

Corollary shift_typ_0_c : forall t c b1 b2, shift_typ 0 b2 (shift_typ c b1 t) = (shift_typ (c + b2) b1 (shift_typ 0 b2 t)).
Proof.
  intros.
  apply shift_typ_le_swap. lia.
Qed.

Lemma typ_subst_shift_typ_comm : forall t u c b, typ_subst (c + b) (shift_typ c b u) (shift_typ c b t) = shift_typ c b (typ_subst c u t).
Proof.
  intros t. induction t; intros; simpl; auto.
  - destruct (Nat.compare_spec x c); simpl.
    + pose proof (nlt_eq_ngt _ _ H) as (H0 & H1 & H2).
      try rewrite H0; try rewrite H1; try rewrite H2.
      unfold typ_subst.
      assert (b + x <? c + b = false) by lia'. rewrite H3.
      assert (b + x =? c + b = true) by lia'. rewrite H4.
      destruct p; auto.
      rewrite dual_shift_typ_comm; auto.
    + pose proof (lt_neq_ngt _ _ H) as (H0 & H1 & H2).
      try rewrite H0; try rewrite H1; try rewrite H2.
      unfold typ_subst.
      simpl.
      assert (x <? c + b = true) by lia'. rewrite H3, H0.
      auto.
    + pose proof (nlt_neq_gt _ _ H) as (H0 & H1 & H2).
      try rewrite H0; try rewrite H1; try rewrite H2.
      unfold typ_subst.
      assert (b + x <? c + b = false) by lia'. rewrite H3.
      assert (b + x =? c + b = false)  by lia'. rewrite H4.
      simpl.
      assert (Init.Nat.pred x <? c = false) by lia'. rewrite H5.
      rewrite Nat.add_pred_r; auto.
      lia.
  - rewrite IHt1, IHt2. auto.
  - rewrite IHt1, IHt2. auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite <- IHt.
    rewrite shift_typ_0_c.
    replace (c + b + 1) with (c + 1 + b) by lia.
    auto.
  - rewrite <- IHt.
    rewrite shift_typ_0_c.
    replace (c + b + 1) with (c + 1 + b) by lia.
    auto.
Qed.

Ltac normalize_shift := repeat rewrite <- shift_ctx_singleton; repeat rewrite <- shift_ctx_app; try apply wf_typ_shift0; try eapply wf_shift_ctx'; try reflexivity; auto.




      



(* We can eta-expand anywhere to turn a general proof into a primitive one. *) 
Open Scope pmell_scope.
Delimit Scope pmell_scope with pmell.

Lemma typ_subst_var :
  forall t c,
    typ_subst (1 + c) (t_var true c) (shift_typ (c + 1) 1 t) = t.
Proof.
  induction t; intros; simpl.
  - reflexivity.
  - destruct (Nat.ltb_spec x (c+1)); simpl.
    + destruct (Nat.ltb_spec x (S c)).
      reflexivity.
      lia.
    + destruct (Nat.ltb_spec (S x) (S c)).
      lia.
      destruct (Nat.eqb_spec x c).
      * subst. destruct p; reflexivity.
      * reflexivity.
  - rewrite IHt1. rewrite IHt2. reflexivity.
  - rewrite IHt1. rewrite IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - replace (S (c + 1)) with (1 + (1 + c)) by lia.
    replace (c + 1 + 1) with ((1 + c) + 1) by lia.
    rewrite IHt.
    reflexivity.
  - replace (S (c + 1)) with (1 + (1 + c)) by lia.
    replace (c + 1 + 1) with ((1 + c) + 1) by lia.
    rewrite IHt.
    reflexivity.
Qed.  
      
Lemma eta_expansion :
  forall PCUT c G u
    (WFU : c ⊢ u wf)
    (WFG : wf_ctx c G),
    pf atomic PCUT c G ([u] ++ [dual u]).
Proof.
  intros. revert G WFG.
  induction WFU; intros G WFG.
  - destruct bt.
    + destruct p.
      * apply pf_exchange'.
        eapply pf_one.
        apply pf_bot. assumption. reflexivity.
      * eapply pf_one. apply pf_bot. assumption. reflexivity.
    +
      apply pf_id; simpl; auto.
  - apply pf_id; simpl; auto.
  - apply pf_exchange'.
    simpl dual.
    eapply pf_tensor.
    2 : { reflexivity. }     
    apply pf_exchange'.
    eapply pf_par. apply IHWFU1; auto. apply IHWFU2; auto.
    rewrite app_assoc. reflexivity.
  - simpl dual.
    eapply pf_tensor.
    2 : { reflexivity. }
    apply pf_exchange'.
    rewrite <- app_assoc.
    eapply pf_par.
    3 : { reflexivity. }
    apply pf_exchange'; auto.
    apply pf_exchange'; auto.
  - apply pf_exchange'.
    eapply pf_bang.
    2 :{ reflexivity. } 
    simpl. 
    apply pf_ques.
    eapply pf_absorb. apply wf_ctx_app. intuition. eassumption. apply wf_ctx_single. apply WFU.
    reflexivity.
    eapply pf_exchange'.
    apply IHWFU. apply wf_ctx_app. intuition. apply wf_ctx_single. assumption.
  - simpl dual.
    eapply pf_bang.
    2 : { reflexivity. } 
    apply pf_ques.
    eapply pf_absorb. 2 : { reflexivity. } apply wf_ctx_app. intuition. apply wf_ctx_single. apply wf_typ_dual. assumption.
    apply IHWFU.
    apply wf_ctx_app. intuition. apply wf_ctx_single. apply wf_typ_dual. assumption.
  - simpl dual.
    eapply pf_exists. 2 : { reflexivity. } 
    simpl shift_ctx.
    apply pf_exchange'.
    eapply pf_forall with (u := t_var true c).
    3 : { reflexivity. } 
    + constructor. lia.
    + rewrite typ_subst_var.
      apply pf_exchange'.
      apply IHWFU.
      apply wf_shift_ctx.
      assumption.
  - simpl dual. 
    apply pf_exchange'.
    eapply pf_exists. 2 : { reflexivity. } 
    simpl shift_ctx.
    apply pf_exchange'.
    eapply pf_forall with (u := t_var true c).
    3 : { reflexivity. }
    + constructor. lia.
    + rewrite typ_subst_var.
      apply IHWFU.
      apply wf_shift_ctx.
      assumption.
Qed.      

#[local] Hint Constructors pf : core.

(* We can eta-expand anywhere to turn a general proof into a primitive one. *) 
Lemma ok_to_prim :
  forall c G D
    (HOK : ⦃c ; G ; D ⊢ok⦄ ),
    ⦃c ; G ; D ⊢prim⦄ .
Proof.
  intros.
  induction HOK; auto.
  - apply eta_expansion; auto.
  - eapply pf_absorb; eauto.
  - eapply pf_cut; eauto.
  - eauto.
  - eapply pf_tensor; eauto.
  - eapply pf_par. 3 : { apply H. } assumption. assumption.
  - eauto.
  - eapply pf_forall; eauto.
  - eapply pf_exists; eauto.
Qed.  


Lemma dual_base_inversion:
  forall t p n,
    dual t = t_base p (b_other n) -> t = t_base (negb p) (b_other n).
Proof.
  intros.
  destruct t; inversion H.
  destruct p0; reflexivity.
Qed.  

Lemma norm_cut_admissibility :
  forall c u G D1 D2 D1' D2',
    D1 ≡ D1' ++ [u] ->
    D2 ≡ D2' ++ [dual u] ->
    c ⊢ u wf ->
    ⦃c ; G ; D1 ⊢norm ⦄ ->
    ⦃c ; G ; D2 ⊢norm⦄ ->
    ⦃c ; G ; D1' ++ D2' ⊢norm⦄.
Proof.
Abort.


Lemma prim_to_norm_elimination :
  forall c G D,
    ⦃c ; G ; D ⊢prim⦄  ->
    ⦃c ; G ; D ⊢norm⦄.
Proof.
Abort.

Lemma cut_elimination :
  forall c G D,
    ⦃c ; G ; D ⊢ok⦄  ->
    ⦃c ; G ; D ⊢norm⦄.
Proof.
Abort.

(*


-----------------
c; G; D ++ [[⊥]] ⊢
 *)

Lemma pf_ok_bot_inf : forall D D' G c (HP : D ≡[P] D' ++ [[⊥]]) (HL: ⦃c; G; D' ⊢ok⦄),
    (⦃c; G; D ⊢ok⦄).
Proof.
  (* intros. *)
  (* revert D HP. *)
  (* induction HL; intros. *)
  (* -  *)
  (* apply (pf_cut _ _ _ _ [[⊥]] D' _ [1]); auto. *)
  (* - unfold any; auto. *)
  (* - apply pf_one with [[⊥]]. constructor. *)
  (*   apply pf_wf_typ in HL; intuition. *)
  (*   reflexivity. *)
  (* -   *)
Abort.
    

(* c : nat *)
(*   G : ctx *)
(*   D' : list typ *)
(*   t, u : typ *)
(*   H : ⦃ c; G; (D' ++ [t] ++ [u]) ⊢cf ⦄ *)
(*   D2, D2' : list typ *)
(*   HWFu : c ⊢ t ⊗ u wf *)
(*   HP2 : D2 ≡[ P] D2' ++ [dual (t ⊗ u)] *)
(*   H4 : ⦃ c; G; D2 ⊢cf ⦄ *)
(*   ============================ *)
(*   ⦃ c; G; (D' ++ D2') ⊢cf ⦄ *)

Lemma pf_cf_shift_inv : forall D G c b, ⦃c; G; D ⊢cf ⦄ -> ⦃(c + b); (shift_ctx 0 b G); (shift_ctx 0 b D) ⊢cf ⦄.
Proof.
  (* intros D G c b H. revert b. *)
  (* induction H; intros. *)
Admitted.
(* Lemma pf_cf_shift_inv : forall D G c b, ⦃c; G; D ⊢cf ⦄ -> ⦃(c + b); (shift_ctx c b G); (shift_ctx c b D) ⊢cf ⦄. *)
(* Proof. *)
(*   intros D G c b H. revert b. *)
(*   induction H; intros. *)
(*   - rewrite shift_ctx_app. simpl. rewrite dual_shift_typ_comm. *)
(*     apply pf_id; auto. *)
(*     apply wf_typ_shift0; auto. *)
(*     apply wf_shift_ctx'; auto. *)
(*   - eapply (pf_absorb _ _ _ (shift_ctx c b G) _ (shift_typ c b t) (shift_ctx c b D)). *)
(*     + normalize_shift. *)
(*     + rewrite H0. rewrite shift_ctx_app. reflexivity. *)
(*     + normalize_shift. *)
(*   - inversion H. *)
(*   - simpl. eapply pf_bot. *)
(*     apply wf_shift_ctx'. auto. *)
(*   - eapply pf_one. *)
(*     + apply IHpf. *)
(*     + erewrite <- shift_typ_one_id. normalize_shift. *)
(*       rewrite H0. reflexivity. *)
(*   - eapply (pf_tensor _ _ _ _ _ (shift_ctx c b D') (shift_typ c b t) (shift_typ c b u)). *)
(*     + normalize_shift. *)
(*     + replace (shift_typ c b t ⊗ shift_typ c b u) with (shift_typ c b (t ⊗ u)) by auto. *)
(*       rewrite H0. normalize_shift. *)
(*   - eapply (pf_par _ _ _ _ (shift_ctx c b D1) (shift_ctx c b D2) _ (shift_typ c b t) (shift_typ c b u)); normalize_shift. *)
(*     replace (t_par (shift_typ c b t) (shift_typ c b u)) with (shift_typ c b (t_par t u)) by auto. *)
(*     rewrite H1. *)
(*     normalize_shift. *)
(*   - eapply (pf_bang _ _ _ _ (shift_ctx c b D1) _ (shift_typ c b t)); normalize_shift. *)
(*     rewrite H0. rewrite shift_ctx_app. reflexivity. *)
(*   - eapply (pf_ques _ _ _ _ (shift_typ c b t)). auto. *)
(*   - eapply (pf_forall _ _ _ _ (shift_ctx c b D1) _ (shift_typ c b u) (shift_typ (c + 1) b t)); normalize_shift. *)
(*     + rewrite typ_subst_shift_typ_comm. *)
(*       (* rewrite typ_subst_shift_typ_comm. normalize_shift. *) *)
(*       admit. *)
(*     + replace ([forall] shift_typ (c + 1) b t) with (shift_typ c b ([forall] t)) by auto. *)
(*       rewrite H1. *)
(*       normalize_shift. *)

(* Lemma Permutation_nil : forall l, P l [] -> l = []. *)
(* Proof. *)
(*   intros. destruct l. *)
(*   - reflexivity. *)
(*   - convertTactics.convert_multiset. permutation_solver. *)
(* Qed. *)

(* Lemma Permutation_rel_nil : forall l, l ≡[P] [] -> l = []. *)
(* Proof. *)
(*   intros. normalize_auxH. *)
(*   apply Permutation_nil; auto. *)
(* Qed. *)

(* Lemma pf_cf_tensor_inv : forall c G D D' t u, *)
(*     ⦃ c; G; D ⊢cf ⦄ -> *)
(*     D ≡[P] (D' ++ [t ⊗ u]) -> *)
(*     ⦃ c; G; D' ++ [t] ++ [u] ⊢cf ⦄. *)
(* Proof. *)
(*   intros c G D D' t u HG HP. *)
(*   revert D' t u HP. *)
(*   induction HG; intros. *)
(*   - apply Permutation_rel_split2 in HP. *)
(*     destruct HP as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]]. *)
(*     + symmetry in HP1. eapply Permutation_rel_singleton_nil in HP1 as (-> & HP1). *)
(*       rewrite <- HP1 in *. replace ([] ++ [dual (t ⊗ u)]) with [dual (t ⊗ u)] by auto. *)
(*       eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP2. *)
(*       assert ([dual (t ⊗ u0)] ++ [t] ++ [u0] ≡[P] [t] ++ [u0] ++ [dual (t ⊗ u0)]). {convertTactics.convert_multisetperm. permutation_solver. } symmetry in H2. apply H2. *)
(*       inversion H0. *)
(*       eapply (pf_par _ _ _ _ [t] [u0]). *)
(*       ++ eapply pf_id; auto. *)
(*       ++ eapply pf_id; auto. *)
(*       ++ simpl. reflexivity. *)
(*     + symmetry in HP1. eapply Permutation_rel_singleton_nil in HP1 as (-> & HP1). *)
(*       apply dual_eq_iff in HP1. rewrite dual_involutive in HP1. rewrite <- HP1 in *. *)
(*       replace ([dual (t ⊗ u0)] ++ []) with ([dual (t ⊗ u0)]) in HP2 by auto. *)
(*       eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP2. assert ([t] ++ [u0] ++ [dual (t ⊗ u0)] ≡[P] [dual (t ⊗ u0)] ++ [t] ++ [u0]). {convertTactics.convert_multisetperm. permutation_solver. } apply H2. *)
(*       inversion H0. *)
(*       apply wf_typ_dual_inv in H5, H6. *)
(*       eapply (pf_par _ _ _ _ [t] [u0]). *)
(*       ++ eapply pf_id; auto. *)
(*       ++ eapply pf_id; auto. *)
(*       ++ simpl. reflexivity. *)
(*   - eapply pf_absorb; try eassumption. *)
(*     eapply pf_perm_rel. tauto. reflexivity. assert (((D' ++ [t]) ++ [t0] ++ [u]) ≡[P]((D' ++ [t0] ++ [u]) ++ [t])). {convertTactics.convert_multisetperm. permutation_solver. } apply H1. *)
(*     eapply IHHG. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - inversion H. *)
(*   - symmetry in HP. eapply Permutation_rel_singleton_nil in HP as (_ & HContra). *)
(*     discriminate. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_one. *)
(*     2: { *)
(*       assert (D'0 ++ [t] ++ [u] ≡[P] (l1' ++ [t] ++ [u]) ++ [[1]]). *)
(*       {convertTactics.convert_multisetperm. permutation_solver. } *)
(*       apply H0. *)
(*     } *)
(*     apply IHHG. assumption. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]. *)
(*     + injection HP1; intros; subst. *)
(*       eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP2. reflexivity. *)
(*       auto. *)
(*     + eapply pf_tensor. *)
(*       2: { *)
(*         assert (D'0 ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [t ⊗ u]). *)
(*         { *)
(*           convertTactics.convert_multisetperm. permutation_solver. *)
(*         } *)
(*         apply H0. } *)
(*       eapply pf_perm_rel. tauto. reflexivity. assert ((l1' ++ [t] ++[u]) ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [t] ++ [u]). *)
(*       {convertTactics.convert_multisetperm. permutation_solver. } *)
(*       apply H0. *)
(*       apply IHHG. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HP. rewrite app_assoc in HP. eapply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     apply Permutation_rel_split2 in HP1. *)
(*     destruct HP1 as [[l3' [HP'1 HP'2]] | [l4' [HP'1 HP'2]]]. *)
(*     + eapply pf_par. *)
(*       3: { *)
(*         assert (D' ++ [t0] ++ [u0] ≡[P] ((l3' ++ [t0] ++ [u0]) ++ D2 ++ [t_par t u])). *)
(*         { convertTactics.convert_multisetperm. permutation_solver. } *)
(*         apply H0. *)
(*       } *)
(*       ++  *)
(*         eapply pf_perm_rel. tauto. reflexivity. *)
(*         assert ((l3' ++ [t]) ++ [t0] ++ [u0] ≡[P] (l3' ++ [t0] ++ [u0]) ++ [t]). *)
(*         {convertTactics.convert_multisetperm. permutation_solver. } *)
(*         apply H0. *)
(*         apply IHHG1. convertTactics.convert_multisetperm. permutation_solver. *)
(*       ++ assumption. *)
(*     + eapply pf_par. *)
(*       3: { *)
(*         assert (D' ++ [t0] ++ [u0] ≡[P] D1 ++ (l4' ++ [t0] ++ [u0]) ++ [t_par t u]). *)
(*         { convertTactics.convert_multisetperm. permutation_solver. } *)
(*         eassumption. *)
(*       } *)
(*       ++ assumption. *)
(*       ++ eapply pf_perm_rel. tauto. reflexivity. *)
(*          assert ((l4' ++ [u]) ++ [t0] ++ [u0] ≡[P] (l4' ++ [t0] ++ [u0]) ++ [u]). *)
(*          {convertTactics.convert_multisetperm. permutation_solver. } *)
(*          eassumption. *)
(*          apply IHHG2. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_bang. *)
(*     2: { *)
(*       assert (D' ++ [t0] ++ [u] ≡[P] (l1' ++ [t0] ++ [u]) ++ [[!]t]). *)
(*       { convertTactics.convert_multisetperm. permutation_solver. } *)
(*       eassumption. *)
(*     } *)
(*     apply IHHG. assumption. *)
(*   - symmetry in HP. eapply Permutation_rel_singleton_nil in HP as (_ & HP). *)
(*     discriminate. *)
(*   - rewrite H0 in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_forall. eassumption. *)
(*     2: { *)
(*       assert (D' ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [[forall]t]). *)
(*       { convertTactics.convert_multisetperm. permutation_solver. } *)
(*       eassumption. *)
(*     } *)
(*     eapply pf_perm_rel. tauto. reflexivity. *)
(*     assert ((l1' ++ [typ_subst c u t]) ++ [t0] ++ [u0] ≡[P] (l1' ++ [t0] ++ [u0]) ++ [typ_subst c u t]). *)
(*     {convertTactics.convert_multisetperm. permutation_solver. } *)
(*     eassumption. *)
(*     apply IHHG. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_exists. *)
(*     2: { *)
(*       assert (D' ++ [t] ++ [u0] ≡[P] (l1' ++ [t] ++ [u0]) ++ [[exists]u]). *)
(*       {convertTactics.convert_multisetperm. permutation_solver. } *)
(*       eassumption. *)
(*     } *)
(*     repeat rewrite shift_ctx_app. *)
(*     eapply pf_perm_rel. tauto. reflexivity. *)
(*     assert ((shift_ctx c 1 l1' ++ [u]) ++ (shift_ctx c 1 [t]) ++ (shift_ctx c 1 [u0]) ≡[P] (shift_ctx c 1 l1' ++ shift_ctx c 1 [t] ++ shift_ctx c 1 [u0]) ++ [u]). *)
(*     {convertTactics.convert_multisetperm. permutation_solver. } *)
(*     eassumption. *)
(*     eapply IHHG. *)
(*     rewrite HP1. rewrite shift_ctx_app. simpl. *)
(*     convertTactics.convert_multisetperm. permutation_solver. *)
(* Qed. *)



Ltac WF_CTX :=
  repeat
    match goal with
    | H : ?C ≡[P] ?D |- _ => destruct H as [H _]
    | H : P ?C ?D |- wf_ctx ?A ?C =>
        apply Permutation_symmetric in H; apply (wf_ctx_Permutation_inj _ _ _ H); clear H
    | H : wf_ctx ?C (?D ++ ?E) |- _ => apply wf_ctx_app in H; destruct H
    | _ : _ |- wf_ctx ?C (?D ++ ?E) => apply wf_ctx_app; split
    | H : wf_ctx ?C [?U] |- _ => apply wf_ctx_single in H
    | _ : _ |- wf_ctx ?C [?U] => apply wf_ctx_single
    | H : wf_ctx (1 + ?C) (shift_ctx ?C 1 ?D) |- _ => apply shift_ctx_strengthen in H
    end.  

Ltac normalize_wf_ctxH' :=
  repeat (match goal with
  | [ H: wf_ctx ?C1 ?D /\ wf_ctx ?C2 ?E |- _ ] => destruct H
  | [ H: wf_ctx ?C1 (?D ++ ?E) |- _ ] => apply wf_ctx_app in H
  | [ H: wf_ctx ?C1 (?a :: ?D) |- _ ] => replace (a :: D) with ([a] ++ [D]) in H by auto
  | [ H: wf_ctx ?C1 [?a] |- _ ] => apply wf_ctx_single in H
  | [ H: wf_typ ?C1 (dual ?a) |- _ ] => apply wf_typ_dual_inv in H
  | [ H: wf_typ ?C1 ([!] ?a) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 ([?] ?a) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 (?a ⊗ ?b) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 (t_par ?a ?b) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 ([forall] ?t) |- _ ] => inversion H; clear H; subst
  | [ H: wf_typ ?C1 ([exists] ?t) |- _ ] => inversion H; clear H; subst
  end).

Ltac normalize_wf_ctx :=
  repeat
    (match goal with
     | [ |- wf_ctx ?C1 ?D /\ wf_ctx ?C2 ?E ] => split
     | [ |- wf_ctx ?C1 (?D ++ ?E) ] => apply wf_ctx_app
     | [ |- wf_ctx ?C1 (?a :: ?D) ] => replace (a :: D) with ([a] ++ [D]) by auto
     | [ |- wf_ctx ?C1 [?a] ] => apply wf_ctx_single
     | [ |- wf_typ ?C1 (dual ?a) ] => apply wf_typ_dual
     | [ |- wf_typ ?C1 ([!] ?a) ] => constructor 
     | [ |- wf_typ ?C1 ([?] ?a) ] => constructor
     | [ |- wf_typ ?C1 (?a ⊗ ?b) ] => constructor
     | [ |- wf_typ ?C1 (t_par ?a ?b) ] => constructor
     | [ |- wf_typ ?C1 ([forall] ?t) ] => constructor
     | [ |- wf_typ ?C1 ([exists] ?t) ] => constructor
     end
    ; eauto).

Ltac normalize_wf_ctx_more :=
  repeat (match goal with
  | [ H: pf ?PID ?PCUT ?c ?G ?D |- _ ] => apply pf_wf_typ in H
  end).

Ltac wf_ctx_solver :=
  normalize_wf_ctx_more; normalize_wf_ctxH'; normalize_wf_ctx; auto.

Example test3 : forall (t1 t2 t3 : typ) G c, wf_ctx c (G ++ [t1 ⊗ t2] ++ (G ++ [dual t3])) -> wf_ctx c (G ++ [t_par t1 t2] ++ [dual (dual t3)]).
Proof.
  intros.
  wf_ctx_solver.
Qed.
  (* Ltac wf_ctx_solver := *)
  (* repeat (eauto; *)
  (*         match goal with *)
  (*         | [ H: wf_ctx ?C1 ?D /\ wf_ctx ?C2 ?E |- _ ] => destruct H *)
  (*         | [ H: wf_ctx ?C1 (?D ++ ?E) |- _ ] => apply wf_ctx_app in H *)
  (*         | [ |- wf_ctx ?C1 (?D ++ ?E) ] => apply wf_ctx_app; split *)
  (*         | [ H: wf_ctx ?C1 (?a :: ?D) |- _ ] => replace (a :: D) with ([a] ++ [D]) in H by auto
  | [ H: wf_typ ?C1 [dual ?D] |- wf_typ ?C1 [?D] ] => apply wf_typ_dual_inv in H; auto
  | [ H: wf_ctx ?C1 [[!] ?D] |- _ ] => inversion H
  | [ H: wf_ctx ?C1 [[?] ?D] |- _ ] => inversion H
                 end).
 *)

(* Lemma pf_cf_bang_inv : forall c G G1 D1 D t, *)
(*     ⦃ c; G1; D ⊢cf ⦄ -> *)
(*     D ≡[P] D1 ++ [[!] t] -> *)
(*     G ≡[P] G1 ++ [t] -> *)
(*     ⦃ c; G; D1 ⊢cf ⦄. *)
(* Proof. *)
(*   intros c G G1 D1 D t HG HPD HPG. *)
(*   revert G D1 t HPD HPG. *)
(*   induction HG; intros. *)
(*   - apply Permutation_rel_split2 in HPD. *)
(*     destruct HPD as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]]. *)
(*     + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1. destruct HP1 as (-> & <-). *)
(*       eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP2. simpl. reflexivity.  *)
(*       apply pf_ques. *)
(*       eapply pf_absorb with (t := t). *)
(*       ++ wf_ctx_solver. *)
(*          (* apply wf_ctx_app; split; try eassumption. *) *)
(*          (* unfold wf_ctx. intros. *) *)
(*          (* apply In_singleton in H2. *) *)
(*          (* rewrite H2; inversion H0; auto. *) *)
(*       ++ auto. *)
(*       ++ eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_exchange. *)
(*          eapply pf_id; inversion H0; auto. *)
(*          apply (wf_ctx_perm_iff HPG). *)
(*          wf_ctx_solver. *)
(*          (* apply wf_ctx_app. intuition. *) *)
(*          (*      unfold wf_ctx. intros. apply In_singleton in H5. *) *)
(*          (*      subst; auto. *) *)
(*     + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1. destruct HP1 as (-> & HP1). *)
(*       apply dual_swap_iff in HP1. rewrite <- HP1 in *. *)
(*       inversion H0. *)
(*       eapply pf_perm_rel. tauto. reflexivity. simpl in HP2. rewrite <- HP2. reflexivity. *)
(*       eapply pf_ques. *)
(*       eapply pf_absorb with (t := t). *)
(*       ++ wf_ctx_solver. *)
(*         (* apply wf_ctx_app; split; eauto. *) *)
(*         (*  unfold wf_ctx; intros. *) *)
(*         (*  apply In_singleton in H5; subst. *) *)
(*         (*  apply wf_typ_dual_inv in H4; auto. *) *)
(*       ++ auto. *)
(*       ++ eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_exchange.  *)
(*          eapply pf_id; auto. *)
(*          +++ wf_ctx_solver. *)
(*            (* apply wf_typ_dual_inv in H4; auto. *) *)
(*          +++ apply (wf_ctx_perm_iff HPG). *)
(*              wf_ctx_solver. *)
(*              (* apply wf_ctx_app; split; auto. *) *)
(*              (* unfold wf_ctx; intros. apply In_singleton in H5; subst. *) *)
(*              (* apply wf_typ_dual_inv in H4; auto. *) *)
(*   - rewrite H0, <- app_assoc in HPG. *)
(*     assert (⦃ c; G ++ [t]; (D1 ++ [[!] t0] ++ [t]) ⊢cf ⦄). *)
(*     { *)
(*       eapply pf_perm_rel. tauto. apply H0. assert (D ++ [t] ≡[P] D1 ++ [[!] t0] ++ [t]). {convertTactics.convert_multisetperm. permutation_solver. } *)
(*       apply H1. *)
(*       assumption. *)
(*     } *)
(*     eapply pf_absorb.  *)
(*     2: { *)
(*       rewrite HPG, app_assoc. apply Permutation_rel_assoc_swap. *)
(*       (* assert (G0 ≡[P] (G ++ [t0]) ++ [t]). *) *)
(*       (* {convertTactics.convert_multisetperm. permutation_solver. } *) *)
(*       (* eassumption. *) *)
(*     } *)
(*     { wf_ctx_solver. } *)
(*     eapply IHHG. *)
(*     2: { rewrite H0, HPG, <- app_assoc. reflexivity. } *)
(*     convertTactics.convert_multisetperm. permutation_solver. *)
(*   - inversion H. *)
(*   - symmetry in HPD. apply Permutation_rel_singleton_nil in HPD as (_ & HPD). discriminate. *)
(*   - rewrite H in HPD. apply Permutation_rel_split_last in HPD. *)
(*     destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate. *)
(*     eapply pf_one. *)
(*     2: {eassumption. } *)
(*     eapply IHHG. *)
(*     + rewrite <- HPD3. eassumption. *)
(*     + assumption. *)
(*   - rewrite H in HPD. apply Permutation_rel_split_last in HPD. *)
(*     destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate. *)
(*     eapply pf_tensor. *)
(*     2: { rewrite HPD2, <- HPD3. reflexivity. } *)
(*     eapply IHHG. *)
(*     2: { eassumption. } *)
(*     convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HPD. rewrite app_assoc in HPD. apply Permutation_rel_split_last in HPD. *)
(*     destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate. *)
(*     apply Permutation_rel_split2 in HPD1. *)
(*     destruct HPD1 as [[l3' [HPD'1 HPD'2]] | [l4' [HPD'1 HPD'2]]]. *)
(*     + eapply pf_par. *)
(*       3: { *)
(*         assert (D0 ≡[P] l3' ++ D2 ++ [t_par t u]). *)
(*         { convertTactics.convert_multisetperm. permutation_solver. } *)
(*         eassumption. *)
(*       } *)
(*       ++ eapply IHHG1. *)
(*          2: {eassumption. } *)
(*          convertTactics.convert_multisetperm. permutation_solver. *)
(*       ++ eapply pf_weakening. tauto. eassumption.  *)
(*          assert (⦃ c; G; (l3' ++ [[!] t0]) ++ [t] ⊢cf ⦄). *)
(*          {eapply pf_perm_rel. tauto. reflexivity. rewrite <- HPD'1. reflexivity. assumption. } *)
(*          wf_ctx_solver. *)
(*          assumption. *)
(*     + eapply pf_par. *)
(*       3: { *)
(*         assert (D0 ≡[P] D1 ++ l4' ++ [t_par t u]). *)
(*         {convertTactics.convert_multisetperm. permutation_solver. } *)
(*         eassumption. *)
(*       } *)
(*       ++ eapply pf_weakening. tauto. eassumption. *)
(*          assert (⦃ c; G; (l4' ++ [[!] t0]) ++ [u] ⊢cf ⦄). *)
(*          {eapply pf_perm_rel. tauto. reflexivity. rewrite <- HPD'1. reflexivity. assumption. } *)
(*          wf_ctx_solver. *)
(*          assumption. *)
(*       ++ eapply IHHG2. *)
(*          2: {eassumption. } *)
(*          convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HPD. apply Permutation_rel_split_last in HPD. *)
(*     destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]. *)
(*     + inversion HPD1; subst. *)
(*       eapply pf_perm_rel. *)
(*       ++ tauto. *)
(*       ++ symmetry in HPG. apply HPG. *)
(*       ++ apply HPD2. *)
(*       ++ assumption. *)
(*     + eapply pf_bang. *)
(*       2: { rewrite HPD2. rewrite <- HPD3. reflexivity. } *)
(*       eapply IHHG. *)
(*       ++ rewrite HPD1. reflexivity. *)
(*       ++ convertTactics.convert_multisetperm. permutation_solver. *)
(*   - symmetry in HPD. apply Permutation_rel_singleton_nil in HPD. *)
(*     destruct HPD as (_ & HPD). discriminate. *)
(*   - rewrite H0 in HPD. apply Permutation_rel_split_last in HPD. *)
(*     destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate. *)
(*     eapply pf_forall. eassumption. *)
(*     2: { rewrite HPD2, <- HPD3. reflexivity. } *)
(*     eapply IHHG. *)
(*     2: { eassumption. } *)
(*     convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HPD. apply Permutation_rel_split_last in HPD. *)
(*     destruct HPD as [[HPD1 HPD2] | [l1' [l2' [HPD1 [HPD2 HPD3]]]]]; try discriminate. *)
(*     eapply pf_exists. *)
(*     2: { rewrite HPD2, <- HPD3. reflexivity. } *)
(*     eapply IHHG. *)
(*     2: { rewrite HPG. rewrite shift_ctx_app. simpl. reflexivity. } *)
(*     rewrite HPD1, shift_ctx_app. *)
(*     simpl. convertTactics.convert_multisetperm. permutation_solver. *)
(* Qed. *)

(* Lemma pf_cf_ques_inv : forall c G D D' t, *)
(*     D ≡[P] D' ++ [[?]t] -> *)
(*     ⦃ c; G; D ⊢cf ⦄ -> ⦃c; G; D' ++ [t] ⊢cf ⦄. *)
(* Proof. *)
(*   intros c G D D' t HP HG. *)
(*   revert D' t HP. *)
(*   induction HG; intros. *)
(*   - apply Permutation_rel_split2 in HP. *)
(*     destruct HP as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]]. *)
(*     + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & <-).  *)
(*       eapply pf_perm_rel. tauto. reflexivity. simpl in HP2. rewrite <- HP2. apply Permutation_rel_exchange. *)
(*       eapply pf_bang. *)
(*       2: {reflexivity. } *)
(*       eapply pf_absorb. *)
(*       2: {reflexivity. } *)
(*       wf_ctx_solver. *)
(*       apply pf_id; wf_ctx_solver. *)
(*     + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1). *)
(*       apply dual_swap_iff in HP1 as <-. *)
(*       eapply pf_perm_rel. tauto. reflexivity. simpl in HP2. rewrite <- HP2. apply Permutation_rel_exchange. *)
(*       eapply pf_bang. *)
(*       2: {reflexivity. } *)
(*       eapply pf_absorb. *)
(*       2: {reflexivity. } *)
(*       wf_ctx_solver. *)
(*       apply pf_id; wf_ctx_solver. *)
(*   - eapply pf_absorb; try eassumption. *)
(*     eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap.  *)
(*     apply IHHG. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - inversion H. *)
(*   - symmetry in HP. apply Permutation_rel_singleton_nil in HP as (_ & HP). discriminate. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_one. 2: {rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. } *)
(*     eapply IHHG. assumption.  *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_tensor. *)
(*     2: { rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. } *)
(*     eapply pf_perm_rel. tauto. reflexivity. assert ((l1' ++ [t] ++ [u]) ++ [t0] ≡[P] (l1' ++ [t0]) ++ [t] ++ [u]). {convertTactics.convert_multisetperm. permutation_solver. } eassumption. *)
(*     eapply IHHG. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HP. rewrite app_assoc in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     apply Permutation_rel_split2 in HP1. *)
(*     destruct HP1 as [[l3' [HP'1 HP'2]] | [l4' [HP'1 HP'2]]]. *)
(*     + eapply pf_par. *)
(*       3: { *)
(*         assert (D' ++ [t0] ≡[P] (l3' ++ [t0]) ++ D2 ++ [t_par t u]). *)
(*         {convertTactics.convert_multisetperm. permutation_solver. } *)
(*         eassumption. *)
(*       } *)
(*       ++ eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap.          apply IHHG1. convertTactics.convert_multisetperm. permutation_solver. *)
(*       ++ assumption. *)
(*     + eapply pf_par. *)
(*       3: { *)
(*         assert (D' ++ [t0] ≡[P] D1 ++ (l4' ++ [t0]) ++ [t_par t u]). *)
(*         {convertTactics.convert_multisetperm. permutation_solver. } *)
(*         eassumption. *)
(*       } *)
(*       ++ assumption. *)
(*       ++ eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap. *)
(*          apply IHHG2. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_bang. *)
(*     2: { *)
(*       rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. *)
(*     } *)
(*     apply IHHG. eassumption. *)
(*   - symmetry in HP. apply Permutation_rel_singleton_nil in HP as (-> & HP). *)
(*     injection HP. intros ->. simpl; assumption. *)
(*   - rewrite H0 in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_forall. *)
(*     3: { rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. } *)
(*     eassumption. *)
(*     eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap. *)
(*     apply IHHG. convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2] | [l1' [l2' [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_exists. *)
(*     2: {rewrite HP2, <- HP3. apply Permutation_rel_assoc_swap. } *)
(*     repeat rewrite shift_ctx_app. *)
(*     eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap. *)
(*     eapply IHHG. rewrite HP1. repeat rewrite shift_ctx_app. simpl. *)
(*     convertTactics.convert_multisetperm. permutation_solver. *)
(* Qed. *)

(* Lemma pf_par_inv : forall c G D D1 D2 t u, *)
(*     ⦃ c; G; D ⊢cf ⦄ -> *)
(*       D ≡[P] (D1 ++ D2 ++ [t_par t u]) -> *)
(*       ⦃ c; G; D1 ++ [t] ⊢cf ⦄ -> ⦃ c; G; D2 ++ [u] ⊢cf ⦄. *)
(* Proof. *)
(*   intros c G D D1 D2 t u HG HP HG1. *)
(*   revert D1 D2 t u HP HG1. *)
(*   induction HG; intros. *)
(*   - rewrite app_assoc in HP. apply Permutation_rel_split2 in HP. *)
(*     destruct HP as [[l1' [HP1 HP2]] | [l1' [l2' [HP1 HP2]]]]. *)
(*     + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1). *)
(*       apply Permutation_rel_singleton_app in HP2. destruct HP2 as [[HP3 HP4] | [HP3 HP4]]. *)
(*       ++  *)
(*   -  *)





  
  (* intros c G D t u HG. *)
  (* revert D1 D2 t u HP. *)
  (* induction HG; intros. *)
  (* - rewrite app_assoc in HP. apply Permutation_rel_split2 in HP. *)
  (*   destruct HP as [[l1' [HP1 HP2]] | [l1' [l2' [HP1 HP2]]]]. *)
  (*   + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1). *)
  (*     apply Permutation_rel_singleton_app in HP2. destruct HP2 as [[HP3 HP4] | [HP3 HP4]]. *)
  (*     ++  *)
  (*     destruct HP2 as [[-> ->] | [-> ->]]. *)
  (*     ++ subst. *)

      




  (* c : nat *)
  (* G : ctx *)
  (* D2 : list typ *)
  (* H4 : ⦃ c; G; D2 ⊢cf ⦄ *)
  (* ============================ *)
  (* ∀ (D2' D' : list typ) (t u : typ), *)
  (*   D2 ≡[ P] D2' ++ [dual (t ⊗ u)] *)
  (*   → c ⊢ t ⊗ u wf *)
  (*     → (⦃ c; G; (D' ++ [t] ++ [u]) ⊢cf ⦄) *)
  (*       → (∀ (u0 : typ) (D3 D1' D2'0 : list typ), *)
  (*            D' ++ [t] ++ [u] ≡[ P] D1' ++ [u0] *)
  (*            → D3 ≡[ P] D2'0 ++ [dual u0] *)
  (*              → c ⊢ u0 wf → (⦃ c; G; D3 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2'0) ⊢cf ⦄) *)
  (*         → ⦃ c; G; (D' ++ D2') ⊢cf ⦄ *)

(* Lemma cut_admissibility_aux_tensor : forall c t u G D1 D2 D2', *)
(*     c ⊢ (t ⊗ u) wf -> *)
(*     D2 ≡[P] D2' ++ [dual (t ⊗ u)] -> *)
(*     ⦃ c; G; D2 ⊢cf ⦄ -> *)
(*     (forall u' D3 D1' D2', D1 ++ [t] ++ [u] ≡[P] D1' ++ [u'] -> D3 ≡[P] D2' ++ [dual u'] -> c ⊢ u' wf -> ⦃ c; G; D3 ⊢cf ⦄ -> ⦃ c; G; (D1' ++ D2') ⊢cf ⦄) -> *)
(*     ⦃ c; G; (D1 ++ [t] ++ [u]) ⊢cf ⦄ -> *)
(*     ⦃ c; G; (D1 ++ D2') ⊢cf ⦄. *)
(* Proof. *)
(*   intros c t u G D1 D2 D2' HWFu HP HG1 IH HG2. *)
(*   revert t u D1 D2' HWFu HP IH HG2. *)
(*   induction HG1; intros. *)
(*   - apply Permutation_rel_split2 in HP. *)
(*     destruct HP as [[l1 [HP1 HP2]]| [l2 [HP1 HP2]]]. *)
(*     + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1). *)
(*       subst. rewrite dual_involutive in HP2. simpl in HP2. *)
(*       eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP2. reflexivity. *)
(*       eapply pf_tensor; eauto. *)
(*       reflexivity. *)
(*     + symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (-> & HP1). *)
(*       apply dual_eq_iff in HP1. subst. rewrite app_nil_r in HP2. *)
(*       eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP2. reflexivity. *)
(*       eapply pf_tensor; eauto. *)
(*       reflexivity. *)
(*   - eapply pf_absorb; try eassumption. *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite <- app_assoc. reflexivity. *)
(*     eapply IHHG1. *)
(*     + eassumption. *)
(*     + convertTactics.convert_multisetperm. permutation_solver. *)
(*     + apply IH. *)
(*     + assumption. *)
(*   - inversion H. *)
(*   - symmetry in HP. *)
(*     apply Permutation_rel_singleton_nil in HP as (_ & Hcontra). *)
(*     discriminate. *)
(*   - rewrite H in HP. *)
(*     apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2]|[l1 [l2 [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite HP2. reflexivity. *)
(*     eapply pf_one. *)
(*     2: { rewrite app_assoc. reflexivity. } *)
(*     eapply IHHG1. *)
(*     + eassumption. *)
(*     (* TODO: Check this, why is conversion tactic fails *) *)
(*     + unfold_destruct_relH HP1. unfold_destruct_relH HP2. unfold_destruct_relH HP3. *)
(*       assert (P D' (l2 ++ [dual (t ⊗ u)])). *)
(*       { *)
(*         convertTactics.convert_multiset. *)
(*         apply (@Perm_MultisetPerm_inj _ _ _ P _ _) in HP1. *)
(*         apply (@Perm_MultisetPerm_surj _ _ _ P _ _). *)
(*         permutation_solver. *)
(*       } *)
(*       eexists; auto. *)
(*     + apply IH. *)
(*     + assumption. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2]|[l1 [l2 [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite HP2. reflexivity. *)
(*     eapply pf_tensor. *)
(*     2: { rewrite app_assoc. reflexivity. } *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite <- app_assoc. reflexivity. *)
(*     eapply IHHG1; try eassumption. *)
(*     convertTactics.convert_multisetperm. permutation_solver. *)
(*   - rewrite H, app_assoc in HP. apply Permutation_rel_split_last in HP. *)
(*     (* destruct HP as [[HP1 HP2]|[l1 [l2 [HP1 [HP2 HP3]]]]]. *) *)
(*     (* + simpl in HP1. injection HP1. intros. rewrite H0, H1 in *. clear HP1. *) *)
(*     admit. *)
(*   - rewrite H in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2]|[l1 [l2 [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite HP2. reflexivity. *)
(*     eapply pf_bang. *)
(*     2: {rewrite app_assoc. reflexivity. } *)
(*     eapply IHHG1. *)
(*     + eassumption. *)
(*     (* TODO: Check this, why is conversion tactic failing *) *)
(*     + normalize_auxH. *)
(*       assert (P D1 (l2 ++ [dual (t0 ⊗ u)])). *)
(*       { convertTactics.convert_multiset. apply Perm_MultisetPerm_inj in HP1. *)
(*         apply Perm_MultisetPerm_surj. permutation_solver. } *)
(*       eexists; auto. *)
(*     + intros. eapply pf_weakening. tauto. reflexivity. apply pf_wf_typ in HG1 as (HG1 & _). apply wf_ctx_app in HG1. intuition. *)
(*       admit. *)
(*     + admit. *)
(*   - symmetry in HP. eapply Permutation_rel_singleton_nil in HP as (_ & HP). *)
(*     discriminate. *)
(*   - rewrite H0 in HP. apply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2]|[l1 [l2 [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite HP2. reflexivity. *)
(*     eapply pf_forall. apply H. *)
(*     2: {rewrite app_assoc. reflexivity. } *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite <- app_assoc. reflexivity. *)
(*     eapply IHHG1. *)
(*     + apply HWFu. *)
(*     + convertTactics.convert_multisetperm. clear HP2 H0. permutation_solver. *)
(*     + assumption. *)
(*     + admit. *)
(*   - rewrite H in HP. eapply Permutation_rel_split_last in HP. *)
(*     destruct HP as [[HP1 HP2]|[l1 [l2 [HP1 [HP2 HP3]]]]]; try discriminate. *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite HP2. reflexivity. *)
(*     eapply pf_exists. *)
(*     2: {rewrite app_assoc. reflexivity. } *)
(*     rewrite shift_ctx_app. *)
(*     eapply pf_perm_rel. tauto. reflexivity. rewrite <- app_assoc. reflexivity. *)
(*     eapply (IHHG1 (shift_typ c 1 t) (shift_typ c 1 u0)). *)
(*     + *)
(*       replace c with (0 + c) in HWFu. *)
(*       eapply wf_typ_shift in HWFu. simpl in HWFu. *)
(*       eapply HWFu. *)
(*       reflexivity. *)
(*     + rewrite HP1. rewrite shift_ctx_app. rewrite HP3. simpl. *)
(*     (*   repeat dual_shift_typ_comm. *) *)
(*     (*   convertTactics.convert_multisetperm. clear HP1 HP2 HP3 H. permutation_solver. *) *)
(*     (* + Search shift_ctx. *) *)

                    
(* Admitted. *)

(* Lemma cut_admissibility_aux_id : *)
(*   forall c G u u' D2 D1' D2', *)
(*     [u] ++ [dual u] ≡[P] D1' ++ [u'] -> *)
(*     D2 ≡[P] D2' ++ [dual u'] -> *)
(*     ⦃ c; G; D2 ⊢cf ⦄ -> *)
(*     ⦃ c; G; (D1' ++ D2') ⊢cf ⦄. *)
(* Proof. *)
(*   intros.  *)
(*     PInvert. *)
(*     + eapply pf_perm. tauto. apply Permutation_reflexive. apply Permutation_symmetric. *)
(*       eapply Permutation_transitive; [ | apply H2]. apply Permutation_append; eauto.  *)
(*       apply Permutation_reflexive. *)
(*       assumption. *)
(*     + subst. rewrite dual_involutive in H2. *)
(*       eapply pf_perm. tauto. apply Permutation_reflexive. apply Permutation_symmetric. *)
(*       eapply Permutation_transitive; [ | apply H2]. apply Permutation_append; eauto.  *)
(*       convertTactics.convert_multiset. permutation_solver. *)
(*       assumption. *)
(* Qed. *)
(* Lemma cut_admissibility_aux_absorb : *)
(*   forall c G G' t D u D2 D1' D2' *)
(*     (HWF : wf_ctx c (G ++ [t]))  *)
(*     (HP1 : G' ≡[P] G ++ [t])  *)
(*     (HG1 : ⦃ c; G'; (D ++ [t]) ⊢cf ⦄) *)
(*     (IHpf: forall (u : typ) (D2 D1' D2' : list typ), D ++ [t] ≡[P] D1' ++ [u] -> D2 ≡[P] D2' ++ [dual u] -> (⦃ c; G'; D2 ⊢cf ⦄ -> ⦃ c; G'; (D1' ++ D2') ⊢cf⦄)), *)
(*     D ≡[P] D1' ++ [u] -> D2 ≡[P] D2' ++ [dual u] -> ⦃ c; G'; D2 ⊢cf ⦄ -> ⦃ c; G'; (D1' ++ D2') ⊢cf ⦄. *)
(* Proof. *)
(*   intros. *)
(*     eapply pf_absorb. *)
(*     eassumption. *)
(*     eassumption. *)
(*     assert (⦃c; G'; ((D1' ++ [t]) ++ D2') ⊢cf⦄). *)
(*     { *)
(*       eapply IHpf with (u := u). *)
(*       rewrite <- app_assoc. *)
(*             convertTactics.convert_multisetperm. permutation_solver. *)
(*             eassumption. *)
(*             eassumption. *)
(*     } *)
(*     eapply pf_perm; eauto. *)
(*     apply Permutation_reflexive. *)
(*     convertTactics.convert_multiset. permutation_solver. *)
(* Qed. *)

(* Lemma cut_admissibility_aux_bot : *)
(*   forall c G u D2 D1' D2', *)
(*     wf_ctx c G -> *)
(*     [[⊥]] ≡[P] D1' ++ [u] -> *)
(*     D2 ≡[P] D2' ++ [dual u] -> *)
(*     ⦃ c; G; D2 ⊢cf ⦄ -> *)
(*     ⦃ c; G; (D1' ++ D2') ⊢cf ⦄. *)
(* Proof. *)
(*   intros. *)
(*   PInvert. LInvert. *)
(*   simpl. simpl dual in H0. *)
(*   assert (⦃c ; G; (D2' ++ [[1]]) ⊢cf⦄). *)
(*   { eapply pf_perm. tauto. apply Permutation_reflexive. eapply Permutation_transitive. eapply Permutation_symmetric. *)
(*     apply H0. *)
(*     convertTactics.convert_multiset. permutation_solver. *)
(*     auto. *)
(*     (* eapply perm_comp. eapply Permutation_exchange. *) *)
(*     (* eapply perm_plus. eapply Permutation_symmetric. apply HP2. apply perm_id. apply H0. *) *)
(*   } *)
(*   eapply pf_unit_inv. tauto. *)
(*   2 : { apply H1. }. *)
(*   reflexivity. *)
(* Qed. *)
    
  (* c : nat *)
  (* G : ctx *)
  (* D1, D2, D : list typ *)
  (* t, u : typ *)
  (* H : ⦃ c; G; (D1 ++ [t]) ⊢cf ⦄ *)
  (* H0 : ⦃ c; G; (D2 ++ [u]) ⊢cf ⦄ *)
  (* H1 : D ≡[ P] D1 ++ D2 ++ [t ∥ u] *)
  (* IHpf1 : ∀ (u : typ) (D2 D1' D2' : list typ), D1 ++ [t] ≡[ P] D1' ++ [u] → D2 ≡[ P] D2' ++ [dual u] → c ⊢ u wf → (⦃ c; G; D2 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄ *)
  (* IHpf2 : ∀ (u0 : typ) (D3 D1' D2' : list typ), D2 ++ [u] ≡[ P] D1' ++ [u0] → D3 ≡[ P] D2' ++ [dual u0] → c ⊢ u0 wf → (⦃ c; G; D3 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄ *)
  (* u0 : typ *)
  (* D0, D1', D2' : list typ *)
  (* HP3 : (t ∥ u) = u0 *)
  (* HP4 : D1 ++ D2 ≡[ P] D1' *)
  (* HP2 : D0 ≡[ P] D2' ++ [dual t ⊗ dual u] *)
  (* HWFu : c ⊢ t ∥ u wf *)
  (* H2 : ⦃ c; G; D0 ⊢cf ⦄ *)
  (* ============================ *)
  (* ⦃ c; G; (D1' ++ D2') ⊢cf ⦄ *)
    
(* TODO: Construct a new pf definition that add in an additional parameter, namely the height of the proof, and strong induction on the height of the proof. *)

(* Section PFN. *)
(* End PFN. *)
(* p : bool *)
(*   b : base_type *)
(*   c : nat *)
(*   G : ctx *)
(*   D1, D2, D1', D2' : list typ *)
(*   HP1 : D1 ≡[ P] D1' ++ [t_base p b] *)
(*   HP2 : D2 ≡[ P] D2' ++ [dual (t_base p b)] *)
(*   HWFu : c ⊢ t_base p b wf *)
(*   HG1 : ⦃ c; G; D1 ⊢cf ⦄ *)
(*   HG2 : ⦃ c; G; D2 ⊢cf ⦄ *)
(*   ============================ *)
(*   ⦃ c; G; (D1' ++ D2') ⊢cf ⦄ *)
Section NAT_STRONGIND.
  Variable P : nat -> Prop.
  Hypothesis HP: (forall m, (forall (k : nat), k < m -> P k ) -> P m).
  Lemma strong_ind: forall n, P n.
  Proof.
    intros n. enough (H0 : forall p, p <= n -> P p).
    - apply H0, le_n.
    - induction n; intros.
      + apply HP. intros.
        lia.
      + apply HP. intros.
        apply IHn. lia.
  Qed.
End NAT_STRONGIND.

Inductive vac2_ephem : ctx -> Prop :=
| vac2_empty : vac2_ephem []
| vac2_one : forall D D',
    D ≡[P] D' ++ [[1]] ->
    vac2_ephem D' -> vac2_ephem D
| vac2_tensor : forall D D' t1 t2,
    vac2_ephem (D' ++ [t1] ++ [t2]) ->
    D ≡[P] D' ++ [t1 ⊗ t2] ->
    vac2_ephem D
| vac2_par : forall D D1 D2 t1 t2,
    vac2_ephem (D1 ++ [t1]) ->
    vac2_ephem (D2 ++ [t2]) ->
    D ≡[P] D1 ++ D2 ++ [t_par t1 t2] ->
    vac2_ephem D
| vac2_bang : forall D t,
    vac2_ephem D ->
    vac2_ephem (D ++ [[!]t])
(* | vac2_ques : forall D D' t, *)
(*     D ≡[P] D' ++ [t] -> *)
(*     vac2_ephem D -> *)
(*     vac2_ephem (D' ++ [[?]t]) *)
| vac2_comp : forall D1 D2,
    vac2_ephem D1 ->
    vac2_ephem D2 ->
    vac2_ephem (D1 ++ D2)
| vac2_perm : forall D1 D2,
    D1 ≡[P] D2 -> 
    vac2_ephem  D1 ->
    vac2_ephem D2
.

Instance Proper_vac2_ephem : Proper (Permutation_rel P ==> flip (impl)) vac2_ephem.
Proof.
  intros. unfold Proper, "==>".
  intros.
  unfold flip, impl.
  apply vac2_perm. symmetry. auto.
Qed.

  (* PID, PCUT : typ → Prop *)
  (* PID_dual : ∀ u : typ, PID u ↔ PID (dual u) *)
  (* D, D1, D2 : list typ *)
  (* t1, t2 : typ *)
  (* H : vac2_ephem (D1 ++ [t1]) *)
  (* H0 : vac2_ephem (D2 ++ [t2]) *)
  (* H1 : D ≡[ P] D1 ++ D2 ++ [t1 ∥ t2] *)
  (* IHvac2_ephem1 : ∀ D2 D3 : list typ, D2 ++ D3 ≡[ P] D1 ++ [t1] → vac2_ephem D2 ∧ vac2_ephem D3 *)
  (* IHvac2_ephem2 : ∀ D1 D3 : list typ, D1 ++ D3 ≡[ P] D2 ++ [t2] → vac2_ephem D1 ∧ vac2_ephem D3 *)
  (* D0, D3, l1' : list typ *)
  (* HP1 : D0 ≡[ P] l1' ++ [t1 ∥ t2] *)
  (* HP2 : l1' ++ D3 ≡[ P] D1 ++ D2 *)
  (* ============================ *)
  (* vac2_ephem D0 ∧ vac2_ephem D3 *)

Lemma vac2_ephem_app : forall D1 D2, vac2_ephem (D1 ++ D2) -> vac2_ephem D1 /\ vac2_ephem D2.
Proof.
  intros. assert (exists D, D1 ++ D2≡[P] D). {exists (D1 ++ D2). reflexivity. }
  destruct H0.
  apply (vac2_perm _ _ H0) in H.
  revert D1 D2 H0.
  induction H; intros.
  - apply Permutation_rel_length in H0.
    destruct D1; try discriminate.
    destruct D2; try discriminate.
    split; constructor.
  - rewrite H in H1. apply Permutation_rel_split2 in H1.
    destruct H1 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + apply IHvac2_ephem in HP2 as (HPP1 & HPP2).
      split; auto.
      rewrite HP1. apply vac2_comp; auto.
      eapply vac2_one. 2: {apply vac2_empty. } reflexivity.
    + apply IHvac2_ephem in HP2 as (HPP1 & HPP2).
      split; auto.
      rewrite HP1. apply vac2_comp; auto.
      eapply vac2_one. 2: {apply vac2_empty. } reflexivity.
  - rewrite H0 in H1. apply Permutation_rel_split2 in H1.
    destruct H1 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + assert ((l1' ++ [t1] ++ [t2]) ++ D2 ≡[P] D' ++ [t1] ++ [t2]).
      {convertTactics.convert_multisetperm. permutation_solver. }
      apply IHvac2_ephem in H1. destruct H1.
      split; auto.
      rewrite HP1.
      eapply vac2_tensor; eauto. reflexivity.
    + assert (D1 ++ (l2' ++ [t1] ++ [t2]) ≡[P] D' ++ [t1] ++ [t2]).
      {convertTactics.convert_multisetperm. permutation_solver. }
      apply IHvac2_ephem in H1. destruct H1.
      split; auto.
      rewrite HP1.
      eapply vac2_tensor; eauto. reflexivity.
  - rewrite H1 in H2. rewrite app_assoc in H2. apply Permutation_rel_split2 in H2.
    destruct H2 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + apply Permutation_rel_split4 in HP2. destruct HP2 as (l211 & l212 & l221 & l222 & HP'1 & HP'2 & HP'3 & HP'4).
      assert ((l211 ++ [t1]) ++ l212 ≡[P] D1 ++ [t1]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac2_ephem1 in H2. destruct H2.
      assert (l222 ++ (l221 ++ [t2]) ≡[P] D2 ++ [t2]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac2_ephem2 in H4. destruct H4.
      split.
      ++ rewrite HP1, HP'3, <- app_assoc. eapply vac2_par.
         3: {reflexivity. }
         +++ assumption.
         +++ assumption.
      ++ rewrite HP'4. eapply vac2_comp; auto.
    + apply Permutation_rel_split4 in HP2. destruct HP2 as (l211 & l212 & l221 & l222 & HP'1 & HP'2 & HP'3 & HP'4).
      assert (l211 ++ (l212 ++ [t1]) ≡[P] D1 ++ [t1]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac2_ephem1 in H2. destruct H2.
      assert (l221 ++ (l222 ++ [t2]) ≡[P] D2 ++ [t2]). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac2_ephem2 in H4. destruct H4.
      split.
      ++ rewrite HP'3. eapply vac2_comp; auto.
      ++ rewrite HP1, HP'4, <- app_assoc. eapply vac2_par.
         3: {reflexivity. }
         +++ assumption.
         +++ assumption.
  - apply Permutation_rel_split2 in H0.
    destruct H0 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]].
    + apply IHvac2_ephem in HP2. destruct HP2. split; intuition.
      rewrite HP1. apply vac2_bang. auto.
    + apply IHvac2_ephem in HP2. destruct HP2. split;  intuition.
      rewrite HP1. apply vac2_bang. auto.
  (* - apply Permutation_rel_split2 in H1. *)
  (*   destruct H1 as [[l1' [HP1 HP2]] | [l2' [HP1 HP2]]]. *)
  (*   + assert ((l1' ++ [t]) ++ D2 ≡[P] D). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac2_ephem in H1. destruct H1. *)
  (*     split; intuition. *)
  (*     rewrite HP1. eapply vac2_ques; try reflexivity; eauto. *)
  (*   + assert (D1 ++ (l2' ++ [t]) ≡[P] D). {convertTactics.convert_multisetperm. permutation_solver. } apply IHvac2_ephem in H1. destruct H1. *)
  (*     split; intuition. *)
  (*     rewrite HP1. eapply vac2_ques; try reflexivity; eauto. *)
  - apply Permutation_rel_split4 in H1. destruct H1 as (l211 & l212 & l221 & l222 & HP'1 & HP'2 & HP'3 & HP'4).
    symmetry in HP'1. apply IHvac2_ephem1 in HP'1. destruct HP'1.
    symmetry in HP'2. apply IHvac2_ephem2 in HP'2. destruct HP'2.
    split;  try rewrite HP'3; try rewrite HP'4; apply vac2_comp; auto.
  - rewrite <- H in H1. apply IHvac2_ephem in H1. auto.
Qed.

Lemma vac2_ephem_vacuous_ephem_inj : forall D, vac2_ephem D -> vacuous_ephem D.
Proof.
  intros D HV. induction HV.
  - apply vacuous_ephem_empty.
  - rewrite H. apply vacuous_ephem_app_iff; intuition.
    apply vacuous_ephem_one.
  - rewrite H. apply vacuous_ephem_app_iff in IHHV as (HV1 & HV2). apply vacuous_ephem_app_iff in HV2 as (HV2 & HV3). apply vacuous_ephem_app_iff; split; intuition.
    apply vacuous_ephem_singleton. apply vacuous_ephem_singleton in HV2, HV3. constructor; auto.
  - rewrite H. apply vacuous_ephem_app_iff in IHHV1, IHHV2. destruct IHHV1, IHHV2.
    repeat (apply vacuous_ephem_app_iff; split); auto.
    apply vacuous_ephem_singleton. apply vacuous_ephem_singleton in H1, H3. constructor; auto.
  - apply vacuous_ephem_app_iff; intuition.
    apply vacuous_ephem_singleton. constructor.
  (* - rewrite H in IHHV. apply vacuous_ephem_app_iff in IHHV. destruct IHHV. *)
  (*   apply vacuous_ephem_app_iff; intuition. *)
    (* apply vacuous_ephem_singleton. apply vacuous_ephem_singleton in H1. constructor; auto. *)
  - apply vacuous_ephem_app_iff; intuition.
  - rewrite <- H; auto.
Qed.

Lemma vacuous_ephem_vac2_ephem_inj : forall D, vacuous_ephem D -> vac2_ephem D.
Proof.
  intros D.
  induction D; intros.
  - constructor.
  - apply vacuous_ephem_cons_iff in H. destruct H.
    replace (a :: D) with ([a] ++ D) by auto.
    constructor; auto.
    clear IHD H0.
    induction H.
    + eapply vac2_one.
      2: {apply vac2_empty. }
      reflexivity.
    + eapply vac2_tensor.
      2: {assert ([t1 ⊗ t2] ≡[P] [] ++ [t1 ⊗ t2]). reflexivity. eassumption. }
      repeat apply vac2_comp; try constructor; auto.
    + eapply vac2_par.
      3: {assert ([t_par t1 t2] ≡[P] [] ++ [] ++ [t_par t1 t2]). reflexivity. eassumption. }
      ++ auto.
      ++ auto.
    + eapply vac2_perm.
      assert ([] ++ [[!] t] ≡[P] [[!]t]) by reflexivity. eassumption.
      eapply vac2_bang.
      eapply vac2_empty.
    (* + eapply vac2_perm. *)
    (*   assert ([] ++ [[?] t] ≡[P] [[?] t]) by reflexivity. eassumption. *)
    (*   eapply vac2_ques. *)
    (*   reflexivity. *)
    (*   auto. *)
Qed.

Corollary vacuous_ephem_vac2_ephem_iff : forall D, vacuous_ephem D <-> vac2_ephem D.
Proof.
  intros; split; try apply vacuous_ephem_vac2_ephem_inj; try apply vac2_ephem_vacuous_ephem_inj.
Qed.

Inductive vac_one_bang : ctx -> Prop :=
| vac_ob_nil : vac_one_bang []
| vac_ob_one : forall D, vac_one_bang D -> vac_one_bang ([[1]] ++ D) 
| vac_ob_bang : forall D t, vac_one_bang D -> vac_one_bang ([[!]t] ++ D) 
.

Lemma pf_cf_bang0 : forall c G D1 D t,
    c ⊢ t wf ->
    ⦃c; G; D1 ⊢cf ⦄ ->
    D ≡[P] D1 ++ [[!]t] ->
    ⦃c; G; D ⊢cf ⦄.
Proof.
  intros.
  eapply pf_bang. 2: {eassumption. }
  eapply pf_weakening. tauto. reflexivity. wf_ctx_solver. assumption.
Qed.

Lemma pf_cf_bang1 : forall c G D1 D t,
    ⦃ c; G; D1 ++ [t] ⊢cf ⦄ ->
    D ≡[P] D1 ++ [[!]t] ->
    ⦃ c; G; D ⊢cf ⦄.
Proof.
  intros.
  eapply pf_bang. 2: {eassumption. }
  eapply pf_absorb. 2: {reflexivity. } wf_ctx_solver.
  eapply pf_weakening. tauto. reflexivity. wf_ctx_solver. assumption.
Qed.

Lemma pf_cf_bang2 : forall c G D1 D t,
    ⦃ c; G; D1 ++ [[!]t] ++ [[!]t] ⊢cf ⦄ ->
    D ≡[P] D1 ++ [[!]t] ->
    ⦃ c; G; D ⊢cf ⦄.
Proof.
  intros.
  eapply pf_bang. 2: {eassumption. }
  eapply pf_contract. tauto.
  (* eapply pf_absorb. 2: {reflexivity. } wf_ctx_solver. *)
  eapply pf_bang_inv. tauto. tauto. 3: {rewrite app_assoc. reflexivity. } 2: {reflexivity. }
  eapply pf_bang_inv. tauto. tauto. eapply H. rewrite app_assoc. reflexivity. reflexivity.
Qed.

Section PFON.

  Reserved Notation " n ⊣ c , D '⊢pf' " (at level 101, D at level 100).

  Inductive pfon : nat -> nat -> ctx -> Prop :=
    
  | pfon_id : forall n c (u:typ),
      c ⊢ u wf ->
      n ⊣ c , [u] ++ [dual u] ⊢pf

(* absorbtion *)                
(* | pfon_absorb : forall n c G G' t D, *)
(*     wf_ctx c (G ++ [t]) -> *)
(*     G' ≡[P] (G ++ [t]) -> *)
(*     n ⊣ c , G' , D ++ [t] ⊢pf -> *)
(*              (S n) ⊣ c , G' , D ⊢pf        *)
                        
(* | pfon_cut : forall n c G D1 D2 D u, *)
(*     c ⊢ u wf -> *)
(*     n ⊣ c , G , D1 ++ [u] ⊢pf -> *)
(*             n ⊣ c , G , D2 ++ [dual u] ⊢pf -> *)
(*                     D ≡[P] (D1 ++ D2) ->                     *)
(*                     (S n) ⊣ c , G , D ⊢pf          *)
                              
| pfon_bot : forall n c,
    n ⊣ c , [ [⊥] ] ⊢pf

| pfon_one : forall n c D D',
    n ⊣ c , D' ⊢pf ->
            D ≡[P] D' ++ [[1]] ->
            (S n) ⊣ c , D ⊢pf
                      
| pfon_tensor : forall n c D D' t u,
    n ⊣ c , D' ++ [t] ++ [u] ⊢pf ->
            D ≡[P] (D' ++ [ t ⊗ u ]) ->
            (S n) ⊣ c , D ⊢pf

| pfon_par : forall n1 n2 c D1 D2 D t u,
    n1 ⊣ c , D1 ++ [t] ⊢pf ->
            n2 ⊣ c , D2 ++ [u] ⊢pf ->
                    D ≡[P] (D1 ++ D2 ++ [ t ∥ u ]) ->
                    (S (Nat.max n1 n2)) ⊣ c , D ⊢pf

| pfon_bang1 : forall n c D1 D t,
    n ⊣ c, D1 ++ [t] ⊢pf ->
                     D ≡[P] D1 ++ [[!] t] ->
                     S n ⊣ c, D ⊢pf
| pfon_bang0 : forall n c D1 D t,
   c ⊢ t wf ->
    n ⊣ c, D1 ⊢pf ->
              D ≡[P] D1 ++ [[!] t] ->
              S n ⊣ c, D ⊢pf
| pfon_bang2 : forall n c D1 D t,
    n ⊣ c, D1 ++ [[!]t] ++ [[!] t]⊢pf ->
              D ≡[P] D1 ++ [[!] t] ->
              S n ⊣ c, D ⊢pf
(* | pfon_bang : forall n c G D1 D t, *)
(*     n ⊣ c , G ++ [t] , D1 ⊢pf -> *)
(*                    D ≡[P] D1 ++ [ [!]t ] -> *)
(*                    (S n) ⊣ c , G , D ⊢pf *)
| pfon_ques : forall n c t,
    n ⊣ c, [t] ⊢pf ->
              S n ⊣ c, [[?]t] ⊢pf
(* | pfon_ques : forall n c G D D' t, *)
(*     n ⊣ c , G , D ++ [t] ⊢pf -> *)
(*                 vac_one_bang D -> *)
(*                 D' ≡[P] D ++ [[?]t] -> *)
(*             (S n) ⊣ c , G , D' ⊢pf *)

| pfon_forall : forall n c D1 D u t,
    c ⊢ u wf ->
    n ⊣ c , D1 ++ [typ_subst c u t] ⊢pf ->
            D ≡[P] D1 ++ [ [forall] t ] ->
            (S n) ⊣ c , D  ⊢pf           

| pfon_exists : forall n c D1 D u,
    n ⊣ (1 + c), (shift_ctx c 1 D1) ++ [u] ⊢pf ->
                                  D ≡[P] D1 ++ [ [exists] u ] ->
                                  (S n) ⊣ c , D ⊢pf 
  where
  "n ⊣ c , D '⊢pf'" := (pfon n c D).

  
  Lemma pfon_perm : forall n c D1 D2
                     (HPD: P D1 D2)
                     (HWF: n ⊣ c, D1 ⊢pf),
      n ⊣ c, D2 ⊢pf.
  Proof.
    intros. revert D2 HPD.
    induction HWF; intros.
    - apply Permutation_symmetric in HPD.
      apply Permutation_doubleton in HPD.
      destruct HPD; subst.
      + apply pfon_id; auto.
      + rewrite <- (dual_involutive u) at 2.
        apply pfon_id. 
        apply wf_typ_dual. assumption. 
    - apply Permutation_symmetric in HPD. apply Permutation_singleton in HPD. subst. 
      constructor.
    - destruct H as [H _].
      apply Permutation_symmetric in H. apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pfon_one. eapply IHHWF; eassumption.
      convert_multisetperm; permutation_solver.
    - destruct H as [H _].
      apply Permutation_symmetric in H. apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pfon_tensor. eapply IHHWF.
      eapply Permutation_append. apply HPD2. apply Permutation_reflexive.
      convert_multisetperm; permutation_solver.
    - destruct H as [H _].
      apply Permutation_symmetric in H. rewrite app_assoc in H.
      apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pfon_par. apply IHHWF1. apply Permutation_reflexive.
      apply IHHWF2; auto. apply Permutation_reflexive. 
      convert_multisetperm. permutation_solver.
    - eapply pfon_bang1.
      + eapply IHHWF. apply Permutation_reflexive.
      + convertTactics.convert_multisetperm. permutation_solver.
    - eapply pfon_bang0 with (t := t).
      + assumption.
      + eapply IHHWF. apply Permutation_reflexive.
      + convertTactics.convert_multisetperm. permutation_solver.
    - eapply pfon_bang2.
      + eapply IHHWF. apply Permutation_reflexive.
      + convertTactics.convert_multisetperm. permutation_solver.
    - apply Permutation_symmetric in HPD. apply Permutation_singleton in HPD.
      subst.
      apply pfon_ques. apply IHHWF. apply Permutation_reflexive.
    - eapply pfon_forall.
      + apply H.
      + eapply IHHWF.
        apply Permutation_reflexive.
      + convert_multisetperm; permutation_solver.
    - eapply pfon_exists.
      eapply IHHWF.
      + apply Permutation_reflexive.
      + convert_multisetperm; permutation_solver.
  Qed.

  
  Lemma pfon_perm_rel : forall n c D1 D2
                     (HPD: D1 ≡[P] D2)
                     (HWF: n ⊣ c,D1 ⊢pf),
      n ⊣ c, D2 ⊢pf.
  Proof.
    intros.
    normalize_auxH.
    eapply pfon_perm; eauto.
  Qed.

  Lemma pfon_perm_rel_iff : forall n c D1 D2,
       D1 ≡[P] D2 -> (n ⊣ c, D1 ⊢pf) <-> (n ⊣ c, D2 ⊢pf) .
  Proof.
    intros; split; intros.
    - eapply pfon_perm_rel; eassumption.
    - symmetry in H. eapply pfon_perm_rel; eassumption.
  Qed.

  Lemma cut_admissibility''_aux_id1 :
    forall m c u u' D2 D1' D2',
      [u] ++ [dual u] ≡[P] D1' ++ [u'] ->
      D2 ≡[P] D2' ++ [dual u'] ->
      m ⊣ c, D2 ⊢pf ->
             exists k, k ⊣ c, (D1' ++ D2') ⊢pf.
  Proof.
    intros.
    PInvert.
    - exists m. eapply pfon_perm. apply Permutation_symmetric.
      eapply Permutation_transitive; [ | apply H2]. apply Permutation_append; eauto.
      apply Permutation_reflexive.
      assumption.
    - subst. rewrite dual_involutive in H2.
      exists m. eapply pfon_perm. apply Permutation_symmetric.
      eapply Permutation_transitive; [ | apply H2]. apply Permutation_append; eauto.
      convertTactics.convert_multiset. permutation_solver. 
      assumption.
  Qed.

  Lemma cut_admissibility''_aux_id2 :
    forall m c u u' D1 D1' D2',
      [u] ++ [dual u] ≡[P] D2' ++ [u'] ->
      D1 ≡[P] D1' ++ [dual u'] ->
      m ⊣ c, D1 ⊢pf ->
             exists k, k ⊣ c, (D1' ++ D2') ⊢pf.
  Proof.
    intros.
    PInvert.
    - exists m. eapply pfon_perm. apply Permutation_symmetric.
      eapply Permutation_transitive; [ | apply H2]. convertTactics.convert_multiset. permutation_solver. 
      assumption.
    - subst. rewrite dual_involutive in H2.
      exists m. eapply pfon_perm. apply Permutation_symmetric.
      eapply Permutation_transitive; [ | apply H2]. convertTactics.convert_multiset. permutation_solver. 
      assumption.
  Qed.

  Lemma pfon_perm_rel_iff_exists: forall c D1 D2,
      D1 ≡[P] D2 -> (exists k1, k1 ⊣ c, D1 ⊢pf) <-> (exists k2, k2 ⊣ c, D2 ⊢pf).
  Proof.
    intros; split; intros.
    - intros. destruct H0. exists x.
      eapply pfon_perm_rel; eauto.
    - intros. destruct H0. exists x.
      eapply pfon_perm_rel_iff; eauto.
  Qed.

  Lemma pfon_par_exists: forall c D1 D2 t1 t2,
      (exists k1, k1 ⊣ c, D1 ++ [t1] ⊢pf) /\ (exists k2, k2 ⊣ c, D2 ++ [t2] ⊢pf) -> exists k3, k3 ⊣ c, D1 ++ D2 ++ [t_par t1 t2] ⊢pf.
  Proof.
    intros. destruct H. destruct H, H0.
    exists (S (Nat.max x x0)). eapply pfon_par; try eassumption.
    reflexivity.
  Qed.

  Lemma pfon_wf_typ : forall n c D,
      n ⊣ c, D ⊢pf -> ( wf_ctx c D).
  Proof.
    intros n c D HP.
    induction HP; intuition; WF_CTX; intuition.
    - apply wf_typ_dual. auto.
    - constructor.
      replace (1 + c) with (c + 1) by lia.
      eapply typ_subst_wf_inversion.
      eauto.
  Qed.    

  Ltac normalize_pfn_wf_ctx_more :=
    repeat (match goal with
            | [ H: ?n ⊣ ?c, ?D ⊢pf |- _ ] => apply pfon_wf_typ in H
            end).

  Ltac pfon_wf_ctx_solver :=
    normalize_pfn_wf_ctx_more; normalize_wf_ctxH'; normalize_wf_ctx; auto.


End PFON.




Section PFN.

  Reserved Notation " n ⊣ c , G , D '⊢pf' " (at level 101, D at level 100, G at level 100).
  Inductive pfn : nat -> nat -> ctx -> ctx -> Prop :=
    
  | pfn_id : forall n c G (u:typ),
      c ⊢ u wf ->
      wf_ctx c G ->
      n ⊣ c , G , [u] ++ [dual u] ⊢pf

(* absorbtion *)                
| pfn_absorb : forall n c G G' t D,
    wf_ctx c (G ++ [t]) ->
    G' ≡[P] (G ++ [t]) ->
    n ⊣ c , G' , D ++ [t] ⊢pf ->
             (S n) ⊣ c , G' , D ⊢pf       
                        
(* | pfn_cut : forall n c G D1 D2 D u, *)
(*     c ⊢ u wf -> *)
(*     n ⊣ c , G , D1 ++ [u] ⊢pf -> *)
(*             n ⊣ c , G , D2 ++ [dual u] ⊢pf -> *)
(*                     D ≡[P] (D1 ++ D2) ->                     *)
(*                     (S n) ⊣ c , G , D ⊢pf          *)
                              
| pfn_bot : forall n c G,
    wf_ctx c G ->    
    n ⊣ c , G , [ [⊥] ] ⊢pf

| pfn_one : forall n c G D D',
    n ⊣ c , G , D' ⊢pf ->
            D ≡[P] (D' ++ [ [1] ]) ->        
            (S n) ⊣ c , G , D ⊢pf
                      
| pfn_tensor : forall n c G D D' t u,
    n ⊣ c , G , D' ++ [t] ++ [u] ⊢pf ->
            D ≡[P] (D' ++ [ t ⊗ u ]) ->
            (S n) ⊣ c , G , D ⊢pf

| pfn_par : forall n1 n2 c G D1 D2 D t u,
    n1 ⊣ c , G , D1 ++ [t] ⊢pf ->
            n2 ⊣ c , G , D2 ++ [u] ⊢pf ->
                    D ≡[P] (D1 ++ D2 ++ [ t ∥ u ]) ->
                    (S (Nat.max n1 n2)) ⊣ c , G , D ⊢pf

(* | pfn_bang1 : forall n c G D1 D t, *)
(*     n ⊣ c, G, D1 ++ [t] ⊢pf -> *)
(*                      D ≡[P] D1 ++ [[!] t] -> *)
(*                      S n ⊣ c, G, D ⊢pf *)
(* | pfn_bang0 : forall n c G D1 D t, *)
(*    c ⊢ t wf -> *)
(*     n ⊣ c, G, D1 ⊢pf -> *)
(*               D ≡[P] D1 ++ [[!] t] -> *)
(*               S n ⊣ c, G, D ⊢pf *)
(* | pfn_bang2 : forall n c G D1 D t, *)
(*     n ⊣ c, G, D1 ++ [[!]t] ++ [[!] t]⊢pf -> *)
(*               D ≡[P] D1 ++ [[!] t] -> *)
(*               S n ⊣ c, G, D ⊢pf *)
| pfn_bang : forall n c G D1 D t,
    n ⊣ c , G ++ [t] , D1 ⊢pf ->
                   D ≡[P] D1 ++ [ [!]t ] ->
                   (S n) ⊣ c , G , D ⊢pf
| pfn_ques : forall n c G t,
    n ⊣ c, G, [t] ⊢pf ->
              S n ⊣ c, G, [[?]t] ⊢pf
(* | pfn_ques : forall n c G D D' t, *)
(*     n ⊣ c , G , D ++ [t] ⊢pf -> *)
(*                 vac_one_bang D -> *)
(*                 D' ≡[P] D ++ [[?]t] -> *)
(*             (S n) ⊣ c , G , D' ⊢pf *)

| pfn_forall : forall n c G D1 D u t,
    c ⊢ u wf ->
    n ⊣ c , G , D1 ++ [typ_subst c u t] ⊢pf ->
            D ≡[P] D1 ++ [ [forall] t ] ->
            (S n) ⊣ c , G , D  ⊢pf           

| pfn_exists : forall n c G D1 D u,
    n ⊣ (1 + c) , (shift_ctx c 1 G) , (shift_ctx c 1 D1) ++ [u] ⊢pf ->
                                  D ≡[P] D1 ++ [ [exists] u ] ->
                                  (S n) ⊣ c , G , D ⊢pf 
  where
  "n ⊣ c , G , D '⊢pf'" := (pfn n c G D).

  Lemma pfn_typ_var_weakening: forall n c G D b,
      n ⊣ c, G, D ⊢pf ->
                n ⊣ (c + b), shift_ctx c b G, shift_ctx c b D ⊢pf.
  Proof. Admitted.              (*  May be if and only if *)

  (* If the type variable is not being used, get rid of it *)
  Print wf_typ.
  Search wf_typ.
  (* Lemma pfn_strengthening : forall c1 c2 b t, *)
  (*     wf_typ (c1 + b + c2) (shift_typ c1 b t) -> *)
  (*     wf_typ (c1 + c2) t.       (* May be if and only if *) *)
      
  Lemma pfn_perm : forall n c G1 G2 D1 D2
                     (HPG: P G1 G2)
                     (HPD: P D1 D2)
                     (HWF: n ⊣ c, G1, D1 ⊢pf),
      n ⊣ c, G2, D2 ⊢pf.
  Proof.
    intros. revert G2 D2 HPG HPD.
    induction HWF; intros.
    - apply Permutation_symmetric in HPD.
      apply Permutation_doubleton in HPD.
      destruct HPD; subst.
      + apply pfn_id; auto. eapply wf_ctx_Permutation_inj; eauto.
      + rewrite <- (dual_involutive u) at 2.
        apply pfn_id. 
        apply wf_typ_dual. assumption. eapply wf_ctx_Permutation_inj; eauto.
    - specialize (IHHWF G2 (D2 ++ [t]) HPG).
      destruct H0.
      eapply pfn_absorb.
      3: { apply IHHWF. eapply Permutation_append. apply HPD.  apply Permutation_reflexive. }
      apply H. eexists; auto. eapply Permutation_transitive. eapply Permutation_symmetric. apply HPG. apply x. 
    (* - unfold_destruct_relH H0. *)
    (*   specialize (IHHWF1 G2 (D1 ++ [u]) HPG). *)
    (*   specialize (IHHWF2 G2 (D2 ++ [dual u]) HPG). *)
    (*   assert (P (D1 ++ D2) D0). *)
    (*   { convert_multiset. permutation_solver. (* eapply Permutation_transitive. eapply Permutation_symmetric. apply x. assumption.  *)} *)
    (*   eapply pfn_cut; eauto. *)
    (*   apply IHHWF1. *)
    (*   apply Permutation_reflexive. *)
    (*   apply IHHWF2. *)
    (*   apply Permutation_reflexive. *)
    (*   convert_multisetperm; permutation_solver. *)
    (*   (* eexists. apply Permutation_symmetric. assumption. auto. *) *)
    - apply Permutation_symmetric in HPD. apply Permutation_singleton in HPD. subst.
      apply pfn_bot. eapply wf_ctx_Permutation_inj. apply HPG; auto. assumption.
    - destruct H as [H _].
      apply Permutation_symmetric in H. apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pfn_one. eapply IHHWF; eassumption. (* assumption. apply HPD2. *)
      convert_multisetperm; permutation_solver.
      (* eexists. eapply perm_comp. eapply Permutation_symmetric. apply HPD. apply HPD1. auto. *)
    - destruct H as [H _].
      apply Permutation_symmetric in H. apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pfn_tensor. eapply IHHWF. assumption.
      eapply Permutation_append. apply HPD2. apply Permutation_reflexive.
      convert_multisetperm; permutation_solver.
      (* eexists. eapply perm_comp. eapply Permutation_symmetric. apply HPD. apply HPD1. auto. *)
    - destruct H as [H _].
      apply Permutation_symmetric in H. rewrite app_assoc in H.
      apply Permutation_destruct1 in H.
      destruct H as [D'' [HPD1 HPD2]].
      eapply pfn_par. apply IHHWF1. assumption. apply Permutation_reflexive.
      apply IHHWF2; auto. apply Permutation_reflexive. 
      convert_multisetperm. permutation_solver.
      (* eexists; [|auto]. eapply Permutation_transitve. eapply Permutation_symmetric. apply HPD. *)
      (* rewrite app_assoc. eapply perm_comp. apply HPD1. *)
      (* eapply perm_plus. apply Permutation_symmetric. assumption. apply perm_id. *)
    (* - eapply pfn_bang1. *)
    (*   + eapply IHHWF. assumption. apply Permutation_reflexive. *)
    (*   + convertTactics.convert_multisetperm. permutation_solver. *)
    (* - eapply pfn_bang0 with (t := t). *)
    (*   + assumption. *)
    (*   + eapply IHHWF. assumption. apply Permutation_reflexive. *)
    (*   + convertTactics.convert_multisetperm. permutation_solver. *)
    (* - eapply pfn_bang2. *)
    (*   + eapply IHHWF. assumption. apply Permutation_reflexive. *)
    (*   + convertTactics.convert_multisetperm. permutation_solver. *)
    - eapply pfn_bang.
      eapply IHHWF.
      eapply Permutation_append. assumption. apply Permutation_reflexive.
      apply Permutation_reflexive.
      convert_multisetperm; permutation_solver.

    (*   (* 2: { destruct H as [H _]. econstructor; auto. *) *)
    (*   (*      eapply perm_comp. apply Permutation_symmetric. apply HPD. apply H. } *) *)
    (*   (* apply perm_id. *) *)
    (* - eapply pfn_ques. *)
    (*   + eapply IHHWF. assumption. apply Permutation_reflexive. *)
    (*   + assumption. *)
    (*   + convertTactics.convert_multisetperm. permutation_solver. *)
    - apply Permutation_symmetric in HPD. apply Permutation_singleton in HPD.
      subst.
      apply pfn_ques. apply IHHWF. assumption. apply Permutation_reflexive.
    - eapply pfn_forall.
      + apply H.
      + eapply IHHWF. assumption.
        apply Permutation_reflexive.
      + convert_multisetperm; permutation_solver.
        (* destruct H0 as [H0 _]. *)
        (* constructor; auto. *)
        (* eapply perm_comp. apply Permutation_symmetric. apply HPD. *)
        (* apply H0. *)
    - eapply pfn_exists.
      eapply IHHWF.
      + apply Permutation_shift_ctx. assumption.
      + apply Permutation_reflexive.
      + convert_multisetperm; permutation_solver.
        (* destruct H as [H _]. *)
        (* constructor; auto. *)
        (* eapply perm_comp. apply Permutation_symmetric. apply HPD. *)
        (* apply H. *)
  Qed.

  Lemma pfn_perm_rel : forall n c G1 G2 D1 D2
                     (HPG: G1 ≡[P] G2)
                     (HPD: D1 ≡[P] D2)
                     (HWF: n ⊣ c, G1, D1 ⊢pf),
      n ⊣ c, G2, D2 ⊢pf.
  Proof.
    intros.
    normalize_auxH.
    eapply pfn_perm; eauto.
  Qed.

  Lemma pfn_perm_rel_iff : forall n c G1 G2 D1 D2,
      G1 ≡[P] G2 -> D1 ≡[P] D2 -> (n ⊣ c, G1, D1 ⊢pf) <-> (n ⊣ c, G2, D2 ⊢pf) .
  Proof.
    intros; split; intros.
    - eapply pfn_perm_rel; eassumption.
    - symmetry in H, H0. eapply pfn_perm_rel; eassumption.
  Qed.

    
  (* Lemma cut_admissibility_base_case : forall c G D, *)
  (*     0 ⊣ c, G, D ⊢pf -> ⦃c; G; D ⊢cf ⦄. *)
  (* Proof. *)
  (*   intros. inversion H. *)
  (*   - apply pf_id; auto. unfold any. auto. *)
  (*   - constructor; auto. *)
  (* Qed. *)
(* u1, u2 : typ *)
(*   IHu1 : ∀ (n m c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
(*            D1 ≡[ P] D1' ++ [u1] *)
(*            → D2 ≡[ P] D2' ++ [dual u1] *)
(*              → (n ⊣ c, G, D1 ⊢pf) → (m ⊣ c, G, D2 ⊢pf) → ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf *)
(*   IHu2 : ∀ (n m c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
(*            D1 ≡[ P] D1' ++ [u2] *)
(*            → D2 ≡[ P] D2' ++ [dual u2] *)
(*              → (n ⊣ c, G, D1 ⊢pf) → (m ⊣ c, G, D2 ⊢pf) → ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf *)
(* (*   n, m, c : nat *) *)
(* (*   G : ctx *) *)
(* (*   D1, D2, D1', D2' : list typ *) *)
(*   HP1 : D1 ≡[ P] D1' ++ [u1 ⊗ u2] *)
(*   HP2 : D2 ≡[ P] D2' ++ [dual (u1 ⊗ u2)] *)
(*   HG1 : n ⊣ c, G, D1 ⊢pf *)
(*   HG2 : m ⊣ c, G, D2 ⊢pf *)
(*   ============================ *)
(*   ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf *)

Lemma cut_admissibility'_aux_id1 :
  forall m c G u u' D2 D1' D2',
    [u] ++ [dual u] ≡[P] D1' ++ [u'] ->
    D2 ≡[P] D2' ++ [dual u'] ->
    m ⊣ c, G, D2 ⊢pf ->
    exists k, k ⊣ c, G, (D1' ++ D2') ⊢pf.
Proof.
  intros.
  PInvert.
  - exists m. eapply pfn_perm. apply Permutation_reflexive. apply Permutation_symmetric.
    eapply Permutation_transitive; [ | apply H2]. apply Permutation_append; eauto.
    apply Permutation_reflexive.
    assumption.
  - subst. rewrite dual_involutive in H2.
     exists m. eapply pfn_perm. apply Permutation_reflexive. apply Permutation_symmetric.
    eapply Permutation_transitive; [ | apply H2]. apply Permutation_append; eauto.
    convertTactics.convert_multiset. permutation_solver. 
    assumption.
Qed.

Lemma cut_admissibility'_aux_id2 :
  forall m c G u u' D1 D1' D2',
    [u] ++ [dual u] ≡[P] D2' ++ [u'] ->
    D1 ≡[P] D1' ++ [dual u'] ->
    m ⊣ c, G, D1 ⊢pf ->
    exists k, k ⊣ c, G, (D1' ++ D2') ⊢pf.
Proof.
  intros.
  PInvert.
  - exists m. eapply pfn_perm. apply Permutation_reflexive. apply Permutation_symmetric.
    eapply Permutation_transitive; [ | apply H2]. convertTactics.convert_multiset. permutation_solver. 
    assumption.
  - subst. rewrite dual_involutive in H2.
     exists m. eapply pfn_perm. apply Permutation_reflexive. apply Permutation_symmetric.
    eapply Permutation_transitive; [ | apply H2]. convertTactics.convert_multiset. permutation_solver. 
    assumption.
Qed.

(* Not very helpful *)
  (* Lemma cut_increase_height : forall n c G D *)
  (*     (HCut : forall u n m c G D1 D2 D1' D2', *)
  (*               D1 ≡[P] D1' ++ [u] -> *)
  (*               D2 ≡[P] D2' ++ [dual u] -> *)
  (*               (n ⊣ c, G, D1 ⊢pf) -> *)
  (*               (m ⊣ c, G, D2 ⊢pf) -> *)
  (*               exists k, k ⊣ c, G, D1' ++ D2' ⊢pf *)
  (*     ), *)
  (*     n ⊣ c, G, D ⊢pf -> *)
  (*     S n ⊣ c, G, D ⊢pf. *)
  (* Proof. *)
  (*   intros.  *)
  (*   destruct H. *)
  (*   - constructor; auto. *)
  (*   - specialize (HCut (dual t) n n c G ([t] ++ [dual t]) (D ++ [t]) [t] D). *)
  (*     assert ([t] ++ [dual t] ≡[P] [t] ++ [dual t]) by reflexivity. *)
  (*     assert (D ++ [t] ≡[P] D ++ [dual (dual t)]) by (rewrite dual_involutive; reflexivity). *)
  (*     assert (n ⊣ c, G, [t] ++ [dual t] ⊢pf). *)
  (*     {constructor; wf_ctx_solver. }  *)
  (*     specialize (HCut H2 H3 H4 ). *)

Lemma pfn_perm_rel_iff_exists: forall c G1 G2 D1 D2,
    G1 ≡[P] G2 -> D1 ≡[P] D2 -> (exists k1, k1 ⊣ c, G1, D1 ⊢pf) <-> (exists k2, k2 ⊣ c, G2, D2 ⊢pf).
  Proof.
    intros; split; intros.
    - intros. destruct H1. exists x.
      eapply pfn_perm_rel; eauto.
    - intros. destruct H1. exists x.
      eapply pfn_perm_rel_iff; eauto.
  Qed.

  Lemma pfn_par_exists: forall c G D1 D2 t1 t2,
      (exists k1, k1 ⊣ c, G, D1 ++ [t1] ⊢pf) /\ (exists k2, k2 ⊣ c, G, D2 ++ [t2] ⊢pf) -> exists k3, k3 ⊣ c, G, D1 ++ D2 ++ [t_par t1 t2] ⊢pf.
  Proof.
    intros. destruct H. destruct H, H0.
    exists (S (Nat.max x x0)). eapply pfn_par; try eassumption.
    reflexivity.
  Qed.

Lemma pfn_wf_typ : forall n c G D,
     n ⊣ c, G, D ⊢pf -> (wf_ctx c G /\ wf_ctx c D).
Proof.
  intros n c G D HP.
  induction HP; intuition; WF_CTX; intuition.
  - apply wf_typ_dual. auto.
  - constructor.
    replace (1 + c) with (c + 1) by lia.
    eapply typ_subst_wf_inversion.
    eauto.
Qed.    

Ltac normalize_pfn_wf_ctx_more :=
  repeat (match goal with
  | [ H: ?n ⊣ ?c, ?G, ?D ⊢pf |- _ ] => apply pfn_wf_typ in H
  end).

Ltac pfn_wf_ctx_solver :=
  normalize_pfn_wf_ctx_more; normalize_wf_ctxH'; normalize_wf_ctx; auto.


Lemma pfn_weakening : forall n D G G1 G2 c, G ≡[P] G1 ++ G2 -> wf_ctx c G2 -> n ⊣ c, G1, D ⊢pf -> n ⊣ c, G, D ⊢pf.
Proof.
  intros n D G G1 G2 c HG HW HP.
  revert G G2 HG HW.
  induction HP; intros.
  - apply pfn_id; auto.
    eapply wf_ctx_app_perm_iff in HG.
    apply HG; intuition.
  - 
    assert ((G ++ [t]) ++ G2 ≡[P] (G ++ G2) ++ [t]).
    {convertTactics.convert_multisetperm. permutation_solver. }
    eapply pfn_absorb.
    + assert (wf_ctx c ((G ++ G2) ++ [t])).
      {
        apply (wf_ctx_perm_iff H1).
        apply wf_ctx_app; intuition.
      }
      apply H2.
    + rewrite H0 in HG.
      eapply transitivity; eauto.
    + eapply IHHP; eauto.
  - apply pfn_bot.
    apply (wf_ctx_app_perm_iff HG). intuition.
  - eapply pfn_one; eauto.
  - eapply pfn_tensor; eauto.
  - eapply pfn_par.
    + eapply IHHP1.
      ++ eauto.
      ++ eauto.
    + eapply IHHP2.
      ++ eauto.
      ++ eauto.
    + eauto.
  (* - eapply pfn_bang1. 2: {apply H. } *)
  (*   eapply IHHP with (G2 := G2); pfn_wf_ctx_solver. *)
  (* - eapply pfn_bang0. *)
  (*   + apply H. *)
  (*   + eapply IHHP with (G2 := G2); pfn_wf_ctx_solver. *)
  (*   + assumption. *)
  (* - eapply pfn_bang2. 2: {apply H. } *)
  (*   eapply IHHP with (G2 := G2); pfn_wf_ctx_solver. *)
  - eapply pfn_bang.
    + eapply IHHP.
      ++ assert (G0 ++ [t] ≡[P] (G ++ [t]) ++ G2).
         {
           convertTactics.convert_multisetperm. permutation_solver.
         }
         eassumption.
      ++ eassumption.
    + assumption.
  - eapply pfn_ques; eauto.
  - eapply pfn_forall; try eassumption.
    eapply IHHP; eassumption.
  - eapply pfn_exists.
    + apply IHHP with (G2 := shift_ctx c 1 G2).
      ++ 
        apply (Permutation_rel_shift_ctx 1 c) in HG.
        rewrite shift_ctx_app in HG.
        assumption.
      ++ apply wf_shift_ctx; assumption.
    + assumption.
Qed.

Lemma pfn_absorb_append : forall n D D1 D2 G c, wf_ctx c (G ++ D2) -> D ≡[P] D1 ++ D2 -> n ⊣ c, (G ++ D2), D ⊢pf -> (n + length D2) ⊣ c, (G ++ D2), D1 ⊢pf.
  Proof.
    intros n D D1 D2 G c HW HP HG.
    normalize_auxH.
    revert n D D1 G c HW HP HG.
    induction D2.
    - intros.
      rewrite app_nil_r in *.
      eapply pfn_perm.
      + apply Permutation_reflexive.
      + apply HP.
      + rewrite Nat.add_0_r. apply HG.
    - intros.
      assert (P ((G ++ [a]) ++ D2) (G ++ a :: D2)).
      {
        convertTactics.convert_multiset. permutation_solver.
      }
      apply (wf_ctx_Permutation_surj _ _ _ X) in HW.
      assert (P D ((D1 ++ [a]) ++ D2)).
      {
        convertTactics.convert_multiset. permutation_solver.
      }
      assert ((n ⊣ c, (G ++ [a]) ++ D2, D ⊢pf)).
      {
        eapply pfn_perm.
        - apply Permutation_symmetric. eassumption.
        - apply Permutation_reflexive.
        - assumption.
      }
      specialize (IHD2 _ _ _ _ _ HW X0 H).
      replace (n + length (a :: D2)) with (S (n + length D2)). 2: {simpl. lia. }
      eapply pfn_absorb.
      + apply wf_ctx_app in HW; destruct HW as (HW1 & HW2).
        apply wf_ctx_app in HW1; destruct HW1 as (HW1 & HW3).
        assert (wf_ctx c (G ++ D2)) by (apply wf_ctx_app; auto).
        apply wf_ctx_app; split.
        ++ apply H0.
        ++ apply HW3.
      + convertTactics.convert_multisetperm. permutation_solver.
      + eapply pfn_perm.
        ++ eassumption.
        ++ apply Permutation_reflexive.
        ++ eassumption.
  Qed.

  Corollary pfn_promote_append : forall n D D1 D2 G c, D ≡[P] D1 ++ D2 -> wf_ctx c D2 -> n ⊣ c, G, D ⊢pf -> n + length D2 ⊣ c, (G ++ D2), D1 ⊢pf.
  Proof.
    intros.
    eapply pfn_absorb_append.
    - apply pfn_wf_typ in H1 as (H1 & _).
      apply wf_ctx_app; intuition.
    - eassumption.
    - eapply pfn_weakening.
      + reflexivity.
      + assumption.
      + eassumption.
  Qed.

  Corollary pfn_promote_cons : forall n D D' G c t, D ≡[P] D' ++ [t] -> c ⊢ t wf -> n ⊣ c, G, D ⊢pf -> S n ⊣ c, (G ++ [t]), D' ⊢pf.
  Proof.
    intros.
    replace (S n) with (n + length [t]) by (simpl; lia).
    eapply pfn_promote_append.
    - eassumption.
    - apply pfn_wf_typ in H1. destruct H1 as (_ & H1).
      apply (wf_ctx_perm_iff H), wf_ctx_app in H1.
      intuition.
    - eassumption.
  Qed.

  Lemma pfn_persist_inv : forall n c G G' D t, G ≡[P] G' ++ [t] -> n ⊣ c, G, D ⊢pf -> exists k n', k ⊣ c, G', D ++ replicate n' t ⊢pf.
  Proof.
    intros n.
    induction (lt_wf n). rename H into IHY. rename H0 into IHWF.
    intros c G G' D t HP HG.
    revert G' t HP. induction HG; intros.
    - intros. exists 0, 0. eapply pfn_id; pfn_wf_ctx_solver. eapply (wf_ctx_perm_iff HP) in H0. wf_ctx_solver.
    - intros. rewrite H0 in HP. apply Permutation_rel_split_last in HP.
      destruct HP as [[-> HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]].
      + assert (n < S n) by lia.
        specialize (IHWF _ H1 _ G' G(D ++ [t0]) t0 H0 HG).
        destruct IHWF as (k & n' & IHWF).
        exists k, (S n').
        eapply pfn_perm_rel. rewrite <- HP'2. reflexivity.
        replace (D ++ replicate (S n') t0) with ((D ++ [t0]) ++ replicate n' t0) by (rewrite <- app_assoc; reflexivity). reflexivity.
        assumption.
      + assert (IHY': forall y : nat, y < n -> Acc lt y). {intros. auto. }
        assert (IHWF': ∀ y : nat, y < n → ∀ (c : nat) (G G' : list typ) (D : ctx) (t : typ), G ≡[ P] G' ++ [t] → (y ⊣ c, G, D ⊢pf) → ∃ k n' : nat, k ⊣ c, G', D ++ replicate n' t ⊢pf).
        {intros. eapply IHWF; try eassumption. lia. }
        specialize (IHHG IHY' IHWF' (l2' ++ [t]) t0).
        assert (G' ≡[P] (l2' ++ [t]) ++ [t0]). {convertTactics.convert_multisetperm. permutation_solver. }
        specialize (IHHG H1).
        destruct IHHG as (k & n' & IHHG).
        exists (S k), n'. eapply pfn_absorb. 2: {eassumption. } pfn_wf_ctx_solver.
        eapply pfn_perm_rel. symmetry. apply HP'2. apply Permutation_rel_assoc_swap. assumption.
    - exists 0, 0. simpl. eapply pfn_bot. apply (wf_ctx_perm_iff HP) in H. pfn_wf_ctx_solver.
    - assert (n < S n) by lia. 
      specialize (IHWF _ H0 _ G G' _ _ HP HG).
      destruct IHWF as (k & n' & IHWF).
      exists (S k), n'. eapply pfn_one. 2: {rewrite H. apply Permutation_rel_assoc_swap. } assumption.
    - admit.
    - 
      assert (IHY'1: forall y : nat, y < n1 -> Acc lt y). {intros. apply IHY. lia. }
      assert (IHWF'1: ∀ y : nat, y < n1 → ∀ (c : nat) (G G' : list typ) (D : ctx) (t : typ), G ≡[ P] G' ++ [t] → (y ⊣ c, G, D ⊢pf) → ∃ k n' : nat, k ⊣ c, G', D ++ replicate n' t ⊢pf). {intros. eapply IHWF with (y := y); try eassumption. lia. }
      specialize (IHHG1 IHY'1 IHWF'1 G' t0 HP).
      assert (IHY'2: forall y : nat, y < n2 -> Acc lt y). {intros. apply IHY. lia. }
      assert (IHWF'2: ∀ y : nat, y < n2 → ∀ (c : nat) (G G' : list typ) (D : ctx) (t : typ), G ≡[ P] G' ++ [t] → (y ⊣ c, G, D ⊢pf) → ∃ k n' : nat, k ⊣ c, G', D ++ replicate n' t ⊢pf). {intros. eapply IHWF with (y := y); try eassumption. lia. }
      specialize (IHHG2 IHY'2 IHWF'2 G' t0 HP).
      destruct IHHG1 as (k1 & n'1 & IHHG1). destruct IHHG2 as (k2 & n'2 & IHHG2).
      exists (S (Nat.max k1 k2)), (n'1 + n'2).
      eapply pfn_par. 3: {assert (D ++ replicate (n'1 + n'2) t0 ≡[P] (D1 ++ replicate n'1 t0) ++ (D2 ++ replicate n'2 t0) ++ [t_par t u]). {rewrite replicate_add. convertTactics.convert_multisetperm. permutation_solver. } eassumption. }
      + eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption.
      + eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption.
    (* - assert (n < S n) by lia. *)
    (*   specialize (IHWF _ H0 _ _ _ _ _ HP HG). *)
    (*   destruct IHWF as (k & n' & IHWF). *)
    (*   exists (S k), (n'). eapply pfn_bang1. 2: {rewrite H. apply Permutation_rel_assoc_swap. } *)
    (*   eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption. *)
    (* - assert (n < S n) by lia. *)
    (*   specialize (IHWF _ H1 _ _ _ _ _ HP HG). *)
    (*   destruct IHWF as (k & n' & IHWF). *)
    (*   exists (S k), n'. eapply pfn_bang0. eapply H. apply IHWF. rewrite H0. apply Permutation_rel_assoc_swap. *)
    (* - assert (n < S n) by lia. *)
    (*   specialize (IHWF _ H0 _ _ _ _ _ HP HG). *)
    (*   destruct IHWF as (k & n' & IHWF). *)
    (*   exists (S k), n'. eapply pfn_bang2. 2: {assert (D ++ replicate n' t0 ≡[P] (D1 ++ replicate n' t0) ++ [[!]t]). {convertTactics.convert_multisetperm. permutation_solver. } eassumption. } *)
    (*   eapply pfn_perm_rel. reflexivity. assert ((D1 ++ [[!]t] ++ [[!]t]) ++ replicate n' t0 ≡[P] (D1 ++ replicate n' t0) ++ [[!]t] ++ [[!]t]). {convertTactics.convert_multisetperm. permutation_solver. } eassumption. assumption. *)
    - assert (n < S n) by lia.
      specialize (IHWF _ H0 c (G ++ [t]) (G' ++ [t]) D1 t0).
      assert (G ++ [t] ≡[P] (G' ++ [t]) ++ [t0]). {convertTactics.convert_multisetperm. permutation_solver. }
      specialize (IHWF H1 HG).
      destruct IHWF as (k & n' & IHWF).
      exists (S k), n'. eapply pfn_bang. 2: {rewrite H. apply Permutation_rel_assoc_swap. } assumption.
    - 
      assert (n < S n) by lia.
      specialize (IHWF _ H c G G' [t] t0 HP HG).
      destruct IHWF as (k & n' & IHWF).

  Abort.

  (* Lemma pfn_bang' : forall n c G G' D D' t, *)
  (*     n ⊣ c, G, D' ⊢pf -> *)
  (*               G ≡[P] G' ++ [t] -> *)
  (*                      D ≡[P] D' ++ [[!] t] -> *)
  (*                     exists k, k ⊣ c, G', D ⊢pf. *)
  (* Proof. *)
  (*   intros n c G G' D D' t HG HPG HPD. *)
  (*   revert G' D t HPG HPD. *)
  (*   induction HG; intros. *)
  (*   - exists (S n). eapply pfn_bang0 with (t := t). *)
  (*     + apply (wf_ctx_perm_iff HPG) in H0. pfn_wf_ctx_solver. *)
  (*     + eapply pfn_id. *)
  (*       ++ eapply H. *)
  (*       ++ apply (wf_ctx_perm_iff HPG) in H0. pfn_wf_ctx_solver. *)
  (*     + apply HPD. *)
  (*   - pose proof HPG as HPG'. rewrite H0 in HPG. apply Permutation_rel_split_last in HPG. *)
  (*     destruct HPG as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]]. *)
  (*     + subst. *)
  (*       specialize (IHHG G (D0 ++ [t0]) t0 H0). *)
  (*       assert (D0 ++ [t0] ≡[P] (D ++ [t0]) ++ [[!] t0]). {convertTactics.convert_multisetperm. permutation_solver. } *)
  (*       specialize (IHHG H1). *)
  (*       destruct IHHG as (k & IHHG). *)
  (*       exists (S (S k)). eapply pfn_perm_rel. apply HP'2. reflexivity. *)
  (*       eapply pfn_bang2. 2: {apply HPD. } rewrite app_assoc. *)
  (*       eapply pfn_bang1. 2: {reflexivity. } *)
  (*       eapply pfn_perm_rel. reflexivity. rewrite <- HPD. reflexivity. assumption. *)
  (*     + *)
  (*       specialize (IHHG G'0 (D0 ++ [t]) t0 HPG'). *)
  (*       assert (D0 ++ [t] ≡[P] (D ++ [t]) ++ [[!]t0]). {clear HP'1 HP'2 HP'3 HPG'. convertTactics.convert_multisetperm. permutation_solver. } *)
  (*       specialize (IHHG H1). *)
  (*       destruct IHHG as (k & IHHG). *)
  (*       exists (S k). eapply pfn_absorb. *)
  (*       3: {apply IHHG. } *)
  (*       2: {apply HP'2. } *)
  (*       pfn_wf_ctx_solver. eapply (wf_ctx_perm_iff HP'2)in H2. pfn_wf_ctx_solver. *)
  (*   - exists 1. eapply pfn_bang0 with (t := t). *)
  (*     + apply (wf_ctx_perm_iff HPG) in H. pfn_wf_ctx_solver. *)
  (*     + eapply pfn_bot. apply (wf_ctx_perm_iff HPG) in H. pfn_wf_ctx_solver. *)
  (*     + assumption. *)
  (*   -  *)
  (*     specialize (IHHG G' (D' ++ [[!]t]) t). *)
  (*     assert (D' ++ [[!]t ] ≡[P] D' ++ [[!]t]) by reflexivity. *)
  (*     specialize (IHHG HPG H0). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     exists (S k). eapply pfn_one. 2: {rewrite HPD, H. apply Permutation_rel_assoc_swap. } *)
  (*     assumption. *)
  (*   - *)
  (*     specialize (IHHG G' ((D' ++ [[!]t0]) ++ [t] ++ [u]) t0). *)
  (*     assert ((D' ++ [[!] t0]) ++ [t] ++ [u] ≡[P] (D' ++ [t] ++ [u]) ++ [[!]t0]). {convertTactics.convert_multisetperm. permutation_solver. } *)
  (*     specialize (IHHG HPG H0). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     exists (S k). eapply pfn_tensor. eassumption. rewrite HPD, H. apply Permutation_rel_assoc_swap. *)
  (*   - *)
  (*     specialize (IHHG1 G' ((D1 ++ [[!]t0]) ++ [t]) t0 HPG (Permutation_rel_assoc_swap _ _ _)). *)
  (*     destruct IHHG1 as (k1 & IHHG1). *)
  (*     specialize (IHHG2 G' ((D2 ++ [[!]t0]) ++ [u]) t0 HPG (Permutation_rel_assoc_swap _ _ _)). *)
  (*     destruct IHHG2 as (k2 & IHHG2). *)
  (*     exists (S (S (Nat.max k1 k2))). eapply pfn_bang2. 2: {eassumption. } *)
  (*     eapply pfn_par. *)
  (*     + eapply IHHG1. *)
  (*     + eapply IHHG2. *)
  (*     + convertTactics.convert_multisetperm. permutation_solver. *)
  (*   - *)
  (*     specialize (IHHG G' ((D1 ++ [[!]t0]) ++ [t]) t0 HPG (Permutation_rel_assoc_swap _ _ _)). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     exists (S k). eapply pfn_bang1. *)
  (*     + apply IHHG. *)
  (*     + rewrite HPD, H. apply Permutation_rel_assoc_swap. *)
  (*   - *)
  (*     specialize (IHHG G' (D1 ++ [[!]t0]) t0 HPG). *)
  (*     assert (D1 ++ [[!] t0] ≡[P] D1 ++ [[!]t0]) by reflexivity. *)
  (*     specialize (IHHG H1). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     exists (S k). eapply pfn_bang0. *)
  (*     + apply H. *)
  (*     + apply IHHG. *)
  (*     + rewrite HPD, H0. apply Permutation_rel_assoc_swap. *)
  (*   - *)
  (*     specialize (IHHG G' ((D1 ++ [[!] t0]) ++ [[!]t] ++ [[!]t]) t0 HPG). *)
  (*     assert ((D1 ++ [[!]t0]) ++ [[!]t] ++ [[!]t] ≡[P] (D1 ++ [[!]t] ++ [[!]t]) ++ [[!]t0]). {convertTactics.convert_multisetperm. permutation_solver. } *)
  (*     specialize (IHHG H0). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     exists (S k). eapply pfn_bang2. *)
  (*     + apply IHHG. *)
  (*     + rewrite HPD, H. apply Permutation_rel_assoc_swap. *)
  (*   -  *)
  (*     specialize (IHHG G' ([t] ++ [[!]t0]) t0 HPG ). *)
  (*     assert ([t] ++ [[!]t0] ≡[P] [t] ++ [[!]t0]) by reflexivity. *)
  (*     specialize (IHHG H). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     admit. *)
      

      (* specialize (IHHG G' ((D ++ [[!]t0]) ++ [t]) t0 HPG). *)
      (* assert ((D ++ [[!]t0]) ++ [t] ≡[P] (D ++ [t]) ++ [[!]t0]) by apply Permutation_rel_assoc_swap. *)
      (* specialize (IHHG H). *)
      (* destruct IHHG as (k & IHHG). *)
      (* exists (S k).  *)
      (* eapply pfn_ques. *)
      (* + apply IHHG.  *)
      (* + apply vac_comp; auto. eapply vac_bang with (D := []). constructor. *)
      (* + rewrite HPD, H0. apply Permutation_rel_assoc_swap. *)
  (*   -  *)
  (*     specialize (IHHG G' ((D1 ++ [[!]t0]) ++ [typ_subst c u t]) t0 HPG). *)
  (*     assert ((D1 ++ [[!]t0]) ++ [typ_subst c u t] ≡[P] (D1 ++ [typ_subst c u t]) ++ [[!]t0]) by apply Permutation_rel_assoc_swap. *)
  (*     specialize (IHHG H1). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     exists (S k). eapply pfn_forall. *)
  (*     + eapply H. *)
  (*     + apply IHHG. *)
  (*     + rewrite HPD, H0. apply Permutation_rel_assoc_swap. *)
  (*   -  *)
  (*     specialize (IHHG (shift_ctx c 1 G') ((shift_ctx c 1 D1 ++ [[!] shift_typ c 1 t]) ++ [u]) (shift_typ c 1 t)). *) (*     assert (shift_ctx c 1 G ≡[P] shift_ctx c 1 G' ++ [shift_typ c 1 t]). {rewrite HPG. rewrite shift_ctx_app. reflexivity. } *)
  (*     assert ((shift_ctx c 1 D1 ++ [[!] shift_typ c 1 t]) ++ [u] ≡[P] (shift_ctx c 1 D1 ++ [u]) ++ [[!] shift_typ c 1 t]) by apply Permutation_rel_assoc_swap. *)
  (*     specialize (IHHG H0 H1). *)
  (*     destruct IHHG as (k & IHHG). *)
  (*     exists (S k). eapply pfn_exists. *)
  (*     + replace (shift_ctx c 1 D1 ++ [[!] shift_typ c 1 t]) with (shift_ctx c 1 (D1 ++ [[!]t])) in IHHG. 2: {rewrite shift_ctx_app. reflexivity. } apply IHHG. *)
  (*     + rewrite HPD, H. apply Permutation_rel_assoc_swap. *)
  (* Qed. *)

  (* Definition cut_admissibility_norm := forall n m c u D1 D2 G G', *)
  (*     D1 = [u] -> *)
  (*     G ≡[P] G' ++ [dual u] -> *)
  (*     n ⊣ c, G', D1 ⊢pf -> *)
  (*     m ⊣ c, G, D2 ⊢pf -> *)
  (*     exists k, k ⊣ c, G, D2 ⊢pf. *)
      

  Definition cut_admissibility_t n m c G1 G1' G2 G2' G3 D1 D1' D2 D2' A1 A2 A3 A4:=
    D1 ≡[P] D1' ++ A1 ->
    D2 ≡[P] D2' ++ A2 ->
    G1 ≡[P] G1' ++ A3 ->
    G2 ≡[P] G2' ++ A4 ->
    n ⊣ c, G1, D1 ⊢pf ->
    m ⊣ c, G2, D2 ⊢pf ->
               exists k, (k ⊣ c, G3, D1' ++ D2' ⊢pf).

  Definition cut_admissibility_norm n m u := forall c G D1 D1' D2 D2', cut_admissibility_t n m c G G G G G D1 D1' D2 D2' [u] [dual u] [] [].
  
  Lemma test : forall n m u, cut_admissibility_norm n m u.
  Proof.
    unfold cut_admissibility_norm. unfold cut_admissibility_t. Abort.

  (* Definition cut_admissibility_bang n m u := forall c G1 G2 D1 D1' D2, cut_admissibility_t n m c G1 G1 G2 G1 G1 D1 D1' D2 D2 [u] [] [] [dual u]. *)
  (* Lemma test : forall n m u, cut_admissibility_bang n m u. *)
  (* Proof. unfold cut_admissibility_bang. unfold cut_admissibility_t. Abort. *)

  (* Definition cut_admissibility_ques n m u := forall c G1 G2 D1 D2 D2', cut_admissibility_t n m c G1 G2 G2 G2 G2 D1 D1 D2 D2' [] [dual u] [u] []. *)
  (* Lemma test : forall n m u, cut_admissibility_ques n m u. *)
  (* Proof. unfold cut_admissibility_ques. unfold cut_admissibility_t. Abort. *)

  Definition cut_admissibility_bang n m u := forall c G1 G2 D1 D2, cut_admissibility_t n m c G1 G1 G2 G1 G1 D1 [] D2 D2 [u] [] [] [dual u].
  Lemma test : forall n m u, cut_admissibility_bang n m u.
  Proof. unfold cut_admissibility_bang. unfold cut_admissibility_t. Abort.

  Definition cut_admissibility_ques n m u := forall c G1 G2 D1 D2, cut_admissibility_t n m c G1 G2 G2 G2 G2 D1 D1 D2 [] [] [dual u] [u] [].
  Lemma test : forall n m u, cut_admissibility_ques n m u.
  Proof. unfold cut_admissibility_ques. unfold cut_admissibility_t. Abort.

  (*   - eapply pfn_perm_rel_iff. reflexivity. apply Permutation_rel_exchange. replace (S (Nat.max m n)) with (S (Nat.max n m)) by lia. *)
  (*     eapply H. *)
  (*     + rewrite dual_involutive in H1. apply H1. *)
  (*     + apply H0. *)
  (*     + apply H3. *)
  (*     + apply H2. *)
  (*     + apply H5. *)
  (*     + apply H4. *)
  (*   - eapply pfn_perm_rel_iff. reflexivity. apply Permutation_rel_exchange. replace (S (Nat.max n m)) with (S (Nat.max m n)) by lia. *)
  (*     eapply H. *)
  (*     + apply H1. *)
  (*     + rewrite dual_involutive. apply H0. *)
  (*     + apply H3. *)
  (*     + apply H2. *)
  (*     + apply H5. *)
  (*     + apply H4. *)
  (* Qed. *)

  (* Lemma cut_admissibility : forall n m u, cut_admissibility_norm n m u /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u) /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u). *)
  Lemma cut_admissibility_imp_norm :
    (forall n m u,
        cut_admissibility_norm n m u
        /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u)
        /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u)) ->
    (forall n m u, cut_admissibility_norm n m u).
  Proof.
    intros. specialize (H n m u). intuition.
  Qed.

  Lemma cut_admissibility_imp_bang :
    (forall n m u,
        cut_admissibility_norm n m u
        /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u)
        /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u)) ->
    (forall n m u, cut_admissibility_bang n m u).
  Proof.
    intros. pose proof H as H'.
    specialize (H' n m u) as (_ & H' & _).
    pose proof (cut_admissibility_imp_norm H).
    apply H'. intros.
    apply H0.
  Qed.

  Lemma cut_admissibility_imp_ques :
    (forall n m u,
        cut_admissibility_norm n m u
        /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u)
        /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u)) ->
    (forall n m u, cut_admissibility_ques n m u).
  Proof.
    intros. pose proof H as H'.
    specialize (H' n m u) as (_ & _ & H').
    pose proof (cut_admissibility_imp_norm H).
    apply H'. intros.
    apply H0.
  Qed.

  Lemma cut_admissibility_imp_norm2 :
    forall u,
      (forall n m,
          cut_admissibility_norm n m u
          /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u)
          /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u)) ->
      (forall n m, cut_admissibility_norm n m u).
  Proof.
    intros. specialize (H n m). intuition.
  Qed.
  Lemma cut_admissibility_imp_bang2 :
    forall u,
      (forall n m,
          cut_admissibility_norm n m u
          /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u)
          /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u)) ->
      (forall n m, cut_admissibility_bang n m u).
  Proof.
    intros. pose proof H as H'.
    specialize (H' n m) as (_ & H' & _).
    pose proof (cut_admissibility_imp_norm2 u H).
    auto.
  Qed.
    
  Lemma cut_admissibility_imp_ques2 :
    forall u,
      (forall n m,
          cut_admissibility_norm n m u
          /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u)
          /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u)) ->
      (forall n m, cut_admissibility_ques n m u).
  Proof.
    intros. pose proof H as H'.
    specialize (H' n m) as (_ & _ & H').
    pose proof (cut_admissibility_imp_norm2 u H).
    auto.
  Qed.


Ltac unfold_admissibilityH H :=
  unfold cut_admissibility_bang, cut_admissibility_ques, cut_admissibility_norm, cut_admissibility_t in H.

Ltac listSimpl :=
  repeat rewrite app_nil_r in *; repeat rewrite app_nil_l in *.

Ltac clear_permrel :=
  repeat match goal with
  | [ H : ?G1 ≡[P] ?G2 |- _ ] => clear H
  end.

Lemma cut_admissibility_tensor_norm :
  forall u1 u2 x n m
    (IHY : ∀ y : nat, y < x → Acc lt y)
    (IHWF : ∀ y : nat,
        y < x
        → ∀ n m : nat,
          y = n + m
          → (∀ n0 m0 : nat,
                cut_admissibility_norm n0 m0 u1
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n0 m0 u1)
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n0 m0 u1))
          → (∀ n0 m0 : nat,
                cut_admissibility_norm n0 m0 u2
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_bang n0 m0 u2)
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_ques n0 m0 u2))
          → cut_admissibility_norm n m (u1 ⊗ u2)
            ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_bang n m (u1 ⊗ u2))
            ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_ques n m (u1 ⊗ u2)))
    (Heqo : x = n + m)
    (IHu1 : ∀ n m : nat,
        cut_admissibility_norm n m u1
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n m u1)
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n m u1))
    (IHu2 : ∀ n m : nat,
        cut_admissibility_norm n m u2
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_bang n m u2)
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_ques n m u2)),
    cut_admissibility_norm n m (u1 ⊗ u2).
Proof.
    intros. unfold cut_admissibility_norm, cut_admissibility_t.
    intros c G D1 D1' D2 D2' HPD1 HPD2 HPG1 HPG2 HG1 HG2.
    destruct HG1; subst.
    - eapply cut_admissibility'_aux_id1; eassumption. 
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
      specialize (IHWF1 c G' (D ++ [t]) (D1' ++ [t]) D2 D2'). listSimpl.
      assert (D ++ [t] ≡[P] (D1' ++ [t]) ++ [u1 ⊗ u2]). {rewrite HPD1. clear_permrel. apply Permutation_rel_assoc_swap. }
      specialize (IHWF1 H1 HPD2 HPG1 HPG2 HG1 HG2).
      destruct IHWF1 as (k & IHWF1).
      exists (S k).
      eapply pfn_absorb; try eassumption.
      eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption.
    - symmetry in HPD1. apply Permutation_rel_singleton_nil in HPD1 as (_ & Hcontra). discriminate.
    - rewrite HPD1 in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
      specialize (IHWF1 c G D' E1 D2 D2').
      assert (D' ≡[P] E1 ++ [u1 ⊗ u2]). {rewrite HPE2, <- HPE3. reflexivity. }
      specialize (IHWF1 H HPD2 HPG1 HPG2 HG1 HG2).
      destruct IHWF1 as (k & IHWF1).
      exists (S k).
      eapply pfn_one.
      2: {rewrite HPE1. apply Permutation_rel_assoc_swap. }
      assumption.
    - rewrite HPD1 in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]].
      + injection HPE1. intros. subst. clear HPE1.
        destruct HG2.
        * eapply pfn_tensor in HG1. 2: {reflexivity. }.
           eapply cut_admissibility'_aux_id2. eassumption. rewrite dual_involutive. eassumption.
           eapply pfn_perm_rel. reflexivity. rewrite HPD1, HPE2. reflexivity. apply HG1.
        * assert (HM1: (S n) + n0 < S n + S n0) by lia.
           specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
           specialize (IHWF1 c G' D D1' (D0 ++ [t0]) (D2' ++ [t0])); listSimpl.
           assert (D0 ++ [t0] ≡[P] (D2' ++ [t0]) ++ [dual (t ⊗ u)]). {rewrite HPD2. apply Permutation_rel_assoc_swap. }
           eapply pfn_tensor in HG1. 2: { rewrite <- HPE2, <- HPD1. reflexivity. }
           specialize (IHWF1 HPD1 H1 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
           exists (S k). eapply pfn_absorb. 3: {rewrite <- app_assoc. eapply IHWF1. } 2: {eapply H0. }. wf_ctx_solver.
        * symmetry in HPD2. apply Permutation_rel_singleton_nil in HPD2 as (_ & Hcontra). discriminate.
        * rewrite HPD2 in H. apply Permutation_rel_split_last in H.
           destruct H as [[HPF1 HPF2]| [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
           assert (HM1: (S n) + n0 < S n + S n0) by lia.
           specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
           specialize (IHWF1 c G D D1' D'0 F2); listSimpl.
           eapply pfn_tensor in HG1.
           2: { rewrite <- HPE2, <- HPD1. reflexivity. }
           specialize (IHWF1 HPD1 HPF2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
           exists (S k). eapply pfn_one.
           apply IHWF1. rewrite HPF1, HPF3, <- app_assoc. reflexivity.
        * rewrite HPD2 in H. apply Permutation_rel_split_last in H.
          destruct H as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
          assert (HM1: S n + n0 < S n + S n0) by lia.
          specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
          specialize (IHWF1 c G D D1' (D'0 ++ [t0] ++ [u0]) (F2 ++ [t0] ++ [u0])); listSimpl.
          assert (HPD'1: D'0 ++ [t0] ++ [u0] ≡[P] (F2 ++ [t0] ++ [u0]) ++ [dual (t ⊗ u)]).
          {rewrite HPF2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. }
          eapply pfn_tensor in HG1.
          2: {rewrite <- HPE2. eassumption. }
          specialize (IHWF1 HPD1 HPD'1 HPG1 HPG1 HG1 HG2) as (k & IHWF1).
          exists (S k). eapply pfn_tensor. rewrite app_assoc in IHWF1. eassumption. rewrite HPF1, HPF3, app_assoc. reflexivity.
        * rewrite HPD2 in H. rewrite app_assoc in H. apply Permutation_rel_split_last in H.
          destruct H as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]].
          -- 
            injection HPF1. intros <- <-.
            specialize (IHu1 n n1) as (IHu1_1 & _ & _); unfold_admissibilityH IHu1_1.
            specialize (IHu1_1 c G (D' ++ [t] ++ [u]) (D' ++ [u]) (D1 ++ [dual t]) D1); listSimpl.
            assert (HPD'1: D' ++ [t] ++ [u] ≡[P] (D' ++ [u]) ++ [t]). {rewrite app_assoc. apply Permutation_rel_assoc_swap. }
            assert (HPD'2: D1 ++ [dual t] ≡[P] D1 ++ [dual t]) by reflexivity.
            specialize (IHu1_1 HPD'1 HPD'2 HPG1 HPG2 HG1 HG2_1) as (k1 & IHu1_1).
            clear HPD'1 HPD'2.
            specialize (IHu2 k1 n2) as (IHu2_1 & _ & _); unfold_admissibilityH IHu2_1.
            specialize (IHu2_1 c G ((D' ++ [u]) ++ D1) (D' ++ D1) (D2 ++ [dual u]) D2); listSimpl.
            assert (HPD'1: (D' ++ [u]) ++ D1 ≡[P] (D' ++ D1) ++ [u]) by apply Permutation_rel_assoc_swap.
            assert (HPD'2 : D2 ++ [dual u] ≡[P] D2 ++ [dual u]) by reflexivity.
            specialize (IHu2_1 HPD'1 HPD'2 HPG1 HPG2 IHu1_1 HG2_2) as (k2 & IHu2_1).
            exists k2. eapply pfn_perm_rel_iff. reflexivity. rewrite HPE2, HPF2, app_assoc. reflexivity. assumption.
         -- 
            apply Permutation_rel_split2 in HPF2.
            destruct HPF2 as [[I1 [HPI1 HPI2]] | [I2 [HPI1 HPI2]]].
            ++
              assert (HM1: S n + n1 < S n + S (Nat.max n1 n2)) by lia.
              specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
              specialize (IHWF1 c G D D1' (D1 ++ [t0]) (I1 ++ [t0])); listSimpl.
              assert (HPD'1: D1 ++ [t0] ≡[P] (I1 ++ [t0]) ++ [dual (t ⊗ u)]). {rewrite HPI1. apply Permutation_rel_assoc_swap. }
              eapply pfn_tensor in HG1. 2: {rewrite <- HPE2. eassumption. }
              specialize (IHWF1 HPD1 HPD'1 HPG1 HPG2 HG1 HG2_1) as (k & IHWF1).
              eapply pfn_perm_rel_iff_exists. reflexivity.
              assert (D1' ++ D2' ≡[P] (D1' ++ I1) ++ D2 ++ [t_par t0 u0]). {rewrite HPF1, HPF3, <- HPI2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. }
              apply H.
              apply pfn_par_exists; split.
              ** exists k. rewrite <- app_assoc. assumption.
              ** exists n2. assumption.
            ++
              assert (HM1: S n + n2 < S n + S (Nat.max n1 n2)) by lia.
              specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
              specialize (IHWF1 c G D D1' (D2 ++ [u0]) (I2 ++ [u0])); listSimpl.
              assert (HPD'1: D2 ++ [u0] ≡[P] (I2 ++ [u0]) ++ [dual (t ⊗ u)]). {rewrite HPI1. apply Permutation_rel_assoc_swap. }
              eapply pfn_tensor in HG1. 2: {rewrite <- HPE2. eassumption. }
              specialize (IHWF1 HPD1 HPD'1 HPG1 HPG2 HG1 HG2_2) as (k & IHWF1).
              eapply pfn_perm_rel_iff_exists. reflexivity.
              assert (D1' ++ D2' ≡[P] D1 ++ (D1' ++ I2) ++ [t_par t0 u0]). {rewrite HPF1, HPF3, <- HPI2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. }
              apply H.
              apply pfn_par_exists; split.
              ** exists n1. assumption.
              ** exists k. rewrite <- app_assoc. assumption.
        * rewrite HPD2 in H. apply Permutation_rel_split_last in H.
           destruct H as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
           assert (HM1: S n + n0 < S n + S n0) by lia.
           (* TODO: need a weakening here and move resource to n0 *)
           specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
           specialize (IHWF1 c (G ++ [t0]) D D1' D1 F1); listSimpl.
           assert (HPD'1 : D1 ≡[P] F1 ++ [dual (t ⊗ u)]). {rewrite HPF2, <- HPF3. reflexivity. }
           eapply pfn_tensor in HG1. 2: {rewrite <- HPE2. apply HPD1. }
           assert (HG'1: S n ⊣ c, (G ++ [t0]), D ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
           assert (HPG'1 : G ++ [t0] ≡[P] G ++ [t0]) by reflexivity.
           specialize (IHWF1 HPD1 HPD'1 HPG'1 HPG'1 HG'1 HG2) as (k & IHWF1).
           exists (S k). eapply pfn_bang. 2: {rewrite HPF1, app_assoc. reflexivity. } assumption.
        * symmetry in HPD2. apply Permutation_rel_singleton_nil in HPD2 as (_ & Hcontra). discriminate.
        * 
          rewrite HPD2 in H0. apply Permutation_rel_split_last in H0.
          destruct H0 as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
          assert (HM1: S n + n0 < S n + S n0) by lia.
          specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
          specialize (IHWF1 c G D D1' (D1 ++ [typ_subst c u0 t0]) (F1 ++ [typ_subst c u0 t0])); listSimpl.
          assert (HPD'1: D1 ++ [typ_subst c u0 t0] ≡[P] (F1 ++ [typ_subst c u0 t0]) ++ [dual (t ⊗ u)]). {rewrite HPF2, <- HPF3. apply Permutation_rel_assoc_swap. }
          eapply pfn_tensor in HG1. 2: {rewrite <- HPE2. eassumption. }
          specialize (IHWF1 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
          exists (S k). eapply pfn_forall; try eassumption. rewrite app_assoc in IHWF1. eassumption. rewrite HPF1, HPF3, app_assoc. reflexivity.
        * 
(* Because can conclude shift_ctx (dual (t ⊗ u)) *)

(* Whenever I have an existential exists u.  *)
(* c, G, D ⊢  *)

(*            *)
          (* TODO: Need to somehow downgrade shift_ctx *)
          (* specialize (H0 _ H1 _ _ c G D (D1 ++ [u0]) D1' (l2' ++ [u0]) eq_refl HP1). *)

          admit.
      + subst.
        assert (HM1: n + m < S n + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
        specialize (IHWF1 c G (D' ++ [t] ++ [u]) (E1 ++ [t] ++ [u]) D2 D2'); listSimpl.
        assert (HPD'1: (D' ++ [t] ++ [u]) ≡[P] (E1 ++ [t] ++ [u]) ++ [u1 ⊗ u2]). {rewrite HPE2, <- HPE3. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. }
        specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
        exists (S k). eapply pfn_tensor. 2: {assert (D1' ++ D2' ≡[P] (E1 ++ D2') ++ [t ⊗ u]). {rewrite HPE1. apply Permutation_rel_assoc_swap. } eassumption. }
        eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption.
    - rewrite HPD1, app_assoc in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      apply Permutation_rel_split2 in HPE2.
      destruct HPE2 as [[F1 [HPF1 HPF2]] | [F2 [HPF1 HPF2]]]; subst.
      + assert (HM1: n1 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). unfold cut_admissibility_norm, cut_admissibility_t in IHWF1.
        specialize (IHWF1 c G (D1 ++ [t]) (F1 ++ [t]) D2 D2'); listSimpl.
        assert (HPD'1: D1 ++ [t] ≡[P] (F1 ++ [t]) ++ [u1 ⊗ u2]). {rewrite HPF1. apply Permutation_rel_assoc_swap. }
        specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1_1 HG2) as (k & IHWF1).
        assert (IHWF'1: k ⊣ c, G, (F1 ++ D2') ++ [t] ⊢pf). {eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption. }
        eapply pfn_perm_rel_iff_exists. reflexivity. assert (D1' ++ D2' ≡[P] (F1 ++ D2') ++ D0 ++ [t_par t u]). {rewrite HPE1, HPE3, <- HPF2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. } eassumption.
        eapply pfn_par_exists; split; eexists; eauto.
      + assert (HM1: n2 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
        specialize (IHWF1 c G (D0 ++ [u]) (F2 ++ [u]) D2 D2'); listSimpl.
        assert (HPD'1: D0 ++ [u] ≡[P] (F2 ++ [u]) ++ [u1 ⊗ u2]). {rewrite HPF1. apply Permutation_rel_assoc_swap. }
        specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1_2 HG2) as (k & IHWF1).
        assert (IHWF'1: k ⊣ c, G, (F2 ++ D2') ++ [u] ⊢pf). {eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption. }
        eapply pfn_perm_rel_iff_exists. reflexivity. assert (D1' ++ D2' ≡[P] D1 ++ (F2 ++ D2') ++ [t_par t u]). {rewrite HPE1, HPE3, <- HPF2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. } eassumption.
        eapply pfn_par_exists; split; eexists; eauto.
    - rewrite HPD1 in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      subst. assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
      specialize (IHWF1 c (G ++ [t]) D1 E1 D2 D2'); listSimpl.
      rewrite <- HPE3 in HPE2.
      assert (HG'1: m ⊣ c, G ++ [t], D2 ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
      assert (HPG'1: G ++ [t] ≡[P] G ++ [t]) by reflexivity.
      specialize (IHWF1 HPE2 HPD2 HPG'1 HPG'1 HG1 HG'1) as (k & IHWF1).
      exists (S k). eapply pfn_perm_rel. reflexivity. rewrite HPE1. apply Permutation_rel_assoc_swap.
      eapply pfn_bang. 2: {reflexivity. } assumption.
    - symmetry in HPD1. apply Permutation_rel_singleton_nil in HPD1 as (_ & Hcontra). discriminate.
    - rewrite HPD1 in H0. apply Permutation_rel_split_last in H0.
      destruct H0 as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      subst. assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); unfold_admissibilityH IHWF1.
      specialize (IHWF1 c G (D1 ++ [typ_subst c u t]) (E1 ++ [typ_subst c u t]) D2 D2'); listSimpl.
      assert (HPD'1: D1 ++ [typ_subst c u t] ≡[P] (E1 ++ [typ_subst c u t]) ++ [u1 ⊗ u2]). {rewrite HPE2, <- HPE3. apply Permutation_rel_assoc_swap. }
      specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
      exists (S k). eapply pfn_perm_rel. reflexivity. rewrite HPE1. apply Permutation_rel_assoc_swap.
      eapply pfn_forall. eassumption. 2: {reflexivity. }
      eapply pfn_perm_rel. reflexivity. eapply Permutation_rel_assoc_swap.  assumption.
    - admit.
  Admitted.

Lemma cut_admissibility_tensor_bang :
  forall u1 u2 x n m
    (IHY : ∀ y : nat, y < x → Acc lt y)
    (IHWF : ∀ y : nat,
        y < x
        → ∀ n m : nat,
          y = n + m
          → (∀ n0 m0 : nat,
                cut_admissibility_norm n0 m0 u1
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n0 m0 u1)
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n0 m0 u1))
          → (∀ n0 m0 : nat,
                cut_admissibility_norm n0 m0 u2
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_bang n0 m0 u2)
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_ques n0 m0 u2))
          → cut_admissibility_norm n m (u1 ⊗ u2)
            ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_bang n m (u1 ⊗ u2))
            ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_ques n m (u1 ⊗ u2)))
    (Heqo : x = n + m)
    (IHu1 : ∀ n m : nat,
        cut_admissibility_norm n m u1
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n m u1)
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n m u1))
    (IHu2 : ∀ n m : nat,
        cut_admissibility_norm n m u2
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_bang n m u2)
        ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_ques n m u2))
    (HC: forall n m, cut_admissibility_norm n m (u1 ⊗ u2)), cut_admissibility_bang n m (u1 ⊗ u2).
  Proof.
    intros. unfold cut_admissibility_bang, cut_admissibility_t.
    intros c G1 G2 D1 D2 HPD1 HPD2 HPG1 HPG2 HG1 HG2. listSimpl. 
    destruct HG2; subst.
    - exists n. apply pfn_id; pfn_wf_ctx_solver. 
    - rewrite HPG2 in H0. apply Permutation_rel_split_last in H0.
      destruct H0 as [[HE1 HE2] | [E1 [E2 [HE1 [HE2 HE3]]]]].
      + 
        subst.
        assert (HM1: n + n0 < n + S n0) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF2 HC). unfold_admissibilityH IHWF2.
        specialize (IHWF2 c G1 G' D1 (D ++ [dual (u1 ⊗ u2)])); listSimpl.
        assert (HPD'1: D ++ [dual (u1 ⊗ u2)] ≡[P] D ++ [dual (u1 ⊗ u2)]) by reflexivity.
        specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
        unfold_admissibilityH HC. specialize (HC n k c G1 D1 [] (D ++ [dual (u1 ⊗ u2)]) D); listSimpl.
        specialize (HC HPD1 HPD'1 HPG1 HPG1 HG1 IHWF2) as (k2 & HC).
        eexists; eauto.
      + assert (HM1 : n + n0 < n + S n0) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
        specialize (IHWF2 c G1 G' D1 (D ++ [t])); listSimpl.
        assert (HPD'1: D ++ [t] ≡[P] D ++ [t]) by reflexivity.
        specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2).
        destruct IHWF2 as (k & IHWF2).
        exists (S k). eapply pfn_absorb. 3: {apply IHWF2. } 2: {apply HE1. } eapply wf_ctx_perm_iff. rewrite <- HE1. reflexivity. pfn_wf_ctx_solver.
    - exists 0. eapply pfn_bot. pfn_wf_ctx_solver.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3);specialize (IHWF2 HC);  unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 D'); listSimpl.
      assert (HPD'1 : D' ≡[P] D') by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_one. apply IHWF2. assumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 (D' ++ [t] ++ [u])); listSimpl.
      assert (HPD'1: D' ++ [t] ++ [u] ≡[P] D' ++ [t] ++ [u]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_tensor. eassumption. assumption.
    - pose proof IHWF as IHWF'.
      assert (HM1: n + n1 < n + S (Nat.max n1 n2)) by lia.
      assert (HM2: n + n2 < n + S (Nat.max n1 n2)) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 (D0 ++ [t])); listSimpl. 
      assert (HPD'1: D0 ++ [t] ≡[P] D0 ++ [t]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2_1) as (k1 & IHWF2).
      specialize (IHWF' _ HM2 _ _ eq_refl IHu1 IHu2) as (IHWF'1 & IHWF'2 & IHWF'3). specialize (IHWF'2 HC); unfold_admissibilityH IHWF'2.
      specialize (IHWF'2 c G1 G D1 (D2 ++ [u])); listSimpl.
      assert (HPD'2 : D2 ++ [u] ≡[P] D2 ++ [u]) by reflexivity.
      specialize (IHWF'2 HPD1 HPD'2 HPG1 HPG2 HG1 HG2_2) as (k2 & IHWF'2).
      exists (S (Nat.max k1 k2)). eapply pfn_par; try eassumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c (G1 ++ [t]) (G ++ [t]) D1 D0); listSimpl.
      assert (HPD'1 : D0 ≡[P] D0) by reflexivity.
      assert (HPG'1 : G1 ++ [t] ≡[P] G1 ++ [t]) by reflexivity.
      assert (HPG'2 : G ++ [t] ≡[P] (G1 ++ [t]) ++ [dual (u1 ⊗ u2)]) by (rewrite HPG2; apply Permutation_rel_assoc_swap).
      assert (HG'1 : n ⊣ c, (G1 ++ [t]), D1 ⊢pf).
      {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
      specialize (IHWF2 HPD1 HPD'1 HPG'1 HPG'2 HG'1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_bang. 2: {eassumption. } assumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 [t]); listSimpl.
      assert (HPD'1: [t] ≡[P] [t]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). apply pfn_ques; assumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 (D0 ++ [typ_subst c u t])); listSimpl.
      assert (HPD'1: D0 ++ [typ_subst c u t] ≡[P] D0 ++[typ_subst c u t]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_forall. eassumption. apply IHWF2. assumption.
    - admit.
  Admitted.

  Lemma cut_admissibility_tensor_ques :
    forall u1 u2 x n m
      (IHY : ∀ y : nat, y < x → Acc lt y)
      (IHWF : ∀ y : nat,
          y < x
          → ∀ n m : nat,
            y = n + m
            → (∀ n0 m0 : nat,
                  cut_admissibility_norm n0 m0 u1
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n0 m0 u1)
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n0 m0 u1))
            → (∀ n0 m0 : nat,
                  cut_admissibility_norm n0 m0 u2
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_bang n0 m0 u2)
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_ques n0 m0 u2))
            → cut_admissibility_norm n m (u1 ⊗ u2)
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_bang n m (u1 ⊗ u2))
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_ques n m (u1 ⊗ u2)))
      (Heqo : x = n + m)
      (IHu1 : ∀ n m : nat,
          cut_admissibility_norm n m u1
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n m u1)
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n m u1))
      (IHu2 : ∀ n m : nat,
          cut_admissibility_norm n m u2
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_bang n m u2)
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_ques n m u2))
      (HC: forall n m, cut_admissibility_norm n m (u1 ⊗ u2)), cut_admissibility_ques n m (u1 ⊗ u2).
  Proof.
    intros. unfold cut_admissibility_ques, cut_admissibility_t.
    intros c G1 G2 D1 D2 HPD1 HPD2 HPG1 HPG2 HG1 HG2. listSimpl. 
    destruct HG1; subst.
    - exists n. apply pfn_id; pfn_wf_ctx_solver. 
    - rewrite HPG1 in H0. apply Permutation_rel_split_last in H0.
      destruct H0 as [[HE1 HE2] | [E1 [E2 [HE1 [HE2 HE3]]]]].
      + 
        subst.
        assert (HM1: n + m < S n + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF3 HC). unfold_admissibilityH IHWF3.
        specialize (IHWF3 c G' G2 (D ++ [u1 ⊗ u2]) D2); listSimpl.
        assert (HPD'1: D ++ [u1 ⊗ u2] ≡[P] D ++ [u1 ⊗ u2]) by reflexivity.
        specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
        unfold_admissibilityH HC. specialize (HC k m c G2 (D ++ [u1 ⊗ u2]) D D2 []); listSimpl.
        specialize (HC HPD'1 HPD2 HPG2 HPG2 IHWF3 HG2) as (k2 & HC).
        eexists; eauto.
      + assert (HM1 : n + m < S n + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
        specialize (IHWF3 c G' G2 (D ++ [t]) D2); listSimpl.
        assert (HPD'1: D ++ [t] ≡[P] D ++ [t]) by reflexivity.
        specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2).
        destruct IHWF3 as (k & IHWF3).
        exists (S k). eapply pfn_absorb. 3: {apply IHWF3. } 2: {apply HE1. } eapply wf_ctx_perm_iff. rewrite <- HE1. reflexivity. pfn_wf_ctx_solver.
    - exists 0. eapply pfn_bot. pfn_wf_ctx_solver.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3);specialize (IHWF3 HC);  unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 D' D2); listSimpl.
      assert (HPD'1 : D' ≡[P] D') by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). eapply pfn_one. apply IHWF3. assumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 (D' ++ [t] ++ [u]) D2); listSimpl.
      assert (HPD'1: D' ++ [t] ++ [u] ≡[P] D' ++ [t] ++ [u]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). eapply pfn_tensor. eassumption. assumption.
    - pose proof IHWF as IHWF'.
      assert (HM1: n1 + m < S (Nat.max n1 n2) + m) by lia.
      assert (HM2: n2 + m < S (Nat.max n1 n2) + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 (D1 ++ [t]) D2); listSimpl. 
      assert (HPD'1: D1 ++ [t] ≡[P] D1 ++ [t]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1_1 HG2) as (k1 & IHWF3).
      specialize (IHWF' _ HM2 _ _ eq_refl IHu1 IHu2) as (IHWF'1 & IHWF'2 & IHWF'3). specialize (IHWF'3 HC); unfold_admissibilityH IHWF'3.
      specialize (IHWF'3 c G G2 (D0 ++ [u]) D2); listSimpl.
      assert (HPD'2 : D0 ++ [u] ≡[P] D0 ++ [u]) by reflexivity.
      specialize (IHWF'3 HPD'2 HPD2 HPG1 HPG2 HG1_2 HG2) as (k2 & IHWF'3).
      exists (S (Nat.max k1 k2)). eapply pfn_par; try eassumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c (G ++ [t]) (G2 ++ [t]) D1 D2); listSimpl.
      assert (HPD'1 : D1 ≡[P] D1) by reflexivity.
      assert (HPG'1 : G2 ++ [t] ≡[P] G2 ++ [t]) by reflexivity.
      assert (HPG'2 : G ++ [t] ≡[P] (G2 ++ [t]) ++ [(u1 ⊗ u2)]) by (rewrite HPG1; apply Permutation_rel_assoc_swap).
      assert (HG'1 : m ⊣ c, (G2 ++ [t]), D2 ⊢pf).
      {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
      specialize (IHWF3 HPD'1 HPD2 HPG'2 HPG'1 HG1 HG'1) as (k & IHWF3).
      exists (S k). eapply pfn_bang. 2: {eassumption. } assumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 [t] D2); listSimpl.
      assert (HPD'1: [t] ≡[P] [t]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). apply pfn_ques; assumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu1 IHu2) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 (D1 ++ [typ_subst c u t]) D2); listSimpl.
      assert (HPD'1: D1 ++ [typ_subst c u t] ≡[P] D1 ++[typ_subst c u t]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). eapply pfn_forall. eassumption. apply IHWF3. assumption.
    - admit.
  Admitted.

  Lemma cut_admissibility_tensor :
    forall u1 u2 n m
  (IHu1 : ∀ n m : nat,
           cut_admissibility_norm n m u1
           ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n m u1)
             ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n m u1))
  (IHu2 : ∀ n m : nat,
           cut_admissibility_norm n m u2
           ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_bang n m u2)
             ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u2) → cut_admissibility_ques n m u2)),
    cut_admissibility_norm n m (u1 ⊗ u2)
    ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_bang n m (u1 ⊗ u2))
      ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (u1 ⊗ u2)) → cut_admissibility_ques n m (u1 ⊗ u2)).
  Proof.
    intros u1 u2 n m.
    remember (n + m) as o.
    revert n m Heqo.
    induction (lt_wf o); intros.
    repeat split.
    - intros. eapply cut_admissibility_tensor_norm; eassumption.
    - intros. eapply cut_admissibility_tensor_bang; eassumption.
    - intros. eapply cut_admissibility_tensor_ques; eassumption.
  Qed.

  Lemma cut_admissibility_bang_norm:
    forall u x n m
      (IHY : ∀ y : nat, y < x → Acc lt y)
      (IHWF : ∀ y : nat,
          y < x
          → ∀ n m : nat,
            y = n + m
            → (∀ n0 m0 : nat,
                  cut_admissibility_norm n0 m0 u
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u)
                     → cut_admissibility_bang n0 m0 u)
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u)
                     → cut_admissibility_ques n0 m0 u))
            → cut_admissibility_norm n m ([!] u)
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u))
                 → cut_admissibility_bang n m ([!] u))
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u))
                 → cut_admissibility_ques n m ([!] u)))
      (Heqo : x = n + m)
      (IHu : ∀ n m : nat,
          cut_admissibility_norm n m u
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_bang n m u)
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_ques n m u)),
  cut_admissibility_norm n m ([!] u).
  Proof.
    intros. unfold cut_admissibility_norm, cut_admissibility_t.
    intros c G D1 D1' D2 D2' HPD1 HPD2 HPG1 HPG2 HG1 HG2.
    destruct HG1; subst.
    - eapply cut_admissibility'_aux_id1; eassumption.
    - subst. assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
      specialize (IHWF1 c G' (D ++ [t]) (D1' ++ [t]) D2 D2').
      assert (HPD'1: D ++ [t] ≡[P] (D1' ++ [t]) ++ [[!] u]). {rewrite HPD1. apply Permutation_rel_assoc_swap. }
      specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1 HG2).
      destruct IHWF1 as (k & IHWF1).
      exists (S k). eapply pfn_absorb. eassumption. eassumption.
      eapply pfn_perm_rel. reflexivity. eapply Permutation_rel_assoc_swap. assumption.
    - symmetry in HPD1. apply Permutation_rel_singleton_nil in HPD1 as (_ & Hcontra). discriminate.
    - rewrite HPD1 in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      subst. assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
      specialize (IHWF1 c G D' E1 D2 D2').
      rewrite <- HPE3 in HPE2.
      specialize (IHWF1 HPE2 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
      exists (S k). eapply pfn_one. 2: {rewrite HPE1. eapply Permutation_rel_assoc_swap. } assumption.
    - rewrite HPD1 in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      subst. assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
      specialize (IHWF1 c G (D' ++ [t] ++ [u0]) (E1 ++ [t] ++ [u0]) D2 D2').
      assert (HPD'1: D' ++ [t] ++ [u0] ≡[P] (E1 ++ [t] ++ [u0] ) ++ [[!] u]). {rewrite HPE2, <- HPE3. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. }
      specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
      exists (S k). eapply pfn_tensor. 2: {rewrite HPE1. apply Permutation_rel_assoc_swap. }
      eapply pfn_perm_rel. reflexivity. assert ((E1 ++ [t] ++ [u0]) ++ D2' ≡[P] ((E1 ++ D2') ++ [t] ++ [u0])). {clear_permrel. convertTactics.convert_multisetperm. permutation_solver. } eassumption. assumption.
    - rewrite HPD1, app_assoc in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      apply Permutation_rel_split2 in HPE2.
      destruct HPE2 as [[F1 [HPF1 HPF2]] | [F2 [HPF1 HPF2]]].
      + subst. assert (HM1: n1 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
        specialize (IHWF1 c G (D1 ++ [t]) (F1 ++ [t]) D2 D2').
        assert (HPD'1: D1 ++ [t] ≡[P]  (F1 ++ [t]) ++ [[!] u]). {rewrite HPF1. apply Permutation_rel_assoc_swap. }
        specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1_1 HG2) as (k & IHWF1).
        exists (S (Nat.max k n2)). eapply pfn_par.
        * 
          eapply pfn_perm_rel. reflexivity. assert ((F1 ++ [t]) ++ D2' ≡[P] (F1 ++ D2') ++ [t]) by apply Permutation_rel_assoc_swap. apply H. assumption.
        * 
          eapply HG1_2.
        * 
          rewrite HPE1, HPE3, <- HPF2. clear HPD1 HPD2 HPE1 HPF1 HPF2 HPE3. convertTactics.convert_multisetperm. permutation_solver.
      + subst. assert (HM1: n2 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
        specialize (IHWF1 c G (D0 ++ [u0]) (F2 ++ [u0]) D2 D2').
        assert (HPD'1: D0 ++ [u0] ≡[P] (F2 ++ [u0]) ++ [[!] u]). {rewrite HPF1. apply Permutation_rel_assoc_swap. }
        specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1_2 HG2) as (k & IHWF1).
        exists (S (Nat.max n1 k)). eapply pfn_par.
        * 
          eapply HG1_1.
        * 
          eapply pfn_perm_rel. reflexivity. assert ((F2 ++ [u0]) ++ D2' ≡[P] (F2 ++ D2') ++ [u0]) by apply Permutation_rel_assoc_swap. apply H. assumption.
        * 
          rewrite HPE1, HPE3, <- HPF2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver.
    - rewrite HPD1 in H. apply Permutation_rel_split_last in H.
      destruct H as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]].
      + injection HPE1. intros; subst. clear HPE1.
        destruct HG2.
        * eapply cut_admissibility'_aux_id2. eassumption. rewrite dual_involutive. eassumption.
          eapply pfn_bang. eassumption. rewrite <- HPE2. assumption.
        * assert (HM1: S n + n0 < S n + S n0) by lia.
          specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
          specialize (IHWF1 c G' (D1 ++ [[!]t]) D1' (D0 ++ [t0]) (D2' ++ [t0])).
          assert (HPD'1: D1 ++ [[!]t] ≡[P] D1' ++ [[!] t]). {rewrite HPE2. reflexivity. }
          assert (HPD'2: D0 ++ [t0] ≡[P] (D2' ++ [t0]) ++ [dual ([!] t)]). {rewrite HPD2. apply Permutation_rel_assoc_swap. }
          eapply pfn_bang in HG1. 2: {reflexivity. }
          specialize (IHWF1 HPD'1 HPD'2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
          exists (S k). eapply pfn_absorb. eassumption. eassumption. rewrite <- app_assoc. assumption.
        * symmetry in HPD2. apply Permutation_rel_singleton_nil in HPD2 as (_ & Hcontra). discriminate.
        * rewrite HPD2 in H. apply Permutation_rel_split_last in H.
          destruct H as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
          assert (HM1: S n + n0 < S n + S n0) by lia.
          specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
          specialize (IHWF1 c G (D1 ++ [[!]t]) D1' D' F2).
          assert (HPD'1: D1 ++ [[!]t] ≡[P] D1' ++ [[!] t]). {rewrite HPE2. reflexivity. }
          eapply pfn_bang in HG1. 2: {reflexivity. }
          specialize (IHWF1 HPD'1 HPF2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
          exists (S k). eapply pfn_one. 2: {rewrite HPF1, HPF3, app_assoc. reflexivity. } assumption.
        * rewrite HPD2 in H. apply Permutation_rel_split_last in H.
          destruct H as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
          assert (HM1: S n + n0 < S n + S n0) by lia.
          specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
          specialize (IHWF1 c G (D1 ++ [[!]t]) D1' (D' ++ [t0] ++ [u]) (F1 ++ [t0] ++ [u])).
          assert (HPD'1: D1 ++ [[!]t] ≡[P] D1' ++ [[!]t]). {rewrite HPE2. reflexivity. }
          assert (HPD'2: D' ++ [t0] ++ [u] ≡[P] (F1 ++ [t0] ++ [u]) ++ [dual ([!]t)]). {rewrite HPF2, <- HPF3. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. }
          eapply pfn_bang in HG1. 2: {reflexivity. }
          specialize (IHWF1 HPD'1 HPD'2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
          exists (S k). eapply pfn_tensor.
          -- rewrite app_assoc in IHWF1. apply IHWF1.
          -- rewrite HPF1. rewrite app_assoc. reflexivity.
        * rewrite HPD2, app_assoc in H. apply Permutation_rel_split_last in H.
          destruct H as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
          apply Permutation_rel_split2 in HPF2.
          destruct HPF2 as [[I1 [HPI1 HPI2]] | [I2 [HPI1 HPI2]]].
          -- assert (HM1: S n + n1 < S n + S (Nat.max n1 n2)) by lia.
             specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
             eapply pfn_bang in HG1. 2: {reflexivity. }
             specialize (IHWF1 c G (D1 ++ [[!]t]) D1' (D0 ++ [t0]) (I1 ++ [t0])).
             assert (HPD'1: D1 ++ [[!]t] ≡[P] D1' ++ [[!]t]). {rewrite HPE2. reflexivity. }
             assert (HPD'2: D0 ++ [t0] ≡[P] (I1 ++ [t0]) ++ [dual ([!]t)]). {rewrite HPI1. apply Permutation_rel_assoc_swap. }
             specialize (IHWF1 HPD'1 HPD'2 HPG1 HPG2 HG1 HG2_1) as (k & IHWF1).
             exists (S (Nat.max k n2)). eapply pfn_par.
             3: {assert (D1' ++ D2' ≡[P] (D1' ++ I1) ++ D2 ++ [t_par t0 u]). {rewrite HPF1 , HPF3, <- HPI2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. } eassumption. }
             ++ rewrite <- app_assoc. assumption.
             ++ assumption.
          -- assert (HM1: S n + n2 < S n + S (Nat.max n1 n2)) by lia.
             specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
             specialize (IHWF1 c G (D1 ++ [[!]t]) D1' (D2 ++ [u]) (I2 ++ [u])).
             assert (HPD'1: D1 ++ [[!] t] ≡[P] D1' ++ [[!]t]). {rewrite HPE2. reflexivity. }
             assert (HPD'2: D2 ++ [u] ≡[P] (I2 ++ [u]) ++ [dual ([!]t)]). {rewrite HPI1. apply Permutation_rel_assoc_swap. }
             eapply pfn_bang in HG1. 2: {reflexivity. }
             specialize (IHWF1 HPD'1 HPD'2 HPG1 HPG2 HG1 HG2_2) as (k & IHWF1).
             exists (S (Nat.max n1 k)). eapply pfn_par.
             3: {assert (D1' ++ D2' ≡[P] D0 ++ (D1' ++ I2) ++ [t_par t0 u]). {rewrite HPF1, HPF3, <- HPI2. clear_permrel. convertTactics.convert_multisetperm. permutation_solver. } eassumption. }
             ++ assumption.
             ++ rewrite <- app_assoc. apply IHWF1.
        * rewrite HPD2 in H. apply Permutation_rel_split_last in H.
          destruct H as [[HPF1 HPF2] | [F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
          assert (HM1: S n + n0 < S n + S n0) by lia.
          specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
          specialize (IHWF1 c (G ++ [t0]) (D1 ++ [[!]t]) D1' D0 F2); listSimpl.
          assert (HPD'1: D1 ++ [[!]t] ≡[P] D1' ++ [[!]t]). {rewrite HPE2. reflexivity. }
          eapply pfn_bang in HG1. 2: {reflexivity. }
          assert (HG'1: S n ⊣ c, G ++ [t0], D1 ++ [[!]t] ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
          assert (HPG'1: G ++ [t0] ≡[P] G ++ [t0]) by reflexivity.
          specialize (IHWF1 HPD'1 HPF2 HPG'1 HPG'1 HG'1 HG2) as (k & IHWF1).
          exists (S k). eapply pfn_bang. 2: {rewrite HPF1, HPF3, app_assoc. reflexivity. } assumption.
        * symmetry in HPD2. apply Permutation_rel_singleton_nil in HPD2 as (-> & HPD2).
          injection HPD2. intros; subst. clear HPD2.
          pose proof (cut_admissibility_imp_ques2 _ IHu n n0) as IHu'.
          unfold_admissibilityH IHu'.
          specialize (IHu' c (G ++ [t]) G D1 [dual t]); listSimpl.
          assert (HPD'1: D1 ≡[P] D1) by reflexivity.
          assert (HPD'2: [dual t] ≡[P] [dual t]) by reflexivity.
          assert (HPG'1: G ++ [t] ≡[P] G ++ [t]) by reflexivity.
          specialize (IHu' HPD'1 HPD'2 HPG'1 HPG2 HG1 HG2) as (k & IHu').
          exists k. eapply pfn_perm_rel. reflexivity. symmetry. apply HPE2. assumption.
        * rewrite HPD2 in H0. apply Permutation_rel_split_last in H0.
          destruct H0 as [[HPF1 HPF2] |[F1 [F2 [HPF1 [HPF2 HPF3]]]]]; try discriminate.
          assert (HM1: S n + n0 < S n + S n0) by lia.
          specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
          specialize (IHWF1 c G D D1' (D0 ++ [typ_subst c u t0]) (F2 ++ [typ_subst c u t0])); listSimpl.
          assert (HPD'2: D0 ++ [typ_subst c u t0] ≡[P] (F2 ++ [typ_subst c u t0]) ++ [dual ([!]t)]). {rewrite HPF2. apply Permutation_rel_assoc_swap. }
          eapply pfn_bang in HG1. 2: {rewrite <- HPE2. apply HPD1. }
          specialize (IHWF1 HPD1 HPD'2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
          exists (S k). eapply pfn_forall. eassumption. rewrite app_assoc in IHWF1. eassumption. rewrite HPF1, HPF3, app_assoc. reflexivity.
        * admit.
      + assert (HM1 : n + m < S n + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). unfold_admissibilityH IHWF1.
        specialize (IHWF1 c (G ++ [t]) D1 E2 D2 D2'); listSimpl.
        assert (HPG'1: G ++ [t] ≡[P] G ++ [t]) by reflexivity.
        assert (HG'1 : m ⊣ c, G ++ [t], D2 ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
        specialize (IHWF1 HPE2 HPD2 HPG'1 HPG'1 HG1 HG'1) as (k & IHWF1).
        exists (S k). eapply pfn_bang. eapply IHWF1. rewrite HPE1, HPE3. apply Permutation_rel_assoc_swap.
    - symmetry in HPD1. apply Permutation_rel_singleton_nil in HPD1 as (_ & Hcontra). discriminate.
    - rewrite HPD1 in H0. apply Permutation_rel_split_last in H0. 
      destruct H0 as [[HPE1 HPE2] | [E1 [E2 [HPE1 [HPE2 HPE3]]]]]; try discriminate.
      assert (HM1 : n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IWHF2 & IHWF3). unfold_admissibilityH IHWF1.
      specialize (IHWF1 c G (D1 ++ [typ_subst c u0 t]) (E2 ++ [typ_subst c u0 t]) D2 D2').
      assert (HPD'1: D1 ++ [typ_subst c u0 t] ≡[P] (E2 ++ [typ_subst c u0 t]) ++ [[!]u]). {rewrite HPE2. apply Permutation_rel_assoc_swap. }
      specialize (IHWF1 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF1).
      exists (S k). eapply pfn_forall. eassumption. 2: {rewrite HPE1, HPE3. apply Permutation_rel_assoc_swap. }
      eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption.
    - admit.
  Admitted.

  Lemma cut_admissibility_bang_bang:
    forall u x n m
      (IHY : ∀ y : nat, y < x → Acc lt y)
      (IHWF : ∀ y : nat,
          y < x
          → ∀ n m : nat,
            y = n + m
            → (∀ n0 m0 : nat,
                  cut_admissibility_norm n0 m0 u
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u)
                     → cut_admissibility_bang n0 m0 u)
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u)
                     → cut_admissibility_ques n0 m0 u))
            → cut_admissibility_norm n m ([!] u)
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u))
                 → cut_admissibility_bang n m ([!] u))
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u))
                 → cut_admissibility_ques n m ([!] u)))
      (Heqo : x = n + m)
      (IHu : ∀ n m : nat,
          cut_admissibility_norm n m u
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_bang n m u)
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_ques n m u))
      (HC: forall n m, cut_admissibility_norm n m ([!] u)),
      cut_admissibility_bang n m ([!] u).
  Proof.
    intros. unfold cut_admissibility_bang, cut_admissibility_t.
    intros c G1 G2 D1 D2 HPD1 HPD2 HPG1 HPG2 HG1 HG2. listSimpl. 
    destruct HG2; subst.
    - exists 0. eapply pfn_id; pfn_wf_ctx_solver.
    - rewrite HPG2 in H0. apply Permutation_rel_split_last in H0.
      destruct H0 as [[HE1 HE2] | [E1 [E2 [HE1 [HE2 HE3]]]]].
      + 
        subst.
        assert (HM1: n + n0 < n + S n0) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF2 HC). unfold_admissibilityH IHWF2.
        specialize (IHWF2 c G1 G' D1 (D ++ [dual ([!] u)])); listSimpl.
        assert (HPD'1: D ++ [dual ([!] u)] ≡[P] D ++ [dual ([!]u)]) by reflexivity.
        specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
        unfold_admissibilityH HC. specialize (HC n k c G1 D1 [] (D ++ [dual ([!]u)]) D); listSimpl.
        specialize (HC HPD1 HPD'1 HPG1 HPG1 HG1 IHWF2) as (k2 & HC).
        eexists; eauto.
      + assert (HM1 : n + n0 < n + S n0) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
        specialize (IHWF2 c G1 G' D1 (D ++ [t])); listSimpl.
        assert (HPD'1: D ++ [t] ≡[P] D ++ [t]) by reflexivity.
        specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2).
        destruct IHWF2 as (k & IHWF2).
        exists (S k). eapply pfn_absorb. 3: {apply IHWF2. } 2: {apply HE1. } eapply wf_ctx_perm_iff. rewrite <- HE1. reflexivity. pfn_wf_ctx_solver.
    - exists 0. eapply pfn_bot. pfn_wf_ctx_solver.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3);specialize (IHWF2 HC);  unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 D'); listSimpl.
      assert (HPD'1 : D' ≡[P] D') by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_one. apply IHWF2. assumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 (D' ++ [t] ++ [u0])); listSimpl.
      assert (HPD'1: D' ++ [t] ++ [u0] ≡[P] D' ++ [t] ++ [u0]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_tensor. eassumption. assumption.
    - pose proof IHWF as IHWF'.
      assert (HM1: n + n1 < n + S (Nat.max n1 n2)) by lia.
      assert (HM2: n + n2 < n + S (Nat.max n1 n2)) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 (D0 ++ [t])); listSimpl. 
      assert (HPD'1: D0 ++ [t] ≡[P] D0 ++ [t]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2_1) as (k1 & IHWF2).
      specialize (IHWF' _ HM2 _ _ eq_refl IHu) as (IHWF'1 & IHWF'2 & IHWF'3). specialize (IHWF'2 HC); unfold_admissibilityH IHWF'2.
      specialize (IHWF'2 c G1 G D1 (D2 ++ [u0])); listSimpl.
      assert (HPD'2 : D2 ++ [u0] ≡[P] D2 ++ [u0]) by reflexivity.
      specialize (IHWF'2 HPD1 HPD'2 HPG1 HPG2 HG1 HG2_2) as (k2 & IHWF'2).
      exists (S (Nat.max k1 k2)). eapply pfn_par; try eassumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c (G1 ++ [t]) (G ++ [t]) D1 D0); listSimpl.
      assert (HPD'1 : D0 ≡[P] D0) by reflexivity.
      assert (HPG'1 : G1 ++ [t] ≡[P] G1 ++ [t]) by reflexivity.
      assert (HPG'2 : G ++ [t] ≡[P] (G1 ++ [t]) ++ [dual ([!]u)]) by (rewrite HPG2; apply Permutation_rel_assoc_swap).
      assert (HG'1 : n ⊣ c, (G1 ++ [t]), D1 ⊢pf).
      {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
      specialize (IHWF2 HPD1 HPD'1 HPG'1 HPG'2 HG'1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_bang. 2: {eassumption. } assumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 [t]); listSimpl.
      assert (HPD'1: [t] ≡[P] [t]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). apply pfn_ques; assumption.
    - assert (HM1: n + n0 < n + S n0) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF2 HC); unfold_admissibilityH IHWF2.
      specialize (IHWF2 c G1 G D1 (D0 ++ [typ_subst c u0 t])); listSimpl.
      assert (HPD'1: D0 ++ [typ_subst c u0 t] ≡[P] D0 ++[typ_subst c u0 t]) by reflexivity.
      specialize (IHWF2 HPD1 HPD'1 HPG1 HPG2 HG1 HG2) as (k & IHWF2).
      exists (S k). eapply pfn_forall. eassumption. apply IHWF2. assumption.
    - admit.
  Admitted.

  Lemma cut_admissibility_bang_ques:
    forall u x n m
      (IHY : ∀ y : nat, y < x → Acc lt y)
      (IHWF : ∀ y : nat,
          y < x
          → ∀ n m : nat,
            y = n + m
            → (∀ n0 m0 : nat,
                  cut_admissibility_norm n0 m0 u
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u)
                     → cut_admissibility_bang n0 m0 u)
                  ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u)
                     → cut_admissibility_ques n0 m0 u))
            → cut_admissibility_norm n m ([!] u)
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u))
                 → cut_admissibility_bang n m ([!] u))
              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u))
                 → cut_admissibility_ques n m ([!] u)))
      (Heqo : x = n + m)
      (IHu : ∀ n m : nat,
          cut_admissibility_norm n m u
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_bang n m u)
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_ques n m u))
      (HC: forall n m, cut_admissibility_norm n m ([!] u)),
      cut_admissibility_ques n m ([!] u).
  Proof.
    intros. unfold cut_admissibility_ques, cut_admissibility_t.
    intros c G1 G2 D1 D2 HPD1 HPD2 HPG1 HPG2 HG1 HG2. listSimpl. 
    destruct HG1; subst.
    - exists n. apply pfn_id; pfn_wf_ctx_solver. 
    - rewrite HPG1 in H0. apply Permutation_rel_split_last in H0.
      destruct H0 as [[HE1 HE2] | [E1 [E2 [HE1 [HE2 HE3]]]]].
      + 
        subst.
        assert (HM1: n + m < S n + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF3 HC). unfold_admissibilityH IHWF3.
        specialize (IHWF3 c G' G2 (D ++ [[!] u]) D2); listSimpl.
        assert (HPD'1: D ++ [[!]u] ≡[P] D ++ [[!]u]) by reflexivity.
        specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
        unfold_admissibilityH HC. specialize (HC k m c G2 (D ++ [[!]u]) D D2 []); listSimpl.
        specialize (HC HPD'1 HPD2 HPG2 HPG2 IHWF3 HG2) as (k2 & HC).
        eexists; eauto.
      + assert (HM1 : n + m < S n + m) by lia.
        specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
        specialize (IHWF3 c G' G2 (D ++ [t]) D2); listSimpl.
        assert (HPD'1: D ++ [t] ≡[P] D ++ [t]) by reflexivity.
        specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2).
        destruct IHWF3 as (k & IHWF3).
        exists (S k). eapply pfn_absorb. 3: {apply IHWF3. } 2: {apply HE1. } eapply wf_ctx_perm_iff. rewrite <- HE1. reflexivity. pfn_wf_ctx_solver.
    - exists 0. eapply pfn_bot. pfn_wf_ctx_solver.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3);specialize (IHWF3 HC);  unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 D' D2); listSimpl.
      assert (HPD'1 : D' ≡[P] D') by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). eapply pfn_one. apply IHWF3. assumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 (D' ++ [t] ++ [u0]) D2); listSimpl.
      assert (HPD'1: D' ++ [t] ++ [u0] ≡[P] D' ++ [t] ++ [u0]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). eapply pfn_tensor. eassumption. assumption.
    - pose proof IHWF as IHWF'.
      assert (HM1: n1 + m < S (Nat.max n1 n2) + m) by lia.
      assert (HM2: n2 + m < S (Nat.max n1 n2) + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 (D1 ++ [t]) D2); listSimpl. 
      assert (HPD'1: D1 ++ [t] ≡[P] D1 ++ [t]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1_1 HG2) as (k1 & IHWF3).
      specialize (IHWF' _ HM2 _ _ eq_refl IHu) as (IHWF'1 & IHWF'2 & IHWF'3). specialize (IHWF'3 HC); unfold_admissibilityH IHWF'3.
      specialize (IHWF'3 c G G2 (D0 ++ [u0]) D2); listSimpl.
      assert (HPD'2 : D0 ++ [u0] ≡[P] D0 ++ [u0]) by reflexivity.
      specialize (IHWF'3 HPD'2 HPD2 HPG1 HPG2 HG1_2 HG2) as (k2 & IHWF'3).
      exists (S (Nat.max k1 k2)). eapply pfn_par; try eassumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c (G ++ [t]) (G2 ++ [t]) D1 D2); listSimpl.
      assert (HPD'1 : D1 ≡[P] D1) by reflexivity.
      assert (HPG'1 : G2 ++ [t] ≡[P] G2 ++ [t]) by reflexivity.
      assert (HPG'2 : G ++ [t] ≡[P] (G2 ++ [t]) ++ [[!]u]) by (rewrite HPG1; apply Permutation_rel_assoc_swap).
      assert (HG'1 : m ⊣ c, (G2 ++ [t]), D2 ⊢pf).
      {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
      specialize (IHWF3 HPD'1 HPD2 HPG'2 HPG'1 HG1 HG'1) as (k & IHWF3).
      exists (S k). eapply pfn_bang. 2: {eassumption. } assumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3). specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 [t] D2); listSimpl.
      assert (HPD'1: [t] ≡[P] [t]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). apply pfn_ques; assumption.
    - assert (HM1: n + m < S n + m) by lia.
      specialize (IHWF _ HM1 _ _ eq_refl IHu) as (IHWF1 & IHWF2 & IHWF3); specialize (IHWF3 HC); unfold_admissibilityH IHWF3.
      specialize (IHWF3 c G G2 (D1 ++ [typ_subst c u0 t]) D2); listSimpl.
      assert (HPD'1: D1 ++ [typ_subst c u0 t] ≡[P] D1 ++[typ_subst c u0 t]) by reflexivity.
      specialize (IHWF3 HPD'1 HPD2 HPG1 HPG2 HG1 HG2) as (k & IHWF3).
      exists (S k). eapply pfn_forall. eassumption. apply IHWF3. assumption.
    - admit.
  Admitted.
    

  Lemma cut_admissibility_bang_case :
    forall u n m 
  (IHu : ∀ n m : nat,
          cut_admissibility_norm n m u
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_bang n m u) ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_ques n m u)),
    cut_admissibility_norm n m ([!] u)
    ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u)) → cut_admissibility_bang n m ([!] u))
      ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' ([!] u)) → cut_admissibility_ques n m ([!] u)).
  Proof.
    intros u n m.
    remember (n + m) as o.
    revert n m Heqo.
    induction (lt_wf o); intros.
    repeat split.
    - intros. eapply cut_admissibility_bang_norm; eassumption.
    - intros. eapply cut_admissibility_bang_bang; eassumption.
    - intros. eapply cut_admissibility_bang_ques; eassumption.
  Qed.

  Lemma cut_admissibility_norm_dual : forall n m u, cut_admissibility_norm n m u <-> cut_admissibility_norm m n (dual u).
  Proof.
    intros. split; unfold cut_admissibility_norm, cut_admissibility_t; intros.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply H.
      + rewrite dual_involutive in H1. apply H1.
      + apply H0.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply H.
      + apply H1.
      + rewrite dual_involutive. apply H0.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
  Qed.

  Lemma cut_admissibility_bang_dual : forall n m u, cut_admissibility_bang n m u <-> cut_admissibility_ques m n (dual u).
  Proof.
    intros. split; unfold cut_admissibility_bang, cut_admissibility_ques, cut_admissibility_t; intros.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply H.
      + rewrite dual_involutive in H1. apply H1.
      + apply H0.
      + apply H3.
      + apply H2.
      + apply H5.
      + apply H4.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply H.
      + apply H1.
      + rewrite dual_involutive. apply H0.
      + apply H3.
      + apply H2.
      + apply H5.
      + apply H4.
  Qed.

  Lemma cut_admissibility_ques_dual : forall n m u, cut_admissibility_ques n m u <-> cut_admissibility_bang m n (dual u).
    Proof.
    intros. split; unfold cut_admissibility_ques, cut_admissibility_bang, cut_admissibility_t; intros.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply H.
      + assumption.
      + eassumption.
      + rewrite dual_involutive in H3. eassumption.
      + assumption.
      + assumption.
      + assumption.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply H.
      + eassumption.
      + assumption.
      + assumption.
      + rewrite dual_involutive. eassumption.
      + assumption.
      + assumption.
  Qed.
    (* ∀ n m : nat, *)
    (*            cut_admissibility_norm n m u1 *)
    (*            ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_bang n m u1) *)
    (*              ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u1) → cut_admissibility_ques n m u1) *)

  Lemma cut_admissibility_dual :
    forall u,
      (forall n m, 
          cut_admissibility_norm n m u
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_bang n m u)
          ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' u) → cut_admissibility_ques n m u))
      <-> (forall n m, cut_admissibility_norm n m (dual u)
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (dual u)) → cut_admissibility_bang n m (dual u))
                ∧ ((∀ n' m' : nat, cut_admissibility_norm n' m' (dual u)) → cut_admissibility_ques n m (dual u))).
  Proof.
    Hint Rewrite <- dual_involutive : core.
    Hint Resolve -> cut_admissibility_norm_dual : core.
    Hint Resolve <- cut_admissibility_norm_dual : core.
    Hint Resolve -> cut_admissibility_bang_dual : core.
    Hint Resolve <- cut_admissibility_bang_dual : core.
    Hint Resolve -> cut_admissibility_ques_dual : core.
    Hint Resolve <- cut_admissibility_ques_dual : core.
    intros. split; intros; specialize (H m n) as (H'1 & H'2 & H'3); repeat split; eauto.
  Qed.

  Lemma cut_admissibility : forall n m u, cut_admissibility_norm n m u /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_bang n m u) /\ ((forall n' m', cut_admissibility_norm n' m' u) -> cut_admissibility_ques n m u).
  Proof. 
    intros n m u. revert n m.
    induction u.
    - admit.
    - admit.
    - intros. eapply cut_admissibility_tensor; eassumption.
    - apply (cut_admissibility_dual (t_par u1 u2)).
      intros. 
      specialize (proj1 (cut_admissibility_dual _) IHu1) as IHu1'. clear IHu1.
      specialize (proj1 (cut_admissibility_dual _) IHu2) as IHu2'. clear IHu2.
      pose proof (cut_admissibility_tensor (dual u1) (dual u2) n m IHu1' IHu2').
      auto.
    - intros. eapply cut_admissibility_bang_case; eassumption.
    - apply (cut_admissibility_dual ([?] u)).
      intros. 
      specialize (proj1 (cut_admissibility_dual _) IHu) as IHu'. clear IHu.
      pose proof (cut_admissibility_bang_case (dual u) n m IHu').
      auto.
    - admit.


      
    (* - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange. *)
    (*   eapply cut_admissibility'_tensor. *)
    (*   + assert (IHu1' : forall n m c G D2 D1 D2' D1', D2 ≡[P] D2' ++ [dual u1] -> D1 ≡[P] D1' ++ [dual (dual u1)] -> (n ⊣ c, G, D1 ⊢pf) -> (m ⊣ c, G, D2 ⊢pf) -> exists k: nat, k ⊣ c, G, D2' ++ D1' ⊢pf). *)
    (*     {intros. eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange. *)
    (*      eapply IHu1. rewrite dual_involutive in H0. eapply H0. eapply H. eassumption. eassumption. *)
    (*     } *)
    (*     intros. eapply IHu1'. eassumption. eassumption. eassumption. eassumption. *)
    (*   + assert (IHu2' : forall n m c G D2 D1 D2' D1', D2 ≡[P] D2' ++ [dual u2] -> D1 ≡[P] D1' ++ [dual (dual u2)] -> (n ⊣ c, G, D1 ⊢pf) -> (m ⊣ c, G, D2 ⊢pf) -> exists k, k ⊣ c, G, D2' ++ D1' ⊢pf). *)
    (*     {intros. eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange. *)
    (*      eapply IHu2. rewrite dual_involutive in H0. eapply H0. eapply H. eassumption. eassumption. *)
    (*     } *)
    (*     intros. eapply IHu2'. eassumption. eassumption. eassumption. eassumption. *)
    (*   + eapply HP2. *)
    (*   + replace (dual u1 ⊗ dual u2) with (dual (t_par u1 u2)) by reflexivity. rewrite dual_involutive. eassumption. *)
    (*   + eapply HG2. *)
    (*   + eapply HG1. *)
      admit.                    (* Should be dual of tensor *)
    - intros. eapply cut_admissibility_bang_case; eassumption.


         
  

  Lemma cut_admissibility'_tensor : forall u1 u2 n m c G D1 D2 D1' D2'
      (IHu1 : ∀ (n m c : nat) (G : ctx) (D1 D2 D1' D2' : list typ),
          D1 ≡[ P] D1' ++ [u1]
          → D2 ≡[ P] D2' ++ [dual u1]
          → (n ⊣ c, G, D1 ⊢pf) → (m ⊣ c, G, D2 ⊢pf) → ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf)
      (IHu2 : ∀ (n m c : nat) (G : ctx) (D1 D2 D1' D2' : list typ),
          D1 ≡[ P] D1' ++ [u2]
          → D2 ≡[ P] D2' ++ [dual u2]
          → (n ⊣ c, G, D1 ⊢pf) → (m ⊣ c, G, D2 ⊢pf) → ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf)
      (HP1 : D1 ≡[ P] D1' ++ [u1 ⊗ u2])
        (HP2 : D2 ≡[ P] D2' ++ [dual (u1 ⊗ u2)])
        (HG1 : n ⊣ c, G, D1 ⊢pf)
        (HG2 : m ⊣ c, G, D2 ⊢pf),
  ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf.
  Proof.
    intros u1 u2 n m c G D1 D2 D1' D2' IHu1 IHu2.
    remember (n + m) as o.
    revert n m c G D1 D2 D1' D2' Heqo.
    induction (lt_wf o).
    intros.
    destruct HG1.
    - eapply cut_admissibility'_aux_id1; eassumption. 
    - assert (n + m < x) by lia.
      assert (n + m = n + m) by lia.
      specialize (H0 (n + m) H3 n m c G' (D ++ [t]) D2 (D1' ++ [t]) D2' H4).
      assert (D ++ [t] ≡[P] (D1' ++ [t]) ++ [u1 ⊗ u2]) by (convertTactics.convert_multisetperm; permutation_solver).
      specialize (H0 H5 HP2 HG1 HG2).
      destruct H0 as (k & H').
      exists (S k).
      eapply pfn_absorb; try eassumption.
      eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption.
    - symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (_ & Hcontra). discriminate.
    - rewrite HP1 in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]]; try discriminate.
      assert (n + m < x) by lia.
      assert (n + m = n + m) by lia.
      specialize (H0 (n + m) H1 n m c G D' D2 l1' D2' H2).
      assert (D' ≡[P] l1' ++ [u1 ⊗ u2]).
      {rewrite HP'2, <- HP'3. reflexivity. }
      specialize (H0 H3 HP2 HG1 HG2).
      destruct H0 as (k & H').
      exists (S k). eapply pfn_one.
      2: {rewrite HP'1. apply Permutation_rel_assoc_swap. }
      assumption.
    - rewrite HP1 in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]].
      + injection HP'1. intros. subst. clear HP'1.
        destruct HG2.
        ++ eapply pfn_tensor in HG1. 2: {reflexivity. }.
           eapply cut_admissibility'_aux_id2. eassumption. rewrite dual_involutive. eassumption.
           eapply pfn_perm_rel. reflexivity. rewrite HP1, HP'2. reflexivity. apply HG1.
        ++ assert ((S n) + n0 < S n + S n0) by lia.
           assert ((S n) + n0 = (S n) + n0) by lia.
           specialize (H0 _ H3 _ _ c G' D (D0 ++ [t0]) D1' (D2' ++ [t0]) H4 HP1).
           assert (D0 ++ [t0] ≡[P] (D2' ++ [t0]) ++ [dual (t ⊗ u)]). {convertTactics.convert_multisetperm. permutation_solver. }
           specialize (H0 H5). clear H3 H4 H5.
           eapply pfn_tensor in HG1.
           2: { rewrite <- HP'2, <- HP1. reflexivity. }
           specialize (H0 HG1 HG2). destruct H0 as (k & HG').
           assert (G' ≡[P] G') by reflexivity.
           assert (D1' ++ D2' ++ [t0] ≡[P] (D1' ++ D2') ++ [t0]) by (rewrite app_assoc; reflexivity).
           eapply (pfn_perm_rel_iff _ _ _ _ _ _ H0 H3) in HG'.
           eapply (pfn_absorb _ _ _ _ _ _ H1 H2) in HG'.
           exists (S k). eassumption.
        ++ symmetry in HP2. apply Permutation_rel_singleton_nil in HP2 as (_ & Hcontra). discriminate.
        ++ rewrite HP2 in H1. apply Permutation_rel_split_last in H1.
           destruct H1 as [[HP''1 HP''2]| [l1' [l2' [HP''1 [HP''2 HP''3]]]]]; try discriminate.
           assert ((S n) + n0 < S n + S n0) by lia.
           assert ((S n) + n0 = S n + n0) by lia.
           specialize (H0 _ H1 _ _ c G D (D'0) D1' l2' H2 HP1 HP''2).
           eapply pfn_tensor in HG1.
           2: { rewrite <- HP'2, <- HP1. reflexivity. }
           specialize (H0 HG1 HG2). destruct H0 as (k & HG').
           exists (S k). eapply pfn_one. 
           apply HG'. rewrite HP''1, HP''3, <- app_assoc. reflexivity.
        ++
          rewrite HP2 in H1. apply Permutation_rel_split_last in H1.
          destruct H1 as [[HP''1 HP''2] | [l1' [l2' [HP''1 [HP''2 HP''3]]]]]; try discriminate.
          assert (S n + n0 < S n + S n0) by lia.
          assert (S n + n0 = S n + n0) by lia.
          specialize (H0 _ H1 _ _ c G D (D'0 ++ [t0] ++ [u0]) D1' (l2' ++ [t0] ++ [u0]) H2 HP1) .
          assert (D'0 ++ [t0] ++ [u0] ≡[P] (l2' ++ [t0] ++ [u0]) ++ [dual (t ⊗ u)]).
          { convertTactics.convert_multisetperm. permutation_solver. }
          eapply pfn_tensor in HG1.
          2: {rewrite <- HP'2. eassumption. }
          specialize (H0 H3 HG1 HG2).
          destruct H0 as (k & HG').
          clear H1 H2 H3 HG1.
          rewrite app_assoc in HG'.
          eapply (pfn_tensor _ _ _ _ _ _ _ ) in HG'.
          2: {reflexivity. }
          exists (S k). eapply pfn_perm_rel_iff. reflexivity. rewrite HP''1, HP''3. reflexivity.
          rewrite app_assoc. assumption.
        ++ 
          rewrite HP2 in H1. rewrite app_assoc in H1. apply Permutation_rel_split_last in H1.
          destruct H1 as [[HP''1 HP''2] | [l1' [l2' [HP''1 [HP''2 HP''3]]]]].
          +++
            injection HP''1. intros <- <-.
            assert (D1 ++ [dual t] ≡[P] D1 ++ [dual t]) by reflexivity.
            assert (D' ++ [t] ++ [u] ≡[P] (D' ++ [u]) ++ [t]). {rewrite app_assoc. apply Permutation_rel_assoc_swap. }
            specialize (IHu1 _ _ _ _ _ _ _ _ H2 H1 HG1 HG2_1).
            destruct IHu1 as (k1 & IHu1).
            assert (D2 ++ [dual u] ≡[P] D2 ++ [dual u]) by reflexivity.
            assert (((D' ++ [u]) ++ D1) ≡[P] (D' ++ D1) ++ [u] ) by apply Permutation_rel_assoc_swap.
            specialize (IHu2 _ _ _ _ _ _ _ _ H4 H3 IHu1 HG2_2).
            destruct IHu2 as (k2 & IHu2).
            clear H1 H2 H3 H4.
            exists k2.
            eapply pfn_perm_rel_iff. reflexivity. rewrite HP'2, HP''2, app_assoc. reflexivity. auto.
          +++ 
            apply Permutation_rel_split2 in HP''2.
            destruct HP''2 as [[F1 [HQ1 HQ2]] | [F2 [HQ1 HQ2]]].
            * assert (S n + n1 < S n + S (Nat.max n1 n2)) by lia.
              assert (S n + n1 = S n + n1) by lia.
              specialize (H0 _ H1 _ _ c G D (D1 ++ [t0]) D1' (F1 ++ [t0]) H2 HP1).
              clear H1 H2.
              assert (D1 ++ [t0] ≡[P] (F1 ++ [t0]) ++ [dual (t ⊗ u)]). {rewrite HQ1. apply Permutation_rel_assoc_swap. }
              eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. eassumption. }
              specialize (H0 H1 HG1 HG2_1). destruct H0 as (k & HG').
              eapply pfn_perm_rel_iff_exists. reflexivity.
              assert (D1' ++ D2' ≡[P] (D1' ++ F1) ++ D2 ++ [t_par t0 u0]). {rewrite HP''1, HP''3, <- HQ2. clear HP''1 HQ1 HQ2 HP''3 H1. convertTactics.convert_multisetperm. permutation_solver. }
              apply H0.
              apply pfn_par_exists; split.
              ** exists k. rewrite <- app_assoc. assumption.
              ** exists n2. assumption.
            * assert (S n + n2 < S n + S (Nat.max n1 n2)) by lia.
              assert (S n + n2 = S n + n2) by reflexivity.
              specialize (H0 _ H1 _ _ c G D (D2 ++ [u0]) D1' (F2 ++ [u0]) H2 HP1).
              clear H1 H2.
              assert (D2 ++ [u0] ≡[P] (F2 ++ [u0]) ++ [dual (t ⊗ u)]). {rewrite HQ1. apply Permutation_rel_assoc_swap. }
              eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. eassumption. }
              specialize (H0 H1 HG1 HG2_2). destruct H0 as (k & HG').
              eapply pfn_perm_rel_iff_exists. reflexivity.
              assert (D1' ++ D2' ≡[P] D1 ++ (D1' ++ F2) ++ [t_par t0 u0]). {rewrite HP''1, HP''3, <- HQ2. clear HP''1 HQ1 HQ2 HP''3 H1. convertTactics.convert_multisetperm. permutation_solver.  }
              apply H0.
              apply pfn_par_exists; split.
              ** exists n1. assumption.
              ** exists k. rewrite <- app_assoc. assumption.
        (* ++ rewrite HP2 in H1. apply Permutation_rel_split_last in H1. *)
        (*    destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate. *)
        (*    assert (S n + n0 < S n + S n0) by lia. *)
        (*    specialize (H0 _ H1 _ _ c G D (D1 ++ [t0]) D1' (l2' ++ [t0]) eq_refl HP1). *)
        (*    assert (D1 ++ [t0] ≡[P] (l2' ++ [t0]) ++ [dual (t ⊗ u)]). {rewrite HQ2. apply Permutation_rel_assoc_swap. } *)
        (*    eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. eassumption. } *)
        (*    specialize (H0 H2 HG1 HG2). *)
        (*    destruct H0 as (k & HG'). *)
        (*    exists (S k). eapply pfn_bang1.  *)
        (*    * rewrite app_assoc in HG'. apply HG'.  *)
        (*    * rewrite HQ1, HQ3, app_assoc. reflexivity. *)
        (* ++ rewrite HP2 in H2. apply Permutation_rel_split_last in H2. *)
        (*    destruct H2 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate. *)
        (*    assert (S n + n0 < S n + S n0) by lia. *)
        (*    specialize (H0 _ H2 _ _ c G D D1 D1' l2' eq_refl HP1 HQ2). *)
        (*    eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. eassumption. } *)
        (*    specialize (H0 HG1 HG2). *)
        (*    destruct H0 as (k & HG'). *)
        (*    exists (S k). eapply pfn_bang0. *)
        (*    * apply H1. *)
        (*    * apply HG'. *)
        (*    * rewrite HQ1, HQ3, app_assoc. reflexivity. *)
        (* ++ rewrite HP2 in H1. apply Permutation_rel_split_last in H1. *)
        (*    destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate. *)
        (*    assert (S n + n0 < S n + S n0) by lia. *)
        (*    specialize (H0 _ H1 _ _ c G D (D1 ++ [[!]t0] ++ [[!]t0]) D1' (l2' ++ [[!]t0] ++ [[!]t0]) eq_refl HP1). *)
        (*    assert (D1 ++ [[!]t0] ++ [[!]t0] ≡[P] (l2' ++ [[!]t0] ++ [[!]t0]) ++ [dual (t ⊗ u)]). {rewrite HQ2. clear HP1 HP2 HP'2 HQ1 HQ2 HQ3. convertTactics.convert_multisetperm. permutation_solver. } *)
        (*    eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. eassumption. } *)
        (*    specialize (H0 H2 HG1 HG2). *)
        (*    destruct H0 as (k & HG'). *)
        (*    exists (S k). eapply pfn_bang2. *)
        (*    * rewrite app_assoc in HG'. apply HG'. *)
        (*    * rewrite HQ1, HQ3, app_assoc. reflexivity. *)

        ++ rewrite HP2 in H1. apply Permutation_rel_split_last in H1.
           destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
           assert (S n + n0 < S n + S n0) by lia.
           (* TODO: need a weakening here and move resource to n0 *)
           specialize (H0 _ H1 _ _ c (G ++ [t0]) D D1 D1' l2' eq_refl).
           clear H1.
           (* assert (D ≡[P] D' ++ [t ⊗ u]) by- reflexivity. *)

           (* assert (D ++ [t] ++ [u] ≡[P] (D1' ++ [t] ++ [u]) ++ [t ⊗ u]). {rewrite HP1. clear HP1 HP2 HP'2 HQ1 HQ2 HQ3. convertTactics.convert_multisetperm. permutation_solver. } *)
           eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. apply HP1. }
           assert (S n ⊣ c, (G ++ [t0]), D ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
           specialize (H0 HP1 HQ2 H1 HG2).
           destruct H0 as (k & HG').
           exists (S k). eapply pfn_bang. 2: {rewrite HQ1, HQ3, app_assoc. reflexivity. } assumption.
        (* ++ rewrite HP2 in H2. apply Permutation_rel_split_last in H2. *)
        (*    destruct H2 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate. *)
        (*    assert (S n + n0 < S n + S n0) by lia. *)
        (*    specialize (H0 _ H2 _ _ c G D (D0 ++ [t0]) D1' (l2' ++ [t0]) eq_refl). *)
        (*    clear H2. *)
        (*    eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. apply HP1. } *)
        (*    (* assert (S n ⊣ c, (G ++ [t0]), D ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. } *) *)
        (*    assert (D0 ++ [t0] ≡[P] (l2' ++ [t0]) ++ [dual (t ⊗ u)]). {rewrite HQ2. apply Permutation_rel_assoc_swap. } *)
        (*    specialize (H0 HP1 H2 HG1 HG2). *)
        (*    destruct H0 as (k & HG'). *)
        (*    exists (S k).  *)
        (*    eapply pfn_ques. *)
        (*    * rewrite app_assoc in HG'. apply HG'. *)
        (*    *  *)
        (*    eapply pfn_bang. 2: {rewrite HQ1, HQ3, app_assoc. reflexivity. } assumption. *)







                                      
           (*     rewrite HP2 in H1. apply Permutation_rel_split_last in H1. *)
           (* destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate. *)
           (* assert (S n + n0 < S n + S n0) by lia. *)
           (* (* TODO: need a weakening here and move resource to n0 *) *)
           (* specialize (H0 _ H1 _ _ c (G ++ [t0]) D D1 D1' l2' eq_refl). *)
           (* clear H1. *)
           (* (* assert (D ≡[P] D' ++ [t ⊗ u]) by- reflexivity. *) *)

           (* (* assert (D ++ [t] ++ [u] ≡[P] (D1' ++ [t] ++ [u]) ++ [t ⊗ u]). {rewrite HP1. clear HP1 HP2 HP'2 HQ1 HQ2 HQ3. convertTactics.convert_multisetperm. permutation_solver. } *) *)
           (* eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. apply HP1. } *)
           (* assert (S n ⊣ c, (G ++ [t0]), D ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. } *)
           (* specialize (H0 HP1 HQ2 H1 HG2). *)
           (* destruct H0 as (k & HG'). *)
           (* exists (S k). eapply pfn_bang. 2: {rewrite HQ1, HQ3, app_assoc. reflexivity. } assumption. *)
        ++ symmetry in HP2. apply Permutation_rel_singleton_nil in HP2 as (_ & Hcontra). discriminate.
        ++
          rewrite HP2 in H2. apply Permutation_rel_split_last in H2.
          destruct H2 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
          assert (S n + n0 < S n + S n0) by lia.
          specialize (H0 _ H2 _ _ c G D (D1 ++ [typ_subst c u0 t0]) D1' (l1' ++ [typ_subst c u0 t0]) eq_refl HP1).
          clear H2.
          assert (D1 ++ [typ_subst c u0 t0] ≡[P] (l1' ++ [typ_subst c u0 t0]) ++ [dual (t ⊗ u)]). {rewrite HQ2, <- HQ3. apply Permutation_rel_assoc_swap. }
          eapply pfn_tensor in HG1. 2: {rewrite <- HP'2. apply HP1. }
          specialize (H0 H2 HG1 HG2).
          destruct H0 as (k & HG').
          exists (S k). eapply pfn_forall; try eassumption.
          2: {rewrite HQ1, app_assoc. reflexivity. }
          rewrite <- app_assoc. assumption.
        ++
          rewrite HP2 in H1. apply Permutation_rel_split_last in H1.
          destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
          assert (S n + n0 < S n + S n0) by lia.

          (*
Because can conclude shift_ctx (dual (t ⊗ u))

Whenever I have an existential exists u. 
c, G, D ⊢ 

           *)
          (* TODO: Need to somehow downgrade shift_ctx *)
          (* specialize (H0 _ H1 _ _ c G D (D1 ++ [u0]) D1' (l2' ++ [u0]) eq_refl HP1). *)

          admit.
      + subst.
        assert (n + m < S n + m) by lia.
        specialize (H0 _ H1 _ _ c G (D' ++ [t] ++ [u]) D2 (l2' ++ [t] ++ [u]) D2' eq_refl).
        assert ((D' ++ [t] ++ [u]) ≡[P] (l2' ++ [t] ++ [u]) ++ [u1 ⊗ u2]). {rewrite HP'2. clear HP1 HP2 HP'1 HP'2 HP'3. convertTactics.convert_multisetperm. permutation_solver. }
        specialize (H0 H2 HP2 HG1 HG2).
        destruct H0 as (k & HG').
        assert (k ⊣ c, G, (l1' ++ D2') ++ [t] ++ [u] ⊢pf). {eapply pfn_perm_rel_iff. reflexivity. 2: {apply HG'. } rewrite HP'3. clear HP1 HP2 HP'1 HP'2 HP'3. convertTactics.convert_multisetperm. permutation_solver. }
        eapply pfn_tensor in H0. 2: {reflexivity. }
        exists (S k). eapply pfn_perm_rel. reflexivity. rewrite HP'1. apply Permutation_rel_assoc_swap. assumption.
    - rewrite HP1, app_assoc in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
      apply Permutation_rel_split2 in HQ2.
      destruct HQ2 as [[F1 [HF1 HF2]] | [F2 [HF1 HF2]]].
      + subst. assert (n1 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (H0 _ H1 _ _ c G (D1 ++ [t]) D2 (F1 ++ [t]) D2' eq_refl).
        clear H1.
        assert (D1 ++ [t] ≡[P] (F1 ++ [t]) ++ [u1 ⊗ u2]). {rewrite HF1. apply Permutation_rel_assoc_swap. }
        specialize (H0 H1 HP2 HG1_1 HG2).
        destruct H0 as (k & HG').
        assert (k ⊣ c, G, (F1 ++ D2') ++ [t] ⊢pf). {eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption. }
        eapply pfn_perm_rel_iff_exists. reflexivity. assert (D1' ++ D2' ≡[P] (F1 ++ D2') ++ D0 ++ [t_par t u]). {rewrite HQ1, HQ3, <- HF2. clear HP1 HP2 HQ1 HF1 HF2 HQ3. convertTactics.convert_multisetperm. permutation_solver. } eassumption.
        eapply pfn_par_exists; split; eexists; eauto.
      + subst. assert (n2 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (H0 _ H1 _ _ c G (D0 ++ [u]) D2 (F2 ++ [u]) D2' eq_refl).
        clear H1.
        assert (D0 ++ [u] ≡[P] (F2 ++ [u]) ++ [u1 ⊗ u2]). {rewrite HF1. apply Permutation_rel_assoc_swap. }
        specialize (H0 H1 HP2 HG1_2 HG2).
        destruct H0 as (k & HG').
        assert (k ⊣ c, G, (F2 ++ D2') ++ [u] ⊢pf). {eapply pfn_perm_rel. reflexivity. apply Permutation_rel_assoc_swap. assumption. }
        eapply pfn_perm_rel_iff_exists. reflexivity. assert (D1' ++ D2' ≡[P] D1 ++ (F2 ++ D2') ++ [t_par t u]). {rewrite HQ1, HQ3, <- HF2. clear HP1 HP2 HQ1 HF1 HF2 HQ3. convertTactics.convert_multisetperm. permutation_solver. } eassumption.
        eapply pfn_par_exists; split; eexists; eauto.
    - rewrite HP1 in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
      subst. assert (n + m < S n + m) by lia.
      specialize (H0 _ H1 _ _ c (G ++ [t]) D1 D2 l1' D2' eq_refl).
      rewrite <- HQ3 in HQ2.
      assert (m ⊣ c, G ++ [t], D2 ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
      specialize (H0 HQ2 HP2 HG1 H2).
      destruct H0 as (k & HG').
      exists (S k). eapply pfn_perm_rel. reflexivity. rewrite HQ1. apply Permutation_rel_assoc_swap.
      eapply pfn_bang. 2: {reflexivity. } assumption.
    - symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (_ & Hcontra). discriminate.
    - rewrite HP1 in H2. apply Permutation_rel_split_last in H2.
      destruct H2 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
      subst. assert (n + m < S n + m) by lia.
      specialize (H0 _ H2 _ _ c G (D1 ++ [typ_subst c u t]) D2 (l2' ++ [typ_subst c u t]) D2' eq_refl).
      assert (D1 ++ [typ_subst c u t] ≡[P] (l2' ++ [typ_subst c u t]) ++ [u1 ⊗ u2]). {rewrite HQ2. apply Permutation_rel_assoc_swap. }
      specialize (H0 H3 HP2 HG1 HG2).
      destruct H0 as (k & HG').
      exists (S k). eapply pfn_perm_rel. reflexivity. rewrite HQ1, HQ3. apply Permutation_rel_assoc_swap. 
      eapply pfn_forall. eassumption. 2: {reflexivity. }
      eapply pfn_perm_rel. reflexivity. eapply Permutation_rel_assoc_swap. assumption.
    - admit.
  Admitted.

  (* u : typ *)
  (* IHu : ∀ (n m c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
  (*         D1 ≡[ P] D1' ++ [u] → D2 ≡[ P] D2' ++ [dual u] → (n ⊣ c, G, D1 ⊢pf) → (m ⊣ c, G, D2 ⊢pf) → ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf *)
  (* n, m, c : nat *)
  (* G : ctx *)
  (* D1, D2, D1', D2' : list typ *)
  (* HP1 : D1 ≡[ P] D1' ++ [[!] u] *)
  (* HP2 : D2 ≡[ P] D2' ++ [dual ([!] u)] *)
  (* HG1 : n ⊣ c, G, D1 ⊢pf *)
  (* HG2 : m ⊣ c, G, D2 ⊢pf *)
  (* ============================ *)
  (* ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf *)

  Lemma cut_admissibility'_bang : forall u n m c G D1 D2 D1' D2'
      (IHu : ∀ (n m c : nat) (G : ctx) (D1 D2 D1' D2' : list typ),
          D1 ≡[ P] D1' ++ [u] → D2 ≡[ P] D2' ++ [dual u] → (n ⊣ c, G, D1 ⊢pf) → (m ⊣ c, G, D2 ⊢pf) → ∃ k : nat, k ⊣ c, G, D1' ++ D2' ⊢pf)
      (HP1 : D1 ≡[P] D1' ++ [[!] u])
      (HP2 : D2 ≡[P] D2' ++ [dual ([!] u)])
      (HG1 : n ⊣ c, G, D1 ⊢pf)
      (HG2 : m ⊣ c, G, D2 ⊢pf),
      exists k, k ⊣ c, G, D1' ++ D2' ⊢pf.
  Proof.
    intros u n m c G D1 D2 D1' D2' IHu.
    remember (n + m) as o.
    revert n m c G D1 D2 D1' D2' Heqo.
    induction (lt_wf o).
    intros.
    destruct HG1.
    - eapply cut_admissibility'_aux_id1; eassumption.
    - subst. assert (n + m < S n + m) by lia.
      specialize (H0 _ H3 _ _ c G' (D ++ [t]) D2 (D1' ++ [t]) D2' eq_refl).
      clear H3.
      assert (D ++ [t] ≡[P] (D1' ++ [t]) ++ [[!] u]). {rewrite HP1. apply Permutation_rel_assoc_swap. }
      specialize (H0 H3 HP2 HG1 HG2).
      destruct H0 as (k & HG').
      exists (S k). eapply pfn_absorb. eassumption. eassumption.
      eapply pfn_perm_rel. reflexivity. eapply Permutation_rel_assoc_swap. assumption.
    - symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (_ & Hcontra). discriminate.
    - rewrite HP1 in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]]; try discriminate.
      subst. assert (n + m < S n + m) by lia.
      specialize (H0 _ H1 _ _ c G D' D2 l1' D2' eq_refl).
      rewrite <- HP'3 in HP'2.
      specialize (H0 HP'2 HP2 HG1 HG2).
      destruct H0 as (k & HG').
      exists (S k). eapply pfn_one. 2: {rewrite HP'1. eapply Permutation_rel_assoc_swap. } assumption.
    - rewrite HP1 in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]]; try discriminate.
      subst. assert (n + m < S n + m) by lia.
      specialize (H0 _ H1 _ _ c G (D' ++ [t] ++ [u0]) D2 (l1' ++ [t] ++ [u0]) D2' eq_refl).
      clear H1.
      assert (D' ++ [t] ++ [u0] ≡[P] (l1' ++ [t] ++ [u0] ) ++ [[!] u]). {rewrite HP'2, <- HP'3. clear HP1 HP2 HP'1 HP'2 HP'3. convertTactics.convert_multisetperm. permutation_solver. }
      specialize (H0 H1 HP2 HG1 HG2).
      destruct H0 as (k & HG').
      exists (S k). eapply pfn_tensor. 2: {rewrite HP'1. apply Permutation_rel_assoc_swap. }
      eapply pfn_perm_rel. reflexivity. assert ((l1' ++ [t] ++ [u0]) ++ D2' ≡[P] ((l1' ++ D2') ++ [t] ++ [u0])). {clear HP1 HP2 HP'1 HP'2 HP'3 H1. convertTactics.convert_multisetperm. permutation_solver. } eassumption. assumption.
    - rewrite HP1, app_assoc in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]]; try discriminate.
      apply Permutation_rel_split2 in HP'2.
      destruct HP'2 as [[F1 [HF1 HF2]] | [F2 [HF1 HF2]]].
      + subst. assert (n1 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (H0 _ H1 _ _ c G (D1 ++ [t]) D2 (F1 ++ [t]) D2' eq_refl).
        clear H1.
        assert (D1 ++ [t] ≡[P]  (F1 ++ [t]) ++ [[!] u]). {rewrite HF1. apply Permutation_rel_assoc_swap. }
        specialize (H0 H1 HP2 HG1_1 HG2).
        destruct H0 as (k & HG').
        exists (S (Nat.max k n2)). eapply pfn_par. 
        ++ 
          eapply pfn_perm_rel. reflexivity. assert ((F1 ++ [t]) ++ D2' ≡[P] (F1 ++ D2') ++ [t]) by apply Permutation_rel_assoc_swap. apply H0. assumption.
        ++
          eapply HG1_2.
        ++
          rewrite HP'1, HP'3, <- HF2. clear HP1 HP2 HP'1 HF1 HF2 HP'3. convertTactics.convert_multisetperm. permutation_solver. 
      + subst. assert (n2 + m < S (Nat.max n1 n2) + m) by lia.
        specialize (H0 _ H1 _ _ c G (D0 ++ [u0]) D2 (F2 ++ [u0]) D2' eq_refl).
        clear H1.
        assert (D0 ++ [u0] ≡[P] (F2 ++ [u0]) ++ [[!] u]). {rewrite HF1. apply Permutation_rel_assoc_swap. }
        specialize (H0 H1 HP2 HG1_2 HG2).
        destruct H0 as (k & HG').
        exists (S (Nat.max n1 k)). eapply pfn_par.
        ++
          eapply HG1_1.
        ++
          eapply pfn_perm_rel. reflexivity. assert ((F2 ++ [u0]) ++ D2' ≡[P] (F2 ++ D2') ++ [u0]) by apply Permutation_rel_assoc_swap. apply H0. assumption.
        ++
          rewrite HP'1, HP'3, <- HF2. clear HP1 HP2 HP'1 HF1 HF2 HP'3. convertTactics.convert_multisetperm. permutation_solver.
    - rewrite HP1 in H1. apply Permutation_rel_split_last in H1.
      destruct H1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]].
      + injection HP'1. intros; subst. clear HP'1.
        destruct HG2.
        * eapply cut_admissibility'_aux_id2. eassumption. rewrite dual_involutive. eassumption.
          eapply pfn_bang. eassumption. rewrite <- HP'2. assumption.
        * assert (S n + n0 < S n + S n0) by lia.
          specialize (H0 _ H3 _ _ c G' (D1 ++ [[!]t]) (D0 ++ [t0]) D1' (D2' ++ [t0]) eq_refl).
          clear H3.
          assert (D1 ++ [[!]t] ≡[P] D1' ++ [[!] t]). {rewrite HP'2. reflexivity. }
          assert (D0 ++ [t0] ≡[P] (D2' ++ [t0]) ++ [dual ([!] t)]). {rewrite HP2. apply Permutation_rel_assoc_swap. }
          eapply pfn_bang in HG1. 2: {reflexivity. }
          specialize (H0 H3 H4 HG1 HG2).
          destruct H0 as (k & HG').
          exists (S k). eapply pfn_absorb. eassumption. eassumption. rewrite <- app_assoc. assumption.
        * symmetry in HP2. apply Permutation_rel_singleton_nil in HP2 as (_ & Hcontra). discriminate.
        * rewrite HP2 in H1. apply Permutation_rel_split_last in H1.
          destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
          assert (S n + n0 < S n + S n0) by lia.
          specialize (H0 _ H1 _ _ c G (D1 ++ [[!]t]) D' D1' l2' eq_refl).
          clear H1.
          assert (D1 ++ [[!]t] ≡[P] D1' ++ [[!] t]). {rewrite HP'2. reflexivity. }
          eapply pfn_bang in HG1. 2: {reflexivity. }
          specialize (H0 H1 HQ2 HG1 HG2).
          destruct H0 as (k & HG').
          exists (S k). eapply pfn_one. 2: {rewrite HQ1, HQ3, app_assoc. reflexivity. } assumption.
        * rewrite HP2 in H1. apply Permutation_rel_split_last in H1.
          destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
          assert (S n + n0 < S n + S n0) by lia.
          specialize (H0 _ H1 _ _ c G (D1 ++ [[!]t]) (D' ++ [t0] ++ [u]) D1' (l1' ++ [t0] ++ [u]) eq_refl).
          clear H1.
          assert (D1 ++ [[!]t] ≡[P] D1' ++ [[!]t]). {rewrite HP'2. reflexivity. }
          assert (D' ++ [t0] ++ [u] ≡[P] (l1' ++ [t0] ++ [u]) ++ [dual ([!]t)]). {rewrite HQ2, <- HQ3. clear HP2 HP1 HP'2 HQ1 HQ2 HQ3. convertTactics.convert_multisetperm. permutation_solver. }
          eapply pfn_bang in HG1. 2: {reflexivity. } 
          specialize (H0 H1 H2 HG1 HG2).
          destruct H0 as (k & HG').
          exists (S k). eapply pfn_tensor.
          ** rewrite app_assoc in HG'. apply HG'.
          ** rewrite HQ1. rewrite app_assoc. reflexivity.
        * rewrite HP2, app_assoc in H1. apply Permutation_rel_split_last in H1.
          destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
          apply Permutation_rel_split2 in HQ2.
          destruct HQ2 as [[F1 [HF1 HF2]] | [F2 [HF1 HF2]]].
          ** assert (S n + n1 < S n + S (Nat.max n1 n2)) by lia.
             specialize (H0 _ H1 _ _ c G (D1 ++ [[!]t]) (D0 ++ [t0]) D1' (F1 ++ [t0]) eq_refl).
             clear H1.
             assert (D1 ++ [[!]t] ≡[P] D1' ++ [[!]t]). {rewrite HP'2. reflexivity. }
             assert (D0 ++ [t0] ≡[P] (F1 ++ [t0]) ++ [dual ([!]t)]). {rewrite HF1. apply Permutation_rel_assoc_swap. }
             eapply pfn_bang in HG1. 2: {reflexivity. } 
             specialize (H0 H1 H2 HG1 HG2_1).
             destruct H0 as (k & HG').
             exists (S (Nat.max k n2)). eapply pfn_par.
             3: {assert (D1' ++ D2' ≡[P] (D1' ++ F1) ++ D2 ++ [t_par t0 u]). {rewrite HQ1, HQ3, <- HF2. clear HP2 HP1 HP'2 HQ1 HF1 HF2 HQ3 H1 H2. convertTactics.convert_multisetperm. permutation_solver. } eassumption. }
             *** rewrite <- app_assoc. assumption.
             *** assumption.
          ** assert (S n + n2 < S n + S (Nat.max n1 n2)) by lia.
             specialize (H0 _ H1 _ _ c G (D1 ++ [[!]t]) (D2 ++ [u]) D1' (F2 ++ [u]) eq_refl).
             clear H1.
             assert (D1 ++ [[!] t] ≡[P] D1' ++ [[!]t]). {rewrite HP'2. reflexivity. }
             assert (D2 ++ [u] ≡[P] (F2 ++ [u]) ++ [dual ([!]t)]). {rewrite HF1. apply Permutation_rel_assoc_swap. }
             eapply pfn_bang in HG1. 2: {reflexivity. }
             specialize (H0 H1 H2 HG1 HG2_2).
             destruct H0 as (k & HG').
             exists (S (Nat.max n1 k)). eapply pfn_par.
             3: {assert (D1' ++ D2' ≡[P] D0 ++ (D1' ++ F2) ++ [t_par t0 u]). {rewrite HQ1, HQ3, <- HF2. clear HP2 HP1 HP'2 HQ1 HF1 HF2 HQ3 H1 H2. convertTactics.convert_multisetperm. permutation_solver. } eassumption. }
             *** assumption.
             *** rewrite <- app_assoc. apply HG'.
        * rewrite HP2 in H1. apply Permutation_rel_split_last in H1.
          destruct H1 as [[HQ1 HQ2] | [l1' [l2' [HQ1 [HQ2 HQ3]]]]]; try discriminate.
          assert (S n + n0 < S n + S n0) by lia.
          specialize (H0 _ H1 _ _ c (G ++ [t0]) (D1 ++ [[!] t]) D0 D1' l2' eq_refl).
          clear H1.
          assert (D1 ++ [[!]t] ≡[P] D1' ++ [[!]t]). {rewrite HP'2. reflexivity. }
          eapply pfn_bang in HG1. 2: {reflexivity. }
          assert (S n ⊣ c, G ++ [t0], D1 ++ [[!]t] ⊢pf). {eapply pfn_weakening. reflexivity. pfn_wf_ctx_solver. assumption. }
          specialize (H0 H1 HQ2 H2 HG2).
          destruct H0 as (k & HG').
          exists (S k). eapply pfn_bang. 2: {rewrite HQ1, HQ3, app_assoc. reflexivity. } assumption.
        * symmetry in HP2. apply Permutation_rel_singleton_nil in HP2 as (-> & HP2).
          injection HP2. intros; subst. clear HP2.
  Admitted. 
          

                               
  Lemma cut_admissibility2 : forall u,
      ()


      
  Lemma cut_admissibility' : forall n m c u G D1 D2 D1' D2',
      D1 ≡[P] D1' ++ [u] ->
      D2 ≡[P] D2' ++ [dual u] ->
      n ⊣ c, G, D1 ⊢pf ->
      m ⊣ c, G, D2 ⊢pf ->
      exists k, k ⊣ c, G, D1' ++ D2' ⊢pf. 
    intros n m c u G D1 D2 D1' D2' HP1 HP2 HG1 HG2.
    revert n m c G D1 D2 D1' D2' HP1 HP2 HG1 HG2.
    induction u; intros.
    - admit.
    - admit.
    - eapply cut_admissibility'_tensor.
      + apply IHu1.
      + apply IHu2.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply cut_admissibility'_tensor.
      + assert (IHu1' : forall n m c G D2 D1 D2' D1', D2 ≡[P] D2' ++ [dual u1] -> D1 ≡[P] D1' ++ [dual (dual u1)] -> (n ⊣ c, G, D1 ⊢pf) -> (m ⊣ c, G, D2 ⊢pf) -> exists k: nat, k ⊣ c, G, D2' ++ D1' ⊢pf).
        {intros. eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
         eapply IHu1. rewrite dual_involutive in H0. eapply H0. eapply H. eassumption. eassumption.
        }
        intros. eapply IHu1'. eassumption. eassumption. eassumption. eassumption.
      + assert (IHu2' : forall n m c G D2 D1 D2' D1', D2 ≡[P] D2' ++ [dual u2] -> D1 ≡[P] D1' ++ [dual (dual u2)] -> (n ⊣ c, G, D1 ⊢pf) -> (m ⊣ c, G, D2 ⊢pf) -> exists k, k ⊣ c, G, D2' ++ D1' ⊢pf).
        {intros. eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
         eapply IHu2. rewrite dual_involutive in H0. eapply H0. eapply H. eassumption. eassumption.
        }
        intros. eapply IHu2'. eassumption. eassumption. eassumption. eassumption.
      + eapply HP2.
      + replace (dual u1 ⊗ dual u2) with (dual (t_par u1 u2)) by reflexivity. rewrite dual_involutive. eassumption.
      + eapply HG2.
      + eapply HG1.
    - 

  Admitted.


  Lemma cut_admissibility' : forall n m c u G D1 D2 D1' D2',
      D1 ≡[P] D1' ++ [u] ->
      D2 ≡[P] D2' ++ [dual u] ->
      n ⊣ c, G, D1 ⊢pf ->
      m ⊣ c, G, D2 ⊢pf ->
      exists k, k ⊣ c, G, D1' ++ D2' ⊢pf. 
    intros n m c u G D1 D2 D1' D2' HP1 HP2 HG1 HG2.
    revert n m c G D1 D2 D1' D2' HP1 HP2 HG1 HG2.
    induction u; intros.
    - admit.
    - admit.
    - eapply cut_admissibility'_tensor.
      + apply IHu1.
      + apply IHu2.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
    - eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
      eapply cut_admissibility'_tensor.
      + assert (IHu1' : forall n m c G D2 D1 D2' D1', D2 ≡[P] D2' ++ [dual u1] -> D1 ≡[P] D1' ++ [dual (dual u1)] -> (n ⊣ c, G, D1 ⊢pf) -> (m ⊣ c, G, D2 ⊢pf) -> exists k: nat, k ⊣ c, G, D2' ++ D1' ⊢pf).
        {intros. eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
         eapply IHu1. rewrite dual_involutive in H0. eapply H0. eapply H. eassumption. eassumption.
        }
        intros. eapply IHu1'. eassumption. eassumption. eassumption. eassumption.
      + assert (IHu2' : forall n m c G D2 D1 D2' D1', D2 ≡[P] D2' ++ [dual u2] -> D1 ≡[P] D1' ++ [dual (dual u2)] -> (n ⊣ c, G, D1 ⊢pf) -> (m ⊣ c, G, D2 ⊢pf) -> exists k, k ⊣ c, G, D2' ++ D1' ⊢pf).
        {intros. eapply pfn_perm_rel_iff_exists. reflexivity. apply Permutation_rel_exchange.
         eapply IHu2. rewrite dual_involutive in H0. eapply H0. eapply H. eassumption. eassumption.
        }
        intros. eapply IHu2'. eassumption. eassumption. eassumption. eassumption.
      + eapply HP2.
      + replace (dual u1 ⊗ dual u2) with (dual (t_par u1 u2)) by reflexivity. rewrite dual_involutive. eassumption.
      + eapply HG2.
      + eapply HG1.
    - 

  Admitted.

End PFN.

Lemma cut_admissibility_base:
  forall c p b G D1 D2 D1' D2',
    D1 ≡[P] D1' ++ [t_base p b] ->
    D2 ≡[P] D2' ++ [dual (t_base p b)] ->
    c ⊢ (t_base p b) wf ->
    ⦃c ; G ; D1 ⊢cf⦄ ->
    ⦃c ; G ; D2 ⊢cf⦄ ->
    ⦃c ; G ; D1' ++ D2' ⊢cf⦄.
Proof.
  intros c p b G D1 D2 D1' D2' HP1 HP2 HWFu HG1 HG2.
  revert p b D2 D1' D2' HP1 HP2 HWFu HG2.
  induction HG1; intros.
  - eapply cut_admissibility_aux_id; eauto.
  - admit.
  - inversion H.
  - eapply cut_admissibility_aux_bot; eauto.
  - rewrite H in HP1. apply Permutation_rel_split_last in HP1.
    destruct HP1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]].
    + injection HP'1. intros. subst.
    (* + eauto. *)
    (* + eauto. *)
    (* + eauto. *)
    (* + intros. *)
    (*   eapply IHHG1. *)
    (*   -  *)
    (*   eapply IHHG1; try eassumption. *)

Admitted.  
Lemma cut_admissibility_aux_id2 :
  forall c G u u' D1 D1' D2',
    [u] ++ [dual u] ≡[P] D2' ++ [u'] ->
    D1 ≡[P] D1' ++ [dual u'] ->
    ⦃ c; G; D1 ⊢cf ⦄->
    ⦃ c; G; (D1' ++ D2') ⊢cf ⦄.
Proof.
  intros. eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_exchange.
  eapply cut_admissibility_aux_id; eassumption.
Qed.



(* u1, u2 : typ *)
(*   IHu1 : ∀ (c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
(*            D1 ≡[ P] D1' ++ [u1] → D2 ≡[ P] D2' ++ [dual u1] → (⦃ c; G; D1 ⊢cf ⦄) → (⦃ c; G; D2 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄ *)
(*   IHu2 : ∀ (c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
(*            D1 ≡[ P] D1' ++ [u2] → D2 ≡[ P] D2' ++ [dual u2] → (⦃ c; G; D1 ⊢cf ⦄) → (⦃ c; G; D2 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄ *)
(*   ============================ *)
(*   ∀ (c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
(*     D1 ≡[ P] D1' ++ [u1 ⊗ u2] → D2 ≡[ P] D2' ++ [dual (u1 ⊗ u2)] → (⦃ c; G; D1 ⊢cf ⦄) → (⦃ c; G; D2 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄ *)
(* Lemma cut_admissibility_tensor : *)
(*   forall u1 u2 c G D1 D2 D1' D2' *)
(*     (IHu1 : ∀ (c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
(*         D1 ≡[ P] D1' ++ [u1] → D2 ≡[ P] D2' ++ [dual u1] → (⦃ c; G; D1 ⊢cf ⦄) → (⦃ c; G; D2 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄) *)
(*     (IHu2 : ∀ (c : nat) (G : ctx) (D1 D2 D1' D2' : list typ), *)
(*         D1 ≡[ P] D1' ++ [u2] → D2 ≡[ P] D2' ++ [dual u2] → (⦃ c; G; D1 ⊢cf ⦄) → (⦃ c; G; D2 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄), *)
(*     D1 ≡[ P] D1' ++ [u1 ⊗ u2] → D2 ≡[ P] D2' ++ [dual (u1 ⊗ u2)] → (⦃ c; G; D1 ⊢cf ⦄) → (⦃ c; G; D2 ⊢cf ⦄) → ⦃ c; G; (D1' ++ D2') ⊢cf ⦄. *)
(* Proof. *)
(*   intros u1 u2 c G D1 D2 D1' D2' IHu1 IHu2 HP1 HP2 HG1 HG2. *)
(*   revert u1 u2 D2 D1' D2' IHu1 IHu2 HP1 HP2 HG2. *)
(*   induction HG1; intros. *)
(*   - eapply cut_admissibility_aux_id; eassumption. *)
(*   - eapply pf_absorb; try eassumption. *)
(*     eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap. *)
(*     eapply IHHG1. *)
(*     + apply IHu1. *)
(*     + apply IHu2. *)
(*     + rewrite HP1. apply Permutation_rel_assoc_swap. *)
(*     + eapply HP2. *)
(*     + assumption. *)
(*   - inversion H. *)
(*   - symmetry in HP1. apply Permutation_rel_singleton_nil in HP1 as (_ & Hcontra). *)
(*     discriminate. *)
(*   - rewrite H in HP1. apply Permutation_rel_split_last in HP1. *)
(*     destruct HP1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]]; try discriminate. *)
(*     eapply pf_one. *)
(*     2: {rewrite HP'2. apply Permutation_rel_assoc_swap. } *)
(*     eapply IHHG1. *)
(*     + apply IHu1. *)
(*     + apply IHu2. *)
(*     + rewrite <- HP'3; auto. *)
(*     + eassumption. *)
(*     + assumption. *)
(*   - rewrite H in HP1. apply Permutation_rel_split_last in HP1. *)
(*     destruct HP1 as [[HP'1 HP'2] | [l1' [l2' [HP'1 [HP'2 HP'3]]]]]. *)
(*     + injection HP'1. intros; subst. clear HP'1. *)
(*       destruct HG2. *)
(*       * eapply pf_tensor in HG1. 2: {reflexivity. } *)
(*         eapply cut_admissibility_aux_id2. *)
(*         ** *)
(*           eapply HP2. *)
(*         ** *)
(*           rewrite dual_involutive, <- HP'2. reflexivity. *)
(*         ** *)
(*           assumption. *)
(*       * eapply pf_absorb; try eassumption. *)
(*         eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap. *)
(*         eapply IHHG1. *)
(*         ** apply IHu1. *)
(*         ** apply IHu2. *)
(* Abort. *)





(* Lemma cut_admissibility : *)
(*   forall c u G D1 D2 D1' D2', *)
(*     D1 ≡[P] D1' ++ [u] -> *)
(*     D2 ≡[P] D2' ++ [dual u] -> *)
(*     ⦃c ; G ; D1 ⊢cf⦄ -> *)
(*     ⦃c ; G ; D2 ⊢cf⦄ -> *)
(*     ⦃c ; G ; D1' ++ D2' ⊢cf⦄. *)
(* Proof. *)
(*   intros c u. *)
(*   revert c. *)
(*   induction u. *)
(*   - admit. *)
(*   - admit. *)
(*   -  *)

Lemma cut_admissibility :
  forall c u G D1 D2 D1' D2',
    D1 ≡[P] D1' ++ [u] ->
    D2 ≡[P] D2' ++ [dual u] ->
    ⦃c ; G ; D1 ⊢cf⦄ ->
    ⦃c ; G ; D2 ⊢cf⦄ ->
    ⦃c ; G ; D1' ++ D2' ⊢cf⦄.
Proof.
  intros c u G D1 D2 D1' D2' HP1 HP2 H.
  revert u D2 D1' D2' HP1 HP2.
  induction H.
  - intros t D2 D1' D2' HP1 HP2 I.
    eapply cut_admissibility_aux_id; eauto.
  - intros u D2 D1' D2' HP1 HP2 H2.
    eapply cut_admissibility_aux_absorb; eauto.
  - intros u0 D0 D1' D2' HP1 HP2 H4.
    inversion H.
  - intros u D2 D1' D2' HP1 HP2 H0.
    eapply cut_admissibility_aux_bot; eauto.
  - intros u D2 D1'  D2' HP1 HP2 HWFu H4.
    (*
- u = 1 => D' ≡ D1'
  D2 ≡ D2' + [⊥]
  then because cut free proof, we can have a normal proof, c; G; D2 ⊢norm
  then D2 = [⊥], D2' = []
D2' has arbitrary number of 1s => Need some lemma
induction on that.
- u != 1 => go through IH
     *)
    rewrite H0 in HP1.
    assert (HP3: [[1]] ++ D' ≡[P] [u] ++ D1').
    {
      convertTactics.convert_multisetperm. 
permutation_solver.
    } 
    unfold_destruct_relH HP3.
    apply Permutation_split in HP3.
    destruct HP3.
    + destruct p as (HPP1 & HPP2); clear HP1.
      subst.
      

      admit.
    +
      (* Can probably optimize this here *)
      destruct s as (l1' & l2' & HPP1 & HPP2).
      destruct HPP1 as (HPP1 & HPP3).
      apply Permutation_symmetric, Perm_ICPerm_inj, ICPerm_inv_TIn_cons_l in HPP3.
      apply TIn_app_exists_inj in HPP3. destruct HPP3 as (l3 & l4 & HPP3).
      rewrite HPP3 in HP1.
      assert (HP3: [] ++ [1] :: D' ≡[P] l3 ++ [1] :: l4 ++ [u]).
      {
        convertTactics.convert_multisetperm. permutation_solver.
        (* eapply transitivity. *)
        (* - replace ([1] :: D') with ([[1]] ++ D') by auto. eapply Permutation_rel_exchange. *)
        (* - assumption. *)
      }
      apply Permutation_rel_mid_cons_iff in HP3.
      replace (l3 ++ l4 ++ [u]) with ((l3 ++ l4) ++ [u]) in HP3 by (rewrite <- app_assoc; auto).
      simpl in HP3.
      specialize (IHpf _ _ _ _ HP3 HP2 HWFu H4).
      rewrite HPP3.
      eapply (pf_perm _ _ _ _ G _ ((l3 ++ l4) ++ D2' ++ [[1]])); auto.
      ++
        apply Permutation_reflexive.
      ++ 
        convertTactics.convert_multiset. permutation_solver.
      ++
        eapply pf_one.
        +++ 
          apply IHpf.
        +++ repeat rewrite <- app_assoc.
            reflexivity.
  - intros u' D2 D1' D2' HP1 HP2 HWFu H4.
    rewrite H0 in HP1.
    apply Permutation_rel_split2 in HP1.
    destruct HP1 as [[l1' [HP'1 HP'2]] | [l2' [HP'1 HP'2]]].
    + eapply pf_perm_rel.
      ++ auto.
      ++ reflexivity.
      ++ assert (D1' ++ D2' ≡[P] (l1' ++ D2') ++ [t ⊗ u]).
         {
           convertTactics.convert_multisetperm. permutation_solver.
         }
         rewrite H1.
         reflexivity.
      ++ eapply pf_tensor.
         2: {
           reflexivity.
         }
         eapply pf_perm_rel.
         auto.
         reflexivity.
         assert ((l1' ++ D2') ++ [t] ++ [u] ≡[P] (l1' ++ [t] ++ [u]) ++ D2').
         {
           convertTactics.convert_multisetperm. permutation_solver.
         }
         rewrite H1.
         reflexivity.
         eapply IHpf.
         2 : {
           apply HP2.
         }
         +++ 
           rewrite HP'1.
           convertTactics.convert_multisetperm. permutation_solver.
         +++ 
           assumption.
         +++ assumption.
    + 
      symmetry in HP'1. apply Permutation_rel_singleton_nil in HP'1 as (-> & HP'1).
      rewrite app_nil_r in HP'2.
      (* eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP'2. reflexivity. *)
      (* subst. *)
      (* clear D1' HP'2 D H0. *)
      (* revert D2' D' t u HP2 HWFu H IHpf. *)
      (* {induction H4; intros. *)
      (*  - admit. *)
      (*  - admit. *)
      (*  - admit. *)
      (* } *)
      admit.
       
      
      (* eapply cut_admissibility_aux_tensor; eauto. *)
  - intros.
    rewrite H1, app_assoc in HP1. apply Permutation_rel_split_last in HP1.
    destruct HP1 as [[HP3 HP4] | [l1' [l2' [HP3 [HP4 HP5]]]]].
    + 
      rewrite <- HP3 in *. simpl in HP2.

      

    + apply Permutation_rel_split2 in HP3.
      destruct HP3 as [[l3' [HP'1 HP'2]] | [l4' [HP'1 HP'2]]].
      ++ eapply pf_par.
         3: {
           assert (D1' ++ D2' ≡[P] (l3' ++ D2') ++ D2 ++ [t_par t u]).
           {convertTactics.convert_multisetperm. permutation_solver. }
           eassumption.
         }
         +++
           eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap.
           eapply IHpf1.
           2: {apply HP2. }
           convertTactics.convert_multisetperm. permutation_solver.
           assumption. assumption.
         +++ 
           assumption.
      ++ eapply pf_par.
         3: {
           assert (D1' ++ D2' ≡[P] D1 ++ (l4' ++ D2') ++ [t_par t u]).
           {convertTactics.convert_multisetperm. permutation_solver. }
           eassumption.
         }
         +++
           assumption.
         +++ 
           eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap.
           eapply IHpf2.
           2: {apply HP2. }
           convertTactics.convert_multisetperm. permutation_solver.
           assumption. assumption.
    admit.
  - intros.
    rewrite H0 in HP1.
    admit.
  - intros.
    symmetry in HP1.
    apply Permutation_rel_singleton in HP1.
    destruct D1'.
    2: { destruct D1'; discriminate. }
    simpl in HP1.
    injection HP1; intros HU.
    eapply IHpf.
    + eapply reflexivity.
    + eapply reflexivity.
    + rewrite HU in HWFu.
      inversion HWFu; auto.
    + rewrite HU in HP2.
      simpl dual in HP2.
      admit.
  - 
    (* eapply pf_one. *)

    (* rewrite H0 in HP1. *)
    (* assert ([[1]] ++ D' ≡[P] [u] ++ D1'). *)
    (* { *)
    (*   convertTactics.convert_multisetperm. permutation_solver. *)
    (* } *)
    (* apply Permutation_split_rel in H1. *)
    (* destruct H1. *)
    (* + destruct H1. *)
    (*   subst. *)
    (*   simpl dual in HP2. *)
    (*   inversion *)
    (* PInvert. *)
    (* eapply pf_one. *)
    admit.
Admitted.





Lemma cut_admissibility :
  forall c u G D1 D2 D1' D2',
    D1 ≡[P] D1' ++ [u] ->
    D2 ≡[P] D2' ++ [dual u] ->
    (* c ⊢ u wf -> *)
    ⦃c ; G ; D1 ⊢cf⦄ ->
    ⦃c ; G ; D2 ⊢cf⦄ ->
    ⦃c ; G ; D1' ++ D2' ⊢cf⦄.
Proof.
  intros c u G D1 D2 D1' D2' HP1 HP2 HWFu H.
  revert u D2 D1' D2' HP1 HP2 HWFu.
  induction H.
  - intros t D2 D1' D2' HP1 HP2 HWFt I.
    PInvert.
    + eapply pf_perm. tauto. apply Permutation_reflexive. apply Permutation_symmetric.
      eapply Permutation_transitive; [ | apply HP0]. apply Permutation_append; eauto. 
      apply Permutation_reflexive.
      assumption.
    + subst. rewrite dual_involutive in HP0.
      eapply pf_perm. tauto. apply Permutation_reflexive. apply Permutation_symmetric.
      eapply Permutation_transitive; [ | apply HP0]. apply Permutation_append; eauto. 
      convertTactics.convert_multiset. permutation_solver.
      assumption.
  - intros u D2 D1' D2' HP1 HP2 HWFu H2.
    eapply pf_absorb.
    eassumption.
    eassumption.
    assert (⦃c; G'; ((D1' ++ [t]) ++ D2') ⊢cf⦄).
    {
      eapply IHpf with (u := u).
      rewrite <- app_assoc.
            convertTactics.convert_multisetperm. permutation_solver.
            eassumption.
            eassumption.
            eassumption.
    }
    eapply pf_perm; eauto.
    apply Permutation_reflexive.
    convertTactics.convert_multiset. permutation_solver.
  - intros u0 D0 D1' D2' HP1 HP2 HWFu H4.
    inversion H.
  - intros u D2 D1' D2' HP1 HP2 HWFu H0.
    PInvert. LInvert.
    simpl. simpl dual in HP0.
    assert (⦃c ; G; (D2' ++ [[1]]) ⊢cf⦄).
    { eapply pf_perm. tauto. apply Permutation_reflexive. eapply Permutation_transitive. eapply Permutation_symmetric.
      apply HP0.
      convertTactics.convert_multiset. permutation_solver.
      auto.
      (* eapply perm_comp. eapply Permutation_exchange. *)
      (* eapply perm_plus. eapply Permutation_symmetric. apply HP2. apply perm_id. apply H0. *)
    }
    eapply pf_cf_unit_inv.
    2 : { apply H1. }.
    reflexivity.
  - intros u D2 D1'  D2' HP1 HP2 HWFu H4.
    (*
- u = 1 => D' ≡ D1'
  D2 ≡ D2' + [⊥]
  then because cut free proof, we can have a normal proof, c; G; D2 ⊢norm
  then D2 = [⊥], D2' = []
D2' has arbitrary number of 1s => Need some lemma
induction on that.
- u != 1 => go through IH
     *)
    rewrite H0 in HP1.
    assert (HP3: [[1]] ++ D' ≡[P] [u] ++ D1').
    {
      convertTactics.convert_multisetperm. 
permutation_solver.
    } 
    unfold_destruct_relH HP3.
    apply Permutation_split in HP3.
    destruct HP3.
    + destruct p as (HPP1 & HPP2); clear HP1.
      subst.
      

      admit.
    +
      (* Can probably optimize this here *)
      destruct s as (l1' & l2' & HPP1 & HPP2).
      destruct HPP1 as (HPP1 & HPP3).
      apply Permutation_symmetric, Perm_ICPerm_inj, ICPerm_inv_TIn_cons_l in HPP3.
      apply TIn_app_exists_inj in HPP3. destruct HPP3 as (l3 & l4 & HPP3).
      rewrite HPP3 in HP1.
      assert (HP3: [] ++ [1] :: D' ≡[P] l3 ++ [1] :: l4 ++ [u]).
      {
        convertTactics.convert_multisetperm. permutation_solver.
        (* eapply transitivity. *)
        (* - replace ([1] :: D') with ([[1]] ++ D') by auto. eapply Permutation_rel_exchange. *)
        (* - assumption. *)
      }
      apply Permutation_rel_mid_cons_iff in HP3.
      replace (l3 ++ l4 ++ [u]) with ((l3 ++ l4) ++ [u]) in HP3 by (rewrite <- app_assoc; auto).
      simpl in HP3.
      specialize (IHpf _ _ _ _ HP3 HP2 HWFu H4).
      rewrite HPP3.
      eapply (pf_perm _ _ _ _ G _ ((l3 ++ l4) ++ D2' ++ [[1]])); auto.
      ++
        apply Permutation_reflexive.
      ++ 
        convertTactics.convert_multiset. permutation_solver.
      ++
        eapply pf_one.
        +++ 
          apply IHpf.
        +++ repeat rewrite <- app_assoc.
            reflexivity.
  - intros u' D2 D1' D2' HP1 HP2 HWFu H4.
    rewrite H0 in HP1.
    apply Permutation_rel_split2 in HP1.
    destruct HP1 as [[l1' [HP'1 HP'2]] | [l2' [HP'1 HP'2]]].
    + eapply pf_perm_rel.
      ++ auto.
      ++ reflexivity.
      ++ assert (D1' ++ D2' ≡[P] (l1' ++ D2') ++ [t ⊗ u]).
         {
           convertTactics.convert_multisetperm. permutation_solver.
         }
         rewrite H1.
         reflexivity.
      ++ eapply pf_tensor.
         2: {
           reflexivity.
         }
         eapply pf_perm_rel.
         auto.
         reflexivity.
         assert ((l1' ++ D2') ++ [t] ++ [u] ≡[P] (l1' ++ [t] ++ [u]) ++ D2').
         {
           convertTactics.convert_multisetperm. permutation_solver.
         }
         rewrite H1.
         reflexivity.
         eapply IHpf.
         2 : {
           apply HP2.
         }
         +++ 
           rewrite HP'1.
           convertTactics.convert_multisetperm. permutation_solver.
         +++ 
           assumption.
         +++ assumption.
    + 
      symmetry in HP'1. apply Permutation_rel_singleton_nil in HP'1 as (-> & HP'1).
      rewrite app_nil_r in HP'2.
      (* eapply pf_perm_rel. tauto. reflexivity. rewrite <- HP'2. reflexivity. *)
      (* subst. *)
      (* clear D1' HP'2 D H0. *)
      (* revert D2' D' t u HP2 HWFu H IHpf. *)
      (* {induction H4; intros. *)
      (*  - admit. *)
      (*  - admit. *)
      (*  - admit. *)
      (* } *)
      admit.
       
      
      (* eapply cut_admissibility_aux_tensor; eauto. *)
  - intros.
    rewrite H1, app_assoc in HP1. apply Permutation_rel_split_last in HP1.
    destruct HP1 as [[HP3 HP4] | [l1' [l2' [HP3 [HP4 HP5]]]]].
    + 
      rewrite <- HP3 in *. simpl in HP2.

      

    + apply Permutation_rel_split2 in HP3.
      destruct HP3 as [[l3' [HP'1 HP'2]] | [l4' [HP'1 HP'2]]].
      ++ eapply pf_par.
         3: {
           assert (D1' ++ D2' ≡[P] (l3' ++ D2') ++ D2 ++ [t_par t u]).
           {convertTactics.convert_multisetperm. permutation_solver. }
           eassumption.
         }
         +++
           eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap.
           eapply IHpf1.
           2: {apply HP2. }
           convertTactics.convert_multisetperm. permutation_solver.
           assumption. assumption.
         +++ 
           assumption.
      ++ eapply pf_par.
         3: {
           assert (D1' ++ D2' ≡[P] D1 ++ (l4' ++ D2') ++ [t_par t u]).
           {convertTactics.convert_multisetperm. permutation_solver. }
           eassumption.
         }
         +++
           assumption.
         +++ 
           eapply pf_perm_rel. tauto. reflexivity. apply Permutation_rel_assoc_swap.
           eapply IHpf2.
           2: {apply HP2. }
           convertTactics.convert_multisetperm. permutation_solver.
           assumption. assumption.
    admit.
  - intros.
    rewrite H0 in HP1.
    admit.
  - intros.
    symmetry in HP1.
    apply Permutation_rel_singleton in HP1.
    destruct D1'.
    2: { destruct D1'; discriminate. }
    simpl in HP1.
    injection HP1; intros HU.
    eapply IHpf.
    + eapply reflexivity.
    + eapply reflexivity.
    + rewrite HU in HWFu.
      inversion HWFu; auto.
    + rewrite HU in HP2.
      simpl dual in HP2.
      admit.
  - 
    (* eapply pf_one. *)

    (* rewrite H0 in HP1. *)
    (* assert ([[1]] ++ D' ≡[P] [u] ++ D1'). *)
    (* { *)
    (*   convertTactics.convert_multisetperm. permutation_solver. *)
    (* } *)
    (* apply Permutation_split_rel in H1. *)
    (* destruct H1. *)
    (* + destruct H1. *)
    (*   subst. *)
    (*   simpl dual in HP2. *)
    (*   inversion *)
    (* PInvert. *)
    (* eapply pf_one. *)
    admit.
Admitted.


Lemma cut_elimination :
  forall c G D,
    ⦃c ; G ; D ⊢ok⦄  ->
    ⦃c ; G ; D ⊢cf⦄.
Proof.
  intros c G D HG.
  induction HG; intros.
  - apply pf_id; auto.
  - eapply pf_absorb; eauto.
  - 
    pose proof cut_admissibility.
    eapply pf_perm_rel.
    + auto.
    + reflexivity.
    + symmetry. apply H1.
    + eapply cut_admissibility.
      ++ reflexivity.
      ++ reflexivity.
      ++ apply H0.
      ++ assumption.
      ++ assumption.
  - apply pf_bot; eauto.
  - eapply pf_one; eauto.
  - eapply pf_tensor; eauto.
  - eapply pf_par.
    + apply IHHG1.
    + apply IHHG2.
    + assumption.
  - eapply pf_bang; eauto.
  - eapply pf_ques; eauto.
  - eapply pf_forall; eauto.
  - eapply pf_exists; eauto.
Qed.
    
    
    



    
  (*   match goal with *)
  (*   | [ H : Permutation ([?x] ++ ?XS) ([?y] ++ ?YS) |- _] => *)
  (*       let EQ := fresh "EQ" in *)
  (*       let HP := fresh H in *)
  (*       let l1 := fresh  in *)
  (*       let l2 := fresh  in *)
  (*       let HI := fresh "H" in *)
  (*       let HJ := fresh "H" in *)
  (*       let HK := fresh "H" in *)
  (*       apply Permutation_split in H; *)
  (*       destruct H as [[EQ HP] | [l1 [l2 [[HI HJ] HK]]] ]; [rewrite EQ in *; clear EQ | ] *)
    
  (*   end. *)
  (*   2 : {  *)
  (*   apply Permutation_split in HP0; *)
  (*   destruct HP0 as [[EQ PX] | A]; [rewrite EQ in *; clear EQ | ]. *)
    
  (*   2 : { destruct HP1 as . *)

    
  (*   destruct HP1 as [HP1 _]. *)
  (*   assert (Permutation ([u] ++ [dual u]) ([t] ++ D1')) as X by *)
  (*   (eapply perm_comp; [apply HP1 | apply Permutation_exchange]). *)
  (*          by eapply perm_comp; [apply HP1 | apply Permutation_exchange]. *)
      
    
    
  (*   PInvert. *)
  (*   destruct D1'. simpl in HP1. *)
  (*   + PInvert. *)
  (*     destruct HP1 as [HP1 _]. *)
  (*     apply Permutation_length in HP1. inversion HP1. *)
  (*   + destruct D1'. *)
  (*     2 : { destruct HP1 as [HP1 _].  apply Permutation_length in HP1. inversion HP1. *)
  (*           destruct D1'; inversion H3. } *)
  (*     apply Permutation_rel_doubleton in HP1. *)
  (*     destruct HP1. *)
  (*     * inversion H2; clear H2. subst. rewrite dual_involutive in HP2. *)
  (*       induction I. *)
  (*       -- destruct D2'. *)
  (*          ++ destruct HP2 as [HP2 _]. *)
              
  
  
  
  (* revert c. *)
  (* induction u; intros c G D1 D2 HWF HP1 HP2. *)
  (* - simpl dual in HP2. *)
  (*   t_base_inversion: *)
  (*     c ; G ; D ++ [t_base p b] ⊢cf *)
  (*     D = [dual (t_base p b)]           *)


Lemma t_base_inversion_perm:
  forall c G D D' p n
    (HWF: c ; G ; D ⊢cf)
    (HD: D ≡ D' ++ [t_base p (b_other n)]),
    (exists  D',  D ≡ D' ++ [t_base (negb p) (b_other n)])
    \/
    In (t_base (negb p) (b_other n)) G.
Proof.
  intros c G D D' p n HWF.
  revert D' p n.
  induction HWF; intros.
  - destruct HD as [HD _].
    apply Permutation_symmetric in HD.
    apply Permutation_doubleton in HD.
    destruct HD as [HD | HD].
    + destruct D'; inversion HD; subst.
      destruct D'; inversion HD.
      2 : { destruct D'; inversion H5. }
      symmetry in H3. apply dual_base_inversion in H3.
      subst. simpl.
      left. exists [(t_base p (b_other n))]. eexists; auto. apply perm_swap.
    + destruct D'; inversion HD; subst.
      destruct D'; inversion HD.
      2 : { destruct D'; inversion H5. }
      subst. simpl.
      left. exists [t_base p (b_other n)]. eexists; auto. apply perm_id.
  - destruct (typ_eq_dec t (t_base p (b_other n))).
    + subst.
      destruct (IHHWF D p n).
      * eexists; auto. apply perm_id.
      * destruct H1 as [D'' [HEQ _]].
        assert (Permutation ([t_base p (b_other n)] ++ D) ([t_base (negb p) (b_other n)] ++ D'')) as HDD.
        { eapply perm_comp. apply Permutation_exchange.
          eapply perm_comp. apply HEQ. apply Permutation_exchange. }
        apply Permutation_split in HDD.
        destruct HDD as [[EQ HDD] | [D1 [D2 [[HD1 HD2] HD3]]]].
        -- inversion EQ. destruct p; inversion H2.
        -- left. exists D1. eexists; auto. eapply perm_comp. apply HD1. eapply Permutation_exchange.
      * right. apply H1.
   + 
        
      


Lemma t_base_inversion1:
  forall c G p n  
    (HWF : c ; G ; [t_base p (b_other n)] ⊢cf),
    exists G', G ≡ G' ++ [t_base (negb p) (b_other n)].
Proof.
  intros.
  remember [t_base p (b_other n)] as D eqn:HD.
  revert p n HD.
  induction HWF; intros; inversion HD.
  - subst.
  - eapply IHHWF1. apply Hu.
  - admit.
  - 
 

Lemma t_base_inversion:
  forall c G D p n
    (HWF : c ; G ; D ++ [t_base p (b_other n)] ⊢cf),
    exists D', D ≡ D' ++ [t_base (negb p) (b_other n)] /\ discardable D'.
Proof.
  intros c G D. revert c G.
  induction D; intros.
  - simpl in HWF.
    inversion HWF; subst.
    + 
  


Lemma t_base_inversion_perm:
  forall c G D D' p n
    (HP: Permutation D D') 
    (HWF: c ; G ; D ++ [t_base p (b_other n)] ⊢cf),
    (exists  D1,  Permutation_rel D' (D1 ++ [t_base (negb p) (b_other n)]))
    \/
    In (t_base p (b_other n)) G
.
Proof.
  intros.
  remember (D ++ [t_base p (b_other n)]) as DD.
  revert p n D D' HP HeqDD.
  induction HWF; intros; subst; try inversion HeqDD.
  - destruct D.
    + simpl in HeqDD. inversion HeqDD.
    + destruct (ListDec.In_dec typ_eq_dec (t_base p (b_other n)) G).
      * right. assumption.
      * 
      * left. split. assumption.
      simpl in HeqDD. inversion HeqDD.
      subst.
      destruct D.
      -- inversion  H5. 
        apply Permutation_symmetric in HP. apply Permutation_singleton in HP.
        subst.
        exists []. simpl.
        assert (t = t_base (negb p) (b_other n)).
        { rewrite <- (dual_involutive t). rewrite H4. simpl. reflexivity. }
        rewrite H2. exists (perm_id _). auto.
      -- inversion H5. destruct D. inversion H6. inversion H6.
  - assert (Permutation ([t] ++ D0) ([t] ++ D')) as HP2.
    { eapply perm_plus. apply perm_id. apply HP. }
    specialize (IHHWF p n ([t] ++ D0) ([t] ++ D') HP2 eq_refl).
    destruct IHHWF as [[HN [D1 [HQ _]]] | HIN].
    + 
    
    
  - admit.
  - replace [[⊥]] with ([] ++ [[⊥]]) in HeqDD by reflexivity.
    apply app_inj_tail_iff in HeqDD. intuition. inversion H2.
  - apply app_inj_tail_iff in HeqDD. intuition. inversion H1.
  - apply app_inj_tail_iff in HeqDD. intuition. inversion H1.
  - rewrite app_assoc in HeqDD. apply app_inj_tail_iff in HeqDD. intuition. inversion H1.
  - apply app_inj_tail_iff in HeqDD. intuition. inversion H1.
  - replace [[?] t] with ([] ++ [[?] t]) in HeqDD by reflexivity.
    apply app_inj_tail_iff in HeqDD. intuition. inversion H1.
  - apply app_inj_tail_iff in HeqDD. intuition. inversion H2.
  - apply app_inj_tail_iff in HeqDD. intuition. inversion H1.
  - 
  
Lemma t_base_inversion:
  forall c G D p n
    (HWF:c ; G ; D ++ [t_base p (b_other n)] ⊢cf),
    exists  D1,  Permutation_rel D (D1 ++ [t_base (negb p) (b_other n)]) .
Proof.
*)
    



    
          
    
    
      
