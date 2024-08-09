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

Notation "[1]" := (t_base true b_unit).   (* Unit for [⊗] *)
Notation "[⊥]" := (t_base false b_unit).  (* Unit for [∥] *)

Notation "'B' n" := (t_base true (b_other n)) (at level 20).
Notation "'B⟂' n" := (t_base false (b_other n)) (at level 20).
Infix "⊗" := t_tensor (at level 80).
Infix "∥" := t_par (at level 90).
Notation "[!] t" := (t_bang t) (at level 30).
Notation "[?] t" := (t_ques t) (at level 30).
Notation "[forall] t" := (t_forall t) (at level 30).
Notation "[exists] t" := (t_exists t) (at level 30).

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

Definition P : list typ -> list typ -> Type := OrderPerm.

Lemma wf_ctx_Permutation :
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

Lemma shift_ctx_app :
  forall b c G1 G2,
    shift_ctx c b (G1 ++ G2) = (shift_ctx c b G1) ++ (shift_ctx c b G2).
Proof.
  intros b c G1 G2.
  unfold shift_ctx.
  rewrite map_app.
  reflexivity.
Qed.

Lemma Permutation_shift_ctx :
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

Section PF.

  Context (PID : typ -> Prop).
  Context (PCUT : typ -> Prop).

Reserved Notation "c ; G ; D '⊢ok'" (at level 101, D at level 100, G at level 100).

Inductive pf : nat -> ctx -> ctx -> Prop :=
| pf_id : forall c G (u:typ),
    PID u ->
    c ⊢ u wf ->
    wf_ctx c G ->
    c ; G ; [u] ++ [dual u] ⊢ok

(* absorbtion *)                
| pf_absorb : forall c G G' t D,
    wf_ctx c (G ++ [t]) ->
    G' ≡[P] (G ++ [t]) ->
    c ; G' ; D ++ [t] ⊢ok ->
    c ; G' ; D ⊢ok       
                
| pf_cut : forall c G D1 D2 D u,
    PCUT u ->
    c ⊢ u wf ->
    c ; G ; D1 ++ [u] ⊢ok ->
    c ; G ; D2 ++ [dual u] ⊢ok ->
    D ≡[P] (D1 ++ D2) ->                    
    c ; G ; D ⊢ok         
                
| pf_bot : forall c G,
    wf_ctx c G ->    
    c ; G ; [ [⊥] ] ⊢ok

| pf_one : forall c G D D',
    c ; G ; D' ⊢ok ->
    D ≡[P] (D' ++ [ [1] ]) ->        
    c ; G ; D ⊢ok
                                 
| pf_tensor : forall c G D D' t u,
    c ; G ; D' ++ [t] ++ [u] ⊢ok ->
    D ≡[P] (D' ++ [ t ⊗ u ]) ->
    c ; G ; D ⊢ok

| pf_par : forall c G D1 D2 D t u,
    c ; G ; D1 ++ [t] ⊢ok ->
    c ; G ; D2 ++ [u] ⊢ok ->
    D ≡[P] (D1 ++ D2 ++ [ t ∥ u ]) ->
    c ; G ; D ⊢ok

| pf_bang : forall c G D1 D t,
    c ; G ++ [t] ; D1 ⊢ok ->
    D ≡[P] D1 ++ [ [!]t ] ->               
    c ; G ; D ⊢ok

| pf_ques : forall c G t,
    c ; G ; [t] ⊢ok ->
    c ; G ; [ [?]t ] ⊢ok

| pf_forall : forall c G D1 D u t,
   c ⊢ u wf ->
   c ; G ; D1 ++ [typ_subst c u t] ⊢ok ->
   D ≡[P] D1 ++ [ [forall] t ] ->
   c ; G ; D  ⊢ok           

| pf_exists : forall c G D1 D u,
   (1 + c) ; (shift_ctx c 1 G) ; (shift_ctx c 1 D1) ++ [u] ⊢ok ->
   D ≡[P] D1 ++ [ [exists] u ] ->
   c ; G ; D ⊢ok 

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
  "c ; G ; D '⊢ok'" := (pf c G D).


Context (PID_dual : forall u, PID u <-> PID (dual u)).


Arguments Permutation_doubleton {_ _ _ _ _ _}.
Arguments Permutation_append {_ _ _ _ _ _}.
Arguments Permutation_singleton {_ _ _ _ _ _}.
Arguments Permutation_destruct1 {_ _ _ _ _ _}.
Arguments Permutation_exchange {_ _ _ _ _ _}.

Import convertTactics.
Import ConvertibleTactics.
#[global]
 Instance PermConvertible_P : PermConvertible typ P.
Proof.
  apply PermConvertible_OrderPerm.
Qed.

Lemma pf_perm : forall c G1 G2 D1 D2
    (HPG: P G1 G2) 
    (HPD: P D1 D2)
    (HWF: c ; G1 ; D1 ⊢ok),
    c ; G2 ; D2 ⊢ok.
  Proof.
    intros. revert G2 D2 HPG HPD.
    induction HWF; intros.
    - apply Permutation_symmetric in HPD.
      apply Permutation_doubleton in HPD.
      destruct HPD; subst.
      + apply pf_id; auto. eapply wf_ctx_Permutation; eauto.
      + rewrite <- (dual_involutive u) at 2.
        apply pf_id. rewrite <- PID_dual. assumption.
        apply wf_typ_dual. assumption. eapply wf_ctx_Permutation; eauto.
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
      apply pf_bot. eapply wf_ctx_Permutation. apply HPG; auto. assumption.
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
        apply Permutation_symmetric in H; apply (wf_ctx_Permutation _ _ _ H); clear H
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

End PF.

Definition atomic (t:typ) : Prop :=
  match t with
  | t_base p (b_other n) => True
  | t_var p x => True
  | _ => False
  end.

Lemma atomic_dual : forall u : typ, atomic u <-> atomic (dual u).
Proof.
  intros u.
  split; intros.
  - destruct u; try contradiction; auto.
  - destruct u; try contradiction; auto.
Qed.

Check pf_exchange.
Definition pf_exchange' {PCUT} := @pf_exchange _ PCUT atomic_dual.

Definition any : typ -> Prop := fun t => True.
Definition no_cut : typ -> Prop := fun t => False.

Lemma any_dual : forall u : typ, any u <-> any (dual u).
Proof.
  intros u. unfold any. tauto.
Qed.

#[local] Hint Resolve any_dual : core.

Notation "c ; G ; D '⊢ok'" := (pf any any c G D) (at level 101, D at level 0, G at level 0).
Notation "c ; G ; D '⊢prim'" := (pf atomic any c G D) (at level 101, D at level 0, G at level 0).
Notation "c ; G ; D '⊢cf'" := (pf any no_cut c G D) (at level 101, D at level 0, G at level 0).
Notation "c ; G ; D '⊢norm'" := (pf atomic no_cut c G D) (at level 101, D at level 0, G at level 0).


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
    (HOK : c ; G ; D ⊢ok),
    c ; G ; D ⊢prim.
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

Arguments Permutation_nil_inv {_ _ _ _ _ _}.
Arguments Permutation_singleton_inv {_ _ _ _ _ _}.
Arguments Permutation_split {_ _ _ _ _ _}.
Arguments Permutation_exchange {_ _ _ _ _ _}.
Arguments Permutation_destruct1 {_ _ _ _ _ _}.
Arguments Permutation_singleton {_ _ _ _ _ _}.
Arguments Permutation_rel_split {_ _ _ _ _ _}.
Arguments Permutation_remove_rel_rr {_ _ _ _ _ _}.

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

Lemma pf_cf_unit_inv :
  forall c G D D'
    (HP: D' ≡[P] (D ++ [[1]])) 
    (H: c ; G ; D' ⊢cf) ,
    c ; G ; D ⊢cf.
Proof.
  intros c G D D' HP H.
  revert D HP.
  induction H; intros D'' HP.
  - PInvert.
    simpl. auto. subst.
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
    apply Permutation_rel_split in HP.
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
     apply Permutation_remove_rel_rr in HP.
     destruct HP as [HP _].     
     eapply pf_perm.
     apply any_dual.
     apply Permutation_reflexive.
     apply HP.
     apply H.
   - rewrite H0 in HP.
     apply Permutation_rel_split in HP.
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
   - rewrite H1 in HP.
     apply Permutation_rel_split in HP.
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
     + apply Permutation_rel_split in EQ1.
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
     apply Permutation_rel_split in HP.
     destruct HP as [[D1' [EQ1 EQ2]] | [D2' [EQ1 EQ2]]].
     + apply IHpf in EQ1.
       eapply pf_bang.
       apply EQ1.
       rewrite EQ2. reflexivity.
     + PInvert. LInvert. inversion H0.
   - PInvert. LInvert. inversion H0.
   - rewrite H1 in HP.
     apply Permutation_rel_split in HP.     
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
     apply Permutation_rel_split in HP.     
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

(*
Lemma cut_elimination :
  forall c G D,
    c ; G ; D |-ok ->
    c ; G ; D |-cf.               
TODO: use the following cut_admissibility as a lemma
 *)

Arguments Permutation_nil_inv {_ _ _ _ _ _}.
Arguments Permutation_singleton_inv {_ _ _ _ _ _}.
Arguments Permutation_split {_ _ _ _ _ _}.
Arguments Permutation_exchange {_ _ _ _ _ _}.
Arguments Permutation_destruct1 {_ _ _ _ _ _}.
Arguments Permutation_singleton {_ _ _ _ _ _}.
Arguments Permutation_rel_split {_ _ _ _ _ _}.
Arguments Permutation_remove_rel_rr {_ _ _ _ _ _}.
Arguments Permutation_doubleton {_ _ _ _ _ _}.
Arguments Permutation_append {_ _ _ _ _ _}.
Arguments Permutation_split_rel {_ _ _ _ _ _}.
Arguments Permutation_rel_exchange {_ _ _ _ _ _}.
Arguments Permutation_rel_singleton {_ _ _ _ _ _}.
    
Lemma norm_cut_admissibility :
  forall c u G D1 D2 D1' D2',
    D1 ≡ D1' ++ [u] ->
    D2 ≡ D2' ++ [dual u] ->
    c ⊢ u wf ->
    c ; G ; D1 ⊢norm ->
    c ; G ; D2 ⊢norm ->
    c ; G ; D1' ++ D2' ⊢norm.
Proof.
Admitted.


Lemma prim_to_norm_elimination :
  forall c G D,
    c ; G ; D ⊢prim  ->
    c ; G ; D ⊢norm.
Proof.
Admitted.

Lemma cut_elimination :
  forall c G D,
    c ; G ; D ⊢ok  ->
    c ; G ; D ⊢norm.
Proof.
Admitted.

(*


-----------------
c; G; D ++ [[⊥]] ⊢
 *)

Lemma pf_ok_bot_inf : forall D D' G c (HP : D ≡[P] D' ++ [[⊥]]) (HL: c; G; D' ⊢ok),
    (c; G; D ⊢ok).
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
    




(* Should not use cut here.
   Maybe we need to use absorb
 *)
(* Lemma pf_G_weaken : forall D G G1 G2 c (HP : G ≡[P] G1 ++ G2) *)
(*                       (HL : c; G1; D ⊢ok), *)
(*     c; G; D ⊢ok. *)
(* Proof. *)
(*   intros. *)
(*   revert G2 G HP. *)
(*   induction HL. *)
(*   - intros. *)
(*     apply pf_id; auto. *)
    

(* Lemma pf_G_weaken : forall D G G1 G2 c (HT : wf_ctx c G2) (HP: G ≡[P] G1 ++ G2) (HL : c; G1; D ⊢cf), c; G; D ⊢cf. *)

(* Lemma pf_G_weaken : forall D G G' c t (HT : c ⊢ t wf) (HP: G ≡[P] G' ++ [t]) *)
(*                       (HL: c; G'; D ⊢ok), c; G; D ⊢ok. *)
(* Proof. *)
(*   intros. *)
(*   revert G t HT HP. *)
(*   induction HL. *)
(*   - intros. *)
(*     apply pf_id; auto. *)
(*     normalize_auxH. *)
(*     assert (P ([t] ++ G) G0). *)
(*     { *)
(*     convertTactics.convert_multiset. permutation_solver. *)
(*     } *)
(*     eapply wf_ctx_Permutation; eauto. *)
(*     apply wf_ctx_app; intuition. *)
(*     unfold wf_ctx. *)
(*     intros. *)
(*     destruct H2; try destruct H2. *)
(*     intuition. *)
(*   -  *)
    
(*     (* TODO: Simplify this to one lemma *) *)
(*     apply Perm_OrderPerm_surj in X. *)
(*     inversion X; subst. *)
    
(*     apply ICPerm_inv_TIn_cons_l in X. *)
(*     apply TIn_app_exists_inj in X. *)
(*     destruct X as (l1 & l2 & X). *)

(*     Search Permutation_rel. *)
(*   -  *)
  

(* Lemma pf_ok_bot_inv : forall D D' c G, D ≡[P] D' ++ [[⊥]] -> c; G; D ⊢ok -> c; G; D' ⊢ok. *)
(* Proof. *)
(*   intros. *)
(*   unfold_destruct_relH H. *)
(*   eapply (pf_cut _ _ [] _ ); auto. *)


(* Lemma pf_cf_bot_inv : forall D D' c G, D ≡[P] D' ++ [[⊥]] -> c; G; D ⊢cf -> c; G; D' ⊢cf. *)
(* Proof. *)
(*   intros. *)
(*   unfold_destruct_relH H. *)
(*   eapply pf_absorb. *)
(*   3 : { eapply pf_perm; auto. *)
(*         apply Permutation_reflexive. *)
(*         apply H. *)
(*         auto. } *)

  
  


(* c : nat *)
(*   G : ctx *)
(*   D : list typ *)
(*   D' : ctx *)
(*   H : c; G; D' ⊢cf *)
(*   H0 : D ≡[ P] D' ++ [[1]] *)
(*   IHpf : ∀ (u : typ) (D2 D1' D2' : list typ), *)
(*            D' ≡[ P] D1' ++ [u] → D2 ≡[ P] D2' ++ [dual u] → c ⊢ u wf → (c; G; D2 ⊢cf) → c; G; (D1' ++ D2') ⊢cf *)
(*   D2, D1', D2' : list typ *)
(*   HWFu : c ⊢ [1] wf *)
(*   HP2 : D2 ≡[ P] D2' ++ [[⊥]] *)
(*   HP1 : D' ++ [[1]] ≡[ P] D1' ++ [[1]] *)
(*   H4 : c; G; D2 ⊢cf *)
(*   H2 : D' ≡[ P] D1' *)
(*   ============================ *)
(*   c; G; (D1' ++ D2') ⊢cf *)

Lemma Permutation_mid_cons_inj : forall l11 l12 l21 l22 a, P (l11 ++ l12) (l21 ++ l22) -> P (l11 ++ a :: l12) (l21 ++ a :: l22).
Proof.
  intros.
  convertTactics.convert_mid.
  apply midperm_cons; auto.
Qed.

Lemma Permutation_mid_cons_surj : forall l11 l12 l21 l22 a, P (l11 ++ a :: l12) (l21 ++ a :: l22) -> P (l11 ++ l12) (l21 ++ l22).
Proof.
  intros.
  assert (P (a :: l11 ++ l12) (l21 ++ a :: l22)).
  {
    convertTactics.convert_multiset. permutation_solver.
  }
  apply Perm_ICPerm_inj in X0.
  apply ICPerm_app_cons_inv in X0.
  convertTactics.convert_ic; auto.
Qed.

Lemma Permutation_rel_mid_cons_iff : forall l11 l12 l21 l22 a, (l11 ++ l12) ≡[P] (l21 ++ l22) <-> (l11 ++ a :: l12) ≡[P] (l21 ++ a :: l22).
Proof.
  intros; split; intros; normalize_auxH; eexists; auto.
  - apply Permutation_mid_cons_inj; auto.
  - eapply Permutation_mid_cons_surj; eauto.
Qed.

Inductive vacuous : typ -> Prop :=
| vacuous_one : vacuous [1]
| vacuous_tensor: forall t1 t2, vacuous t1 -> vacuous t2 -> vacuous (t1 ⊗ t2)
| vacuous_par : forall t1 t2, vacuous t1 -> vacuous t2 -> vacuous (t1 ∥ t2)
| vacuous_bang: forall t, vacuous t -> vacuous ([!]t)
| vacuous_ques : forall t, vacuous t -> vacuous ([?]t)
.

Definition vacuous_ephem (D : ctx) :=
  forall t, In t D -> vacuous t.

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

Lemma pf_weakening : forall PID PCUT D G G1 G2 c, G ≡[P] G1 ++ G2 -> wf_ctx c G2 -> pf PID PCUT c G1 D -> pf PID PCUT c G D.
Proof.
  intros PID PCUT D G G1 G2 c HG HW HP.
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

Lemma pf_cf_bang_inv : forall D D' G c t, D ≡[P] D' ++ [[!] t] -> c; G; D ⊢cf -> c; G; D' ⊢cf.
Proof.
  Print pf.

  (* c : nat *)
  (* G : ctx *)
  (* t : typ *)
  (* H : c; G; [t] ⊢cf *)
  (* IHpf : ∀ (u : typ) (D2 D1' D2' : list typ), *)
  (*          [t] ≡[ P] D1' ++ [u] *)
  (*          → D2 ≡[ P] D2' ++ [dual u] *)
  (*            → c ⊢ u wf → (c; G; D2 ⊢cf) → c; G; (D1' ++ D2') ⊢cf *)
  (* u : typ *)
  (* D2, D2' : list typ *)
  (* HP1 : [u] = [[?] t] *)
  (* HP2 : D2 ≡[ P] D2' ++ [[!] dual t] *)
  (* HWFu : c ⊢ u wf *)
  (* H0 : c; G; D2 ⊢cf *)
  (* HU : u = [?] t *)
  (* ============================ *)
  (* c; G; (D2' ++ [dual t]) ⊢cf *)
   
Lemma cut_admissibilityy :
  forall c u G D1 D2 D1' D2',
    D1 ≡[P] D1' ++ [u] ->
    D2 ≡[P] D2' ++ [dual u] ->
    c ⊢ u wf ->
    c ; G ; D1 ⊢cf ->
    c ; G ; D2 ⊢cf ->
    c ; G ; D1' ++ D2' ⊢cf.
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
    assert (c; G'; ((D1' ++ [t]) ++ D2') ⊢cf).
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
    assert (c ; G; (D2' ++ [[1]]) ⊢cf).
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
    + destruct p as (HPP1 & HPP2).
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
    admit.
  - intros.
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



    

      (* unfold_destruct_relH HP3. apply Perm_ICPerm_inj in HP3. *)
      (* apply ICPerm_app_cons_inv in HP3. *)
      (* apply (@Perm_ICPerm_surj _ _ _ P PermRel_OrderPerm PermConvertible_P) in HP3. *)
      (* assert (HP4 : D' ≡[P] (l3 ++ l4) ++ [u]). *)
      (* { rewrite app_assoc in HP3. eexists; auto. } *)



      (* Search MidPerm. *)
      (* Search Permutation. *)
      (* Search TIn. *)
      (* Search ICPerm. *)


    (*
     : ∀ (A : Type) (EqDecision0 : EqDecision A) (H : Countable A) (P : list A → list A → Type) 
         (H0 : PermRel P),
         PermConvertible A P
         → ∀ (a1 a2 : A) (l1 l2 : list A),
             P ([a1] ++ l1) ([a2] ++ l2)
             → (a1 = a2) * P l1 l2 +
               {l1' : list A &
               {l2' : list A & (P l1 ([a2] ++ l1') * P l2 ([a1] ++ l2') * P l1' l2')%type}}

Arguments Permutation_split {A}%type_scope {EqDecision0 H} {P}%function_scope 
     *)
    destruct decide_rel
    admit.
  - 
    eapply pf_one.

    rewrite H0 in HP1.
    assert ([[1]] ++ D' ≡[P] [u] ++ D1').
    {
      convertTactics.convert_multisetperm. permutation_solver.
    }
    apply Permutation_split_rel in H1.
    destruct H1.
    + destruct H1.
      subst.
      simpl dual in HP2.
      inversion
    PInvert.
    eapply pf_one.

    
    
    
    



    
    match goal with
    | [ H : Permutation ([?x] ++ ?XS) ([?y] ++ ?YS) |- _] =>
        let EQ := fresh "EQ" in
        let HP := fresh H in
        let l1 := fresh  in
        let l2 := fresh  in
        let HI := fresh "H" in
        let HJ := fresh "H" in
        let HK := fresh "H" in
        apply Permutation_split in H;
        destruct H as [[EQ HP] | [l1 [l2 [[HI HJ] HK]]] ]; [rewrite EQ in *; clear EQ | ]
    
    end.
    2 : { 
    apply Permutation_split in HP0;
    destruct HP0 as [[EQ PX] | A]; [rewrite EQ in *; clear EQ | ].
    
    2 : { destruct HP1 as .

    
    destruct HP1 as [HP1 _].
    assert (Permutation ([u] ++ [dual u]) ([t] ++ D1')) as X by
    (eapply perm_comp; [apply HP1 | apply Permutation_exchange]).
           by eapply perm_comp; [apply HP1 | apply Permutation_exchange].
      
    
    
    PInvert.
    destruct D1'. simpl in HP1.
    + PInvert.
      destruct HP1 as [HP1 _].
      apply Permutation_length in HP1. inversion HP1.
    + destruct D1'.
      2 : { destruct HP1 as [HP1 _].  apply Permutation_length in HP1. inversion HP1.
            destruct D1'; inversion H3. }
      apply Permutation_rel_doubleton in HP1.
      destruct HP1.
      * inversion H2; clear H2. subst. rewrite dual_involutive in HP2.
        induction I.
        -- destruct D2'.
           ++ destruct HP2 as [HP2 _].
              
  
  
  
  revert c.
  induction u; intros c G D1 D2 HWF HP1 HP2.
  - simpl dual in HP2.
    t_base_inversion:
      c ; G ; D ++ [t_base p b] ⊢cf
      D = [dual (t_base p b)]          


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
    



    
          
    
    
      
