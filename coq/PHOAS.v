(*

    #
    |
 +o[^]o-o[]o+
 |          |
 +----------+
             

 +---------+
 |         |
 +o[]o-o[]o+

*)

From Coq Require Import List.
Open Scope list_scope.
Import ListNotations.

Section PHOAS.
  Variable (A:Prop).
  
(* Polymorphic Definition TM := *)
(*   forall (X:Prop) (var: A -> X) (app:X -> X -> X) (lam:(A -> X) -> X), X. *)


Polymorphic Definition TM :=
  forall (X:Type) (app:X -> X -> X) (lam:(X -> X) -> X), X.

Polymorphic Definition OTM :=
  forall (X:Type) (var : nat -> X) (app:X -> X -> X) (lam:(X -> X) -> X), X.

Definition inc (t:TM) : OTM :=
  fun X var app lam =>
    t X app lam.

Definition FV (X:Type) := (list nat).

Definition fv (t:OTM) : list nat :=
  t (list nat -> list nat)
    (fun n l => n::l)
    (fun t1 t2 l => t1 (t2 l))
    (fun f l => f (fun x => x) l) [].

Definition fv' (t:OTM) : list nat :=
  t (list nat)
    (fun n => [n])
    (fun t1 t2 => t1 ++ t2)
    (fun f => f []).

Definition example_OT : OTM :=
  fun X (var : nat -> X) (app : X -> X -> X) (lam : (X -> X) -> X) =>
    lam (fun v => app v (app (var 0) (var 1))).

Definition example_OT2 : OTM :=
  fun X (var : nat -> X) (app : X -> X -> X) (lam : (X -> X) -> X) =>
    lam (fun v => app (var 1) (app v (var 1))).

Eval compute in (fv' example_OT).
Eval compute in (fv example_OT2).

Polymorphic Definition ABS (n:nat) (t:OTM) : OTM :=
  fun X (var : nat -> X) (app : X -> X -> X) (lam : (X -> X) -> X) =>
    (lam (fun v =>
            (t X
               (fun x => if Nat.eqb n x then v else var x)
               (fun t1 t2 => app t1 t2)
               (fun f => lam f)
            )
    )).

Eval compute in (ABS 1 example_OT).
Eval compute in (ABS 1 example_OT2).

Fixpoint maxl (n:nat) (l:list nat) : nat :=
  match l with
  | [] => n
  | x::xs => if Nat.ltb n x then maxl x xs else maxl n xs
  end.

Fixpoint fresh (l:list nat) : nat :=
  match l with
  | [] => 0
  | x::xs => S(maxl x xs)
  end.

Polymorphic Definition OPEN (t:OTM) : OTM :=
  fun X var app lam =>
    let z := fresh (fv t) in
    t (bool -> X)
      (fun x _ => var x)
      (fun t1 t2 _ => app (t1 false) (t2 false))
      (fun f b =>
         if b then
           f (fun _ => var z) false
         else
           lam (fun x => f (fun _ => x) false))
      true.

Definition both (t:OTM) := (fresh (fv t), OPEN t).


Axiom REC : forall (t:TM)
    (X:Type)
    (app : X -> X -> X)
    (lam : (X -> X) -> X)
    (P : X -> Prop)
    (Happ: forall f g, P f -> P g -> P (app f g))
    (Hlam: forall b (H:forall a, P a -> P (b a)), P (lam b)),
    P (t X app lam).  


(*
Polymorphic Definition CASE (t:OTM) :
  forall (X:Type)
    (var : nat -> X)
    (app : OTM -> OTM -> X)
    (lam : nat -> OTM -> X) , X :=
  fun X var app lam =>
    fst (t 
         (fun n a o => (var n, o (fun X var app lam => var n)))
         (fun f g a o => f a (fun o1 =>
                             
            _)
            
         (fun b a o => _) OTM (fun o => o)).

Polymorphic Definition CASE (t:OTM) :
  forall (X:Type)
    (var : nat -> X)
    (app:OTM -> OTM -> X)
    lam, X :=
  fun X var app lam =>
    fst (t (X * OTM)%type
           (fun n => (var n, fun X var app lam => var n))
           (fun f g => (app (snd f) (snd g),
                      fun X var app lam =>
                        app (snd f X var app lam) (snd g X var app lam)))
           (fun b => 
              
           )
           ).
*)


Definition PAR_TM X := (list X -> X)%type.
Definition parallel_reduce (t:TM) : TM :=
  fun X (app : X -> X -> X) (lam : (X -> X) -> X) =>
       ( t (PAR_TM X)
          
          (fun (t1:PAR_TM X) (t2:PAR_TM X) (stack : list X) =>
             (t1 ((t2 [])::stack))
          )
      
          (fun (body : (PAR_TM X) -> (PAR_TM X)) (l : list X) =>
             match l with
             | [] => lam (fun (v:X) => body (fun stack => List.fold_left app stack v) [])
             | x::xs =>  body (fun stack => List.fold_left app stack x) xs
             end
          )
          []
       ).

Definition TRUE : TM :=
  fun X app lam => lam (fun x => lam (fun y => x)).

Definition FALSE : TM :=
  fun X app lam => lam (fun x => lam (fun y => y)).

Definition ID : TM :=
  fun X app lam => lam (fun y => y).

Definition W : TM :=
  fun X app lam => lam (fun y => app y y).

Definition U : TM :=
  fun X app lam => lam (fun y => app (app y y) y).

Definition OMEGA : TM :=
  fun X app lam => app (W X app lam) (W X app lam).

Definition Y : TM :=
  fun X app lam => lam (fun f => (app (lam (fun x => app f (app x x))) (lam (fun x => app f (app x x))))).

Definition Y_ID : TM :=
  fun X app lam => app (Y X app lam) (ID X app lam).

Definition APP (t u : TM) : TM :=
  fun X app lam => app (t X app lam) (u X app lam).

Definition example : TM :=
  APP (APP (APP (APP TRUE FALSE) TRUE) FALSE) TRUE.

Eval compute in (parallel_reduce example).

Eval compute in (parallel_reduce (parallel_reduce example)).

Definition ex2 : TM :=
  APP (APP (APP TRUE ID) W) U.

Eval compute in (parallel_reduce ex2).

Eval compute in (OPEN (inc TRUE)).
Eval compute in (OPEN (inc FALSE)).
Eval compute in (OPEN (inc OMEGA)).

Definition count (t:TM) : nat :=
  t nat (plus) (fun f => f 1).

Lemma count_example : (count example) = 5.
Proof.
  unfold count.
  unfold example.
  unfold APP, TRUE, FALSE.
  reflexivity.
Qed.

Inductive tm :=
| Var (x:nat)
| Abs (x:nat) (t:tm)
| App (t1 t2:tm).

Fixpoint tm_eq (t:tm) (u:tm) : bool :=
  match t with
  | Var x =>
      match u with
      | Var y => Nat.eqb x y
      | _ => false
      end
  | Abs x t' =>
      match u with
      | Abs y u' =>
          Nat.eqb x y && (tm_eq t' u')
      | _ => false
      end
  | App t1 t2 =>
      match u with
      | App u1 u2 => (tm_eq t1 u1) && (tm_eq t2 u2)
      | _ => false
      end
  end.

Definition name_ (t:TM) :=
    (t (nat -> (nat * tm))
       (fun t1 t2 n =>
          let '(n',t1') := t1 n in
          let '(n'',t2') := t2 n' in
          (n'', App t1' t2'))
       (fun f n =>
          let (n', t') := f (fun x => (x, Var n)) (S n) in
          (n', Abs n t'))
       ).

Definition name (t:TM) : tm :=
  snd (name_ t 0).

Eval compute in (name OMEGA).
Eval compute in (name FALSE).
Eval compute in (name TRUE).

Fixpoint lookup {X:Type} (l:list (nat * X)) n (default:X) : X :=
  match l with
  | [] => default
  | (m,x)::xs => if Nat.eqb m n then x else lookup xs n default
  end.

Definition phoas (t:tm) : TM :=
  fun X (app:X -> X -> X) (lam : (X -> X) -> X) =>
    let fix go (u:tm) env : X :=
      match u with
      | Var x => lookup env x (lam (fun w => w))
      | Abs n t => lam (fun x => go t ((n,x)::env))
      | App t1 t2 => app (go t1 env) (go t2 env)
      end
    in go t [].

Definition tm_TRUE := Abs 0 (Abs 1 (Var 0)).
Definition tm_FALSE := Abs 0 (Abs 1 (Var 1)).
Definition tm_APP := App tm_TRUE tm_FALSE.

Eval compute in (phoas tm_TRUE).
Eval compute in (phoas tm_FALSE).
Eval compute in (phoas tm_APP).

Definition TM_EQ (t:TM) (u:TM) : bool :=
  (tm_eq (name t) (name u)).

(*
Definition TM_EQ (t:TM) : TM -> bool :=
  t (TM -> bool)
    (fun t1 t2 u =>
       u _
         (_)
         (_)

       _)
    (_).




    
  
  Context (P:TM -> Prop) (app:TM -> TM -> TM) (lam : (TM -> TM) -> TM)
                         (HApp: forall x y, P x -> P y -> P (app x y))
                         (HLam: forall (f:TM -> TM), (forall y, P y -> P (f y)) -> P (lam f)).

  Lemma ind : forall (t:TM), P t.
  Proof.
    intros t.
*)    

  

Definition PN := fun (t:TM) (n:nat) => ~ exists (n':nat), exists (x:nat), name_ t n = (n', Var x).

Lemma name_t_neq_var : forall (t:TM) (n:nat), PN t n.
Proof.
  intros.
  unfold PN.
  unfold name_.
Abort.
  
Lemma phoas_name : forall (t:TM), TM_EQ t (phoas (name t)) = true.
Proof.

  intros t.
  unfold TM_EQ. 
  remember (name t) as u.
  revert t Hequ.
  induction u; intros.
  - simpl. unfold name in Hequ. unfold TM in *.
Abort.  

End PHOAS.
