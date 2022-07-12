(* The basic structure of types are that they define "open" graphs: the graphs
   have (typed) nodes, some of which are exposed via the interface to the graph.

GType poly_id_type :=
  { 
    T : given 
    x : T^    
    y : T
  | x-y                     ;;; ??? can we have a well-formed type without this constraint?  
                            ;;; ANS: yes, but it's void?  (Affine vs. linear?)
  }


Graph poly_id : poly_id_type :=
  { 
    _.T => a                      ;;; the identifiers T and x mentioned here are "bound" in the type annotation
    _.x : a <-> _.y : a^          ;;; the edge port => type_var binds a type variable 
  }


GType nat :=
  { 
    T : given 
    x : T^   
    y : T    
    f : !^ { 
             x : T^ 
             y : T
             | x-y  ;;; ??? what are the constraints on f's type? 
           }    
  | 
    T-x-y-f
  }

Graph two : nat :=
  {|
    _.T => a
    _.f -> f1        ;;; ??? maybe replace all of these by _.f -> n  where (n ∈ nat) ???
    _.f -> f2  
    _.x <-> f1.x
    f1.y <-> f2.x
    _.y  <-> f2.y
  |}



  port =>  type_var 
  port <=  [closure]type
  port ->  port_id
  port <-  [closure]term
  port <-> port


Parameter atom : Set.     (* names that can be alpha varied / bound *)
Definition port := atom * bool.     

GType 
  g := { 
         givens : fset atom        (* foralls *)
         takens : fset atom        (* exists  *)
                : fmap atom GType  (* !^ *)
         output  : 
         ports  :  fmap atom port 
         
       }

*)

From Coq Require Import
     List
     Classes.RelationClasses
     Arith.Arith
     Lia
     .
From Equations Require Import
     Equations.
     
Import Relation_Definitions.

Definition port := (nat * bool)%type.

Inductive gtype :=
  mk_gtype {
      given  : nat            (* [[∀]] binders  *)
    ; taken  : nat            (* [[∃]] binders *)
    ; gnabs  : list gtype   (* !^ replicable inputs - binders with nested scopes *)
    ; bangs  : list gtype   (* !  reusable outputs  - binders with nested scopes *)
    ; ports  : list port    (* linear nodes - binders whose rhs are in scope *) 
    ; flows  : nat -> nat -> bool   (* could be in Prop, but this is more computational *)
    }.

Definition num_fields (g:gtype) : nat :=
  (given g) + (taken g) + (length (gnabs g)) + (length (bangs g)) + (length (ports g)).


Section Induction.
  Variable P : gtype -> Prop.
  Hypothesis IH_CHILDREN : forall (g:gtype),
      (forall h, List.In h (gnabs g) -> P h) -> (forall h, List.In h (bangs g) -> P h) -> P g.

  Lemma gtype_ind_strong : forall (g:gtype), P g.
  Proof.
    fix IH 1.
    destruct g.
    apply IH_CHILDREN.
    - revert gnabs0.
       { fix IHELT 1. intros [|u children'].
        - intros. inversion H.
        - intros u' [<-|Hin].
          * apply IH.
          * eapply IHELT. apply Hin.
       }
    - revert bangs0.
       { fix IHELT 1. intros [|u children'].
        - intros. inversion H.
        - intros u' [<-|Hin].
          * apply IH.
          * eapply IHELT. apply Hin.
       }
  Qed.
End Induction.

(*
wf_gtype c g means that g is well-formed with c type variables in scope.
 *)

Definition wf_port (c:nat) (p : port) : Prop :=
  let '(pn, _) := p in 
  pn < c.


Definition rel {A:Type} (R : A -> A -> bool) : relation A :=
  fun (a b:A) => R a b = true.

Definition Scoped (c:nat) (R : relation nat) : Prop :=
  forall (x y : nat), R x y -> x < c /\ y < c.

Definition wf_flow (c:nat) (C : nat -> nat -> bool) : Prop :=
  (Symmetric (rel C)) /\ (Irreflexive (rel C)) /\ (Scoped c (rel C)).
  

Inductive wf_gtype : nat -> gtype -> Prop :=
| WF_gtype :
  forall (c : nat)
    (a e : nat)
    (rs bs : list gtype)
    (ps : list port)
    (C : nat -> nat -> bool) 
    (HRS : forall n g, List.nth_error rs n = Some g -> wf_gtype (c + a + e) g)
    (HBS : forall n g, List.nth_error bs n = Some g -> wf_gtype (c + a + e) g)
    (HPS : forall n p, List.nth_error ps n = Some p -> wf_port (c + a + e) p)
    (HC: wf_flow (a + e + (List.length rs) + (List.length bs) + (List.length ps)) C),
    wf_gtype c (mk_gtype a e rs bs ps C).

Import ListNotations.

Definition zero : gtype :=
  mk_gtype 0 0 [] [] [] (fun x y => false).

Lemma wf_zero : forall c, wf_gtype c zero.
Proof.
  intros c.
  apply WF_gtype; intros.
  - destruct n; inversion H.
  - destruct n; inversion H.
  - destruct n; inversion H.
  - simpl. unfold wf_flow. unfold rel.
    repeat split.
    + repeat intro. inversion H.
    + repeat intro. inversion H.
    + repeat intro. inversion H.
    + repeat intro. inversion H.
Qed.      
