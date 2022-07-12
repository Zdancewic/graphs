From Coq Require Import List.
Import ListNotations.


Definition atom := nat.
Definition cstr := (atom * atom)%type.

Infix "==" := Nat.eqb (at level 20).

Infix "≺" := (pair) (at level 20).

Definition system := list cstr.

Definition In (a:atom) (s:system) :=
  exists b, (List.In (a ≺ b) s) \/ (List.In (b ≺ a) s).

Inductive closure (s : system) : atom -> atom -> Prop :=
| clo_base : forall a b, List.In (a ≺ b) s -> closure s a b
| clo_trans : forall a b c, List.In (a ≺ b) s -> closure s b c -> closure s a c.

Definition inconsistent (s : system) :=
  exists a, closure s a a.

Definition consistent (s : system) :=
  forall (a:atom), ~ closure s a a.

Definition contains l x : bool :=
  List.existsb (Nat.eqb x) l.

Fixpoint before (l:list atom) (a b : atom) : bool :=
  match l with
  | [] => false
  | x::xs => if x == a then contains xs b else
             before xs a b
  end.

Fixpoint system_of (l:list atom) : system :=
  match l with
  | [] => []
  | [x] => []
  | x::xs => let s' := system_of xs in
           match xs with
           | [] => []
           | y::ys => (x ≺ y)::s'
           end
  end.

Example system1 := [0 ≺ 1 ; 1 ≺ 2 ; 1 ≺ 3 ; 2 ≺ 4 ; 1 ≺ 4].
Example system2 := system1 ++ [5 ≺ 2; 4 ≺ 5; 6 ≺ 3].                                              
Example system3 := system1 ++ [6 ≺ 3 ].

(* generates a list containing the union of l and acc (assuming acc is unique) *)
Fixpoint merge l acc : list atom :=
  match l with
  | [] => acc
  | x::xs => if contains acc x then merge xs acc else merge xs (x::acc)
  end.

Definition roots (s : system) : list atom :=
  let (ps, ss) := List.split s in
  let nodes := List.filter (fun a => negb (contains ss a)) ps in
  merge nodes [].


Definition edges_from (a:atom) (s:system) :=
  List.filter (fun '(x,_) => x == a) s.

Definition successors (s:system) a :=
  List.map snd (edges_from a s).

Example cycle := [(1 ≺ 2); (2 ≺ 3); (3 ≺ 1)].

Definition delete_root '(edges, s) (root:atom) :=
  let s' := List.filter (fun '(x,_) => negb (x == root)) s in
  ((root, successors s root)::edges, s').

Definition partition (s : system) (roots : list atom) :=
  List.fold_left delete_root roots ([], s).

Fixpoint insert_node_h (a:atom) (succs:list atom) (order:list atom) : option (list atom) :=
  let xs := merge succs order in 
  if contains xs a then None else Some (a::xs).
  
Definition insert_node order '(a, succs) : option (list atom) :=
  match order with
  | None => None
  | Some order =>
      insert_node_h a succs order 
  end.


Fixpoint toposort_h (fuel:nat) (s:system) : option (list atom) :=
  match fuel with
  | 0 => None
  | S fuel =>
      match s with
      | [] => Some []  (* The empty system has only the empty solution *)
      | _ =>
          let roots := roots s in
          match roots with
          | [] => None (* nonempty system with no roots must contain a cycle (x ≺ y) (y ≺ z) (z ≺ x) *)
          | _ =>
              let '(edge_groups, s') := partition s roots in
              let order := toposort_h fuel s' in
              List.fold_left insert_node edge_groups order
          end
      end
  end.

Definition toposort (s:system) : option (list atom) :=
  toposort_h (200 * List.length s) s.

Example system11 := [1 ≺ 2; 1 ≺ 3; 2 ≺ 4; 1 ≺ 4].

Eval compute in (successors system1 1).
Eval compute in partition system3 [0;6].
Eval compute in (partition system11 [1]).

Print system1.
Eval compute in (toposort system1).
Eval compute in system2.
Eval compute in (toposort system2).
Eval compute in (toposort system3).

Example system4 := [1 ≺ 2; 2 ≺ 3].
Eval compute in roots system4.
Eval compute in (toposort system4).

Example system5 := [1 ≺ 2; 2 ≺ 3; 4 ≺ 1].
Eval compute in roots system5.
Eval compute in (toposort system5).          





                                                 
