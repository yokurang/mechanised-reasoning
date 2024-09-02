(* week-01_polymorphism.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 19 Aug 2023, uniformly declaring eqb_nat rather than using the alias beq_nat *)
(* was: *)
(* Version of 15 Aug 2023 *)

(* ********** *)

Require Import Arith Bool.

Inductive polymorphic_binary_tree (V : Type) : Type :=
| PLeaf : V -> polymorphic_binary_tree V
| PNode : polymorphic_binary_tree V -> polymorphic_binary_tree V -> polymorphic_binary_tree V.

(* ********** *)

(* Exercise 05 *)

(* Part a *)

Compute(PLeaf (nat * bool) (2, true)).

(*
 = PLeaf (nat * bool) (2, true)
 : polymorphic_binary_tree (nat * bool)
 *)

(* Part b *)

Compute(PLeaf(polymorphic_binary_tree nat) (PLeaf nat 2)).

(* = PLeaf (polymorphic_binary_tree nat) (PLeaf nat 2)
   : polymorphic_binary_tree (polymorphic_binary_tree nat)
 *)

(* ********** *)

(* Exercise 06 *)

(* Part a *)

Fixpoint eqb_polymorphic_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : polymorphic_binary_tree V) : bool :=
  match t1 with
  | PLeaf _ v1 =>
    match t2 with
    | PLeaf _ v2 =>
      eqb_V v1 v2
    | PNode _ t11 t12 =>
      false
    end
  | PNode _ t11 t12 =>
    match t2 with
    | PLeaf _ v2 =>
      false
    | PNode _ t21 t22 =>
      eqb_polymorphic_binary_tree V eqb_V t11 t21
      &&
      eqb_polymorphic_binary_tree V eqb_V t12 t22
    end
  end.

Definition eqb_nat := Nat.eqb.

Definition eqb_bool := Bool.eqb.

Definition eqb_pair_nat_bool (p1 p2 : (nat * bool)) : bool :=
  match (p1, p2) with
  | ((n1, b1), (n2, b2)) => eqb_nat n1 n2 && eqb_bool b1 b2
  end.                                                 

(* Part b *)

Definition eqb_binary_tree_of_nats (t1 t2 : polymorphic_binary_tree nat) : bool :=
  eqb_polymorphic_binary_tree nat eqb_nat t1 t2.

Definition eqb_binary_tree_of_pair_nat_bool (t1 t2 : polymorphic_binary_tree (nat * bool))
  : bool :=
  eqb_polymorphic_binary_tree (nat * bool) eqb_pair_nat_bool t1 t2.

Definition eqb_binary_tree_of_binary_tree_of_nats (t1 t2 : polymorphic_binary_tree (polymorphic_binary_tree nat)) : bool :=
  eqb_polymorphic_binary_tree (polymorphic_binary_tree nat) eqb_binary_tree_of_nats t1 t2.

(* ********** *)
(* Exercise 07 *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
  | Some v1 =>
    match ov2 with
    | Some v2 =>
      eqb_V v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
    | Some v =>
      false
    | None =>
      true
    end
  end.

Check (eqb_polymorphic_binary_tree nat).
Check (eqb_polymorphic_binary_tree (option nat)).
Check (eqb_option (polymorphic_binary_tree nat)).

Definition eqb_binary_tree_of_optional_nats (t1 t2 : polymorphic_binary_tree (option nat)) : bool :=
  eqb_polymorphic_binary_tree (option nat) (eqb_option nat eqb_nat) t1 t2.


Definition eqb_optional_binary_tree_of_nats (t1 t2 : option (polymorphic_binary_tree nat)) : bool :=
  eqb_option (polymorphic_binary_tree nat) eqb_binary_tree_of_nats t1 t2.


Definition eqb_optional_binary_tree_of_optional_nats (t1 t2 : option (polymorphic_binary_tree (option nat))) : bool :=
  eqb_option (polymorphic_binary_tree (option nat)) eqb_binary_tree_of_optional_nats t1 t2.


Definition eqb_binary_tree_of_optional_binary_tree_of_nats (t1 t2 : polymorphic_binary_tree (option (polymorphic_binary_tree nat))) : bool :=
  eqb_polymorphic_binary_tree (option (polymorphic_binary_tree nat)) eqb_optional_binary_tree_of_nats t1 t2.


Definition eqb_binary_tree_of_optional_binary_tree_of_optional_nats (t1 t2 : polymorphic_binary_tree (option (polymorphic_binary_tree (option nat)))) : bool :=
  eqb_polymorphic_binary_tree (option (polymorphic_binary_tree (option nat))) eqb_optional_binary_tree_of_optional_nats t1 t2.

(* end of week-01_polymorphism.v *)
