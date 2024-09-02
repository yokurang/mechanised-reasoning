(* week-01_functional-programming-in-Gallina.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 18 Aug 2023, where the definition of specification_of_evenp is corrected (":=" instead of ":"), and with an explicit Prop declaration for specifications (Prop is the type of propositions) *)
(* was: *)
(* Version of 15 Aug 2023 *)

(* ********** *)

(* name: Zhu Wentao
   e-mail address: zhu.wentao@u.yale-nus.edu.sg
   student number: A0224190N
*)

(* name: 
   e-mail address: 
   student number: 
*)

(* name: 
   e-mail address: 
   student number: 
*)

(* name: 
   e-mail address: 
   student number: 
*)

(* name: 
   e-mail address: 
   student number: 
*)

(* ********** *)

Check 0.

Check O.

(* Note: "nat" is the type of natural numbers. *)

(* ********** *)

Check 1.

Check (S 0).

Check (S O).

(* ********** *)

Check 2.

Check (S (S 0)).

Check (S (S O)).

(* ********** *)

Check 3.

Compute 3.

(* Note: natural numbers are self-evaluating. *)

(* ********** *)

Compute (4 + 6).

Check (4 + 6).

(* ********** *)

Compute (plus 4 6).

Check (plus 4 6).

(* Note: infix + is syntactic sugar for plus. *)

(* ********** *)

Check (plus 4).

(* Note: plus refers to a library function. *)

Compute (plus 4).
Compute (plus 3).
Compute (plus 2).
Compute (plus 1).
Compute (plus 0).

(* Note: functions are written as in OCaml,
   with the keyword "fun" followed by the formal parameter
   (and optionally its type), "=>", and the body. *)

Compute (fun m : nat => S m).

(*
   For comparison,
     fun m : nat => S m
   would be written
     fun m => succ m
   or
     fun m => m + 1
   or
     fun m => 1 + m
   in OCaml and
     (lambda (m) (1+ m))
   in Scheme.
*)

Compute ((fun m : nat => S m) 3).

(* ********** *)

Definition three := 3.

Check three.

Compute three.

Definition ten := 4 + 6.

Check ten.

Compute ten.

(* ********** *)

(* The following definitions are all equivalent: *)

Definition succ_v0 := fun m : nat => S m.

Definition succ_v1 := fun m => S m.

Definition succ_v2 (m : nat) :=
  S m.

Definition succ_v3 (m : nat) : nat :=
  S m.

Definition succ_v4 m :=
  S m.

(* Note: the definition of succ_v3 is the recommended one here. *)

(* Note: variables are defined once and for all in a file. *)

(* ********** *)

(* Ditto for the following definitions: *)

Definition zerop_v0 : nat -> bool :=
  fun n =>
    match n with
    | O =>
      true
    | S n' =>
      false
    end.

Compute (zerop_v0 0). (* = true : bool *)
Compute (zerop_v0 7). (* = false : bool *)

Definition zerop_v1 (n : nat) : bool :=
  match n with
  | O =>
    true
  | S n' =>
    false
  end.

Compute (zerop_v1 0). (* = true : bool *)
Compute (zerop_v1 7). (* = false : bool *)

(* ********** *)

(* The addition function: *)

Definition specification_of_addition (add : nat -> nat -> nat) : Prop :=
  (forall j : nat,
      add 0 j = j)
  /\
  (forall n j : nat,
      add (S n) j = S (add n j)).

(* ***** *)

(* Unit tests: *)

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (Nat.eqb (candidate 0 0) 0)
  &&
  (Nat.eqb (candidate 0 1) 1)
  &&
  (Nat.eqb (candidate 1 0) 1)
  &&
  (Nat.eqb (candidate 1 1) 2)
  &&
  (Nat.eqb (candidate 1 2) 3)
  &&
  (Nat.eqb (candidate 2 1) 3)
  &&
  (Nat.eqb (candidate 2 2) 4)
  &&
  (* commutativity: *)
  (Nat.eqb (candidate 2 10) (candidate 10 2))
  &&
  (* associativity: *)
  (Nat.eqb (candidate 2 (candidate 5 10))
           (candidate (candidate 2 5) 10))
  (* etc. *)
  .

(* Testing the unit-test function: *)

Compute (test_add Nat.add).

(* Version 1: recursive *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v1 i' j)
  end.

Compute (test_add add_v1).

(* Version 2: tail recursive *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

(* Version 3: recursive, lambda-dropped *)

Definition add_v3 (i j : nat) : nat :=
  let fix visit n :=
    match n with
      | O => j
      | S n' => S (visit n')
    end
  in visit i.

Compute (test_add add_v3).

(* ********** *)

(* The multiplication function: *)

Definition specification_of_multiplication (mul : nat -> nat -> nat) : Prop :=
  (forall j : nat,
      mul 0 j = 0)
  /\
  (forall n j : nat,
      mul (S n) j = j + (mul n j)).

(* ***** *)

(* Unit tests: *)

Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (Nat.eqb (candidate 0 0) 0)
  &&
  (Nat.eqb (candidate 0 1) 0)
  &&
  (Nat.eqb (candidate 1 0) 0)
  &&
  (Nat.eqb (candidate 1 1) 1)
  &&
  (Nat.eqb (candidate 1 2) 2)
  &&
  (Nat.eqb (candidate 2 1) 2)
  &&
  (Nat.eqb (candidate 2 2) 4)
  &&
  (* commutativity: *)
  (Nat.eqb (candidate 2 10) (candidate 10 2))
  &&
  (* associativity: *)
  (Nat.eqb (candidate 2 (candidate 5 10))
           (candidate (candidate 2 5) 10))
  (* etc. *)
  .


(* ***** *)

(* Testing the unit-test function: *)


Compute (test_mul Nat.mul).


(* ***** *)

(* Version 1: recursive *)

Fixpoint mul_v1 (i j : nat) : nat :=
   match i with
    | O => O
    | S i' => j + (mul_v1 i' j)
   end.

Compute (test_mul mul_v1).


(* ***** *)

(* Version 2: tail recursive with an accumulator *)

Fixpoint mul_v2_aux (i j a : nat) : nat :=
  match i with
  | O =>
    a
  | S i' =>
    mul_v2_aux i' j (j + a)
  end.

Definition mul_v2 (i j : nat) : nat :=
  mul_v2_aux i j 0.


Compute (test_mul mul_v2).

(* ***** *)

(* The exponentiation function: *)

Definition specification_of_power (power : nat -> nat -> nat) : Prop :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall x n : nat,
      power x (S n) = x * (power x n)).

(* ***** *)

(* Unit tests: *)


Definition test_power (candidate: nat -> nat -> nat) : bool :=
  (Nat.eqb (candidate 0 0) 1)
  &&
  (Nat.eqb (candidate 0 1) 0)
  &&
  (Nat.eqb (candidate 1 0) 1)
  &&
  (Nat.eqb (candidate 1 1) 1)
  &&
  (Nat.eqb (candidate 1 2) 1)
  &&
  (Nat.eqb (candidate 2 1) 2)
  &&
  (Nat.eqb (candidate 2 2) 4)
  &&
  (Nat.eqb (candidate 3 2) 9)
  (* etc. *)
  .


(* ***** *)

(* Version 1: recursive *)


Fixpoint power_v1 (x n : nat) : nat :=
  match n with
  | O => 1
  | S n' => x * power_v1 x n'
  end.

Compute (test_power power_v1).


(* ***** *)

(* Version 2: tail recursive with an accumulator *)

Fixpoint power_v2_aux (x n a : nat) : nat :=
  match n with
  | 0 => a
  | S n' => power_v2_aux x n' (x * a)
  end.

Definition power_v2 (x n : nat) : nat :=
  power_v2_aux x n 1.

Compute (test_power power_v2).

(* ********** *)

(* The factorial function: *)

Definition specification_of_fac (fac : nat -> nat) : Prop :=
  (fac 0 = 1)
  /\
  (forall n : nat,
      fac (S n) = S n * fac n).

(* ***** *)

(* Unit tests: *)


Definition test_fac (candidate: nat -> nat) : bool :=
  (Nat.eqb (candidate 0) 1)
  &&
  (Nat.eqb (candidate 1) 1)
  &&
  (Nat.eqb (candidate 2) 2)
  &&
  (Nat.eqb (candidate 3) 6)
  &&
  (Nat.eqb (candidate 4) 24)
  &&
  (Nat.eqb (candidate 5) 120)
  (* etc. *)
  .

(* ***** *)

(* Version 1: recursive *)


Fixpoint fac_v1 (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fac_v1 n'
  end.

Compute (test_fac fac_v1).

(* ***** *)

(* Version 2: tail recursive with an accumulator *)

Fixpoint fac_v2_aux (n a : nat) :nat :=
  match n with
  | 0 => a
  | S n' => fac_v2_aux n' (n * a)
  end.

Definition fac_v2 (n : nat) : nat :=
  fac_v2_aux n 1.

Compute (test_fac fac_v2).
  
(* ********** *)

(* The fibonacci function: *)

Definition specification_of_fib (fib : nat -> nat) : Prop :=
  (fib 0 = 0)
  /\
  (fib 1 = 1)
  /\
  (forall n : nat,
      fib (S (S n)) = fib n + fib (S n)).

(* ***** *)

(* Unit tests: *)


Definition test_fib (candidate: nat -> nat) : bool :=
  (Nat.eqb (candidate 2) 1)
  &&
  (Nat.eqb (candidate 3) 2)
  &&
  (Nat.eqb (candidate 4) 3)
  &&
  (Nat.eqb (candidate 5) 5)
  &&
  (Nat.eqb (candidate 6) 8)
  &&
  (Nat.eqb (candidate 7) 13)
  &&
  (Nat.eqb (candidate 8) 21)
  &&
  (Nat.eqb (candidate 12) 144)
  (* etc. *)
  .

(* ***** *)

(* Version 1: recursive *)


Fixpoint fib_v1 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S p => fib_v1 p + fib_v1 (p - 1)
  end.

 Compute (test_fib fib_v1).

 (* Version 3: Not going faster than the music *)
 
 Fixpoint fib_v3 (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib_v3 n' + fib_v3 n''
            end
  end.

 Compute (test_fib fib_v3).



(* ********** *)

(* The even predicate: *)

Definition bool_eqb (b1 b2 : bool) : bool :=
  match b1 with
  | true =>
    match b2 with
    | true =>
      true
    | false =>
      false
    end
  | false =>
    match b2 with
    | true =>
      false
    | false =>
      true
    end
  end.

Definition specification_of_evenp (evenp : nat -> bool) : Prop :=
  (evenp 0 = true)
  /\
  (forall n : nat,
    evenp (S n) = negb (evenp n)).

(* ***** *)

(* Unit tests: *)

Definition test_evenp (candidate: nat -> bool) : bool :=
  (bool_eqb (candidate 2) true)
  &&
  (bool_eqb (candidate 3) false)
  &&
  (bool_eqb (candidate 4) true)
  &&
  (bool_eqb (candidate 5) false)
  &&
  (bool_eqb (candidate 24) true)
  &&
  (bool_eqb (candidate 75) false)
  &&
  (bool_eqb (candidate 301) false)
  &&
  (bool_eqb (candidate 430) true)
  (* etc. *)
  .

(* ***** *)

(* Version 1: recursive *)


Fixpoint even_v1 (n : nat) : bool :=
  match n with
  | O => true
  | S p => match p with
           | O => false
           | S q => even_v1 q
           end
  end.

Compute (test_evenp even_v1).


(* ***** *)

(* Version 2: tail recursive with an accumulator *)

Fixpoint even_v2_auc (n : nat) (a : bool) : bool :=
  match n with
  | O => a
  | S p => even_v2_auc p (negb a)
  end.

Definition even_v2 (n : nat) : bool :=
  even_v2_auc n true.

Compute (test_evenp even_v2).

(* ********** *)

(* The odd predicate: *)

Definition specification_of_oddp (oddp : nat -> bool) : Prop :=
  (oddp 0 = false)
  /\
  (forall n : nat,
      oddp (S n) = negb (oddp n)).

(* ***** *)

(* Unit tests: *)

Definition test_oddp (candidate: nat -> bool) : bool :=
  (bool_eqb (candidate 2) false)
  &&
  (bool_eqb (candidate 3) true)
  &&
  (bool_eqb (candidate 4) false)
  &&
  (bool_eqb (candidate 5) true)
  &&
  (bool_eqb (candidate 24) false)
  &&
  (bool_eqb (candidate 75) true)
  &&
  (bool_eqb (candidate 301) true)
  &&
  (bool_eqb (candidate 430) false)
  (* etc. *)
  .

(* ***** *)

(* Version 1: recursive *)


Fixpoint odd_v1 (n : nat) : bool :=
  match n with
  | O => false
  | S p => match p with
           | O => true
           | S q => odd_v1 q
           end
  end.

Compute (test_oddp odd_v1).


(* ***** *)

(* Version 2: tail recursive with an accumulator *)

Fixpoint odd_v2_auc (n : nat) (a : bool) : bool :=
  match n with
  | O => a
  | S p => odd_v2_auc p (negb a)
  end.

Definition odd_v2 (n : nat) : bool :=
  odd_v2_auc n false.

Compute (test_oddp odd_v2).



(* ********** *)

Inductive binary_tree_nat : Type :=
  Leaf_nat : nat -> binary_tree_nat
| Node_nat : binary_tree_nat -> binary_tree_nat -> binary_tree_nat.

Fixpoint beq_binary_tree_nat (t1 t2 : binary_tree_nat) : bool :=
  match t1 with
    Leaf_nat n1 =>
    match t2 with
      Leaf_nat n2 =>
      Nat.eqb n1 n2
    | Node_nat t21 t22 =>
      false
    end
  | Node_nat t11 t12 =>
    match t2 with
      Leaf_nat n2 =>
      false
    | Node_nat t21 t22 =>
      (beq_binary_tree_nat t11 t21) && (beq_binary_tree_nat t12 t22)
    end
  end.

(* ********** *)

(* How many leaves in a given binary tree? *)

Definition specification_of_number_of_leaves (number_of_leaves : binary_tree_nat -> nat) : Prop :=
  (forall n : nat,
      number_of_leaves (Leaf_nat n) = 1)
  /\
  (forall t1 t2 : binary_tree_nat,
      number_of_leaves (Node_nat t1 t2) = number_of_leaves t1 + number_of_leaves t2).

(* ***** *)

(* Unit tests: *)

Definition test_number_of_leaves (candidate: binary_tree_nat -> nat) : bool :=
  (Nat.eqb (candidate (Leaf_nat 1))
           1)
  &&
  (Nat.eqb (candidate (Node_nat (Leaf_nat 1)
                                (Leaf_nat 2)))
           2)
  (* etc. *)
  .

(* ***** *)

(* Version 1: recursive *)

Fixpoint number_of_leaves_v1 (t : binary_tree_nat) : nat :=
  match t with
    Leaf_nat n =>
    1
  | Node_nat t1 t2 =>
    (number_of_leaves_v1 t1) + (number_of_leaves_v1 t2)
  end.

(* ***** *)

Compute (test_number_of_leaves number_of_leaves_v1).

(* Version 2: recursive with an accumulator *)

(*
...
*)

(* ********** *)

(* How many nodes in a given binary tree? *)

Definition specification_of_number_of_nodes (number_of_nodes : binary_tree_nat -> nat) : Prop :=
  (forall n : nat,
      number_of_nodes (Leaf_nat n) = 0)
  /\
  (forall t1 t2 : binary_tree_nat,
      number_of_nodes (Node_nat t1 t2) = S (number_of_nodes t1 + number_of_nodes t2)).

(* ***** *)

(* Unit tests: *)

(*
Definition test_number_of_nodes (candidate: binary_tree_nat -> nat) : bool :=
  ...
  (* etc. *)
  .
*)

(* ***** *)

(* Version 1: recursive *)

(*
Fixpoint number_of_nodes_v1 (t : binary_tree_nat) : nat :=
  ...

Compute (test_number_of_nodes number_of_nodes_v1).
*)

(* ********** *)

(* What is the smallest leaf in a given binary tree? *)

Compute (Nat.ltb 1 2).
Compute (Nat.leb 1 2).

(*
Definition test_smallest_leaf (candidate: binary_tree_nat -> nat) : bool :=
  ...
  (* etc. *)
  .

Fixpoint smallest_leaf_v1 (t : binary_tree_nat) : nat :=
  ...

Compute (test_smallest_leaf smallest_leaf_v1).
*)

(* ********** *)

(* What is the sum of the payloads in the leaves of a given binary tree? *)

Definition specification_of_weight (weight : binary_tree_nat -> nat) : Prop :=
  (forall n : nat,
      weight (Leaf_nat n) = n)
  /\
  (forall t1 t2 : binary_tree_nat,
      weight (Node_nat t1 t2) = weight t1 + weight t2).

(* ***** *)

(* Unit tests: *)

(*
Definition test_weight (candidate: binary_tree_nat -> nat) : bool :=
  ...
  (* etc. *)
  .
*)

(* ***** *)

(* Version 1: recursive *)

Fixpoint weight_v1 (t : binary_tree_nat) : nat :=
  match t with
  | Leaf_nat n =>
    n
  | Node_nat t1 t2 =>
    weight_v1 t1 + weight_v1 t2
  end.

(*
Compute (test_weight weight_v1).
*)

(* ***** *)

(* Version 2: recursive with an accumulator *)

(*
...
*)

(* ********** *)

(* What is the length of the longest path from the root of a given binary tree to its leaves? *)

(* ***** *)

(*
Definition test_length_of_longest_path (candidate: binary_tree_nat -> nat) : bool :=
  ...
  (* etc. *)
  .
*)

(* ***** *)

(* Version 1: recursive *)

(*
Fixpoint length_of_longest_path_v1 (t : binary_tree_nat) : nat :=
  ...

Compute (test_length_of_longest_path length_of_longest_path_v1).
*)

(* ********** *)

(* What is the length of the shortest path from the root of a given binary tree to its leaves? *)

(* ***** *)

(*
Definition test_length_of_shortest_path (candidate: binary_tree_nat -> nat) : bool :=
  ...
  (* etc. *)
  .
*)

(* ***** *)

(* Version 1: recursive *)

(*
Fixpoint length_of_shortest_path_v1 (t : binary_tree_nat) : nat :=
  ...

Compute (test_length_of_shortest_path length_of_shortest_path_v1).
*)

(* ********** *)

Definition specification_of_the_mirror_function (mirror : binary_tree_nat -> binary_tree_nat) : Prop :=
  (forall n : nat,
      mirror (Leaf_nat n) = Leaf_nat n)
  /\
  (forall t1 t2 : binary_tree_nat,
      mirror (Node_nat t1 t2) = Node_nat (mirror t1) (mirror t2)).

(* ***** *)

(* Unit tests: *)

Definition test_mirror (candidate: binary_tree_nat -> binary_tree_nat) : bool :=
  (beq_binary_tree_nat (candidate (Leaf_nat 1))
                       (Leaf_nat 1))
  &&
  (beq_binary_tree_nat (candidate (Node_nat (Leaf_nat 1)
                                            (Leaf_nat 2)))
                       (Node_nat (Leaf_nat 2)
                                 (Leaf_nat 1)))
  (* etc. *)
  .

(* ***** *)

(* Version 1: recursive *)

(*
Fixpoint mirror_v1 (t : binary_tree_nat) : binary_tree_nat :=
  ...

Compute (test_mirror mirror_v1).
*)

(* ********** *)

(* Calder mobiles: *)

Definition specification_of_balancedp (balancedp : binary_tree_nat -> bool) : Prop :=
  (forall n : nat,
      balancedp (Leaf_nat n) = true)
  /\
  (forall t1 t2 : binary_tree_nat,
      balancedp t1 = true ->
      balancedp t2 = true ->
      weight_v1 t1 = weight_v1 t2 ->
      balancedp (Node_nat t1 t2) = true).

(* ***** *)

(* Unit tests: *)

(*
...
*)

(* ***** *)

(* Version 1: recursive *)

(*
...
*)

(* ********** *)

(* end of week-01_functional-programming-in-Gallina.v *)
