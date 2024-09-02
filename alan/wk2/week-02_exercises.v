(* week-02_exercises.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 22 Aug 2023 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

(* Exercises about types: *)


Definition ta : forall A : Type, A -> A * A :=
  fun A x => (x, x).


Definition tb : forall A B : Type, A -> B -> A * B :=
  fun A B x y => (x, y).


Definition tc : forall A B : Type, A -> B -> B * A :=
  fun A B x y => (y, x).

Check (tt : unit).


Definition td : forall (A : Type), (unit -> A) -> A :=
  fun A f => f tt.


Definition te : forall A B : Type, (A -> B) -> A -> B :=
  fun A B f x => f x.


Definition tf : forall A B : Type, A -> (A -> B) -> B :=
  fun A B x f => f x.


Definition tg : forall A B C : Type, (A -> B -> C) -> A -> B -> C :=
  fun A B C f x y => f x y.


Definition th : forall A B C : Type, (A -> B -> C) -> B -> A -> C :=
  fun A B C f y x => f x y.


Definition ti : forall A B C D : Type, (A -> C) -> (B -> D) -> A -> B -> C * D :=
  fun A B C D f g x y => (f x, g y).



Definition tj : forall A B C : Type, (A -> B) -> (B -> C) -> A -> C :=
  fun A B C f g x => g (f x).



Definition tk : forall A B : Type, A * B -> B * A :=
  fun A B p => match p with
               | (x, y) => (y, x)
               end.
(* Hint: use a match expression to destructure the input pair. *)



Definition tl : forall A B C : Type, (A * B -> C) -> A -> B -> C :=
  fun A B C f x y => f (x, y).


Definition tm : forall A B C : Type, (A -> B -> C) -> A * B -> C :=
  fun A B C f p => match p with
                   | (x, y) => f x y
                   end.


Definition tn : forall A B C : Type, A * (B * C) -> (A * B) * C :=
  fun A B C p => match p with
                 | (x, (y, z)) => ((x, y), z)
                 end.

(* ********** *)

(* Exercises about propositions: *)

Proposition pa :
  forall A : Prop,
    A -> A /\ A.
Proof.
  intro A.
  intros H_A.
  split.
  - exact H_A.
  - exact H_A.

Restart.

  intro A.
  intros H_A.
  exact (conj H_A H_A).
  (* Wow!  *)
  
Qed.

Proposition pb :
  forall A B : Prop,
    A -> B -> A /\ B.
Proof.
  intros A B.
  intros H_A H_B.
  split.
  - exact H_A.
  - exact H_B.

Restart.
    
  intros A B.
  intros H_A H_B.
  exact (conj H_A H_B).
  
Qed.

Proposition pc :
  forall A B : Prop,
    A -> B -> B /\ A.
Proof.
  intros A B.
  intros H_A H_B.
  split.
  - exact H_B.  
  - exact H_A.

Restart.
    
  intros A B.
  intros H_A H_B.
  exact (conj H_B H_A).
  
Qed.

Check tt.

Proposition pd :
  forall (A : Prop),
    (unit -> A) -> A.
Proof.
  intros A H_A.
  apply (H_A tt).

Restart.
  
  intros A H_A.
  exact (H_A tt).
Qed.  

Proposition pe :
  forall A B : Prop,
    (A -> B) -> A -> B.
Proof.
  intros A B.
  intros H_A_implies_B.
  exact H_A_implies_B.
Qed.

Proposition pf :
  forall A B : Prop,
    A -> (A -> B) -> B.
Proof.
  intros A B.
  intros H_A H_A_implies_B.
  exact (H_A_implies_B H_A).
Qed.

Proposition pg :
  forall A B C : Prop,
    (A -> B -> C) -> A -> B -> C.
Proof.
  intros A B C.
  intros H_A_implies_B_implies_C H_A.
  apply H_A_implies_B_implies_C.
  exact H_A.

  (* Note: H_A is superfluous see next proof. *)

Restart.
  
  intros A B C.
  intros H_A_implies_B_implies_C.
  exact H_A_implies_B_implies_C.

Qed.

Proposition ph :
  forall A B C : Prop,
    (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C.
  intros H_A_implies_B_implies_C H_B H_A.
  Check H_A_implies_B_implies_C H_A H_B.
  exact (H_A_implies_B_implies_C H_A H_B).

Restart.

  intros A B C.
  intros H_A_implies_B_implies_C H_B H_A.
  revert H_A H_B.
  exact H_A_implies_B_implies_C.
Qed.

Proposition pi :
  forall A B C D : Prop,
    (A -> C) -> (B -> D) -> A -> B -> C /\ D.
Proof.
  intros A B C D.
  intros H_A_implies_C H_B_implies_D.
  intros H_A H_B.
  split.
  apply H_A_implies_C.
  exact H_A.
  apply H_B_implies_D.
  exact H_B.

  (* Note: Previous explicit application approach *)
  
Restart.  
  
  intros A B C D.
  intros H_A_implies_C H_B_implies_D.
  intros H_A H_B.
  split.
  - exact (H_A_implies_C H_A).
  - exact (H_B_implies_D H_B).
Qed.


Proposition pj :
  forall A B C : Prop,
    (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros A B C.
  intros H_A_implies_B H_B_implies_C.
  intros H_A.
  apply H_B_implies_C.
  apply H_A_implies_B.
  exact H_A.
  Show Proof.

 Restart.
  
  intros A B C.
  intros H_A_implies_B H_B_implies_C.
  intros H_A.
  Check (H_B_implies_C (H_A_implies_B H_A)).
  exact (H_B_implies_C (H_A_implies_B H_A)).
  Show Proof.

  (* Note: The proofs are the same. *)

Qed.

Proposition pk :
  forall A B : Prop,
    A /\ B -> B /\ A.
Proof.
  intros A B [H_A H_B].
  exact (conj H_B H_A).
Qed.

Proposition pl :
  forall A B C : Prop,
    (A /\ B -> C) -> A -> B -> C.
Proof.
  intros A B C.
  intros H_A_conj_B_implies_C.
  intros H_A H_B.
  exact (H_A_conj_B_implies_C (conj H_A H_B)).
Qed.

Proposition pm :
  forall A B C : Prop,
    (A -> B -> C) -> A /\ B -> C.
Proof.
  intros A B C.
  intros H_A_implies_B_implies_C.
  intros [H_A H_B].
  Check (H_A_implies_B_implies_C H_A H_B).
  exact (H_A_implies_B_implies_C H_A H_B).
Qed.  

Proposition pn :
  forall A B C : Prop,
    (A /\ (B /\ C)) -> (A /\ B) /\ C.
Proof.
  intros A B C.
  intros [H_A [H_B H_C]].
  split.
  - split.
    -- exact H_A.
    -- exact H_B.
  - exact H_C.

Restart.

  intros A B C.
  intros [H_A [H_B H_C]].
  exact (conj (conj H_A H_B) H_C).

  (* Note: Minimise use of uneccessary splits. *)

Qed.

(* ********** *)

(* Exercise 05 *)

Proposition binomial_expansion_2_warmup :
  forall x y : nat,
    (x + y) * (x + y) = x * x + x * y + x * y + y * y.
Proof.
  intros x y.
  rewrite -> (Nat.mul_add_distr_l (x + y) x y).
  rewrite -> (Nat.mul_add_distr_r x y x).
  rewrite -> (Nat.mul_add_distr_r x y y).
  rewrite -> (Nat.mul_comm y x).
  rewrite -> (Nat.add_assoc (x * x + x * y) (x * y) (y * y)).
  reflexivity.
Qed.

Lemma twice_a_nat :
    forall x : nat,
      x + x = 2 * x.
Proof.
  intro n.
  Search (S _ * _ = _ + _).
(*
  Nat.mul_succ_l: forall n m : nat, S n * m = n * m + m
  the induction step of multiplication
 *)
  Check (Nat.mul_succ_l 1 n).
  rewrite -> (Nat.mul_succ_l 1 n).
  Check (Nat.mul_succ_l 0 n).
  rewrite -> (Nat.mul_succ_l 0 n).
  Search (0 * _ = _).
(*
  Nat.mul_0_l: forall n : nat, 0 * n = 0
  the base case of multiplication
*)
  Check (Nat.mul_0_l n).
  rewrite -> (Nat.mul_0_l n).
  Search (0 + _ = _).
(*
  Nat.add_0_l: forall n : nat, 0 + n = n
  the base case of addition
*)
  Check (Nat.add_0_l n).
  rewrite -> (Nat.add_0_l n).
  reflexivity.

Restart.

  intro n.
  Check (Nat.mul_succ_l 1 n).
  rewrite -> (Nat.mul_succ_l 1 n).
  Search (1 * _ = _).
  rewrite -> (Nat.mul_1_l n).
  reflexivity.
Qed.

Proposition binomial_expansion_2 :
  forall x y : nat,
    (x + y) * (x + y) = x * x + 2 * (x * y) + y * y.
Proof.
  intros x y.
  rewrite -> (binomial_expansion_2_warmup x y).
  Check (twice_a_nat (x * y)).
  rewrite <- (twice_a_nat (x * y)).
  Search (_ + (_ + _)).
  Check (Nat.add_assoc (x * x) (x * y) (x * y)).
  rewrite -> (Nat.add_assoc (x * x) (x * y) (x * y)).
  reflexivity.

Restart.

  intros x y.
  rewrite -> (binomial_expansion_2_warmup x y).
  Check (twice_a_nat (x * y)).
  rewrite <- (twice_a_nat (x * y)).
  Search (_ + (_ + _)).
  Check (Nat.add_assoc (x * x) (x * y) (x * y)).
  rewrite <- (Nat.add_assoc (x * x) (x * y) (x * y)).
  reflexivity.

Restart.

  intros x y.
  rewrite -> (binomial_expansion_2_warmup x y).
  Search (_ + (_ + _)).
  Check (Nat.add_assoc (x * x) (x * y) (x * y)).
  rewrite <- (Nat.add_assoc (x * x) (x * y) (x * y)).
  Check (twice_a_nat (x * y)).
  rewrite <- (twice_a_nat (x * y)).
  reflexivity.

Restart.

  intros x y.
  rewrite -> (binomial_expansion_2_warmup x y).
  Search (_ + (_ + _)).
  Check (Nat.add_assoc (x * x) (x * y) (x * y)).
  rewrite <- (Nat.add_assoc (x * x) (x * y) (x * y)).
  Check (twice_a_nat (x * y)).
  rewrite -> (twice_a_nat (x * y)).
  reflexivity.
Qed.


Lemma thrice_a_nat :
    forall x : nat,
      x + x + x = 3 * x.
Proof.
  intro n. 
  Check (twice_a_nat n).
  rewrite -> (twice_a_nat n).
  Check (Nat.mul_succ_l 2 n).
  rewrite <- (Nat.mul_succ_l 2 n).
  reflexivity.

Restart.
  
  intro n. 
  Check (twice_a_nat n).
  rewrite -> (twice_a_nat n).
  Check (Nat.mul_succ_l 2 n).
  rewrite -> (Nat.mul_succ_l 2 n).
  reflexivity.

Restart.

  intro n.
  Check (Nat.mul_succ_l 2 n).
  rewrite -> (Nat.mul_succ_l 2 n).
  Check (twice_a_nat n).
  rewrite -> (twice_a_nat n).
  reflexivity.

Restart.

  intro n.
  Check (Nat.mul_succ_l 2 n).
  rewrite -> (Nat.mul_succ_l 2 n).
  Check (twice_a_nat n).
  rewrite <- (twice_a_nat n).
  reflexivity.
Qed.
 
(* ********** *)

(* Exercise 11 *)

Proposition conjunction_distributes_over_disjunction_on_the_left:
  forall A B C : Prop,
    A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  split.

  - intros [H_A [H_B | H_C]].
    
    + left.
      split.

      * exact H_A.

      * exact H_B.

    + right.
      split.

      * exact H_A.

      * exact H_C.

  - intros [[H_A H_B] | [H_A' H_C]].

    + split.

      * exact H_A.

      * left.
        exact H_B.
        
    + split.
      
      * exact H_A'.
      
      * right.
        exact H_C.
Qed.


Proposition conjunction_distributes_over_disjunction_on_the_right :
  forall A B C : Prop,
    (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
  intros A B C.
  split.

  - intros [[H_A | H_B] H_C].

    + left.
      split.
      
      * exact H_A.
      
      * exact H_C.

    + right.
      split.
      
      * exact H_B.
      
      * exact H_C.

  - intros [[H_A H_C] | [H_B H_C']].

    + split.
      
      * left.
        exact H_A.
      
      * exact H_C.

    + split.
      
      * right.
        exact H_B.
      
      * exact H_C'.
Qed.

(* end of week-02_exercises.v *)
