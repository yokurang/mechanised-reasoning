(* week-05_folding-left-and-right-over-peano-numbers.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 12 Sep 2023 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Definition specification_of_power (power : nat -> nat -> nat) :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall (x : nat)
          (n' : nat),
      power x (S n') = x * power x n').

(* ***** *)

Proposition there_is_at_most_one_function_satisfying_the_specification_of_power :
  forall power1 power2 : nat -> nat -> nat,
    specification_of_power power1 ->
    specification_of_power power2 ->
    forall x n : nat,
      power1 x n = power2 x n.
Proof.
  intros power1 power2.
  unfold specification_of_power.
  intros [S1_O S1_S] [S2_O S2_S] x n.
  induction n as [ | n' IHn'].
  - rewrite -> (S2_O x).
    exact (S1_O x).
  - rewrite -> (S1_S x n').
    rewrite -> (S2_S x n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ***** *)

Definition test_power (candidate : nat -> nat -> nat) : bool :=
  (candidate 2 0 =? 1) &&
  (candidate 10 2 =? 10 * 10) &&
  (candidate 3 2 =? 3 * 3).

(* ***** *)

Fixpoint power_v0_aux (x n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    x * power_v0_aux x n'
  end.

Definition power_v0 (x n : nat) : nat :=
  power_v0_aux x n.

Compute (test_power power_v0).

Lemma fold_unfold_power_v0_aux_O :
  forall x : nat,
    power_v0_aux x 0 = 1.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Lemma fold_unfold_power_v0_aux_S :
  forall x n' : nat,
    power_v0_aux x (S n') = x * power_v0_aux x n'.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Proposition power_v0_safisfies_the_specification_of_power :
  specification_of_power power_v0.
Proof.
  unfold specification_of_power, power_v0.
  split.
  - exact fold_unfold_power_v0_aux_O.
  - exact fold_unfold_power_v0_aux_S.
Qed.

(* ***** *)

Fixpoint power_v1_aux (x n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    power_v1_aux x n' (x * a)
  end.

Definition power_v1 (x n : nat) : nat :=
  power_v1_aux x n 1.

Compute (test_power power_v1).

Lemma fold_unfold_power_v1_aux_O :
  forall x a : nat,
    power_v1_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

Lemma fold_unfold_power_v1_aux_S :
  forall x n' a : nat,
    power_v1_aux x (S n') a =
    power_v1_aux x n' (x * a).
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

(* ***** *)

(* Eureka lemma: *)

Lemma about_power_v0_aux_and_power_v1_aux :
  forall x n a : nat,
    power_v0_aux x n * a = power_v1_aux x n a.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_O x).
    rewrite -> (fold_unfold_power_v1_aux_O x a).
    exact (Nat.mul_1_l a).
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_S x n').
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    Check (IHn' (x * a)).
    rewrite <- (IHn' (x * a)).
    rewrite -> (Nat.mul_comm x (power_v0_aux x n')).
    Check (Nat.mul_assoc).
    symmetry.
    exact (Nat.mul_assoc (power_v0_aux x n') x a).
Qed.

Theorem power_v0_and_power_v1_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  unfold power_v0, power_v1.
  Check (about_power_v0_aux_and_power_v1_aux x n 1).
  rewrite <- (Nat.mul_1_r (power_v0_aux x n)).
  exact (about_power_v0_aux_and_power_v1_aux x n 1).
Qed.

(* ********** *)

Fixpoint nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s (nat_fold_right V z s n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_right V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_right V z s (S n') =
    s (nat_fold_right V z s n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

(* ***** *)

Fixpoint nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_fold_left V (s z) s n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_left V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_left V z s (S n') =
    nat_fold_left V (s z) s n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ********** *)

Definition power_v0_alt (x n : nat) : nat :=
  nat_fold_right nat 1 (fun ih => x * ih) n.

Compute (test_power power_v0_alt).

Proposition power_v0_alt_safisfies_the_specification_of_power :
  specification_of_power power_v0_alt.
Proof.
  unfold specification_of_power, power_v0_alt.
  split.
  - intro x.
    rewrite -> (fold_unfold_nat_fold_right_O nat 1 (fun ih : nat => x * ih)).
    reflexivity.
  - intros x n'.
    rewrite -> (fold_unfold_nat_fold_right_S nat 1 (fun ih : nat => x * ih) n').
    reflexivity.
Qed.

Corollary power_v0_and_power_v0_alt_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v0_alt x n.
Proof.
  intros x n.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
Qed.

(* ***** *)

Definition power_v1_alt (x n : nat) : nat :=
  nat_fold_left nat 1 (fun ih => x * ih) n.

Compute (test_power power_v1_alt).

Lemma power_v1_and_power_v1_alt_are_equivalent_aux :
  forall x n a : nat,
    power_v1_aux x n a = nat_fold_left nat a (fun ih : nat => x * ih) n.
Proof.
Admitted.

Proposition power_v1_and_power_v1_alt_are_equivalent :
  forall x n : nat,
    power_v1 x n = power_v1_alt x n.
Proof.
  intros x n.
  unfold power_v1, power_v1_alt.
  exact (power_v1_and_power_v1_alt_are_equivalent_aux x n 1).
Qed.

(* ********** *)

(* Exercise 01 *)

Theorem folding_left_and_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V z s n = nat_fold_right V z s n.
Proof.
Admitted.

(* ********** *)

Corollary power_v0_and_power_v1_are_equivalent_alt :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  rewrite -> (power_v0_and_power_v0_alt_are_equivalent x n).
  rewrite -> (power_v1_and_power_v1_alt_are_equivalent x n).
  unfold power_v0_alt, power_v1_alt.
  symmetry.
  exact (folding_left_and_right nat 1 (fun ih : nat => x * ih) n).
Qed.

(* ********** *)

Fixpoint add_v0 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v0 i' j)
  end.

(*
Definition add_v0_alt (i j : nat) : nat :=
  ...nat_fold_right...
*)

(*
Proposition add_v0_and_add_v0_alt_are_equivalent :
  forall i j : nat,
    add_v0 i j = add_v0_alt i j.
*)

(* ***** *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v1 i' (S j)
  end.

(*
Definition add_v1_alt (i j : nat) : nat :=
  ...nat_fold_left...
*)

(*
Proposition add_v1_and_add_v1_alt_are_equivalent :
  forall i j : nat,
    add_v1 i j = add_v1_alt i j.
*)

(* ********** *)

Fixpoint mul_v0_aux (i j : nat) : nat :=
  match i with
    | O => 0
    | S i' => j + (mul_v0_aux i' j)
  end.

Definition mul_v0 (i j : nat) : nat :=
  mul_v0_aux i j.

(*
Definition mul_v0_alt (i j : nat) : nat :=
  ...nat_fold_right...
*)

(*
Proposition mul_v0_and_mul_v0_alt_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v0_alt i j.
 *)

Definition specification_of_multiplication (multiplication : nat -> nat -> nat) :=
  (forall x : nat,
      multiplication x 0 = 0)
  /\
  (forall (x : nat)
          (y : nat),
      multiplication x (S y) = x + multiplication x y).

Proposition there_is_at_most_one_function_satisfying_the_specification_of_multiplication :
  forall multiplication1 multiplication2 : nat -> nat -> nat,
    specification_of_multiplication multiplication1 ->
    specification_of_multiplication multiplication2 ->
    forall x y : nat,
      multiplication1 x y = multiplication2 x y.
Proof.
  intros multiplication1 multiplication2.
  unfold specification_of_multiplication.
  intros [S1_O S1_S] [S2_O S2_S] x.
  induction x as [ | x' IHx'].
  - induction y as [ | y' IHy'].
    -- rewrite -> (S1_O 0).
       rewrite -> (S2_O 0).
       reflexivity.
    -- Check (S1_S 0 y').   
       rewrite -> (S1_S 0 y').
       rewrite -> (S2_S 0 y').
       rewrite -> IHy'.
       reflexivity.
  - induction y as [ | y' IHy'].
    -- Check (S1_O (S x')).
       rewrite (S1_O (S x')).
       rewrite (S2_O (S x')).
       reflexivity.
    -- Check (S1_S (S x') y'). 
       rewrite (S1_S (S x') y').
       rewrite (S2_S (S x') y').
       rewrite IHy'.
       reflexivity.
Qed.

Definition test_mult (candidate : nat -> nat -> nat) : bool :=
  (candidate 0 0 =? 0) &&
  (candidate 0 1 =? 0) &&
  (candidate 1 0 =? 0) &&
  (candidate 1 1 =? 1) && 
  (candidate 10 2 =? 20).

Compute test_mult Nat.mul.

Lemma fold_unfold_mul_v0_aux_O :
  forall x : nat,
    mul_v0_aux x 0 = 0.
Proof.
  intro x.
  unfold mul_v0_aux.
Abort.

Lemma fold_unfold_mul_v0_aux_S :
  forall x n' : nat,
    mul_v0_aux x (S n') = x * mul_v0_aux x n'.
Proof.
  (* fold_unfold_tactic mul_v0_aux. *)
Abort.

Proposition mul_v0_safisfies_the_specification_of_power :
  specification_of_multiplication mul_v0.
Proof.
  unfold specification_of_multiplication, mul_v0.
  split.
  - intro x.
    unfold mul_v0_aux.
    induction x as [ | x' IHx'].
    -- reflexivity.
    -- rewrite IHx'. 
       Search (0 + 0 = 0).
Qed.


Definition mul_v0_alt (i j : nat) : nat :=
  nat_fold_right nat 0 (fun ih => i + ih) j.

Compute test_mult mul_v0.

Compute test_mult mul_v0_alt.


Proposition mul_v0_and_mul_v0_alt_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v0_alt i j.
Proof.

(* ***** *)

Fixpoint mul_v1_aux (i j a : nat) : nat :=
  match i with
    | O => a
    | S i' => mul_v1_aux i' j (j + a)
  end.

Definition mul_v1 (i j : nat) : nat :=
  mul_v1_aux i j 0.

(*
Definition mul_v1_alt (i j : nat) : nat :=
  ...nat_fold_left...
*)

(*
Proposition mul_v1_and_mul_v1_alt_are_equivalent :
  forall i j : nat,
    mul_v1 i j = mul_v1_alt i j.
*)

(* ***** *)

Fixpoint mul_v1_aux (i j a : nat) : nat :=
  match i with
    | O => a
    | S i' => mul_v1_aux i' j (j + a)
  end.

Definition mul_v1 (i j : nat) : nat :=
  mul_v1_aux i j 0.

(*
Definition mul_v1_alt (i j : nat) : nat :=
  ...nat_fold_left...
*)

(*
Proposition mul_v1_and_mul_v1_alt_are_equivalent :
  forall i j : nat,
    mul_v1 i j = mul_v1_alt i j.
*)

(* ********** *)

Fixpoint nat_parafold_right (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s n' (nat_parafold_right V z s n')
  end.

Lemma fold_unfold_nat_parafold_right_O :
  forall (V : Type) (z : V) (s : nat -> V -> V),
    nat_parafold_right V z s 0 =
    z.
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

Lemma fold_unfold_nat_parafold_right_S :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n' : nat),
    nat_parafold_right V z s (S n') =
    s n' (nat_parafold_right V z s n').
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

Fixpoint nat_parafold_left (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_parafold_left V (s n' z) s n'
  end.

Lemma fold_unfold_nat_parafold_left_O :
  forall (V : Type) (z : V) (s : nat -> V -> V),
    nat_parafold_left V z s 0 =
    z.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

Lemma fold_unfold_nat_parafold_left_S :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n' : nat),
    nat_parafold_left V z s (S n') =
    nat_parafold_left V (s n' z) s n'.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

(* ***** *)

Check nat_rect.

Definition nat_parafold_right' (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  nat_rect (fun (_ : nat) => V) z s n.

Lemma fold_unfold_nat_parafold_right'_O :
  forall (V : Type) (z : V) (s : nat -> V -> V),
    nat_parafold_right' V z s 0 =
    z.
Proof.
  fold_unfold_tactic nat_parafold_right'.
Qed.

Lemma fold_unfold_nat_parafold_right'_S :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n' : nat),
    nat_parafold_right' V z s (S n') =
    s n' (nat_parafold_right' V z s n').
Proof.
  fold_unfold_tactic nat_parafold_right'.
Qed.

Proposition equivalence_of_nat_parafold_right_and_nat_parafold_right' :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n : nat),
    nat_parafold_right V z s n = nat_parafold_right' V z s n.
Proof.
  intros V z s n.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_nat_parafold_right_O V z s).
    rewrite -> (fold_unfold_nat_parafold_right'_O V z s).
    reflexivity.
  - rewrite -> (fold_unfold_nat_parafold_right_S V z s n').
    rewrite -> (fold_unfold_nat_parafold_right'_S V z s n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ********** *)

(* Exercise 06 *)

Theorem parafolding_left_and_right :
  exists (V : Type) (z : V) (s : nat -> V -> V) (n : nat),
    nat_parafold_left V z s n <> nat_parafold_right V z s n.
Proof.
Abort.  

(* ********** *)

(* end of week-05_folding-left-and-right-over-peano-numbers.v *)
