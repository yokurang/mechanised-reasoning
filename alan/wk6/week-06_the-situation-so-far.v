(* week-06_the-situation-so-far.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 22 Sep 2023 *)

(* ********** *)

Require Import Arith Bool List.

(* ********** *)

Proposition clearly :
  forall A B : Prop,
    A -> B -> A.
Proof.
  intros A B H_A H_B.
  clear H_B.
  exact H_A.
Qed.

(* ********** *)

Proposition true_or_false :
  forall b : bool,
    b = true \/ b = false.
Proof.
  intro b.
  case b as [ | ] eqn:H_b.
  - left.
    reflexivity.
  - right.
    reflexivity.
Qed.

(* ********** *)

Proposition reflexivity_of_implication :
  forall A : Prop,
    A -> A.
Proof.
  intros A H_A.
  exact H_A.
Qed.

(* ********** *)

Proposition zero_is_not_one :
  0 <> 1.
Proof.
  unfold not.
  (* the goal is now: 0 = 1 -> False *)
  intro H_absurd.
  discriminate H_absurd.
Qed.

Proposition nil_is_not_cons :
  forall (V : Type)
         (v : V),
  nil <> v :: nil.
Proof.
  intros V v.
  unfold not.
  intro H_absurd.
  discriminate H_absurd.
Qed.

(* ***** *)

Proposition a_list_is_not_another_list :
  forall (n1 n2 : nat),
    n1 :: 2 :: n2 :: nil <> 1 :: n2 :: 3 :: nil.
Proof.
  intros n1 n2.
  unfold not.
  intro H_tmp.
  injection H_tmp as eq_n1_1 eq_2_n2 eq_n2_3.
  rewrite <- eq_2_n2 in eq_n2_3.
  discriminate eq_n2_3.
Qed.

(* ********** *)

Proposition even_or_odd :
  forall n : nat,
    (exists q : nat,
        n = 2 * q)
    \/
    (exists q : nat,
        n = S (2 * q)).
Proof.
  intro n.
  induction n as [ | n' [[q IHq] | [q IHq]]].
  - left.
    exists 0.
    exact (eq_sym (Nat.mul_0_l 2)).
  - rewrite -> IHq.
    right.
    exists q.
    reflexivity.
  - rewrite -> IHq.
    left.
    exists (S q).
    Search (_ * S _ = _ + _).
    rewrite -> (Nat.mul_succ_r 2 q).
    rewrite <- (plus_n_Sm (2 * q) 1).
    rewrite -> (Nat.add_1_r (2 * q)).
    reflexivity.
Qed.

(* ********** *)

Let v1 := 3.
Let v2 := 2.

Compute (v1, v2) <> (v2, v1).

Let v1' := 3.
Let v2' := 3.

Compute (v1', v2') <> (v2', v1').

Lemma exists_v1_v2_not_equal : exists (V : Type) (v1 v2 : V), v1 <> v2.
Proof.
  exists nat, 0, 1.
  intro H_eq.
  discriminate H_eq.
Qed.

(* We know this_one can't hold  because there exist some values of v1, v2 where (v1, v2) = (v2,v1). But we give it a go anyway. *)

Proposition this_one :
  forall (V : Type)
         (v1 v2 : V),
    (v1, v2) <> (v2, v1).
Proof.
  intro v.
  intros v1 v2.
  Print Visibility.
  unfold not.
  intro h.
  injection h as h1 h2.
  (* Same as rewrite pair_equal_spec in h. *)
  (* The hypotheses at this stage tell us the counterexample we are looking for is when v1=v2.  *)
Abort.

(* We prove that there does exist some value of v1, v2 where (v1, v2) = (v2,v1). *)

Proposition this_one_counterexample :
  exists (V : Type)
         (v1 v2 : V),
    (v1, v2) = (v2, v1).
Proof.
  exists nat, 1, 1.
  reflexivity.
Qed.

(* We then use the that counterexample to prove that this_one cannot be true, i.e., not (this_one). *)

Theorem this_one_cannot_hold :
  ~ (forall (V : Type)
             (v1 v2 : V),
      (v1, v2) <> (v2, v1)).
Proof.
  intros H.
  destruct this_one_counterexample as [V' [v1' [v2' H_eq]]].
  apply H with (V := V') (v1 := v1') (v2 := v2').
  exact H_eq.
Qed.

(* that_one is a softer version of this_one as it only requires that there exists some values of v1, v2 where (v1, v2) <> (v2, v1), compared to forall values in this_one. *)

Proposition that_one :
  exists (V : Type)
         (v1 v2 : V),
    (v1, v2) <> (v2, v1).
Proof.
  exists nat, 0, 1.
  intro H.
  discriminate H.
Qed.

(* ********** *)

(* end of week-06_the-situation-so-far.v *)

