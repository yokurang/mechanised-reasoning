(* week-02_proving-logical-properties.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 27 Aug 2023, with the propositions in Exercises 12 and 13 renamed more clearly *)
(* was: *)
(* Version of 25 Aug 2023, with the exercise numbers re-aligned with that in the lecture notes *)
(* was: *)
(* Version of 22 Aug 2023 *)

(* ********** *)

Lemma identity :
  forall A : Prop,
    A -> A.
Proof.
  intro A.
  intro H_A.
  exact H_A.
Qed.

(* ********** *)

Lemma proving_a_conjunction :
  forall A B : Prop,
    A -> B -> A /\ B.
Proof.
  intros A B H_A H_B.
  split.

  exact H_A.

  exact H_B.

  Restart.

  intros A B H_A H_B.
  split.
  { exact H_A. }
  { exact H_B. }

  Restart.

  intros A B H_A H_B.
  split.
  - exact H_A.

  - exact H_B.

  Restart.

  intros A B H_A H_B.
  Check (conj H_A H_B).
  exact (conj H_A H_B).
Qed.

(* ********** *)

Lemma proving_a_ternary_conjunction :
  forall A B C : Prop,
    A -> B -> C -> A /\ B /\ C.
Proof.
  intros A B C.
  intros H_A H_B H_C.
  split.
  - exact H_A.
  - split.
    + exact H_B.
    + exact H_C.

  Restart.

  intros A B C.
  intros H_A H_B H_C.
  exact (conj H_A (conj H_B H_C)).
Qed.

(* ********** *)

Lemma proving_a_disjunction :
  forall A B : Prop,
    A -> B -> A \/ B.
Proof.
  intros A B H_A H_B.
  left.
  exact H_A.

  Restart.

  intros A B H_A H_B.
  right.
  exact H_B.
Qed.

(* ********** *)

(* Exercise 06 *)

Lemma conjunction_is_commutative :
  forall A B : Prop,
    A /\ B <-> B /\ A.
Proof.
  intros A B.
  split.

  - intros [H_A H_B].
    exact (conj H_B H_A).

  - intros [H_B H_A].
    exact (conj H_A H_B).
Qed.

Lemma conjunction_is_commutative_aux :
  forall A B : Prop,
    A /\ B -> B /\ A.
Proof.
  intros A B [H_A H_B].
  exact (conj H_B H_A).
Qed.

Lemma conjunction_is_commutative_revisited :
  forall A B : Prop,
    A /\ B <-> B /\ A.
Proof.
  intros A B.
  split.

  - exact (conjunction_is_commutative_aux A B).

  - exact (conjunction_is_commutative_aux B A).
Qed.

(* ********** *)

(* Exercise 07 *)

Lemma conjunction_is_associative :
  forall A B C : Prop,
    A /\ (B /\ C) <-> (A /\ B) /\ C.
Proof.
Abort.

(* ********** *)

(* Exercise 08 *)

Lemma disjunction_is_commutative :
  forall A B : Prop,
    A \/ B <-> B \/ A.
Proof.
Abort.

(* ********** *)

(* Exercise 09 *)

Lemma disjunction_is_associative :
  forall A B C : Prop,
    A \/ (B \/ C) <-> (A \/ B) \/ C.
Proof.
Abort.

(* ********** *)

(* Exercise 10 *)

(* Prove that disjunction distribute over conjunction on the left and on the right. *)

Proposition disjunction_distributes_over_conjunction_on_the_left :
  forall A B C : Prop,
    A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  split.

  - intros [H_A | [H_B H_C]].

    + split.

      * left.
        exact H_A.

      * left.
        exact H_A.

    + split.

      * right.
        exact H_B.

      * right.
        exact H_C.

  - intros [[H_A | H_B] [H_A' | H_C]].

    + left.
      exact H_A.

    + left.
      exact H_A.

    + left.
      exact H_A'.

    + right.

      * split.
        exact H_B.
        exact H_C.

Qed.


Proposition disjunction_distributes_over_conjunction_on_the_right :
  forall A B C : Prop,
    (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
  intros A B C.
  split.

  - intros [[H_A H_B] | H_C].

    + split.

      * left.
        exact H_A.

      * left.
        exact H_B.

    + split.

      * right.
        exact H_C.

      * right.
        exact H_C.

  - intros [[H_A | H_C] [H_B | H_C']].

    + left.

      * split.
        exact H_A.
        exact H_B.
 
    + right.
      exact H_C'.

    + right.
      exact H_C.

    + right.
      exact H_C.

Qed.

(* ********** *)

(* Exercise 11 *)

(*
Does conjunction distribute over disjunction on the left?
And what about on the right?
*)

(* ********** *)

Proposition modus_ponens :
  forall A B : Prop,
    A -> (A -> B) -> B.
Proof.
  intros A B.
  intros H_A H_A_implies_B.
  Check (H_A_implies_B H_A).
  exact (H_A_implies_B H_A).

  Restart.
    
  intros A B.
  intros H_A H_A_implies_B.
  apply H_A_implies_B.
  exact H_A.
Qed.

(* ********** *)

Proposition modus_tollens :
  forall A B : Prop,
    ~B -> (A -> B) -> ~A.
Proof.
  intros A B.
  unfold not.
  intros H_B_implies_False H_A_implies_B H_A.
  apply H_B_implies_False.
  apply H_A_implies_B.
  exact H_A.
 
  Restart.

  intros A B.
  unfold not.
  intros H_B_implies_False H_A_implies_B H_A.
  Check (H_A_implies_B H_A).
  Check (H_B_implies_False (H_A_implies_B H_A)).
  exact (H_B_implies_False (H_A_implies_B H_A)).

  Restart.

  intros A B.
  unfold not.
  intros H_B_implies_False H_A_implies_B H_A.
  Check (modus_ponens A B).
  Check (modus_ponens A B H_A).
  Check (modus_ponens A B H_A H_A_implies_B).
  Check (H_B_implies_False (modus_ponens A B H_A H_A_implies_B)).
  exact (H_B_implies_False (modus_ponens A B H_A H_A_implies_B)).
Qed.

(* ********** *)

(* Exercise 12 *)

Proposition implication_distributes_over_conjunction_on_the_left :
  forall A B C : Prop,
    (A -> B /\ C) <-> ((A -> B) /\ (A -> C)).
Proof.
  intros A B C.
  split.

  - intros H_A_implies_B_and_C.
    split.

    * intro H_A.
      Check (H_A_implies_B_and_C H_A).
      destruct (H_A_implies_B_and_C H_A) as [H_B _].
      exact H_B.

    * intro H_A.
      destruct (H_A_implies_B_and_C H_A) as [_ H_C].
      exact H_C.

  - intros [H_A_implies_B H_A_implies_C] H_A.
    Check (H_A_implies_B H_A).
    Check (H_A_implies_C H_A).
    Check (conj (H_A_implies_B H_A) (H_A_implies_C H_A)).
    exact (conj (H_A_implies_B H_A) (H_A_implies_C H_A)).
Qed.

(* ********** *)

(* Exercise 13 *)

Proposition implication_distributes_over_disjunction_on_the_right_and_with_a_twist :
  forall A B C : Prop,
    ((A \/ B) -> C) <-> ((A -> C) /\ (B -> C)).
Proof.
  intros A B C.
  split.

  - intros H_A_or_B_implies_C.
    split.

    + intro H_A.
      apply H_A_or_B_implies_C.
      left.
      exact H_A.

    + intro H_B.
      apply H_A_or_B_implies_C.
      right.
      exact H_B.

  - intros [H_A_implies_C H_B_implies_C] [H_A | H_B].

    + Check (H_A_implies_C H_A).
      exact (H_A_implies_C H_A).

    + exact (H_B_implies_C H_B).
Qed.

(* ********** *)

(* Exercise 14 *)

Proposition contrapositive_of_implication :
  forall A B : Prop,
    (A -> B) -> ~B -> ~A.
Proof.
  intros A B.
  intros H_A_implies_B H_not_B.
  Check (modus_tollens A B H_not_B H_A_implies_B).
  exact (modus_tollens A B H_not_B H_A_implies_B).
Qed.

(* ********** *)

(* Exercise 15 *)

Proposition contrapositive_of_contrapositive_of_implication :
  forall A B : Prop,
    (~B -> ~A) -> ~~A -> ~~B.
Proof.
Abort.

(* ********** *)

(* Exercise 16 *)

Proposition double_negation :
  forall A : Prop,
    A -> ~~A.
Proof.
Abort.

(* ********** *)

(* end of week-02_proving-logical-properties.v *)
