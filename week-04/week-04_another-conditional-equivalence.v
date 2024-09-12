(* week-04_another-conditional-equivalence.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 05 Sep 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Simpler error messages than string encoding. *)

Inductive msg : Type :=
  Numerical_underflow : nat -> msg.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : msg -> expressible_value.

Fixpoint evaluate_ltr (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus e1 e2 =>
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Minus e1 e2 =>
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (Numerical_underflow (n2 - n1))
        else Expressible_nat (n1 - n2)               
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  end.

Lemma fold_unfold_evaluate_ltr_Literal :
  forall n : nat,
    evaluate_ltr (Literal n) =
    Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Plus :
  forall e1 e2 : arithmetic_expression,
    evaluate_ltr (Plus e1 e2) =
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Minus :
  forall e1 e2 : arithmetic_expression,
    evaluate_ltr (Minus e1 e2) =
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (Numerical_underflow (n2 - n1))
        else Expressible_nat (n1 - n2)               
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

(* ********** *)

(* Task 1: Prove the following observational inequivalence. *)

Proposition Minus_is_not_associative_sort_of :
  exists ae1 ae2 ae3 : arithmetic_expression,
    evaluate_ltr (Minus (Minus ae1 ae2) ae3)
    <>
    evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
  exists (Literal 1).
  exists (Literal 2).
  exists (Literal 3).
  rewrite ->2 fold_unfold_evaluate_ltr_Minus.
  rewrite ->2 fold_unfold_evaluate_ltr_Literal.
  Search ( _ < S _ ). (* Nat.lt_1_2: *)
  Search ( _ <? _ = _).
  destruct (Nat.ltb_lt 1 2) as [_ H_1_2].
  rewrite -> (H_1_2 Nat.lt_1_2).
  clear H_1_2.
  rewrite -> fold_unfold_evaluate_ltr_Minus.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  rewrite -> fold_unfold_evaluate_ltr_Plus.
  rewrite ->2 fold_unfold_evaluate_ltr_Literal.
  Search (_ < _ -> _).
  case (1 <? 2 +3) as [H_absurd | H_true].

  - simpl.
    unfold not.
    intro H_absurd.
    injection H_absurd as one_equals_four.
    discriminate one_equals_four.

  - unfold not.
    intro H_absurd.
    discriminate H_absurd.
Qed.

(* ********** *)

(* Task 2: Complete and prove the following conditional observational equivalence. *)

Proposition Minus_is_conditionally_associative_sort_of :
  forall ae1 ae2 ae3 : arithmetic_expression,
  exists n : nat,
    evaluate_ltr (Minus ae1 ae2) = Expressible_nat n
    <->
      evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
      evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  split.
  intros [n [H_n_left H_n_right]].

(* Reminder: The treatment of errors is simplified. *)

(* ********** *)

(* end of week-04_another-conditional-equivalence.v *)
