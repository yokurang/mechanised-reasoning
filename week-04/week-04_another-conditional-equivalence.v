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

Compute (evaluate_ltr (Minus (Literal 0) (Literal 2))).

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
    evaluate_ltr (Minus (Minus ae1 ae2) ae3) <>
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

  - simpl.
    unfold not.
    intro H_absurd.
    discriminate H_absurd.
Qed.

(* ********** *)

(* Task 2: Complete and prove the following conditional observational equivalence. *)

(*
My own attempt at finding a large and friendly disjunction hasn't succeeded yet.

Learning from the other conditional properties,

* the first conjunct must be
    (forall s : string,
        evaluate ae1 = Expressible_msg s)
  since ae1 is evaluated first both on the LHS and on the RHS

* then, for the same reason, we must also have
    (forall s : string,
        evaluate ae2 = Expressible_msg s)
  as well as
    (forall s : string,
        evaluate ae3 = Expressible_msg s)
  which you have listed

* otherwise, the last possibility is that they are all nats,
  and then I concur with you:
    (forall n1 n2 n3 : nat,
        evaluate ae1 = Expressible_nat n1 ->
        evaluate ae2 = Expressible_nat n2 ->
        evaluate ae3 = Expressible_nat n3 ->
        n2 + n3 <= n1)

but this enumeration doesn't look complete (the proof doesn't go through), and it is just past midnight,
time to call it a day.
*)

Proposition Minus_is_conditionally_associative_sort_of' :
  forall ae1 ae2 ae3 : arithmetic_expression,
    (forall m1 : nat,
        evaluate_ltr ae1 = Expressible_msg (Numerical_underflow m1))
    \/
      (forall m2 : nat,
        evaluate_ltr ae2 = Expressible_msg (Numerical_underflow m2))
    \/
      (forall m3 n1 n2 : nat,
        evaluate_ltr ae3 = Expressible_msg (Numerical_underflow m3) ->
        evaluate_ltr ae1 = Expressible_nat n1 ->
        evaluate_ltr ae2 = Expressible_nat n2 ->
        n2 <= n1 \/ n2 = n1 + m3)
    \/
      (forall n1 n2 n3 : nat,
          evaluate_ltr ae1 = Expressible_nat n1 ->
          evaluate_ltr ae2 = Expressible_nat n2 ->
          evaluate_ltr ae3 = Expressible_nat n3 ->
          n2 + n3 <= n1)
    ->
      evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
        evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
Admitted.

Lemma nat_lt_eureka :
  forall (n1 n2 : nat),
    n2 <= n1 ->
    (n1 <? n2) = false
  /\
    forall (n3 : nat),
      (n1 <? n2 + n3) = false
      /\
        n1 - n2 <? n3 = false.
    
Admitted.

Proposition Minus_is_conditionally_associative_sort_of :
  forall ae1 ae2 ae3 : arithmetic_expression,
    (forall m1 : nat,
        evaluate_ltr ae1 = Expressible_msg (Numerical_underflow m1))
    \/
      (forall m2 : nat,
          evaluate_ltr ae2 = Expressible_msg (Numerical_underflow m2))
    \/
      (forall n1 n2 m3 : nat,
          evaluate_ltr ae3 = Expressible_msg (Numerical_underflow m3) ->
          evaluate_ltr ae1 = Expressible_nat n1 ->
          evaluate_ltr ae2 = Expressible_nat n2 ->
        n2 <= n1 \/ n2 = n1 + m3)
    \/
      (forall n1 n2 : nat,
          evaluate_ltr ae1 = Expressible_nat n1 ->
          evaluate_ltr ae2 = Expressible_nat n2 ->
          n2 <= n1)
    ->
      evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
        evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
  Compute (
      let ae1 := Literal 2 in
      let ae2 := Literal 5  in
      let ae3 := Minus (Literal 0) (Literal 1) in
      evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
        evaluate_ltr (Minus ae1 (Plus ae2 ae3))
    ).
  intro ae1.
  induction ae1 as [n1 | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - intros ae2 ae3 [H_ae1 | [H_ae2 | [H_ae3 | H_ae1_ae2]]].
    + rewrite -> fold_unfold_evaluate_ltr_Literal in H_ae1.
      discriminate (H_ae1 n1).
    + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
      rewrite -> fold_unfold_evaluate_ltr_Literal.
      rewrite -> fold_unfold_evaluate_ltr_Plus.
      rewrite -> (H_ae2 n1).
      reflexivity.
    + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
      rewrite -> fold_unfold_evaluate_ltr_Literal.
      rewrite -> fold_unfold_evaluate_ltr_Plus.
      case (evaluate_ltr ae2) as [n2 | s2] eqn:E_a2.
      * case (n1 <? n2) as [ | ] eqn:H_lt_n1_n2.
        -- case (evaluate_ltr ae3) as [n3 | s3] eqn:E_ae3.
           ++ assert (H_ae3 := H_ae3 n1 n2 n3).
                                              


(*
          rewrite -> (H_ae3 (n2 - n1)).
           reflexivity.
        -- rewrite -> (H_ae3 n1).
           reflexivity.
      * reflexivity.
    + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
      rewrite -> fold_unfold_evaluate_ltr_Literal.
      rewrite -> fold_unfold_evaluate_ltr_Plus.
      case (evaluate_ltr ae2) as [n2 | s2] eqn:E_ae2.
      rewrite -> fold_unfold_evaluate_ltr_Literal in H_ae1_ae2.
      Check (H_ae1_ae2 n1 n2).
      assert (H_ae1_ae2 := H_ae1_ae2 n1 n2).
      assert (H_ae1_ae2 := H_ae1_ae2 eq_refl eq_refl).
      destruct (nat_lt_eureka n1 n2) as [H_lt_n1_n2 H_lt_n3].
      * exact H_ae1_ae2.
      * rewrite -> H_lt_n1_n2.
        case (evaluate_ltr ae3) as [n3 | s3] eqn:E_ae3.
        -- destruct (H_lt_n3 n3) as [H_lt_n31 H_lt_n32].
           rewrite -> H_lt_n31.
           rewrite -> H_lt_n32.
           rewrite -> (Nat.sub_add_distr n1 n2 n3).
           reflexivity.
        -- reflexivity.
      * reflexivity.
  - intros ae3 ae4.
    rewrite ->3 fold_unfold_evaluate_ltr_Minus.
    rewrite ->2 fold_unfold_evaluate_ltr_Plus.
    case (evaluate_ltr ae1) as [n1 | s1] eqn:E_ae1.
    + Check (IHae1 ae3 ae4).
      assert (IHae1 := IHae1 ae3 ae4).
*)

Qed.




(* Reminder: The treatment of errors is simplified. *)

(* ********** *)

(* end of week-04_another-conditional-equivalence.v *)
