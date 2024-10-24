(* week-04_another-conditional-equivalence.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 26 Sep 2024 *)

(* student name: Adam Chan
   e-mail address: adam.chan@u.yale-nus.edu.sg
   student ID number: A0242453O)
 *)

(* student name: Alan Matthew Anggara
   e-mail address: alan.matthew@u.yale-nus.edu.sg
   student ID number: A0224197B
 *)

(* student name: Kim Young Il
   e-mail address: youngil.kim@u.yale-nus.edu.sg
   student ID number: A0207809Y
 *)

(* student name: Vibilan Jayanth
   e-mail address: vibilan@u.yale-nus.edu.sg
   student ID number: A0242417L
 *)

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
  case (1 <? 2 + 3) as [H_absurd | H_true].
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

Proposition Minus_is_conditionally_associative_sort_of :
  forall ae1 ae2 ae3 : arithmetic_expression,
    (forall m1 : nat,
        evaluate_ltr ae1 = Expressible_msg (Numerical_underflow m1))
    \/
      (forall m2 : nat,
          evaluate_ltr ae2 = Expressible_msg (Numerical_underflow m2))
    \/
      (forall m3 : nat,
          evaluate_ltr ae3 = Expressible_msg (Numerical_underflow m3)
          /\
            forall (n1 n2 : nat),
              n2 <= n1 \/ n2 = n1 + m3 ->
              evaluate_ltr ae1 = Expressible_nat n1 ->
              evaluate_ltr ae2 = Expressible_nat n2)
    \/
      (forall n1 n2 : nat,
          evaluate_ltr ae1 = Expressible_nat n1 ->
          evaluate_ltr ae2 = Expressible_nat n2 ->
          n2 <= n1 /\
            (forall n3 : nat,
                n2 + n3 <= n1 ->
                evaluate_ltr ae3 = Expressible_nat n3))
    <->
      evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
        evaluate_ltr (Minus ae1 (Plus ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  split.
  - intro H.
    destruct H as [E_ae1_m | [ E_ae2_m | [ E_ae3_m | E_ae_n ]]].
  + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
    rewrite -> (E_ae1_m 1).
    reflexivity.
  + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
    rewrite -> fold_unfold_evaluate_ltr_Plus.
    case (evaluate_ltr ae1) as [n1 | m1] eqn:E_ae1.
    * rewrite -> (E_ae2_m 1).
      reflexivity.
    * reflexivity.
  + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
    rewrite -> fold_unfold_evaluate_ltr_Plus.
    case (evaluate_ltr ae1) as [n1 | m1] eqn:E_ae1.
    * case (evaluate_ltr ae2) as [n2 | m2] eqn:E_ae2.
      -- case (evaluate_ltr ae3) as [n3 | m3] eqn:E_ae3.
         destruct (E_ae3_m 1) as [H_absurd H_qq].
         ++ discriminate H_absurd.
         ++ 
      -- destruct (E_ae3_m 1) as [E_ae3_m' H_ae1_ae2].
         rewrite -> E_ae3_m'.
        Check (H_ae1_ae2 n1 n2 eq_refl eq_refl).
        destruct (H_ae1_ae2 n1 n2 eq_refl eq_refl) as [H_lte_n2_n1 | H_eq_n2_Sn1].
        ++ Search (_ <? _).
           Check (Nat.ltb_ge n1 n2).
           destruct (Nat.ltb_ge n1 n2) as [_ H_lt_n1_n2].
           rewrite -> (H_lt_n1_n2 H_lte_n2_n1).
           reflexivity.
        -- rewrite -> H_eq_n2_Sn1.
           rewrite -> Nat.add_1_r.
           Search (_ <? _).
           destruct (Nat.ltb_lt n1 (S n1)) as [_ H_lt_n1_Sn1].
           rewrite -> (H_lt_n1_Sn1 (Nat.lt_succ_diag_r n1)).
           Search (S _ - _ = _).
           Check (Nat.sub_succ_l n1 n1 (Nat.le_refl n1)).
           rewrite -> (Nat.sub_succ_l n1 n1 (Nat.le_refl n1)).
           rewrite -> (Nat.sub_diag n1).
           reflexivity.
      * reflexivity.
    + reflexivity.
  - rewrite ->3 fold_unfold_evaluate_ltr_Minus.
    rewrite -> fold_unfold_evaluate_ltr_Plus.
    case (evaluate_ltr ae1) as [n1 | m2] eqn:E_ae1.
    + case (evaluate_ltr ae2) as [n2 | m2] eqn:E_ae2.
      * case (evaluate_ltr ae3) as [n3 | m3] eqn:E_ae3.
        -- destruct (E_ae_n n1 n2 eq_refl eq_refl) as [H_lte_n2_n1 H_n3].
           destruct (Nat.ltb_ge n1 n2) as [_ H_lt_n1_n2].
           rewrite -> (H_lt_n1_n2 H_lte_n2_n1).
           destruct (Nat.ltb_ge n1 (n2 + n3)) as [_ H_lt_n1_n2n3].
           rewrite -> (H_lt_n1_n2n3 (H_n3 n3 eq_refl)).
           destruct (Nat.ltb_ge (n1 - n2) n3) as [_ H_lt_n3_n1n2].
           Search (_ <= _ - _).
           Check (Nat.le_add_le_sub_l n2 n1 n3 (H_n3 n3 eq_refl)).
           assert (H_lte_n3_n1n2 := (Nat.le_add_le_sub_l n2 n1 n3 (H_n3 n3 eq_refl))).
           Check (H_lt_n3_n1n2 H_lte_n3_n1n2).
           rewrite -> (H_lt_n3_n1n2 H_lte_n3_n1n2).
           rewrite -> Nat.sub_add_distr.
           reflexivity.
        -- destruct (E_ae_n n1 n2 eq_refl eq_refl) as [H_lte_n2_n1 _].
           destruct (Nat.ltb_ge n1 n2) as [_ H_lt_n1_n2].
           rewrite -> (H_lt_n1_n2 H_lte_n2_n1).
           reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

Proposition Minus_is_conditionally_associative_sort_of_backward :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate_ltr (Minus (Minus ae1 ae2) ae3) =
      evaluate_ltr (Minus ae1 (Plus ae2 ae3)) <->
      (forall m1 : nat,
          evaluate_ltr ae1 = Expressible_msg (Numerical_underflow m1))
      \/
        (forall m2 : nat,
            evaluate_ltr ae2 = Expressible_msg (Numerical_underflow m2))
      \/
        (forall n1 n2 m3 : nat,
            n2 <= n1 \/ n2 = n1 + m3 ->
            evaluate_ltr ae1 = Expressible_nat n1 ->
            evaluate_ltr ae2 = Expressible_nat n2 ->
            evaluate_ltr ae3 = Expressible_msg (Numerical_underflow m3))
      \/
        (forall n1 n2 n3 : nat,
            n2 <= n1 /\ n2 + n3 <= n1 ->
            evaluate_ltr ae1 = Expressible_nat n1 ->
            evaluate_ltr ae2 = Expressible_nat n2 ->
            evaluate_ltr ae3 = Expressible_nat n3).
Proof.
  intros ae1 ae2 ae3.
  split.
  - intros _.
    case (evaluate_ltr ae1) as [n1 | m1] eqn:E_ae1.
    + case (evaluate_ltr ae2) as [n2 | m2] eqn:E_ae2.
      * case (evaluate_ltr ae3) as [n3 | m3] eqn:E_ae3.
        -- right; right; right.
           intros n1 n2 n3.
           reflexivity.
        -- right; right; left.
           case m3 as [m3].
           exists n1, n2, m3.
           intros _ _ _.
           reflexivity.
      * right; left.
        case m2 as [m2].
        exists m2.
        reflexivity.
    + left.
      case m1 as [m1].
      exists m1.
      reflexivity.

  - intro H.
    destruct H as [ E_ae1_m | [ E_ae2_m | [ E_ae3_m | E_ae_n ]]].
    + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
      destruct E_ae1_m as [m1 E_ae1_m].
      rewrite -> (E_ae1_m).
      reflexivity.
    + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
      rewrite -> fold_unfold_evaluate_ltr_Plus.
      case (evaluate_ltr ae1) as [n1 | m1] eqn:E_ae1.
      * destruct E_ae2_m as [m2 E_ae2_m].
        rewrite -> E_ae2_m.
        reflexivity.
      * reflexivity.
    + rewrite ->3 fold_unfold_evaluate_ltr_Minus.
      rewrite -> fold_unfold_evaluate_ltr_Plus.
      case (evaluate_ltr ae1) as [n1 | m1] eqn:E_ae1.
      * case (evaluate_ltr ae2) as [n2 | m2] eqn:E_ae2.
        -- destruct E_ae3_m as [_ _ _ H_ae1_ae2].
                rewrite -> E_ae3_m'.

Qed.

(* ********** *)

(* end of week-04_another-conditional-equivalence.v *)
