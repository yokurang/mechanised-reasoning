(* week-04_refactoring-typefully.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 05 Sep 2024 *)

(* ********** *)

(* The new points below are delimited with \begin{NEW} and \end{NEW}. *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Fixpoint arithmetic_expression_fold (T : Type) (Literal_case : nat -> T) (Plus_case : T -> T -> T) (Minus_case : T -> T -> T) (ae : arithmetic_expression) : T :=
  match ae with
    Literal n =>
      Literal_case n
  | Plus ae1 ae2 =>
      Plus_case
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae1)
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae2)
  | Minus ae1 ae2 =>
      Minus_case
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae1)
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae2)
  end.

Lemma fold_unfold_arithmetic_expression_fold_Literal :
  forall (T : Type)
    (Literal_case : nat -> T)
    (Plus_case : T -> T -> T)
    (Minus_case : T -> T -> T)
    (n : nat),
    arithmetic_expression_fold T Literal_case Plus_case Minus_case (Literal n) =
      Literal_case n.
Proof.
    fold_unfold_tactic arithmetic_expression_fold.
Qed.

Lemma fold_unfold_arithmetic_expression_fold_Plus :
  forall (T : Type)
    (Literal_case : nat -> T)
    (Plus_case : T -> T -> T)
    (Minus_case : T -> T -> T)
    (ae1 ae2 : arithmetic_expression),
    arithmetic_expression_fold T Literal_case Plus_case Minus_case (Plus ae1 ae2) =
      Plus_case
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae1)
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae2).
Proof.
  fold_unfold_tactic arithmetic_expression_fold.
Qed.

Lemma fold_unfold_arithmetic_expression_fold_Minus :
    forall (T : Type)
      (Literal_case : nat -> T)
      (Plus_case : T -> T -> T)
      (Minus_case : T -> T -> T)
      (ae1 ae2 : arithmetic_expression),
      arithmetic_expression_fold T Literal_case Plus_case Minus_case (Minus ae1 ae2) =
        Minus_case
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae1)
        (arithmetic_expression_fold T Literal_case Plus_case Minus_case ae2).
Proof.
  fold_unfold_tactic arithmetic_expression_fold.
Qed.

(* \begin{NEW} *)
(* Simpler error messages than string encoding. *)

Inductive msg : Type :=
  Numerical_underflow : nat -> msg.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : msg -> expressible_value.
(* \end{NEW} *)

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

Fixpoint eqb_arithmetic_expression (ae1 ae2 : arithmetic_expression) : bool :=
  match ae1 with
  | Literal n1 =>
      match ae2 with
      | Literal n2 => Nat.eqb n1 n2
      | _ => false
      end
  | Plus ae11 ae12 =>
      match ae2 with
      | Plus ae21 ae22 =>
          eqb_arithmetic_expression ae11 ae21 && eqb_arithmetic_expression ae12 ae22
      | _ => false
      end
  | Minus ae11 ae12 =>
      match ae2 with
      | Minus ae21 ae22 =>
          eqb_arithmetic_expression ae11 ae21 && eqb_arithmetic_expression ae12 ae22
      | _ => false
      end
  end.

(* ********** *)

Fixpoint super_refactor_right (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
    Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_right_aux ae1 (super_refactor_right ae2)
  | Minus ae1 ae2 =>
    Minus (super_refactor_right ae1) (super_refactor_right ae2)
  end
  with super_refactor_right_aux (ae1 a : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
      Literal n =>
      Plus (Literal n) a
    | Plus ae1 ae2 =>
      super_refactor_right_aux ae1 (super_refactor_right_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus (Minus (super_refactor_right ae1) (super_refactor_right ae2)) a
    end.

Lemma fold_unfold_super_refactor_right_Literal :
  forall n : nat,
    super_refactor_right (Literal n) = Literal n.
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_Plus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_right (Plus ae1 ae2) =
      super_refactor_right_aux ae1 (super_refactor_right ae2).
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_right (Minus ae1 ae2) =
      Minus (super_refactor_right ae1) (super_refactor_right ae2).
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    super_refactor_right_aux (Literal n) a = Plus (Literal n) a.
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Plus :
  forall ae1 ae2 a : arithmetic_expression,
    super_refactor_right_aux (Plus ae1 ae2) a =
      super_refactor_right_aux ae1 (super_refactor_right_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Minus :
  forall ae1 ae2 a : arithmetic_expression,
    super_refactor_right_aux (Minus ae1 ae2) a =
      Plus (Minus (super_refactor_right ae1) (super_refactor_right ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

(* ********** *)

(* \begin{NEW} *)

(* Task 1: What does super_refactor_right do?
   Capture the effect of super_refactor_right into a predicate. *)

Inductive intermediate_expression : Type :=
| ExpPlus : intermediate_expression
| ExpOK : intermediate_expression
| ExpKO : intermediate_expression.

Fixpoint intermediate_expression_from_arithmetic_expression (ae : arithmetic_expression) :
  intermediate_expression :=
  match ae with
  | Literal n =>
      ExpOK
  | Plus ae1 ae2 =>
      match intermediate_expression_from_arithmetic_expression ae1 with
      | ExpPlus =>
          ExpKO
      | ExpOK =>
          match intermediate_expression_from_arithmetic_expression ae2 with
          | ExpPlus =>
              ExpPlus
          | ExpOK =>
              ExpPlus
          | ExpKO =>
              ExpKO
          end
      | ExpKO =>
          ExpKO
      end
  | Minus ae1 ae2 =>
      match intermediate_expression_from_arithmetic_expression ae1 with
      | ExpPlus =>
          match intermediate_expression_from_arithmetic_expression ae2 with
          | ExpPlus =>
              ExpOK
          | ExpOK =>
              ExpOK
          | ExpKO =>
              ExpKO
          end
      | ExpOK =>
          match intermediate_expression_from_arithmetic_expression ae2 with
          | ExpPlus =>
              ExpOK
          | ExpOK =>
              ExpOK
          | ExpKO =>
              ExpKO
          end
      | ExpKO =>
          ExpKO
      end
  end.

Lemma fold_unfold_intermediate_expression_from_arithmetic_expression_Literal :
  forall n : nat,
    intermediate_expression_from_arithmetic_expression (Literal n) = ExpOK.
Proof.
  fold_unfold_tactic intermediate_expression_from_arithmetic_expression.
Qed.

Lemma fold_unfold_intermediate_expression_from_arithmetic_expression_Plus :
  forall ae1 ae2 : arithmetic_expression,
    intermediate_expression_from_arithmetic_expression (Plus ae1 ae2) =
      match intermediate_expression_from_arithmetic_expression ae1 with
      | ExpPlus =>
          ExpKO
      | ExpOK =>
          match intermediate_expression_from_arithmetic_expression ae2 with
          | ExpPlus =>
              ExpPlus
          | ExpOK =>
              ExpPlus
          | ExpKO =>
              ExpKO
          end
      | ExpKO =>
          ExpKO
      end.
Proof.
  fold_unfold_tactic intermediate_expression_from_arithmetic_expression.
Qed.

Lemma fold_unfold_intermediate_expression_from_arithmetic_expression_Minus :
  forall ae1 ae2 : arithmetic_expression,
    intermediate_expression_from_arithmetic_expression (Minus ae1 ae2) =
      match intermediate_expression_from_arithmetic_expression ae1 with
      | ExpPlus =>
          match intermediate_expression_from_arithmetic_expression ae2 with
          | ExpPlus =>
              ExpOK
          | ExpOK =>
              ExpOK
          | ExpKO =>
              ExpKO
          end
      | ExpOK =>
          match intermediate_expression_from_arithmetic_expression ae2 with
          | ExpPlus =>
              ExpOK
          | ExpOK =>
              ExpOK
          | ExpKO =>
              ExpKO
          end
      | ExpKO =>
          ExpKO
      end.
Proof.
  fold_unfold_tactic intermediate_expression_from_arithmetic_expression.
Qed.

Definition test_ae1 := Literal 0.
Definition test_ae2 := Plus (Plus (Literal 0) (Literal 0)) (Literal 0). (* should KO *)
Definition test_ae3 := Plus (Literal 0) (Plus (Literal 0) (Literal 0)).   
Definition test_ae4 := Plus (Literal 0) (Literal 0).
Definition test_ae5 := Plus (Literal 0) test_ae2. (* should KO *)
Definition test_ae6 := Minus (Plus (Literal 5) (Literal 0)) (Plus (Literal 2) (Literal 0)).
Definition test_ae7 := Minus (Plus (Literal 5) (Literal 0)) (Literal 0).
Definition test_ae8 := Minus (Plus (Literal 5) (Literal 0)) test_ae2. (* should KO *)
Definition test_ae9 := Minus (Literal 10) (Plus (Literal 2) (Literal 0)).
Definition test_ae10 := Minus (Literal 10) (Literal 0).
Definition test_ae11 := Minus (Literal 10) test_ae2. (* should KO *)
Definition test_ae12 := Minus test_ae2 test_ae1. (* should KO *)             

Definition eqb_intermediate_expression (ie : intermediate_expression) : bool :=
  match ie with
  | ExpPlus =>
      true
  | ExpOK =>
      true
  | ExpKO =>
      false
  end.

Definition test_intermediate_expression_from_arithmetic_expression
  (candidate : arithmetic_expression -> intermediate_expression) : bool :=
  eqb_intermediate_expression (candidate test_ae1)
  &&
    eqb_intermediate_expression (candidate test_ae3)
  &&
    eqb_intermediate_expression (candidate test_ae4)
  &&
    eqb_intermediate_expression (candidate test_ae6)
  &&
    eqb_intermediate_expression (candidate test_ae7)
  &&
    eqb_intermediate_expression (candidate test_ae9)
  &&
    eqb_intermediate_expression (candidate test_ae10)
  &&
    (negb (eqb_intermediate_expression (candidate test_ae2))
     ||
       (eqb_intermediate_expression (candidate test_ae5))
     ||
       (eqb_intermediate_expression (candidate test_ae8))
     ||
       (eqb_intermediate_expression (candidate test_ae11))).
                                     
Compute (test_intermediate_expression_from_arithmetic_expression
           intermediate_expression_from_arithmetic_expression).

(* add more test cases here vibilan ? *)
Definition test_super_refactored_rightp (candidate : arithmetic_expression -> bool) :=
  let false_ae1 := (Plus (Plus (Literal 1) (Literal 2))
                      (Plus (Literal 3) (Literal 4))) in
  let true_ae1 := Literal 1 in
  let true_ae2 := Plus (Literal 1) (Literal 2) in
  let true_ae3 :=  Minus (Literal 2) (Literal 1) in
  (candidate true_ae1) &&
    (candidate true_ae2) &&
    (candidate true_ae3) &&
    (negb (candidate false_ae1)).

Definition super_refactored_rightp (ae : arithmetic_expression) : bool :=
  match intermediate_expression_from_arithmetic_expression ae with
    ExpPlus =>
      true
    | ExpOK =>
      true
    | ExpKO =>
      false
  end.

Compute (test_super_refactored_rightp super_refactored_rightp).

Theorem applying_disjunction_left :
  forall A B C : Prop,
    (A \/ B -> C) -> A -> C.
Proof.
  intros A B C H_AB_C H_A.
  apply H_AB_C.
  left.
  exact H_A.
Qed.

Theorem applying_disjunction_right :
  forall A B C : Prop,
    (A \/ B -> C) -> B -> C.
Proof.
  intros A B C H_AB_C H_B.
  apply H_AB_C.
  right.
  exact H_B.
Qed.

Lemma super_refactor_right_yields_super_refactored_rightp_results_aux :
  forall ae : arithmetic_expression,
    (intermediate_expression_from_arithmetic_expression
       (super_refactor_right ae) = ExpPlus
     \/
       intermediate_expression_from_arithmetic_expression
         (super_refactor_right ae) = ExpOK)
    /\
      (forall a : arithmetic_expression,
          (intermediate_expression_from_arithmetic_expression a = ExpPlus
           \/
             intermediate_expression_from_arithmetic_expression a = ExpOK) ->
          intermediate_expression_from_arithmetic_expression
            (super_refactor_right_aux ae a) = ExpPlus
          \/
            intermediate_expression_from_arithmetic_expression
              (super_refactor_right_aux ae a) = ExpOK).
Proof.
  intro ae.
  induction ae as [ n
                  | ae1 [[sr_ae1_Plus | sr_ae1_OK ] sr_aux_ae1]
                      ae2 [[sr_ae2_Plus | sr_ae2_OK] sr_aux_ae2]
                  | ae1 [[sr_ae1_Plus | sr_ae1_OK] sr_aux_ae1]
                      ae2 [[sr_ae2_Plus | sr_ae2_OK] sr_aux_ae2]].
  - split.
    { right.
      rewrite -> fold_unfold_super_refactor_right_Literal.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Literal.
      reflexivity. }
    { intro a.
      rewrite -> fold_unfold_super_refactor_right_aux_Literal.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Literal.
      intros [H_Plus | H_OK].
      + rewrite -> H_Plus.
        left.
        reflexivity.
      + rewrite -> H_OK.
        left.
        reflexivity.
    }
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Plus.
      Check (applying_disjunction_left).
      Check (sr_aux_ae1 (super_refactor_right ae2)).
      Check (applying_disjunction_left
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_Plus).
      exact (applying_disjunction_left
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_Plus).
    }
    
    { intros a [H_a_Plus | H_a_OK].
      - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (applying_disjunction_left).
        Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
       Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
        assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                            intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
        { apply sr_aux_ae2. left. exact H_a_Plus. }
        destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
        { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
        {  exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). }
      - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
         assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                             intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
         { apply sr_aux_ae2. right. exact H_a_OK. }
         destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
         { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
          { exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). } }
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Plus.
      Check (applying_disjunction_right
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_OK).
      exact (applying_disjunction_right
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_OK). }
    { intros a [H_a_Plus | H_a_OK].
      - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (applying_disjunction_left).
        Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
       Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
        assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                            intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
        { apply sr_aux_ae2. left. exact H_a_Plus. }
        destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
        { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
        {  exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). }
      - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
         assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                             intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
         { apply sr_aux_ae2. right. exact H_a_OK. }
         destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
         { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
          { exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). } }
  - split.
     { rewrite -> fold_unfold_super_refactor_right_Plus.
      Check (applying_disjunction_left
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_Plus).
      exact (applying_disjunction_left
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_Plus). }
     { intros a [H_a_Plus | H_a_OK].
       - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
         Check (applying_disjunction_left).
         Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
       Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
        assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                            intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
        { apply sr_aux_ae2. left. exact H_a_Plus. }
        destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
        { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
        {  exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). }
        - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
         assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                             intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
         { apply sr_aux_ae2. right. exact H_a_OK. }
         destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
         { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
          { exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). } }
  - split.
     { rewrite -> fold_unfold_super_refactor_right_Plus.
      Check (applying_disjunction_right
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_OK).
      exact (applying_disjunction_right
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpPlus)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right ae2) = ExpOK)
               (intermediate_expression_from_arithmetic_expression
                  (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpPlus \/
                  intermediate_expression_from_arithmetic_expression
                    (super_refactor_right_aux ae1 (super_refactor_right ae2)) = ExpOK)
               (sr_aux_ae1 (super_refactor_right ae2))
               sr_ae2_OK). }
    { intros a [H_a_Plus | H_a_OK].
      - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (applying_disjunction_left).
        Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
       Check (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))).
        assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                            intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
        { apply sr_aux_ae2. left. exact H_a_Plus. }
        destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
        { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)
                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
        {  exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). }
      - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
         assert (H_ae2_a : intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus \/
                             intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK).
         { apply sr_aux_ae2. right. exact H_a_OK. }
         destruct H_ae2_a as [H_ae2_a_Plus | H_ae2_a_OK].
         { exact (applying_disjunction_left
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                 (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                        (super_refactor_right_aux ae2 a)) = ExpPlus
                  \/
                    intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right_aux ae2 a)) = ExpOK)

                 (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                 H_ae2_a_Plus). }
          { exact (applying_disjunction_right
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpPlus)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae2 a) = ExpOK)
                    (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right_aux ae2 a)) = ExpPlus
                     \/
                       intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                             (super_refactor_right_aux ae2 a)) = ExpOK)
                    (sr_aux_ae1 (super_refactor_right_aux ae2 a))
                    H_ae2_a_OK). } }
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Minus.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
      rewrite -> sr_ae1_Plus.
      rewrite -> sr_ae2_Plus.
      right.
      reflexivity. }
    { intros a [H_a_Plus | H_a_OK].
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_Plus.
        rewrite -> sr_ae2_Plus.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_Plus.
        rewrite -> sr_ae2_Plus.
        rewrite -> H_a_OK.
        left.
        reflexivity. }
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Minus.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
      rewrite -> sr_ae1_Plus.
      rewrite -> sr_ae2_OK.
      right.
      reflexivity. }
    { intros a [H_a_Plus | H_a_OK].
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_Plus.
        rewrite -> sr_ae2_OK.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_Plus.
        rewrite -> sr_ae2_OK.
        rewrite -> H_a_OK.
        left.
        reflexivity. }
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Minus.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
      rewrite -> sr_ae1_OK.
      rewrite -> sr_ae2_Plus.
      right.
      reflexivity. }
    { intros a [H_a_Plus | H_a_OK].
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_OK.
        rewrite -> sr_ae2_Plus.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_OK.
        rewrite -> sr_ae2_Plus.
        rewrite -> H_a_OK.
        left.
        reflexivity. }
  - split.
        { rewrite -> fold_unfold_super_refactor_right_Minus.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
      rewrite -> sr_ae1_OK.
      rewrite -> sr_ae2_OK.
      right.
      reflexivity. }
    { intros a [H_a_Plus | H_a_OK].
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_OK.
        rewrite -> sr_ae2_OK.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      - rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_OK.
        rewrite -> sr_ae2_OK.
        rewrite -> H_a_OK.
        left.
        reflexivity. }
Qed.

Theorem super_refactor_right_yields_super_refactored_rightp_results :
    forall ae : arithmetic_expression,
      super_refactored_rightp (super_refactor_right ae) = true.
 Proof.
   intro ae.
   unfold super_refactored_rightp.
   case ae as [ n | ae1 ae2 | ae1 ae2 ] eqn:C_ae.
   - rewrite -> fold_unfold_super_refactor_right_Literal.
     rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Literal.
     reflexivity.
   - rewrite -> fold_unfold_super_refactor_right_Plus.
     Check (super_refactor_right_yields_super_refactored_rightp_results_aux ae1).
     destruct (super_refactor_right_yields_super_refactored_rightp_results_aux ae1) as [[H_sr_ae1_Plus | H_sr_ae1_OK] H_a1].
     Check (H_a1 (super_refactor_right ae2)).
     assert (H_a1 := H_a1 (super_refactor_right ae2)).
     { Check (super_refactor_right_yields_super_refactored_rightp_results_aux ae2).
       destruct (super_refactor_right_yields_super_refactored_rightp_results_aux ae2) as [[H_sr_ae2_Plus | H_sr_ae2_OK] H_a2].
       - Check (applying_disjunction_left
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                         (super_refactor_right ae2)) = ExpPlus
                   \/
                     intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right ae2)) = ExpOK)
                  H_a1
                  H_sr_ae2_Plus).
         assert (H_ie2_Plus_OK :=
                   (applying_disjunction_left
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                         (super_refactor_right ae2)) = ExpPlus
                   \/
                     intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right ae2)) = ExpOK)
                  H_a1
                  H_sr_ae2_Plus)).
         destruct H_ie2_Plus_OK as [H_ie2_Plus | H_ie2_OK].
         + rewrite -> H_ie2_Plus.
           reflexivity.
         + rewrite -> H_ie2_OK.
           reflexivity.
       - Check (applying_disjunction_right
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                         (super_refactor_right ae2)) = ExpPlus
                   \/
                     intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right ae2)) = ExpOK)
                  H_a1
                  H_sr_ae2_OK).
         assert (H_ie2_Plus_OK :=
                  (applying_disjunction_right
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                         (super_refactor_right ae2)) = ExpPlus
                   \/
                     intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right ae2)) = ExpOK)
                  H_a1
                  H_sr_ae2_OK)).
         destruct H_ie2_Plus_OK as [H_ie2_Plus | H_ie2_OK].
         + rewrite -> H_ie2_Plus.
           reflexivity.
         + rewrite -> H_ie2_OK.
           reflexivity. }
      { Check (super_refactor_right_yields_super_refactored_rightp_results_aux ae2).
       destruct (super_refactor_right_yields_super_refactored_rightp_results_aux ae2) as [[H_sr_ae2_Plus | H_sr_ae2_OK] H_a2].
        - assert (H_a1 := H_a1 (super_refactor_right ae2)).
          Check (applying_disjunction_left
                   (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                   (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                   (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right ae2)) = ExpPlus
                    \/
                      intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                            (super_refactor_right ae2)) = ExpOK)
                   H_a1
                   H_sr_ae2_Plus).
         assert (H_ie2_Plus_OK :=
                   (applying_disjunction_left
                   (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                   (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                   (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                          (super_refactor_right ae2)) = ExpPlus
                    \/
                      intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                            (super_refactor_right ae2)) = ExpOK)
                   H_a1
                   H_sr_ae2_Plus)).
         destruct H_ie2_Plus_OK as [H_ie2_Plus | H_ie2_OK].
         + rewrite -> H_ie2_Plus.
           reflexivity.
         + rewrite -> H_ie2_OK.
           reflexivity.
        - assert (H_a1 := H_a1 (super_refactor_right ae2)).
          Check (applying_disjunction_right
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                         (super_refactor_right ae2)) = ExpPlus
                   \/
                     intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right ae2)) = ExpOK)
                  H_a1
                  H_sr_ae2_OK).
         assert (H_ie2_Plus_OK :=
                  (applying_disjunction_right
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpPlus)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right ae2) = ExpOK)
                  (intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                         (super_refactor_right ae2)) = ExpPlus
                   \/
                     intermediate_expression_from_arithmetic_expression (super_refactor_right_aux ae1
                                                                           (super_refactor_right ae2)) = ExpOK)
                  H_a1
                  H_sr_ae2_OK)).
         destruct H_ie2_Plus_OK as [H_ie2_Plus | H_ie2_OK].
         + rewrite -> H_ie2_Plus.
           reflexivity.
         + rewrite -> H_ie2_OK.
           reflexivity. }
   - rewrite -> fold_unfold_super_refactor_right_Minus.
     rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
     Check (super_refactor_right_yields_super_refactored_rightp_results_aux ae1).
     destruct (super_refactor_right_yields_super_refactored_rightp_results_aux ae1) as [[H_sr_ae1_Plus | H_sr_ae1_OK] H_a1].
     { destruct (super_refactor_right_yields_super_refactored_rightp_results_aux ae2) as [[H_sr_ae2_Plus | H_sr_ae2_OK] H_a2].
       - rewrite -> H_sr_ae1_Plus.
         rewrite -> H_sr_ae2_Plus.
         reflexivity.
       - rewrite -> H_sr_ae1_Plus.
         rewrite -> H_sr_ae2_OK.
         reflexivity. }
     { destruct (super_refactor_right_yields_super_refactored_rightp_results_aux ae2) as [[H_sr_ae2_Plus | H_sr_ae2_OK] H_a2].
       - rewrite -> H_sr_ae1_OK.
         rewrite -> H_sr_ae2_Plus.
         reflexivity.
       - rewrite -> H_sr_ae1_OK.
         rewrite -> H_sr_ae2_OK.
         reflexivity. }
 Qed.

(* A typeful take: characterizing refactored expressions with a type. *)

Inductive arithmetic_expression_right : Type :=
  Literal_right : nat -> arithmetic_expression_right
| Plus_right_Literal : nat -> arithmetic_expression_right -> arithmetic_expression_right
| Plus_right_Minus : arithmetic_expression_right * arithmetic_expression_right -> arithmetic_expression_right -> arithmetic_expression_right
| Minus_right : arithmetic_expression_right -> arithmetic_expression_right -> arithmetic_expression_right.

Fixpoint arithmetic_expression_from_arithmetic_expression_right (aer : arithmetic_expression_right) : arithmetic_expression :=
  match aer with
    Literal_right n =>
    Literal n
  | Plus_right_Literal n1 aer2 =>
    Plus (Literal n1) (arithmetic_expression_from_arithmetic_expression_right aer2)    
  | Plus_right_Minus (aer11, aer12) aer2 =>
    Plus
      (Minus
         (arithmetic_expression_from_arithmetic_expression_right aer11)
         (arithmetic_expression_from_arithmetic_expression_right aer12))
      (arithmetic_expression_from_arithmetic_expression_right aer2)
  | Minus_right aer1 aer2 =>
    Minus
      (arithmetic_expression_from_arithmetic_expression_right aer1)
      (arithmetic_expression_from_arithmetic_expression_right aer2)
  end.

Lemma fold_unfold_arithmetic_expression_right_Literal_right :
  

Fixpoint super_refactor_right' (ae : arithmetic_expression) : arithmetic_expression_right :=
  match ae with
    Literal n =>
    Literal_right n
  | Plus ae1 ae2 =>
    super_refactor_right'_aux ae1 (super_refactor_right' ae2)
  | Minus ae1 ae2 =>
    Minus_right (super_refactor_right' ae1) (super_refactor_right' ae2)
  end
  with super_refactor_right'_aux (ae1 : arithmetic_expression) (a : arithmetic_expression_right) : arithmetic_expression_right :=
    match ae1 with
      Literal n =>
      Plus_right_Literal n a
    | Plus ae1 ae2 =>
      super_refactor_right'_aux ae1 (super_refactor_right'_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus_right_Minus (super_refactor_right' ae1, super_refactor_right' ae2) a
    end.

Theorem super_refactor_right_yields_super_refactored_right_results_revisited :
  forall ae : arithmetic_expression,
    super_refactored_rightp (arithmetic_expression_from_arithmetic_expression_right (super_refactor_right' ae)) = true.
Admitted.
(* ********** *)

(* \end{NEW} *)

(* end of week-04_refactoring-typefully.v *)
