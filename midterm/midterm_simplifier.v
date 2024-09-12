(* midterm_simplifier.v *)

(* MR 2024 - YSC 2024-2025, Sem1 *)
(* Version of 12 Sep 2024 *)

(* ********** *)

(* student name: Adam Chan
   e-mail address: adam.chan@u.yale-nus.edu.sg
   student ID number: A0242453O)
 *)

(* student name: Alan Matthew Anggara
   e-mail address: alan.matthew@u.yale-nus.edu.sg
   student ID number: A0207754B
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
| Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Fixpoint eqb_arithmetic_expression (ae1 ae2 : arithmetic_expression) : bool :=
  match ae1 with
  | Literal n1 =>
      match ae2 with
      | Literal n2 =>
          Nat.eqb n1 n2
      | _ =>
          false
      end
  | Plus ae11 ae12 =>
      match ae2 with
      | Plus ae21 ae22 =>
          eqb_arithmetic_expression ae11 ae21 && eqb_arithmetic_expression ae12 ae22
      | _ =>
          false
      end
  | Times ae11 ae12 =>
      match ae2 with
      | Times ae21 ae22 =>
          eqb_arithmetic_expression ae11 ae21 && eqb_arithmetic_expression ae12 ae22
      | _ =>
          false
      end
  end.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value.

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
      end
    end
  | Times e1 e2 =>
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      end
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
      end
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Times :
  forall e1 e2 : arithmetic_expression,
    evaluate_ltr (Times e1 e2) =
    match evaluate_ltr e1 with
    | Expressible_nat n1 =>
      match evaluate_ltr e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      end
    end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

(* ********** *)

Definition test_case1 : arithmetic_expression :=
  Plus (Plus (Literal 0)
             (Literal 1))
       (Plus (Literal 2)
             (Literal 3)).

Definition test_case2 : arithmetic_expression :=
  Plus (Plus (Literal 4)
             (Literal 5))
       (Plus (Literal 6)
             (Literal 7)).

Definition test_case3 : arithmetic_expression :=
  (Plus
     (Plus
        (Plus
           (Plus
              (Literal 0)
              (Literal 1))
           (Literal 2))
        (Literal 3))
     (Literal 4)).

Definition test_case4 : arithmetic_expression := (Plus (Literal 0) (Plus (Literal 1) (Plus (Literal 2) (Plus (Literal 3) (Literal 4))))).

Definition test_case5 : arithmetic_expression := (Plus (Plus (Literal 0) (Literal 1)) (Plus (Literal 2) (Literal 3))).

Definition test_case6 := Plus (Literal 1) (Literal 0).

Definition test_case7 := Plus (Literal 0) (Literal 1).

Definition test_case8 := Times (Literal 1) (Literal 2).

Definition test_case9 := Times (Literal 2) (Literal 1).

Definition test_case10 := Times (Literal 2) (Literal 0).

Definition test_case11 := Times (Literal 0) (Literal 2).

Definition test_simplifier (candidate : arithmetic_expression -> arithmetic_expression) :=
  (eqb_arithmetic_expression (candidate test_case1)
       (Plus (Literal 1) (Plus (Literal 2) (Literal 3)))) &&
    (eqb_arithmetic_expression (candidate test_case2) test_case2) &&
    (eqb_arithmetic_expression (candidate test_case3)
       (Plus
          (Plus
             (Plus
                (Literal 1)
                (Literal 2))
             (Literal 3))
          (Literal 4))) &&
    (eqb_arithmetic_expression (candidate test_case4)
       (Plus (Literal 1)
          (Plus (Literal 2)
             (Plus (Literal 3) (Literal 4))))) &&
    (eqb_arithmetic_expression (candidate test_case5)
       (Plus (Literal 1) (Plus (Literal 2) (Literal 3)))) &&
    (eqb_arithmetic_expression (candidate test_case6) (Literal 1)) &&
    (eqb_arithmetic_expression (candidate test_case7) (Literal 1)) &&
    (eqb_arithmetic_expression (candidate test_case8) (Literal 2)) &&
    (eqb_arithmetic_expression (candidate test_case9) (Literal 2)) &&
    (eqb_arithmetic_expression (candidate test_case10) (Literal 0)) &&
    (eqb_arithmetic_expression (candidate test_case11) (Literal 0)).

Fixpoint simplifier (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
      Literal n
  | Plus ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          simplifier ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              simplifier ae1
          | _ =>
              Plus (simplifier ae1) (simplifier ae2)
          end
      end
  | Times ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          Literal 0
      | Literal 1 =>
          simplifier ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              Literal 0
          | Literal 1 =>
              simplifier ae1
          | _ =>
              Times (simplifier ae1) (simplifier ae2)
          end
      end
  end.

Compute (test_simplifier simplifier).

(* ********** *)

Definition 

Fixpoint simplifiedp (ae : arithmetic_expression) : bool :=
  match ae with
  | Literal n =>
  ...
  | Plus ae1 ae2 =>
  ...
  | Times ae1 ae2 =>
  ...
  end.

(* ********** *)



(* ********** *)

(* end of midterm_simplifier.v *)
