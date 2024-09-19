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

(* Paraphrenalia *)

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

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus e1 e2 =>
    match evaluate e1 with
    | Expressible_nat n1 =>
      match evaluate e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      end
    end
  | Times e1 e2 =>
    match evaluate e1 with
    | Expressible_nat n1 =>
      match evaluate e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      end
    end
  end.

Lemma fold_unfold_evaluate_Literal :
  forall n : nat,
    evaluate (Literal n) =
      Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall e1 e2 : arithmetic_expression,
    evaluate (Plus e1 e2) =
    match evaluate e1 with
    | Expressible_nat n1 =>
      match evaluate e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      end
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Times :
  forall e1 e2 : arithmetic_expression,
    evaluate (Times e1 e2) =
    match evaluate e1 with
    | Expressible_nat n1 =>
      match evaluate e2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      end
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

(* ********** *)

Definition testcase_P_balanced : arithmetic_expression :=
  Plus (Plus (Literal 0)
             (Literal 1))
       (Plus (Literal 2)
             (Literal 3)).

Definition testcase_P_balanced_2 : arithmetic_expression :=
  Plus (Plus (Literal 4)
             (Literal 5))
       (Plus (Literal 6)
             (Literal 7)).

Definition testcase_P_left : arithmetic_expression :=
  (Plus
     (Plus
        (Plus
           (Plus
              (Literal 0)
              (Literal 1))
           (Literal 2))
        (Literal 3))
     (Literal 4)).

Definition testcase_P_right : arithmetic_expression :=
  (Plus
     (Literal 0)
     (Plus
        (Literal 1)
        (Plus
           (Literal 2)
           (Plus
              (Literal 3)
              (Literal 4))))).

Definition testcase_P_10 := Plus (Literal 1) (Literal 0).

Definition testcase_P_01 := Plus (Literal 0) (Literal 1).

Definition testcase_T_12 := Times (Literal 1) (Literal 2).

Definition testcase_T_21 := Times (Literal 2) (Literal 1).

Definition testcase_T_20 := Times (Literal 2) (Literal 0).

Definition testcase_T_02 := Times (Literal 0) (Literal 2).

Definition test_simplify_naive (candidate : arithmetic_expression -> arithmetic_expression) :=
  (eqb_arithmetic_expression
     (candidate testcase_P_balanced)
     (Plus (Literal 1) (Plus (Literal 2) (Literal 3)))) &&
    (eqb_arithmetic_expression
       (candidate testcase_P_balanced_2)
       testcase_P_balanced_2) &&
    (eqb_arithmetic_expression (candidate testcase_P_left)
       (Plus
          (Plus
             (Plus
                (Literal 1)
                (Literal 2))
             (Literal 3))
          (Literal 4))) &&
    (eqb_arithmetic_expression (candidate testcase_P_right)
       (Plus
          (Literal 1)
          (Plus
             (Literal 2)
             (Plus
                (Literal 3)
                (Literal 4))))) &&
    (eqb_arithmetic_expression (candidate testcase_P_10) (Literal 1)) &&
    (eqb_arithmetic_expression (candidate testcase_P_01) (Literal 1)) &&
    (eqb_arithmetic_expression (candidate testcase_T_12) (Literal 2)) &&
    (eqb_arithmetic_expression (candidate testcase_T_21) (Literal 2)) &&
    (eqb_arithmetic_expression (candidate testcase_T_02) (Literal 0)) &&
    (eqb_arithmetic_expression (candidate testcase_T_20) (Literal 0)).

Fixpoint simplify_naive (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
      Literal n
  | Plus ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          simplify_naive ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              simplify_naive ae1
          | _ =>
              Plus (simplify_naive ae1) (simplify_naive ae2)
          end
      end
  | Times ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          Literal 0
      | Literal 1 =>
          simplify_naive ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              Literal 0
          | Literal 1 =>
              simplify_naive ae1
          | _ =>
              Times (simplify_naive ae1) (simplify_naive ae2)
          end
      end
  end.

Compute (test_simplify_naive simplify_naive).

Lemma fold_unfold_simplify_naive_Literal :
  forall n : nat,
    simplify_naive (Literal n) =
      Literal n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_simplify_naive_Plus :
  forall ae1 ae2 : arithmetic_expression,
    simplify_naive (Plus ae1 ae2) =
      match ae1 with
      | Literal 0 =>
          simplify_naive ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              simplify_naive ae1
          | _ =>
              Plus (simplify_naive ae1) (simplify_naive ae2)
          end
      end.
Proof.
  fold_unfold_tactic simplify_naive.
Qed.

Lemma fold_unfold_simplify_naive_Times :
  forall ae1 ae2 : arithmetic_expression,
    simplify_naive (Times ae1 ae2) =
       match ae1 with
      | Literal 0 =>
          Literal 0
      | Literal 1 =>
          simplify_naive ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              Literal 0
          | Literal 1 =>
              simplify_naive ae1
          | _ =>
              Times (simplify_naive ae1) (simplify_naive ae2)
          end
      end.
Proof.
  fold_unfold_tactic simplify_naive.
Qed.

(* The naive implementation above does work.
   However, in the proof, we will have to
   consider ae1 as Literal 0, Literal 1, or anything else, and
   consider ae2 as Literal 0, Literal 1, or anything else in each of the cases of ae1.
 *)

Inductive intermediate_arithmetic_expression : Type :=
| Z : intermediate_arithmetic_expression
| W : intermediate_arithmetic_expression
| AE : arithmetic_expression -> intermediate_arithmetic_expression.
                                  
Fixpoint arithmetic_expression_of_intermediate_arithmetic_expression (iae : intermediate_arithmetic_expression) : arithmetic_expression :=
  match iae with
  | Z =>
      Literal 0
  | W =>
      Literal 1
  | AE ae =>
      ae
  end.
  
Fixpoint simplify (ae : arithmetic_expression) : intermediate_arithmetic_expression :=
  match ae with
  | Literal n =>
      match n with
      | 0 =>
          Z
      | 1 =>
          W
      | _ =>
          AE (Literal n)
      end
  | Plus ae1 ae2 =>
      match simplify ae1 with
      | Z =>
          simplify ae2
      | W =>
          match simplify ae2 with
          | Z =>
              W
          | W =>
              AE (Plus (Literal 1) (Literal 1))
          | AE ae2' =>
              AE (Plus (Literal 1) ae2')
          end
      | AE ae1' =>
          match simplify ae2 with
          | Z =>
              AE ae1'
          | W =>
              AE (Plus ae1' (Literal 1))
          | AE ae2' =>
              AE (Plus ae1' ae2')
          end
      end
  | Times ae1 ae2 =>
      match simplify ae1 with
      | Z =>
          Z
      | W =>
          simplify ae2
      | AE ae1' =>
          match simplify ae2 with
          | Z =>
              Z
          | W =>
              AE ae1'
          | AE ae2' =>
              AE (Times ae1' ae2')
          end
      end
  (*
  | Minus ae1 ae2 =>
      match simplify ae1 with
      | Z =>
          match simplify ae2 with
          | Z =>
              Z
          | W =>
              AE (Minus (Literal 0) (Literal 1))
          | AE ae2' =>
              AE (Minus (Literal 0) ae2')
          end
      | W =>
          match simplify ae2 with
          | Z =>
              W
          | W =>
              AE (Minus (Literal 1) (Literal 1))
          | AE ae2' =>
              AE (Minus (Literal 1) ae2')
          end
      | AE ae1' =>
          match simplify ae2 with
          | Z =>
              AE ae1'
          | W =>
              AE (Minus ae1' (Literal 1))
          | AE ae2' =>
              AE (Minus ae1' ae2')
          end
      end *)
  end.

Lemma fold_unfold_simplify_Literal :
  forall n : nat,
    simplify (Literal n) =
      match n with
      | 0 =>
          Z
      | 1 =>
          W
      | _ =>
          AE (Literal n)
      end.
Proof.
  fold_unfold_tactic simplify.
Qed.

Lemma fold_unfold_simplify_Plus :
  forall ae1 ae2 : arithmetic_expression,
    simplify (Plus ae1 ae2) =
      match simplify ae1 with
      | Z =>
          simplify ae2
      | W =>
          match simplify ae2 with
          | Z =>
              W
          | W =>
              AE (Plus (Literal 1) (Literal 1))
          | AE ae2' =>
              AE (Plus (Literal 1) ae2')
          end
      | AE ae1' =>
          match simplify ae2 with
          | Z =>
              AE ae1'
          | W =>
              AE (Plus ae1' (Literal 1))
          | AE ae2' =>
              AE (Plus ae1' ae2')
          end
      end.
Proof.
  fold_unfold_tactic simplify.
Qed.

Lemma fold_unfold_simplify_Times :
  forall ae1 ae2 : arithmetic_expression,
    simplify (Times ae1 ae2) =
      match simplify ae1 with
      | Z =>
          Z
      | W =>
          simplify ae2
      | AE ae1' =>
          match simplify ae2 with
          | Z =>
              Z
          | W =>
              AE ae1'
          | AE ae2' =>
              AE (Times ae1' ae2')
          end
      end.
Proof.
  fold_unfold_tactic simplify.
Qed.

Definition eqb_intermediate_arithmetic_expression (iae1 iae2 : intermediate_arithmetic_expression) :=
  match iae1 with
  | Z =>
      match iae2 with
      | Z =>
          true
      | _ =>
          false
      end
  | W =>
      match iae2 with
      | W =>
          true
      | _ =>
          false
      end
  | AE ae1 =>
      match iae2 with
      | AE ae2 =>
          eqb_arithmetic_expression ae1 ae2
      | _ =>
          false
      end
  end.

Definition test_simplify (candidate : arithmetic_expression -> intermediate_arithmetic_expression) :=
  (eqb_intermediate_arithmetic_expression (candidate testcase_P_10) W) &&
    (eqb_intermediate_arithmetic_expression (candidate testcase_P_01) W) &&
    (eqb_intermediate_arithmetic_expression (candidate testcase_T_12) (AE (Literal 2))) &&
    (eqb_intermediate_arithmetic_expression (candidate testcase_T_21) (AE (Literal 2))) &&
    (eqb_intermediate_arithmetic_expression (candidate testcase_T_20) Z) &&
    (eqb_intermediate_arithmetic_expression (candidate testcase_T_02) Z).

Compute (test_simplify simplify).

Definition test_simplify_p (candidate : arithmetic_expression -> bool) :=
  (candidate (arithmetic_expression_of_intermediate_arithmetic_expression
                (simplify testcase_P_10))) &&
    (candidate (arithmetic_expression_of_intermediate_arithmetic_expression
                  (simplify testcase_P_01))) &&
    (candidate (arithmetic_expression_of_intermediate_arithmetic_expression
                  (simplify testcase_P_balanced))) &&
    (candidate (arithmetic_expression_of_intermediate_arithmetic_expression
                  (simplify testcase_P_balanced_2))) &&
    (candidate (arithmetic_expression_of_intermediate_arithmetic_expression
                  (simplify testcase_T_02))) &&
    (candidate (arithmetic_expression_of_intermediate_arithmetic_expression
                  (simplify testcase_T_20))) &&
    (negb (candidate testcase_T_20)) &&
    (negb (candidate testcase_T_02)).

Fixpoint simplify_p (ae : arithmetic_expression) : bool :=
  match ae with
  | Literal n =>
      true
  | Plus ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          false
      | _ =>
          match ae2 with
          | Literal 0 =>
              false
          | _ =>
              (simplify_p ae1) && (simplify_p ae2)
          end
      end
  | Times ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          false
      | _ =>
          match ae2 with
          | Literal 0 =>
              false
          | _ =>
              (simplify_p ae1) && (simplify_p ae2)
          end
      end
  end.

Compute (test_simplify_p simplify_p).

(* ********** *)

(* end of midterm_simplifier.v *)
