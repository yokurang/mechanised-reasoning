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

Definition test_simplify_naive (candidate : arithmetic_expression -> arithmetic_expression) :=
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

Inductive simplified_ae : Type :=
| Z : simplified_ae
| W : simplified_ae
| Literal_sum : nat -> simplified_ae
| Plus_sum : simplified_ae -> simplified_ae -> simplified_ae
| Times_sum : simplified_ae -> simplified_ae -> simplified_ae. 

Fixpoint sum_to_expression (ams : simplified_ae) : arithmetic_expression  :=
  match ams with
  | Z => Literal 0
  | W => Literal 1
  | Literal_sum n =>
      Literal n
  | Plus_sum as1 as2 =>
      Plus (sum_to_expression as1) (sum_to_expression as2)
  | Times_sum as1 as2 =>
      Times (sum_to_expression as1) (sum_to_expression as2)
  end.

Fixpoint simplify (ae : arithmetic_expression) : simplified_ae :=
  match ae with
  | Literal n =>
      match n with
      | 0 => Z
      | 1 => W
      | _ => Literal_sum n
      end
  | Plus ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          simplify ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              simplify ae1
          | _ =>
              Plus_sum (simplify ae1) (simplify ae2)
          end
      end
  | Times ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          Z
      | Literal 1 =>
          simplify ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              Z
          | Literal 1 =>
              simplify ae1
          | _ =>
              Times_sum (simplify ae1) (simplify ae2)
          end
      end
  end.

Fixpoint eqb_simplified_ae (as1 as2 : simplified_ae) :=
  match as1 with
  | Z =>
      match as2 with
      | Z => true
      | _ => false
      end
  | W =>
      match as2 with
      | W => true
      | _ => false
      end
  | Literal_sum n1 =>
      match as2 with
      | Literal_sum n2 =>
          n1 =? n2
      | _ =>
          false
      end
  | Plus_sum as11 as12 =>
      match as2 with
      | Plus_sum as21 as22 =>
          (eqb_simplified_ae as11 as21) && (eqb_simplified_ae as12 as22)
      | _ =>
          false
      end
  | Times_sum as11 as12 =>
      match as2 with
      | Times_sum as21 as22 =>
          (eqb_simplified_ae as11 as21) && (eqb_simplified_ae as12 as22)
      | _ =>
          false
      end
  end.

Compute (eqb_simplified_ae Z Z).
Compute (eqb_simplified_ae W W).
Compute (negb (eqb_simplified_ae Z W)).
Compute (negb (eqb_simplified_ae Z (Literal_sum 4))).
Compute (negb (eqb_simplified_ae (Literal_sum 2) (Plus_sum W W))).
(* explain why this is correct *)

Definition test_simplify (candidate : arithmetic_expression -> simplified_ae) :=
  let ae1 := Plus (Literal 1) (Literal 0) in
  let ae2 := Plus (Literal 0) (Literal 1) in
  let ae3 := Times (Literal 1) (Literal 2) in
  let ae4 := Times (Literal 2) (Literal 1) in
  let ae5 := Times (Literal 2) (Literal 0) in
  let ae6 := Times (Literal 0) (Literal 2) in
  (eqb_simplified_ae (candidate ae1) W) &&
    (eqb_simplified_ae (candidate ae2) W) &&
    (eqb_simplified_ae (candidate ae3) (Literal_sum 2)) &&
    (eqb_simplified_ae (candidate ae4) (Literal_sum 2)) &&
    (eqb_simplified_ae (candidate ae5) Z) &&
    (eqb_simplified_ae (candidate ae6) Z).

Compute (test_simplify simplify).

(* ********** *)

(* end of midterm_simplifier.v *)
