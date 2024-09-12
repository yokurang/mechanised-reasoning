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

Definition test_simplifier_ltr (candidate : arithmetic_expression -> arithmetic_expression) :=
  let ae1 := Plus (Literal 1) (Literal 0) in
  let ae2 := Plus (Literal 0) (Literal 1) in
  let ae3 := Times (Literal 1) (Literal 2) in
  let ae4 := Times (Literal 2) (Literal 1) in
  let ae5 := Times (Literal 2) (Literal 0) in
  let ae6 := Times (Literal 0) (Literal 2) in
  (eqb_arithmetic_expression (candidate ae1) (Literal 1)) &&
    (eqb_arithmetic_expression (candidate ae2) (Literal 1)) &&
    (eqb_arithmetic_expression (candidate ae3) (Literal 2)) &&
    (eqb_arithmetic_expression (candidate ae4) (Literal 2)) &&
    (eqb_arithmetic_expression (candidate ae5) (Literal 0)) &&
    (eqb_arithmetic_expression (candidate ae6) (Literal 0)).

Fixpoint simplifier_ltr (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
      Literal n
  | Plus ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          simplifier_ltr ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              simplifier_ltr ae1
          | _ =>
              Plus (simplifier_ltr ae1) (simplifier_ltr ae2)
          end
      end
  | Times ae1 ae2 =>
      match ae1 with
      | Literal 0 =>
          Literal 0
      | Literal 1 =>
          simplifier_ltr ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              Literal 0
          | Literal 1 =>
              simplifier_ltr ae1
          | _ =>
              Times (simplifier_ltr ae1) (simplifier_ltr ae2)
          end
      end
  end.

Compute (test_simplifier_ltr simplifier_ltr).


Lemma fold_unfold_simplifier_ltr_Literal :
  forall n : nat,
    simplifier_ltr (Literal n) =
      Literal n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_simplifier_ltr_Plus :
  forall ae1 ae2 : arithmetic_expression,
    simplifier_ltr (Plus ae1 ae2) =
      match ae1 with
      | Literal 0 =>
          simplifier_ltr ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              simplifier_ltr ae1
          | _ =>
              Plus (simplifier_ltr ae1) (simplifier_ltr ae2)
          end
      end.
Proof.
  fold_unfold_tactic simplifier_ltr.
Qed.

Lemma fold_unfold_simplifier_ltr_Times :
  forall ae1 ae2 : arithmetic_expression,
    simplifier_ltr (Times ae1 ae2) =
       match ae1 with
      | Literal 0 =>
          Literal 0
      | Literal 1 =>
          simplifier_ltr ae2
      | _ =>
          match ae2 with
          | Literal 0 =>
              Literal 0
          | Literal 1 =>
              simplifier_ltr ae1
          | _ =>
              Times (simplifier_ltr ae1) (simplifier_ltr ae2)
          end
      end.
Proof.
  fold_unfold_tactic simplifier_ltr.
Qed.

(* The naive implementation above does work.
   However, in the proof, we will have to
   consider ae1 as Literal 0, Literal 1, or anything else, and
   consider ae2 as Literal 0, Literal 1, or anything else in each of the cases of ae1.
 *)


Inductive arithmetic_sum : Type :=
| Z : arithmetic_sum
| W : arithmetic_sum
| Literal_sum : nat -> arithmetic_sum
| Plus_sum : arithmetic_sum -> arithmetic_sum -> arithmetic_sum
| Times_sum : arithmetic_sum -> arithmetic_sum -> arithmetic_sum. 
Fixpoint sum_to_expression (ams : arithmetic_sum) : arithmetic_expression  :=
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
                                                      
Fixpoint simplify (ae : arithmetic_expression) : arithmetic_sum :=
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

Fixpoint eqb_arithmetic_sum (as1 as2 : arithmetic_sum) :=
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
          (eqb_arithmetic_sum as11 as21) && (eqb_arithmetic_sum as12 as22)
      | _ =>
          false
      end
  | Times_sum as11 as12 =>
      match as2 with
      | Times_sum as21 as22 =>
          (eqb_arithmetic_sum as11 as21) && (eqb_arithmetic_sum as12 as22)
      | _ =>
          false
      end
  end.

Compute (eqb_arithmetic_sum Z Z).
Compute (eqb_arithmetic_sum W W).
Compute (negb (eqb_arithmetic_sum Z W)).
Compute (negb (eqb_arithmetic_sum Z (Literal_sum 4))).
Compute (negb (eqb_arithmetic_sum (Literal_sum 2) (Plus_sum W W))).
(* explain why this is correct *)

Definition test_simplify (candidate : arithmetic_expression -> arithmetic_sum) :=
  let ae1 := Plus (Literal 1) (Literal 0) in
  let ae2 := Plus (Literal 0) (Literal 1) in
  let ae3 := Times (Literal 1) (Literal 2) in
  let ae4 := Times (Literal 2) (Literal 1) in
  let ae5 := Times (Literal 2) (Literal 0) in
  let ae6 := Times (Literal 0) (Literal 2) in
  (eqb_arithmetic_sum (candidate ae1) W) &&
    (eqb_arithmetic_sum (candidate ae2) W) &&
    (eqb_arithmetic_sum (candidate ae3) (Literal_sum 2)) &&
    (eqb_arithmetic_sum (candidate ae4) (Literal_sum 2)) &&
    (eqb_arithmetic_sum (candidate ae5) Z) &&
    (eqb_arithmetic_sum (candidate ae6) Z).

Compute (test_simplify simplify).

(* ********** *)

(* end of midterm_simplifier.v *)
