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


Inductive arithmetic_expressionp : Type :=
  Literalp : nat -> arithmetic_expressionp
| Plusp : arithmetic_expressionp -> arithmetic_expressionp -> arithmetic_expressionp
| Plusp_right_Literal : arithmetic_expressionp -> arithmetic_expressionp -> arithmetic_expressionp
| Plusp_right_Plusp : arithmetic_expressionp -> arithmetic_expressionp -> arithmetic_expressionp
| Plusp_right_Minusp : arithmetic_expressionp -> arithmetic_expressionp -> arithmetic_expressionp
| Minusp : arithmetic_expressionp -> arithmetic_expressionp -> arithmetic_expressionp.

Definition super_refactored_rightp_aux (ae : arithmetic_expression) : arithmetic_expressionp :=
  arithmetic_expression_fold arithmetic_expressionp Literalp Plusp Minusp ae.


Compute (super_refactored_rightp_aux (Plus (Literal 2) (Literal 3))).


Fixpoint super_refactored_rightp (ae : arithmetic_expression) : bool :=
  match ae with
  | Literal n =>
      true
  | Plus ae1 ae2 =>
      match (super_refactored_rightp_aux ae1) with
      | Literalp =>
          true
      | Plusp aep1 aep2
            
   
  end.

Fixpoint super_refactored_rightp' (ae : arithmetic_expression) : bool :=
  match ae with
    Literal n =>
      true
  | Plus ae1 ae2 =>
      match ae1 with
        Literal n1 =>
          super_refactored_rightp' ae2
      | Plus ae11 ae12 =>
          false
      | Minus ae11 ae12 =>
          super_refactored_rightp' ae11
          &&
            super_refactored_rightp' ae12
          &&
            super_refactored_rightp' ae2
      end
  | Minus ae1 ae2 =>
      super_refactored_rightp' ae1
      &&
        super_refactored_rightp' ae2
  end.


(* soundness: *)

Lemma super_refactoring_right_preserves_super_refactored_rightp_aux :
  forall (ae a : arithmetic_expression),
    super_refactored_rightp (super_refactor_right_aux ae a) = super_refactored_rightp (Plus ae a).
Proof.
   intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ];
    intro a.
  - rewrite -> fold_unfold_super_refactor_right_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_right_aux_Plus.
    rewrite -> (IHae1 (super_refactor_right_aux ae2 a)).
    rewrite -> fold_unfold_super_refactored_rightp_Plus.
    rewrite -> (IHae2 a).
    case (super_refactored_rightp ae1) as [t1 | f1] eqn:Refp_ae1.
    + rewrite ->2 fold_unfold_super_refactored_rightp_Plus.
      rewrite -> Refp_ae1.
      case (evaluate ae2) as [n2 | s2] eqn:E_ae2.
      * case (evaluate a) as [n | s] eqn:E_a.
        -- rewrite -> Nat.add_assoc.
           reflexivity.
        -- reflexivity.
      * reflexivity.
    + rewrite ->2 fold_unfold_evaluate_Plus.
      rewrite -> E_ae1.
      reflexivity.
  - rewrite -> fold_unfold_refactor_aux_Minus.
    rewrite ->2 fold_unfold_evaluate_Plus.
    rewrite ->2 fold_unfold_evaluate_Minus.
    rewrite -> (IHae1 (Literal 0)).
    rewrite -> (IHae2 (Literal 0)).
    rewrite ->2 fold_unfold_evaluate_Plus.
    case (evaluate ae1) as [n1 | s1] eqn:E_ae1.
    + case (evaluate ae2) as [n2 | s2] eqn:E_ae2.
      * rewrite -> fold_unfold_evaluate_Literal.
        rewrite ->2 Nat.add_0_r.
        reflexivity.
      * rewrite -> fold_unfold_evaluate_Literal.
        reflexivity.
    + reflexivity.
  Admitted.

Theorem super_refactor_right_yields_super_refactored_right_results :
  forall ae : arithmetic_expression,
    super_refactored_rightp (super_refactor_right ae) = true.
Proof.
  intro ae.
  destruct (super_refactor_right_yields_super_refactored_right_results_aux ae) as [H_sr _].
  exact H_sr.
  Restart.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - rewrite -> fold_unfold_super_refactor_right_Literal.
    rewrite -> fold_unfold_super_refactored_rightp_Literal.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_right_Plus.
    Check (super_refactored_rightp_eureka).
    Check (super_refactored_rightp_eureka ae1 ae2).
    rewrite -> (super_refactored_rightp_eureka ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    rewrite -> andb_diag.
    reflexivity.
 - rewrite -> fold_unfold_super_refactor_right_Minus.
   rewrite -> fold_unfold_super_refactored_rightp_Minus.
   rewrite -> IHae1.
   rewrite -> IHae2.
   rewrite -> andb_diag.
   reflexivity.
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

(*
Theorem super_refactor_right_yields_super_refactored_right_results_revisited :
  forall ae : arithmetic_expression,
    super_refactored_rightp (arithmetic_expression_from_arithmetic_expression_right (super_refactor_right' ae)) = true.
*)

(* ********** *)

(* \end{NEW} *)

(* end of week-04_refactoring-typefully.v *)
