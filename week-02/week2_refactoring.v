(* week2_refactoring.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 22 Aug 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 -- caveat emptor *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          end
      end
  | Minus ae1 ae2 =>
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          end
      end
  end.

Lemma fold_unfold_evaluate_Literal :
  forall (n : nat),
    evaluate (Literal n) =
      Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Plus ae1 ae2) =
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          end
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Minus ae1 ae2) =
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          end
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Definition expressible_value_eqb (ev1 ev2 : expressible_value) : bool :=
  match ev1 with
  | Expressible_nat n1 =>
      match ev2 with
      | Expressible_nat n2 =>
          Nat.eqb n1 n2
      | Expressible_msg s2 =>
          false
      end
  | Expressible_msg s1 =>
      match ev2 with
      | Expressible_nat n2 =>
          false
      | Expressible_msg s2 =>
          String.eqb s1 s2
      end
  end.

Proposition Literal_0_is_neutral_for_Plus_on_the_right :
  forall ae : arithmetic_expression,
    evaluate (Plus ae (Literal 0)) = evaluate ae.
Proof.
  intro ae.
  rewrite -> fold_unfold_evaluate_Plus.
  rewrite -> fold_unfold_evaluate_Literal.
  case (evaluate ae) as [n | s].
  - rewrite -> (Nat.add_0_r n).
    reflexivity.
  - reflexivity.
Qed.

(* ********** *)

Fixpoint refactor_aux (ae a : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Plus (Literal n) a
  | Plus ae1 ae2 =>
    refactor_aux ae1 (refactor_aux ae2 a)
  | Minus ae1 ae2 =>
    Plus (Minus (refactor_aux ae1 (Literal 0)) (refactor_aux ae2 (Literal 0))) a
  end.

Lemma fold_unfold_refactor_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    refactor_aux (Literal n) a =
    Plus (Literal n) a.
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Lemma fold_unfold_refactor_aux_Plus :
  forall ae1 ae2 a : arithmetic_expression,
    refactor_aux (Plus ae1 ae2) a =
    refactor_aux ae1 (refactor_aux ae2 a).
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Lemma fold_unfold_refactor_aux_Minus :
  forall ae1 ae2 a : arithmetic_expression,
    refactor_aux (Minus ae1 ae2) a =
    Plus (Minus (refactor_aux ae1 (Literal 0)) (refactor_aux ae2 (Literal 0))) a.
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Definition refactor (ae : arithmetic_expression) : arithmetic_expression :=
  refactor_aux ae (Literal 0).

(* Task 1: What does refactor do?
   Capture your observations into a unit-test function. *)

Compute (let ae := Literal 2 in
         refactor ae).
(* If the arithmetic expression is a Literal, the Literal 0 is added to it on the right. This does not change the result as 0 is neutral on the right for addition *)

Compute (let ae := Plus (Literal 2) (Literal 1) in
         refactor ae).
(* If the arithmetic expression is a Plus, the Literal 0 is added to right of the second subexpression. This does not change the result as 0 is neutral on the right for addition *)

Compute (let ae := Minus (Literal 2) (Literal 1) in
         refactor ae).
(* If the arithmetic expression is a Minus, the Literal 0 is added on the right to the overall expression and both of its subexpressions. This does not change the result as 0 is neutral on the right for addition *)

Compute (let ae := Plus
                     (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         refactor ae).
(* When there are many Plus nodes, we can see a pattern in the tree that is being produced. Instead of a balanced tree, we get a tree that is "flattened" by associating to the right. *)

Compute (let ae := Minus
                     (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         refactor ae).
(* When there are many Minus nodes, we see a similar pattern in the resulting tree but in th eopposite direction. The tree is not fully flattened but associates to the left with Plus with 0. *)

Compute (let ae1 := Literal 1 in
         let ae2 := Plus (ae1) (ae1) in
         let ae3 := Minus (ae1) (ae1) in
         let ae4 := Plus (ae2) (ae3) in
         (expressible_value_eqb (evaluate ae1) (evaluate (refactor ae1)))
         && (expressible_value_eqb (evaluate ae2) (evaluate (refactor ae2)))
         && (expressible_value_eqb (evaluate ae3) (evaluate (refactor ae3)))
         && (expressible_value_eqb (evaluate ae4) (evaluate (refactor ae4)))
        ).

(* ********** *)

(* Task 2: Prove that refactoring preserves evaluation. *)

(*
Compute (let ae := Minus (Plus (Literal 3) (Literal 4)) (Literal 2) in
         let a := (Minus (Literal 5) (Literal 4)) in
    evaluate (refactor_aux ae a)) = evaluate (Plus ae a).
*)

Lemma refactoring_preserves_evaluation_aux :
  forall (ae a : arithmetic_expression),
    evaluate (refactor_aux ae a) = evaluate (Plus ae a).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ];
    intro a.
  - rewrite -> fold_unfold_refactor_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite -> (IHae1 (refactor_aux ae2 a)).
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> (IHae2 a).
    case (evaluate ae1) as [n1 | s1] eqn:E_ae1.
    + rewrite ->3 fold_unfold_evaluate_Plus.
      rewrite -> E_ae1.
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
    rewrite -> IHae1, IHae2.
    rewrite ->2 fold_unfold_evaluate_Plus.
    case (evaluate ae1) as [n1 | s1] eqn:E_ae1.
    + case (evaluate ae2) as [n2 | s2] eqn:E_ae2.
      * rewrite -> fold_unfold_evaluate_Literal.
        rewrite ->2 Nat.add_0_r.
        reflexivity.
      * rewrite -> fold_unfold_evaluate_Literal.
        reflexivity.
    + reflexivity.
Qed.

Lemma refactoring_preserves_evaluation_aux_alt :
  forall ae a : arithmetic_expression,
    (forall s1 : string,
        evaluate ae = Expressible_msg s1 ->
        evaluate (refactor_aux ae a) = Expressible_msg s1)
    /\
      (forall n1 : nat,
          evaluate ae = Expressible_nat n1 ->
          forall s2 : string,
            evaluate a = Expressible_msg s2 ->
            evaluate (refactor_aux ae a) = Expressible_msg s2)
    /\
      (forall n1 : nat,
          evaluate ae = Expressible_nat n1 ->
          forall n2 : nat,
            evaluate a = Expressible_nat n2 ->
            evaluate (refactor_aux ae a) = Expressible_nat (n1 + n2)).
Proof.
  intros ae a.
Admitted.

Theorem refactoring_preserves_evaluation :
  forall ae : arithmetic_expression,
    evaluate (refactor ae) = evaluate ae.
Proof.
  intro ae.
  unfold refactor.
  rewrite -> (refactoring_preserves_evaluation_aux ae (Literal 0)).
  rewrite -> Literal_0_is_neutral_for_Plus_on_the_right.
  reflexivity.
Qed.

(* ********** *)

Fixpoint super_refactor (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n 
  | Plus ae1 ae2 =>
    super_refactor_aux ae1 (super_refactor ae2)
  | Minus ae1 ae2 =>
    Minus (super_refactor ae1) (super_refactor ae2)
  end
  with super_refactor_aux (ae1 a : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
    | Literal n =>
      Plus (Literal n) a
    | Plus ae1 ae2 =>
      super_refactor_aux ae1 (super_refactor_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus (Minus (super_refactor ae1) (super_refactor ae2)) a
    end.

(* ***** *)

Lemma fold_unfold_super_refactor_Literal :
  forall (n : nat),
    super_refactor (Literal n) =
      (Literal n).
Proof.
  fold_unfold_tactic super_refactor.
Qed.

Lemma fold_unfold_super_refactor_Plus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor (Plus ae1 ae2) =
    super_refactor_aux ae1 (super_refactor ae2).
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Lemma fold_unfold_super_refactor_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor (Minus ae1 ae2) =
    Minus (super_refactor ae1) (super_refactor ae2).
Proof.
  fold_unfold_tactic refactor_aux.
Qed.

Lemma fold_unfold_super_refactor_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    super_refactor_aux (Literal n) a =
      Plus (Literal n) a.
Proof.
  fold_unfold_tactic super_refactor_aux.
Qed.

Lemma fold_unfold_super_refactor_aux_Plus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_aux (Plus ae1 ae2) a =
      super_refactor_aux ae1 (super_refactor_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_aux.
Qed.

Lemma fold_unfold_super_refactor_aux_Minus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_aux (Minus ae1 ae2) a =
      Plus (Minus (super_refactor ae1) (super_refactor ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_aux.
Qed.

(* ***** *)

(* Task 3: What does super_refactor do?
   Capture your observations into a unit-test function. *)

Compute (let ae := Minus
                     (Minus (Literal 2) (Literal 1))
                     (Minus (Literal 4) (Literal 3)) in
         super_refactor ae).

(* Task 4: Prove that super-refactoring preserves evaluation. *)

Lemma super_refactoring_preserves_evaluation_aux :
  forall ae : arithmetic_expression,
    (evaluate (super_refactor ae) = evaluate ae)
    /\
      (forall a : arithmetic_expression,
          (evaluate (super_refactor_aux ae a) = evaluate (Plus ae a))).
Proof.
  intro ae.
  induction ae as [ n
                  | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
                  | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux] ]; split.
  - rewrite -> fold_unfold_super_refactor_Literal.
    reflexivity.
  - intro a.
    rewrite -> fold_unfold_super_refactor_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_Plus.
    Check (IHae1_aux (super_refactor ae2)).
    rewrite -> (IHae1_aux (super_refactor ae2)).
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> IHae2.
    rewrite -> fold_unfold_evaluate_Plus.
    reflexivity.
  - intro a.
    rewrite -> fold_unfold_super_refactor_aux_Plus.
    rewrite -> (IHae1_aux (super_refactor_aux ae2 a)).
    rewrite -> fold_unfold_evaluate_Plus.
    case (evaluate ae1) as [n1 | s1] eqn:E_ae1.
    + rewrite -> IHae2_aux.
      rewrite ->3 fold_unfold_evaluate_Plus.
      rewrite -> E_ae1.
      case (evaluate ae2) as [n2 | s2] eqn:E_ae2.
      * case (evaluate a) as [n | s] eqn:E_a.
        -- rewrite -> Nat.add_assoc. (* Key aha! moment, mention in report *)
           reflexivity.
        -- reflexivity.
      * reflexivity.
    + rewrite ->2 fold_unfold_evaluate_Plus.
      rewrite -> E_ae1.
      reflexivity.
  - rewrite -> fold_unfold_super_refactor_Minus.
    rewrite ->2 fold_unfold_evaluate_Minus.
    rewrite -> IHae1.
    case (evaluate ae1) as [n1 | s1] eqn:E_ae1.
    + rewrite -> IHae2.
      reflexivity.
    + reflexivity.
  - intro a.
    rewrite -> fold_unfold_super_refactor_aux_Minus.
    rewrite ->2 fold_unfold_evaluate_Plus.
    rewrite ->2 fold_unfold_evaluate_Minus.
    rewrite -> IHae1, IHae2.
    case (evaluate ae1) as [n1 | s1] eqn:E_ae1.
    + case (evaluate ae2) as [n2 | s2] eqn:E_ae2.
      * reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

Theorem super_refactoring_preserves_evaluation :
  forall ae : arithmetic_expression,
    evaluate (super_refactor ae) = evaluate ae.
Proof.
  intro ae.
  Check (super_refactoring_preserves_evaluation_aux ae).
  destruct (super_refactoring_preserves_evaluation_aux ae) as [ H_sr H_sr_aux ].
  exact H_sr.
Qed.
    
(* ********** *)

(* Preview of Week 03 (out of scope of Week 02, but maybe some of you are Very Fast): *)

(* Design and implement a function
     simplify : arithmetic_expression -> arithmetic_expression
   that exploits the following properties:

   forall ae : arithmetic_expression, evaluate (Plus (Literal 0) ae) = evaluate ae

   forall ae : arithmetic_expression, evaluate (Plus ae (Literal 0)) = evaluate ae

   forall ae : arithmetic_expression, evaluate (Minus ae (Literal 0)) = evaluate ae

   (assuming that the last property holds -- does it?)

   So in a simplified expression,

   * there should be no occurrence of Literal 0 as a first argument of Plus,

   * there should be no occurrence of Literal 0 as a second argument of Plus, and

   * there should be no occurrence of Literal 0 as a second argument of Minus.

   Misc. questions:

   * is simplify idempotent?

   * does simplification preserve evaluation?
*)

(* ********** *)

(* end of week2_refactoring.v *)
