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

Compute (let ae := Literal 1 in
         refactor ae).

Compute (let ae := Literal 0 in
         evaluate (refactor ae)).

Compute (let ae := Literal 1 in
         (refactor (refactor ae))).

Compute (let ae := Literal 1 in
         evaluate (refactor (refactor ae))).

(* If the arithmetic expression is a Literal, the Literal 0 is added to it on the right.
   This does not change the result as 0 is neutral on the right for addition *)

Compute (let ae := Plus (Literal 1) (Literal 2) in
         refactor ae).

Compute (let ae := Plus (Literal 1) (Literal 2) in
         refactor (refactor ae)).

(* If the arithmetic expression is a Plus, the Literal 0 is added to right of the second subexpression.
   This does not change the result as 0 is neutral on the right for addition *)

Compute (let ae := Minus (Literal 2) (Literal 1) in
         refactor ae).

(* If the arithmetic expression is a Minus, the Literal 0 is added on the right to the overall expression and both of its subexpressions.
   This does not change the result as 0 is neutral on the right for addition *)

Compute (let ae := Plus
                     (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         refactor ae).

(*      +
       / \
      1   +
         / \
        2   +
           / \
          3   +
             / \
            4   0
*)

(* When there are many Plus nodes, we can see a pattern in the tree that is being produced
   Instead of a balanced tree, we get a tree that is "flattened" by associating to the right. *)

Compute (let ae := Minus
                     (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         refactor ae).

Compute (let ae := Minus
                     (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         refactor (refactor ae)).

Compute (let ae := Minus
                     (Plus (Literal 1) (Literal 2))
                     (Literal 3) in
         refactor ae).

(*             +
              / \
        ->   -   0
            / \ 
           +   +
          / \ 3 0
         1   +
            / \
           2   0

 *)

(* When there are many Minus nodes, we don't see a clear pattern, but we can see that the "flattened" binary trees are being appended to each other, with a 0 on the RHS.
. *)

Compute (let ae1 := Literal 1 in
         let ae2 := Plus (ae1) (ae1) in
         let ae3 := Minus (ae1) (ae1) in
         let ae4 := Plus (ae2) (ae3) in
         (expressible_value_eqb (evaluate ae1) (evaluate (refactor ae1)))
         && (expressible_value_eqb (evaluate ae2) (evaluate (refactor ae2)))
         && (expressible_value_eqb (evaluate ae3) (evaluate (refactor ae3)))
         && (expressible_value_eqb (evaluate ae4) (evaluate (refactor ae4)))).

(* ********** *)

(* Task 2: Prove that refactoring preserves evaluation. *)

Compute (let ae := Minus (Plus (Literal 3) (Literal 4)) (Literal 2) in
         let a := (Minus (Literal 5) (Literal 4)) in
         evaluate (refactor_aux ae a) = evaluate (Plus ae a)).

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
Qed.

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

Proposition equivalence_of_the_two_lemmas_for_refactor :
  forall ae : arithmetic_expression,
    (forall s : string,
        evaluate ae = Expressible_msg s ->
        forall a : arithmetic_expression,
          evaluate (refactor_aux ae a) = Expressible_msg s)
    /\
      (forall (n : nat)
              (s : string),
          evaluate ae = Expressible_nat n ->
          forall a : arithmetic_expression,
            evaluate a = Expressible_msg s ->
            evaluate (refactor_aux ae a) = Expressible_msg s)
    /\
      (forall n1 n2 : nat,
          evaluate ae = Expressible_nat n1 ->
          forall a : arithmetic_expression,
            evaluate a = Expressible_nat n2 ->
            evaluate (refactor_aux ae a) = Expressible_nat (n1 + n2))
    <->
      forall a : arithmetic_expression,
        evaluate (refactor_aux ae a) = evaluate (Plus ae a).
Proof.
  intro ae.
  split.
  - intros [E_s [E_n_s E_n_n]] a.
    rewrite -> fold_unfold_evaluate_Plus.
    case (evaluate ae) as [ n | s ] eqn:E_ae;
      case (evaluate a) as [ n' | s' ] eqn:E_a.
    + Check (E_n_n n n' (eq_refl (Expressible_nat n)) a E_a).
      exact (E_n_n n n' (eq_refl (Expressible_nat n)) a E_a).
    + Check (E_n_s n s' (eq_refl (Expressible_nat n)) a E_a).
      exact (E_n_s n s' (eq_refl (Expressible_nat n)) a E_a).
    + Check (E_s s (eq_refl (Expressible_msg s)) a).
      exact (E_s s (eq_refl (Expressible_msg s)) a).
    + Check (E_s s (eq_refl (Expressible_msg s)) a).
      exact (E_s s (eq_refl (Expressible_msg s)) a).
  - intro E. 
    split.
      { intros s E_ae_s a.
        rewrite -> E.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_ae_s.
        reflexivity.
      }
      split.
      { intros n' s E_ae_n' a E_a_s.
        rewrite -> E.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_ae_n'.
        rewrite -> E_a_s.
        reflexivity.
      }
      { intros n1 n2 E_ae_n a E_a_n.
        rewrite -> E.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_ae_n.
        rewrite -> E_a_n.
        reflexivity.
      }
Qed.

(* ***** *)

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
          (eqb_arithmetic_expression ae11 ae21) && (eqb_arithmetic_expression ae12 ae22)
      | _ =>
          false
      end
  | Minus ae11 ae12 =>
      match ae2 with
      | Minus ae21 ae22 =>
          (eqb_arithmetic_expression ae11 ae21) && (eqb_arithmetic_expression ae12 ae22)
      | _ =>
          false
      end
  end.

Compute (eqb_arithmetic_expression (Literal 1) (Literal 1)).
Compute (eqb_arithmetic_expression (Literal 1) (Literal 2)).
Compute (eqb_arithmetic_expression (Plus (Literal 0) (Literal 1)) (Literal 1)).
Compute (eqb_arithmetic_expression (Literal 1) (Minus (Literal 1) (Literal 0))).
Compute (eqb_arithmetic_expression (Minus (Literal 1) (Literal 0)) ((Minus (Literal 1) (Literal 0)))).
Compute (eqb_arithmetic_expression (Minus (Literal 0) (Literal 1)) ((Minus (Literal 0) (Literal 1)))).

Proposition refactor_is_never_idempotent :
  forall (ae : arithmetic_expression),
      refactor ae <> refactor (refactor ae).
Proof.
  intro ae.
  unfold refactor.
  case ae as [ n | ae1 ae2 | ae1 ae2 ].
  - rewrite -> fold_unfold_refactor_aux_Literal.
    rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite ->2 fold_unfold_refactor_aux_Literal.
    Check (eqb_arithmetic_expression (Plus (Literal n) (Literal 0)) (Plus (Literal n) (Plus (Literal 0)(Literal 0)))).
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
  fold_unfold_tactic super_refactor.
Qed.

Lemma fold_unfold_super_refactor_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor (Minus ae1 ae2) =
      Minus (super_refactor ae1) (super_refactor ae2).
Proof.
  fold_unfold_tactic super_refactor.
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

Compute (let ae := Literal 2 in
         super_refactor ae).

Compute (let ae := Literal 2 in
         super_refactor (super_refactor ae)).

Compute (let ae := Literal 2 in
         evaluate (super_refactor ae)).

Compute (let ae := Literal 2 in
         (evaluate (super_refactor (super_refactor ae)))).

(* If the arithmetic expression is a Literal, Does nothing, surprisingly *)

Compute (let ae := Plus (Literal 2) (Literal 1) in
         super_refactor ae).

Compute (let ae := Plus (Literal 2) (Literal 1) in
         super_refactor (super_refactor ae)).

Compute (let ae := Plus (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3)(Literal 4)) in
         super_refactor (super_refactor ae)).

(* If the arithmetic expression is a Plus of two literals, nothing changes, if the ae is a chain of Pluses, a right-skewed binary tree, this time no Literal 0 in the nil case. *)

Compute (let ae := Minus (Literal 2) (Literal 1) in
         super_refactor ae).

Compute (let ae := Minus (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3)(Literal 4)) in
         super_refactor ae).

Compute (let ae := Minus (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3)(Literal 4)) in
         super_refactor ae).

(* Minus of two expressios does nothing, original expression is preserved. *)

Compute (let ae := Plus
                     (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         super_refactor ae).

(*      +
       / \
      1   +
         / \
        2   +
           / \
          3   4
*)

(* When there are many Plus nodes, we can see a pattern in the tree that is being produced
   Instead of a balanced tree, we get a tree that is "flattened" by associating to the right and the nil
case accumulator is the right-most leaf of the original binary tree *)

Compute (let ae := Minus
                     (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         super_refactor ae).

Compute (let ae := Minus
                     (Plus (Literal 1) (Literal 2))
                     (Literal 3) in
         super_refactor ae).

(*      ->   - 
            / \ 
           +   3
          / \ 
         1   2

*)

Compute (let ae := Minus
                     (Minus (Literal 2) (Literal 1))
                     (Minus (Literal 4) (Literal 3)) in
         super_refactor ae).

Compute (let ae := Minus
                     (Minus (Literal 2) (Literal 1))
                     (Minus (Literal 4) (Literal 3)) in
         super_refactor (super_refactor ae)).

Compute (let ae := Minus
                     (Minus (Literal 2) (Literal 1))
                     (Minus (Literal 4) (Literal 3)) in
         evaluate (super_refactor ae)).

Compute (let ae := Minus
                     (Minus (Literal 2) (Literal 3))
                     (Minus (Literal 4) (Literal 3)) in
         evaluate (super_refactor_aux ae (Literal 0))).

(* Minus is similar to list_append, (Literal 0) as the accumulator *)

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
                  | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux] ];
    split.
  - rewrite -> fold_unfold_super_refactor_Literal.
    reflexivity.
  - intro a.
    rewrite -> fold_unfold_super_refactor_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_super_refactor_Plus.
    rewrite -> (IHae1_aux (super_refactor ae2)).
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> IHae2.
    rewrite <- fold_unfold_evaluate_Plus.
    reflexivity.
  - intro a.
    rewrite -> fold_unfold_super_refactor_aux_Plus.
    rewrite -> (IHae1_aux (super_refactor_aux ae2 a)).
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> IHae2_aux.
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
  - rewrite -> fold_unfold_super_refactor_Minus.
    rewrite ->2 fold_unfold_evaluate_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - intro a.
    rewrite -> fold_unfold_super_refactor_aux_Minus.
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> fold_unfold_evaluate_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    rewrite <- fold_unfold_evaluate_Minus.
    rewrite <- fold_unfold_evaluate_Plus.
    reflexivity.
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

Proposition equivalence_of_the_two_lemmas_for_super_refactor :
  forall ae : arithmetic_expression,
    (forall s : string,
        evaluate ae = Expressible_msg s ->
        forall a : arithmetic_expression,
          (evaluate (super_refactor ae) = Expressible_msg s)
          /\
            evaluate (super_refactor_aux ae a) = Expressible_msg s)
    /\
      (forall (n : nat)
              (s : string),
          evaluate ae = Expressible_nat n ->
          forall a : arithmetic_expression,
            evaluate a = Expressible_msg s ->
            (evaluate (super_refactor ae) = Expressible_nat n)
            /\
              evaluate (super_refactor_aux ae a) = Expressible_msg s)
    /\
      (forall n1 n2 : nat,
          evaluate ae = Expressible_nat n1 ->
          forall a : arithmetic_expression,
            evaluate a = Expressible_nat n2 ->
            (evaluate (super_refactor ae) = Expressible_nat n1)
            /\
              evaluate (super_refactor_aux ae a) = Expressible_nat (n1 + n2))
    <->
      (evaluate (super_refactor ae) = evaluate ae)
      /\
        forall a : arithmetic_expression,
          evaluate (super_refactor_aux ae a) = evaluate (Plus ae a).
Proof.
  intro ae.
  split.
  { intros [E_s [E_n_s E_n_n]].
    case (evaluate ae) as [n1 | s1] eqn:E_ae.
    - split.
      + Check (E_n_n n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
        destruct (E_n_n n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)) as [ly _].
        exact ly.
      + intro a.
        case (evaluate a) as [n2 | s2] eqn:E_a.
        * rewrite -> fold_unfold_evaluate_Plus.
          rewrite -> E_ae, E_a.
          Check (E_n_n n1 n2 (eq_refl (Expressible_nat n1)) a E_a).
          destruct (E_n_n n1 n2 (eq_refl (Expressible_nat n1)) a E_a) as [_ ly].
          exact ly.
        * rewrite -> fold_unfold_evaluate_Plus.
          rewrite -> E_ae, E_a.
          Check (E_n_s n1 s2 (eq_refl (Expressible_nat n1)) a E_a).
          destruct (E_n_s n1 s2 (eq_refl (Expressible_nat n1)) a E_a) as [_ ly].
          exact ly.
    - split.
      + Check (E_s s1 (eq_refl (Expressible_msg s1)) (Literal 0)).
        destruct (E_s s1 (eq_refl (Expressible_msg s1)) (Literal 0)) as [ly _].
        exact ly.
      + intro a.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite E_ae.
        Check (E_s s1 (eq_refl (Expressible_msg s1)) a).
        destruct (E_s s1 (eq_refl (Expressible_msg s1)) a) as [_ ly].
        exact ly.
  }
  { intros [E_sr_ae E_sr_aux_ae].
    split.
    { intros s E_ae_s a.
      split.
      - rewrite E_ae_s in E_sr_ae.
        exact E_sr_ae.
      - rewrite -> (E_sr_aux_ae a).
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_ae_s.
        reflexivity.
    }
    split.
    { intros n s E_ae_n a E_a_s.
      split.
      - rewrite E_ae_n in E_sr_ae.
        exact E_sr_ae.
      - rewrite -> (E_sr_aux_ae a).
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_ae_n, E_a_s.
        reflexivity.
    }
    { intros n1 n2 E_ae_n a E_a_n.
      split.
      - rewrite E_ae_n in E_sr_ae.
        exact E_sr_ae.
      - rewrite -> (E_sr_aux_ae a).
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_ae_n, E_a_n.
        reflexivity.
    }
  }
Qed.

Proposition super_refactor_is_idempotent :
  forall (ae : arithmetic_expression),
    evaluate (super_refactor ae) = evaluate (super_refactor (super_refactor ae)).
Proof.
  intro ae.
  rewrite -> (super_refactoring_preserves_evaluation (super_refactor ae)).
  reflexivity.
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
