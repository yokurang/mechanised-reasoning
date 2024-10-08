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

Definition eqb_expressible_value (ev1 ev2 : expressible_value) : bool :=
  match ev1 with
  | Expressible_nat n1 =>
      match ev2 with
      | Expressible_nat n2 => Nat.eqb n1 n2
      | Expressible_msg _ => false
      end
  | Expressible_msg s1 =>
      match ev2 with
      | Expressible_nat _ => false
      | Expressible_msg s2 => String.eqb s1 s2
      end
  end.

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

Compute (let ae := Literal 1 in
         (refactor (refactor ae))).

Compute (let ae := Plus (Literal 1) (Literal 2) in
         refactor ae).

Compute (let ae := Plus (Literal 1) (Literal 2) in
         refactor (refactor ae)).

Compute (let ae := Minus (Literal 2) (Literal 1) in
         refactor ae).

Compute (let ae := Minus (Literal 2) (Literal 1) in
         refactor (refactor ae)).

(* Single refactor ae case :
    Literal: Creates a binary tree where Plus is the root, the left child is the original (Literal n) and the right child is the accumulator (Literal 0).
    Plus: Creates a right-skewed binary tree where Plus is the root. The left child is ae1. The right child is the refactoring of ae2.
    Minus: Creates a Plus node as the root. The left child is the Minus node with the refactoring of ae1 and ae2 as its children. The right child is the accumulator (Literal 0).
 *)

Compute (let ae := Plus
                     (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         refactor ae).

Compute (let ae := Plus
                     (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         refactor (refactor ae)).

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

Compute (let ae := Minus
                     (Plus (Literal 1) (Literal 2))
                     (Literal 3) in
         refactor (refactor ae)).

(* Nested refactor ae case :
    Plus: For nested Plus operations, refactoring essentially flattens the binary tree. The flattened tree holds the values in the left leaves and a (Literal 0) is the accumulator/nil case located at the right-most child of the flattened tree.
    Minus: For nested Minus operations, Creates a Plus node as the root. The left child is the Minus node with the refactoring of ae1 and ae2 as its children. The right child is the accumulator (Literal 0).
    Overall effect: Plus always on the root of the resulting binary tree, 
    right leaf is always Plus or (Literal 0) in the right-most leaf.
 *)

Definition test_refactor (candidate : arithmetic_expression -> arithmetic_expression) :=
  (* Test Literal *)
  (eqb_arithmetic_expression (candidate (Literal 1))
     (Plus (Literal 1) (Literal 0))) &&

    (* Test Plus *)
    (eqb_arithmetic_expression
       (candidate (Plus (Literal 1) (Literal 2)))
       (Plus (Literal 1) (Plus (Literal 2) (Literal 0)))) &&

    (* Test nested Plus *)
    (eqb_arithmetic_expression
       (candidate (Plus (Plus (Literal 1) (Literal 2)) (Plus (Literal 3) (Literal 4))))
       (Plus (Literal 1) (Plus (Literal 2) (Plus (Literal 3) (Plus (Literal 4) (Literal 0)))))) &&

    (* Test Minus *)
    (eqb_arithmetic_expression
       (candidate (Minus (Literal 2) (Literal 1)))
       (Plus (Minus (Plus (Literal 2) (Literal 0)) (Plus (Literal 1) (Literal 0))) (Literal 0))) &&

    (* Test nested Minus *)
    (eqb_arithmetic_expression
       (candidate (Minus (Minus (Literal 2) (Literal 1)) (Minus (Literal 4) (Literal 3))))
       (Plus (Minus
                (Plus (Minus (Plus (Literal 2) (Literal 0)) (Plus (Literal 1) (Literal 0))) (Literal 0))
                (Plus (Minus (Plus (Literal 4) (Literal 0)) (Plus (Literal 3) (Literal 0))) (Literal 0)))
          (Literal 0))).

Compute (test_refactor refactor).

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

Lemma refactoring_preserves_evaluation_aux' :
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
            evaluate (refactor_aux ae a) = Expressible_nat (n1 + n2)).
Proof.
  intro ae.
  induction ae as [ n
                  | ae1 [H_ae1_s [H_ae1_n_s H_ae1_n1_n2]]
                      ae2 [H_ae2_s [H_ae2_n_s H_ae2_n1_n2]]
                  | ae1 [H_ae1_s [H_ae1_n_s H_ae1_n1_n2]]
                      ae2 [H_ae2_s [H_ae2_n_s H_ae2_n1_n2]]].
  - split.
    { intros s.
      rewrite -> fold_unfold_evaluate_Literal.
      intro H_absurd.
      discriminate H_absurd. }
    split.
    { intros n' s E_n_eq_n' a E_a_eq_s.
      rewrite -> fold_unfold_refactor_aux_Literal.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> fold_unfold_evaluate_Literal.
      rewrite -> E_a_eq_s.
      reflexivity. }
    { intros n1 n2 E_n_n1 a E_a_eq_n2.
      rewrite -> fold_unfold_refactor_aux_Literal.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> E_n_n1.
      rewrite -> E_a_eq_n2.
      reflexivity. }
  - split.
    { intros s.
      rewrite -> fold_unfold_evaluate_Plus.
      case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
      + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
        * intro H_absurd.
          discriminate H_absurd.
        * intro H_eq_s2_s.
          injection H_eq_s2_s as H_eq_s2_s.
          rewrite <- H_eq_s2_s.
          intro a.
          rewrite -> fold_unfold_refactor_aux_Plus.
          Check (H_ae1_n_s n1 s2).
          Check (H_ae1_n_s n1 s2 (eq_refl (Expressible_nat n1))). 
          Check (H_ae1_n_s n1 s2 (eq_refl (Expressible_nat n1)) (refactor_aux ae2 a)).
          apply (H_ae1_n_s n1 s2 (eq_refl (Expressible_nat n1)) (refactor_aux ae2 a)).
          Check (H_ae2_s s2 (eq_refl (Expressible_msg s2)) a).
          exact (H_ae2_s s2 (eq_refl (Expressible_msg s2)) a).
      + intro H_eq_s1_s.
        injection H_eq_s1_s as H_eq_s1_s.
        rewrite <- H_eq_s1_s.
        intro a.
        rewrite -> fold_unfold_refactor_aux_Plus.
        Check (H_ae1_s s1 (eq_refl (Expressible_msg s1)) (refactor_aux ae2 a)).
        rewrite -> (H_ae1_s s1 (eq_refl (Expressible_msg s1)) (refactor_aux ae2 a)).
        reflexivity.
    }
    split.
    { intros n s.
      rewrite -> fold_unfold_evaluate_Plus.
      case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
      + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2. 
        * intros _ a H_eval_a_s.
          rewrite -> fold_unfold_refactor_aux_Plus.
          Check (H_ae1_n_s n1 s (eq_refl (Expressible_nat n1)) (refactor_aux ae2 a)).
          apply (H_ae1_n_s n1 s (eq_refl (Expressible_nat n1)) (refactor_aux ae2 a)).
          Check (H_ae2_n_s n2 s (eq_refl (Expressible_nat n2)) a H_eval_a_s).
          exact (H_ae2_n_s n2 s (eq_refl (Expressible_nat n2)) a H_eval_a_s).
        * intro H_absurd.
          discriminate H_absurd.
      + intro H_absurd.
        discriminate H_absurd.
    }
    { intros n n3.
      rewrite -> fold_unfold_evaluate_Plus.
      case (evaluate ae1) as [ n1 | s1 ] eqn:H_ae1.
      + case (evaluate ae2) as [ n2 | s2 ] eqn:H_ae2.
        * intro H_n1_n2_n.
          injection H_n1_n2_n as H_n1_n2_n.
          intros a H_a_n3.
          rewrite -> fold_unfold_refactor_aux_Plus.
          rewrite <- H_n1_n2_n.
          rewrite <- Nat.add_assoc.
          Check (H_ae1_n1_n2 n1 (n2 + n3) (eq_refl (Expressible_nat n1)) (refactor_aux ae2 a)).
          apply (H_ae1_n1_n2 n1 (n2 + n3) (eq_refl (Expressible_nat n1)) (refactor_aux ae2 a)).
          Check (H_ae2_n1_n2 n2 n3 (eq_refl (Expressible_nat n2)) a H_a_n3).
          exact (H_ae2_n1_n2 n2 n3 (eq_refl (Expressible_nat n2)) a H_a_n3).
        * intro H_absurd.
          discriminate H_absurd.
      +  intro H_absurd.
         discriminate H_absurd.         
    }
  - split.
    { intro s.
      rewrite -> fold_unfold_evaluate_Minus.
      case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
+ case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
        * case (n1 <? n2) as [ | ] eqn:H_n1_n2.
          -- intros H_err_s a.
             rewrite -> fold_unfold_refactor_aux_Minus.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> fold_unfold_evaluate_Minus.
             Check (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1))).
             Check (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1)) (Literal 0)).
             Check (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             Check (H_ae2_n1_n2 n2 0 (eq_refl (Expressible_nat n2)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> (H_ae2_n1_n2 n2 0 (eq_refl (Expressible_nat n2)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> 2 Nat.add_0_r.
             rewrite -> H_n1_n2.
             rewrite -> H_err_s.
             reflexivity.
          -- intro H_absurd.
             discriminate H_absurd.
        * intros H_eq_s2_s a.
          rewrite -> fold_unfold_refactor_aux_Minus.
          rewrite -> fold_unfold_evaluate_Plus.
          rewrite -> fold_unfold_evaluate_Minus.
          Check (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1))).
          Check (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1)) (Literal 0)).
          Check (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
          rewrite -> (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
          Check (H_ae2_s s H_eq_s2_s (Literal 0)).
          rewrite -> (H_ae2_s s H_eq_s2_s (Literal 0)).
          reflexivity.
      + intros H_eq_s1_s a.
        rewrite -> fold_unfold_refactor_aux_Minus.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> fold_unfold_evaluate_Minus.
        Check (H_ae1_s s H_eq_s1_s (Literal 0)).
        rewrite -> (H_ae1_s s H_eq_s1_s (Literal 0)).
        reflexivity.
    }
    split.
    { intros n s.
      rewrite -> fold_unfold_evaluate_Minus.
      case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
      + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
        * case (n1 <? n2) as [ | ] eqn:H_n1_n2.
          -- intro H_absurd.
             discriminate H_absurd.
          -- intros H_eq_n1_n2_n a H_eval_a_s.
             rewrite -> fold_unfold_refactor_aux_Minus.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> fold_unfold_evaluate_Minus.
             rewrite -> (H_ae1_n1_n2 n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> (H_ae2_n1_n2 n2 0 (eq_refl (Expressible_nat n2)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> 2 Nat.add_0_r.
             rewrite -> H_n1_n2.
             rewrite -> H_eval_a_s.
             reflexivity.
        * intros H_absurd.
          discriminate H_absurd.
      + intro H_absurd.
        discriminate H_absurd.
    }
    { intros n1 n2.
      rewrite -> fold_unfold_evaluate_Minus.
      case (evaluate ae1) as [ n1' | s1' ] eqn:E_ae1.
      + case (evaluate ae2) as [ n2' | s2' ] eqn:E_ae2.
        * case (n1' <? n2') as [ | ] eqn:H_n1'_n2'.
          -- intro H_absurd.
             discriminate H_absurd.
          -- intros H_eq_n1'_n2'_n1 a H_eval_a_n2.
             rewrite -> fold_unfold_refactor_aux_Minus.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> fold_unfold_evaluate_Minus.
             Check (H_ae1_n1_n2 n1' 0 (eq_refl (Expressible_nat n1'))).
             Check (H_ae1_n1_n2 n1' 0 (eq_refl (Expressible_nat n1')) (Literal 0)).
             Check (H_ae1_n1_n2 n1' 0 (eq_refl (Expressible_nat n1')) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> (H_ae1_n1_n2 n1' 0 (eq_refl (Expressible_nat n1')) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             Check (H_ae2_n1_n2 n2' 0 (eq_refl (Expressible_nat n2')) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> (H_ae2_n1_n2 n2' 0 (eq_refl (Expressible_nat n2')) (Literal 0) (fold_unfold_evaluate_Literal 0)).
             rewrite -> 2 Nat.add_0_r.
             rewrite -> H_n1'_n2'.
             rewrite -> H_eval_a_n2.
             injection H_eq_n1'_n2'_n1 as H_eq_n1'_n2'_n1.
             rewrite -> H_eq_n1'_n2'_n1.
             reflexivity.
        * intro H_absurd.
          discriminate H_absurd.
      + intro H_absurd.
        discriminate H_absurd.
    }
Qed.

Theorem refactoring_preserves_evaluation' :
  forall ae : arithmetic_expression,
    evaluate (refactor ae) = evaluate ae.
Proof.
  intro ae.
  unfold refactor.
  case (evaluate ae) as [ n | s ] eqn:E_ae;
    remember (refactoring_preserves_evaluation_aux' ae) as H_ae;
    destruct H_ae as [ E_s [  E_n_s E_n_n ]].
  - Check (E_n_n n 0 E_ae (Literal 0) (fold_unfold_evaluate_Literal 0)).
    rewrite -> (E_n_n n 0 E_ae (Literal 0) (fold_unfold_evaluate_Literal 0)).
    rewrite -> Nat.add_0_r.
    reflexivity.
  - Check (E_s s E_ae (Literal 0)).
    exact (E_s s E_ae (Literal 0)).
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

Proposition refactor_is_not_idempotent :
  exists (ae : arithmetic_expression),
      refactor ae <> refactor (refactor ae).
Proof.
  exists (Minus (Literal 1) (Literal 0)).
  compute.
  intro H_absurd.
  discriminate H_absurd.
Qed.

Lemma refactor_is_conditionally_idempotent_aux :
  forall (ae a : arithmetic_expression),
    refactor_aux ae a = refactor_aux (refactor_aux ae a) (Literal 0).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].
  - intro a.
    rewrite -> fold_unfold_refactor_aux_Literal.
    rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite -> fold_unfold_refactor_aux_Literal.
    (* Plus (Literal n)
       a =
       Plus (Literal n)
       (refactor_aux a (Literal 0))
     *)
    admit.
  - intro a.
    rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite <- IHae1.
    reflexivity.
  - intro a.
    rewrite -> fold_unfold_refactor_aux_Minus.
    rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite -> fold_unfold_refactor_aux_Minus.
    rewrite <- IHae1.
    rewrite <- IHae2.
    (* Plus (Minus (refactor_aux ae1 (Literal 0)) (refactor_aux ae2 (Literal 0)))
       a =
       Plus (Minus (refactor_aux ae1 (Literal 0)) (refactor_aux ae2 (Literal 0)))
       (refactor_aux a (Literal 0))
     *)
    admit.
Abort.

Lemma refactor_is_conditionally_idempotent_aux :
  forall (ae a : arithmetic_expression),
    (forall a' : arithmetic_expression,
        a' = (refactor_aux a' (Literal 0))) ->
    refactor_aux ae a = refactor_aux (refactor_aux ae a) (Literal 0).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].
  - intro a.
    intro H_a.
    rewrite -> fold_unfold_refactor_aux_Literal.
    rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite -> fold_unfold_refactor_aux_Literal.
    Check (H_a a).
    rewrite <- (H_a a) at 1.
    reflexivity.
  - intro a.
    intros H_a.
    rewrite -> fold_unfold_refactor_aux_Plus.
    Check (IHae1 (refactor_aux ae2 a) H_a).
    exact (IHae1 (refactor_aux ae2 a) H_a).
  - intro a.
    intro H_a.
    rewrite -> fold_unfold_refactor_aux_Minus.
    rewrite -> fold_unfold_refactor_aux_Plus.
    rewrite -> fold_unfold_refactor_aux_Minus.
    Check (IHae2 (Literal 0) H_a).
    rewrite <- (IHae2 (Literal 0) H_a).
    Check (IHae2 (Literal 0) H_a).
    rewrite <- (IHae1 (Literal 0) H_a).
    rewrite <- (H_a a).
    reflexivity.
Qed.

Proposition refactor_is_conditionally_idempotent :
  (forall a' : arithmetic_expression,
      a' = refactor_aux a' (Literal 0)) ->
  forall (ae : arithmetic_expression),
    refactor ae = refactor (refactor ae).
Proof.
  intro H_a'.
  unfold refactor.
  intro ae.
  Check (refactor_is_conditionally_idempotent_aux ae (Literal 0) H_a').
  exact (refactor_is_conditionally_idempotent_aux ae (Literal 0) H_a').
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

Compute (let ae := Plus (Literal 2) (Literal 1) in
         super_refactor ae).

Compute (let ae := Plus (Literal 2) (Literal 1) in
         super_refactor (super_refactor ae)).

Compute (let ae := Minus (Literal 2) (Literal 1) in
         super_refactor ae).

Compute (let ae := Minus (Literal 2) (Literal 1) in
         super_refactor (super_refactor ae)).

Compute (let ae := Minus (Literal 2) (Literal 3) in
         super_refactor ae).

Compute (let ae := Minus (Literal 2) (Literal 3) in
         super_refactor (super_refactor ae)).

(*
   Single super_refactor ae case :
   Literal : Nothing
   Plus : Nothing
   Minus : Nothing

   So super_refactor ae = ae when ae is single Literal, Plus or Minus.
 *)

Compute (let ae := Plus (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         super_refactor ae).

Compute (let ae := Plus (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3)(Literal 4)) in
         super_refactor (super_refactor ae)).

Compute (let ae := Minus (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         super_refactor ae).

Compute (let ae := Minus (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         super_refactor (super_refactor ae)).

Compute (let ae := Minus (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         super_refactor ae).

Compute (let ae := Minus (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         super_refactor (super_refactor ae)).

Compute (let ae := Plus
                     (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         super_refactor ae).

Compute (let ae := Plus
                     (Plus (Literal 1) (Literal 2))
                     (Plus (Literal 3) (Literal 4)) in
         super_refactor (super_refactor ae)).

(*      +
       / \
      1   +
         / \
        2   +
           / \
          3   4
*)

Compute (let ae := Minus
                     (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         super_refactor ae).

Compute (let ae := Minus
                     (Minus (Literal 1) (Literal 2))
                     (Minus (Literal 3) (Literal 4)) in
         super_refactor (super_refactor ae)).

Compute (let ae := Minus
                     (Plus (Literal 1) (Literal 2))
                     (Literal 3) in
         super_refactor ae).

Compute (let ae := Minus
                     (Plus (Literal 1) (Literal 2))
                     (Literal 3) in
         super_refactor (super_refactor ae)).

Compute (let ae := Minus
                     (Minus (Literal 2) (Literal 1))
                     (Minus (Literal 4) (Literal 3)) in
         super_refactor ae).

Compute (let ae := Minus
                     (Minus (Literal 2) (Literal 1))
                     (Minus (Literal 4) (Literal 3)) in
         super_refactor (super_refactor ae)).

(* Nested super_refactor ae case :
   Plus : Creates a right-skewed binary tree where Plus is the root. The right-most leaf of the original binary tree is the accumulator of the refactored binary tree.
   Minus: Creates a binary tree where Minus is the root. The left child is the refactored ae1 and the right child is the refactored ae2. In both refactored children, the accumulator is the right-most leaf of the original binary tree.
   Overall effect: Unlike refactor, Literal, Plus and Minus can all lie on the root of the returned binary tree. The right-most leaf of the original binary tree is the right-most leaf of the returned binary tree (and is also the accumulator for that tree).
 *)

Definition test_super_refactor (candidate : arithmetic_expression -> arithmetic_expression) :=
  (* Test Literal *)
  (eqb_arithmetic_expression (candidate (Literal 1)) (Literal 1)) &&

  (* Test Plus *)
  (eqb_arithmetic_expression
    (candidate (Plus (Literal 1) (Literal 2)))
    (Plus (Literal 1) (Literal 2))) &&

  (* Test nested Plus *)
  (eqb_arithmetic_expression
    (candidate
    (Plus (Plus (Literal 1) (Literal 2))
    (Plus (Literal 3) (Literal 4))))
    (Plus (Literal 1) (Plus (Literal 2)
    (Plus (Literal 3) (Literal 4))))) &&

  (* Test Minus *)
  (eqb_arithmetic_expression
    (candidate (Minus (Literal 2) (Literal 1)))
    (Minus (Literal 2) (Literal 1))) &&

  (* Test nested Minus *)
  (eqb_arithmetic_expression
    (candidate (Minus (Minus (Literal 2) (Literal 1))
    (Minus (Literal 4) (Literal 3))))
    (Minus (Minus (Literal 2) (Literal 1))
    (Minus (Literal 4) (Literal 3)))) &&

  (* Test Mixed Plus and Minus *)
  (eqb_arithmetic_expression
    (candidate
    (Minus (Plus (Literal 1) (Literal 2)) (Literal 3)))
    (Minus (Plus (Literal 1) (Literal 2)) (Literal 3))).

Compute (test_super_refactor super_refactor).

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
        
Lemma super_refactoring_preserves_evaluation_aux' :
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
              evaluate (super_refactor_aux ae a) = Expressible_nat (n1 + n2)).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].
  - split.
    { intro s.
      rewrite -> fold_unfold_evaluate_Literal.
      intro H_absurd.
      discriminate H_absurd.
    }
    split.
    { intros n1 s E_n_eq_n1 a E_a_eq_s.
      split.
      { rewrite -> fold_unfold_super_refactor_Literal.
        exact E_n_eq_n1.
      }
      { rewrite -> fold_unfold_super_refactor_aux_Literal.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_n_eq_n1.
        rewrite -> E_a_eq_s.
        reflexivity.
      }
    }
    { intros n1 n2 E_n_eq_n1 a E_a_eq_n2.
      split.
      { rewrite -> fold_unfold_super_refactor_Literal.
        exact E_n_eq_n1.
      }
      { rewrite -> fold_unfold_super_refactor_aux_Literal.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> E_n_eq_n1.
        rewrite -> E_a_eq_n2.
        reflexivity.
      }
    }
  - split.
    { intro s.
      rewrite -> fold_unfold_evaluate_Plus.
      intro H_eval.
      split.
      { case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
        + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
          * discriminate H_eval.
          * rewrite -> fold_unfold_super_refactor_Plus.
            destruct IHae1 as [ _ [ H_ae1_n_s _ ]].
            Check (H_ae1_n_s n1 s
                     (eq_refl (Expressible_nat n1))
                     (super_refactor ae2)).
            destruct IHae2 as [ H_ae2_s _ ].
            destruct (H_ae2_s s H_eval a) as [ E_sr_ae2_eq_s _ ].
            Check (H_ae1_n_s n1 s
                     (eq_refl (Expressible_nat n1))
                     (super_refactor ae2)
                     E_sr_ae2_eq_s).
            destruct (H_ae1_n_s n1 s
                        (eq_refl (Expressible_nat n1))
                        (super_refactor ae2)
                        E_sr_ae2_eq_s) as [_ ly].
            exact ly.
        + rewrite -> fold_unfold_super_refactor_Plus.
          destruct IHae1 as [ H_ae1_s _ ].
          clear IHae2.
          Check (H_ae1_s s
                   H_eval
                   (super_refactor ae2)).
          destruct (H_ae1_s s
                      H_eval
                      (super_refactor ae2)) as [_ ly].
          exact ly.
      }
      { rewrite -> fold_unfold_super_refactor_aux_Plus.
        case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
        + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
          * discriminate H_eval.
          * destruct IHae1 as [ _ [ H_ae1_n_s _ ]].
            Check (H_ae1_n_s n1 s
                     (eq_refl (Expressible_nat n1))
                     (super_refactor_aux ae2 a)).
            destruct IHae2 as [ H_ae2_s _ ].
            destruct (H_ae2_s s H_eval a) as [ _ E_sr_aux_ae2_eq_s ].
            Check (H_ae1_n_s n1 s
                     (eq_refl (Expressible_nat n1))
                     (super_refactor_aux ae2 a)
                     E_sr_aux_ae2_eq_s).
            destruct (H_ae1_n_s n1 s
                        (eq_refl (Expressible_nat n1))
                        (super_refactor_aux ae2 a)
                        E_sr_aux_ae2_eq_s) as [_ ly].
            exact ly.
        + destruct IHae1 as [ H_ae1_s _ ].
          clear IHae2.
          Check (H_ae1_s s
                   H_eval
                   (super_refactor_aux ae2 a)).
          destruct (H_ae1_s s
                      H_eval
                      (super_refactor_aux ae2 a)) as [_ ly].
          exact ly.
      }
    }
    { split.
      { intros n s.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> fold_unfold_super_refactor_Plus.
        intros H_eval a E_a.
        split.
        { case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
          + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
            * destruct IHae1 as [ _ [ _ H_ae1_n_n ]].
              injection H_eval as H_eval.
              rewrite <- H_eval.
              Check (H_ae1_n_n n1 n2
                       (eq_refl (Expressible_nat n1))
                       (super_refactor ae2)).
              destruct IHae2 as [ _ [_ H_ae2_n_n ]].
              Check (H_ae2_n_n n2 n2
                       (eq_refl (Expressible_nat n2))
                       ae2 E_ae2).
              destruct (H_ae2_n_n n2 n2
                          (eq_refl (Expressible_nat n2))
                          ae2 E_ae2) as [E_sr_ae2_eq_n2 _].
              Check (H_ae1_n_n n1 n2
                       (eq_refl (Expressible_nat n1))
                       (super_refactor ae2)
                       E_sr_ae2_eq_n2).
              destruct (H_ae1_n_n n1 n2
                          (eq_refl (Expressible_nat n1))
                          (super_refactor ae2)
                          E_sr_ae2_eq_n2) as [_ ly].
              exact ly.
            * discriminate H_eval.
          + discriminate H_eval.
        }
        { rewrite -> fold_unfold_super_refactor_aux_Plus.
          case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
          + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
            * destruct IHae1 as [ _ [ H_ae1_n_s _ ]].
              Check (H_ae1_n_s n1 s
                       (eq_refl (Expressible_nat n1))
                       (super_refactor_aux ae2 a)).
              destruct IHae2 as [ _ [ H_ae2_n_s _ ]].
              Check (H_ae2_n_s n2 s
                       (eq_refl (Expressible_nat n2))
                       a E_a).
              destruct (H_ae2_n_s n2 s
                          (eq_refl (Expressible_nat n2))
                          a E_a) as [_ E_sr_aux_ae2_eq_s].
              Check (H_ae1_n_s n1 s
                       (eq_refl (Expressible_nat n1))
                       (super_refactor_aux ae2 a)
                       E_sr_aux_ae2_eq_s).
              destruct (H_ae1_n_s n1 s
                          (eq_refl (Expressible_nat n1))
                          (super_refactor_aux ae2 a)
                          E_sr_aux_ae2_eq_s) as [_ ly].
              exact ly.
            * discriminate H_eval.
          + discriminate H_eval.
        }
      }
      intros n1 n2.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> fold_unfold_super_refactor_Plus.
      intros H_eval a E_a.
      split.
      { case (evaluate ae1) as [ n1' | s1' ] eqn:E_ae1.
        + case (evaluate ae2) as [ n2' | s2' ] eqn:E_ae2.
          * injection H_eval as H_eval.
            rewrite <- H_eval.
            destruct IHae1 as [ _ [ _ H_ae1_n1_n2 ]].
            Check (H_ae1_n1_n2 n1' n2'
                     (eq_refl (Expressible_nat n1'))
                     (super_refactor ae2)).
            destruct IHae2 as [ _ [ _ H_ae2_n1_n2 ]].
            Check (H_ae2_n1_n2 n2' n2
                     (eq_refl (Expressible_nat n2'))
                     a E_a).
            destruct (H_ae2_n1_n2 n2' n2
                        (eq_refl (Expressible_nat n2'))
                        a E_a) as [E_sr_ae2_eq_n2' _].
            Check (H_ae1_n1_n2 n1' n2'
                     (eq_refl (Expressible_nat n1'))
                     (super_refactor ae2)
                     E_sr_ae2_eq_n2').
            destruct (H_ae1_n1_n2 n1' n2'
                        (eq_refl (Expressible_nat n1'))
                        (super_refactor ae2)
                        E_sr_ae2_eq_n2') as [_ ly].
            exact ly.
          * discriminate H_eval.
        + discriminate H_eval.
      }
      { case (evaluate ae1) as [ n1' | s1' ] eqn:E_ae1.
        + case (evaluate ae2) as [ n2' | s2' ] eqn:E_ae2.
          * rewrite -> fold_unfold_super_refactor_aux_Plus.
            injection H_eval as H_eval.
            rewrite <- H_eval.
            destruct IHae1 as [ _ [ _ H_ae1_n1_n2 ]].
            Check (H_ae1_n1_n2 n1' (n2' + n2)
                     (eq_refl (Expressible_nat n1'))
                     (super_refactor_aux ae2 a)).
            destruct IHae2 as [ _ [ _ H_ae2_n1_n2 ]].
            Check (H_ae2_n1_n2 n2' n2
                     (eq_refl (Expressible_nat n2'))
                     a E_a).
            destruct (H_ae2_n1_n2 n2' n2
                        (eq_refl (Expressible_nat n2'))
                        a E_a) as [_ E_sr_aux_ae2_eq_n2'].
            Check (H_ae1_n1_n2 n1' (n2' + n2)
                     (eq_refl (Expressible_nat n1'))
                     (super_refactor_aux ae2 a)
                     E_sr_aux_ae2_eq_n2').
            destruct (H_ae1_n1_n2 n1' (n2' + n2)
                        (eq_refl (Expressible_nat n1'))
                        (super_refactor_aux ae2 a)
                        E_sr_aux_ae2_eq_n2') as [_ ly].
            rewrite -> Nat.add_assoc in ly. (* Aha! Moment *)
            exact ly.
          * discriminate H_eval.
        + discriminate H_eval.
      }
    }
  - split.
    {
      intro s.
      rewrite -> fold_unfold_evaluate_Minus.
      case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
      + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
        * case (n1 <? n2) as [ | ] eqn:H_n1_n2.
          -- intros H_err_s a.
             rewrite -> fold_unfold_super_refactor_Minus.
             rewrite -> fold_unfold_evaluate_Minus.
             rewrite -> fold_unfold_super_refactor_aux_Minus.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> fold_unfold_evaluate_Minus.
             destruct IHae1 as [ _ [ _ H_ae1_n_n ]]. 
             Check (H_ae1_n_n n1 n2
                      (eq_refl (Expressible_nat n1))
                      ae2 E_ae2).
             destruct (H_ae1_n_n n1 n2
                         (eq_refl (Expressible_nat n1))
                         ae2 E_ae2) as [E_sr_ae1_eq_n1 _].
             rewrite -> E_sr_ae1_eq_n1.
             destruct IHae2 as [ _ [ _ H_ae2_n_n ]].
             Check (H_ae2_n_n n2 n1
                      (eq_refl (Expressible_nat n2))
                      ae1 E_ae1).
             destruct (H_ae2_n_n n2 n1
                         (eq_refl (Expressible_nat n2))
                         ae1 E_ae1) as [E_sr_ae2_eq_n2 _].
             rewrite -> E_sr_ae2_eq_n2.
             rewrite -> H_n1_n2.
             exact (conj H_err_s H_err_s).
          -- intros H_absurd.
             discriminate H_absurd.
        * intros H_s2_s a.
          rewrite -> fold_unfold_super_refactor_Minus.
          rewrite -> fold_unfold_evaluate_Minus.
          rewrite -> fold_unfold_super_refactor_aux_Minus.
          rewrite -> fold_unfold_evaluate_Plus.
          rewrite -> fold_unfold_evaluate_Minus.
          destruct IHae1 as [ _ [ H_ae1_n_s _ ] ].
          Check (H_ae1_n_s n1 s2
                   (eq_refl (Expressible_nat n1))
                   ae2 E_ae2).
          destruct (H_ae1_n_s n1 s2
                      (eq_refl (Expressible_nat n1))
                      ae2 E_ae2) as [E_sr_ae1_eq_n1 _].
          rewrite -> E_sr_ae1_eq_n1.
          destruct IHae2 as [ H_ae2_s _ ].
          Check (H_ae2_s s2
                   (eq_refl (Expressible_msg s2))
                   a).         
          destruct (H_ae2_s s2
                      (eq_refl (Expressible_msg s2))
                      a) as [E_sr_ae2_eq_s2 _].
          rewrite -> E_sr_ae2_eq_s2.
          rewrite -> H_s2_s.
          exact (conj (eq_refl (Expressible_msg s)) (eq_refl (Expressible_msg s))).
      + intros H_s1_s a.
        rewrite -> fold_unfold_super_refactor_Minus.
        rewrite -> fold_unfold_evaluate_Minus.
        rewrite -> fold_unfold_super_refactor_aux_Minus.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> fold_unfold_evaluate_Minus.
        destruct IHae1 as [ H_ae1_s _ ].
        Check (H_ae1_s s1
                 (eq_refl (Expressible_msg s1))
                 ae2).
        destruct (H_ae1_s s1
                    (eq_refl (Expressible_msg s1))
                    ae2) as [E_sr_ae1_eq_s1 _].
        rewrite -> E_sr_ae1_eq_s1.
        rewrite -> H_s1_s.
        exact (conj (eq_refl (Expressible_msg s)) (eq_refl (Expressible_msg s))).
    }
    split. 
    { intros n s.
      rewrite -> fold_unfold_evaluate_Minus.
      case (evaluate ae1) as [ n1 | s1 ] eqn:E_ae1.
      + case (evaluate ae2) as [ n2 | s2 ] eqn:E_ae2.
        * case (n1 <? n2) as [ | ] eqn:H_n1_n2.
          -- intro H_absurd.
             discriminate H_absurd.
          -- intros H_eq_n1_n2_n a H_eval_a_s.
             rewrite -> fold_unfold_super_refactor_Minus.
             rewrite -> fold_unfold_evaluate_Minus.
             rewrite -> fold_unfold_super_refactor_aux_Minus.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> fold_unfold_evaluate_Minus.
             destruct IHae1 as [ _ [ _ H_ae1_n_n ]].
             Check (H_ae1_n_n n1 n2
                      (eq_refl (Expressible_nat n1))
                      ae2 E_ae2).
             destruct (H_ae1_n_n n1 n2
                         (eq_refl (Expressible_nat n1))
                         ae2 E_ae2) as [E_sr_ae1_eq_n1 _].
             rewrite -> E_sr_ae1_eq_n1.
             destruct IHae2 as [ _ [ _ H_ae2_n_n ]].
             Check (H_ae2_n_n n2 n1
                      (eq_refl (Expressible_nat n2))
                      ae1 E_ae1).
             destruct (H_ae2_n_n n2 n1
                         (eq_refl (Expressible_nat n2))
                         ae1 E_ae1) as [E_sr_ae2_eq_n2 _].
             rewrite -> E_sr_ae2_eq_n2.
             rewrite -> H_n1_n2.
             injection H_eq_n1_n2_n as H_eq_n1_n2_n.
             split.
             ++ rewrite -> H_eq_n1_n2_n.
                reflexivity.
             ++ rewrite -> H_eval_a_s.
                reflexivity.
        * intro H_absurd.
          discriminate H_absurd.
      + intros H_absurd.
        discriminate H_absurd.
    }
    { intros n1 n2.
      rewrite -> fold_unfold_evaluate_Minus.
      case (evaluate ae1) as [ n1' | s1' ] eqn:E_ae1.
      + case (evaluate ae2) as [ n2' | s2' ] eqn:E_ae2.
        * case (n1' <? n2') as [ | ] eqn:H_n1_n2.
          -- intro H_absurd.
             discriminate H_absurd. 
          -- intros H_eq_n1_n2_n a H_eval_a_n2.
             rewrite -> fold_unfold_super_refactor_Minus.
             rewrite -> fold_unfold_evaluate_Minus.
             rewrite -> fold_unfold_super_refactor_aux_Minus.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> fold_unfold_evaluate_Minus.
             destruct IHae1 as [ _ [ _ H_ae1_n1_n2 ]].
             Check (H_ae1_n1_n2 n1' n2'
                      (eq_refl (Expressible_nat n1'))
                      ae2 E_ae2).
             destruct (H_ae1_n1_n2 n1' n2'
                         (eq_refl (Expressible_nat n1'))
                         ae2 E_ae2) as [E_sr_ae1_eq_n1' _].
             rewrite -> E_sr_ae1_eq_n1'.
             destruct IHae2 as [ _ [ _ H_ae2_n1_n2 ]].
             Check (H_ae2_n1_n2 n2' n1'
                      (eq_refl (Expressible_nat n2'))
                      ae1 E_ae1).
             destruct (H_ae2_n1_n2 n2' n1'
                         (eq_refl (Expressible_nat n2'))
                         ae1 E_ae1) as [E_sr_ae2_eq_n2' _].
             rewrite -> E_sr_ae2_eq_n2'.
             rewrite -> H_n1_n2.
             injection H_eq_n1_n2_n as H_eq_n1_n2_n.
             split.
             (* Aha! Moment incoming. PLEASE mention in report *)
             ++ rewrite -> H_eq_n1_n2_n.
                reflexivity.
             ++ rewrite -> H_eval_a_n2.
                rewrite -> H_eq_n1_n2_n.
                reflexivity.
        * intro H_absurd.
          discriminate H_absurd.
      + intros H_absurd.
        discriminate H_absurd.
    }
Qed.

Theorem super_refactoring_preserves_evaluation' :
  forall ae : arithmetic_expression,
    evaluate (super_refactor ae) = evaluate ae.
Proof.
  intro ae.
  case (evaluate ae) as [ n | s ] eqn:E_ae;
    remember (super_refactoring_preserves_evaluation_aux' ae) as H_ae;
    destruct H_ae as [ E_s [ E_n_s E_n_n ]].
  - Check (E_n_n n 0).
    destruct (E_n_n n 0 E_ae (Literal 0) (fold_unfold_evaluate_Literal 0)) as [E_sr_n _].
    exact E_sr_n.
  - destruct (E_s s E_ae (Literal 0)) as [E_sr_s _].
    exact E_sr_s.
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

Lemma super_refactor_is_idempotent_aux:
    forall ae : arithmetic_expression,
      super_refactor (super_refactor ae) = super_refactor ae
      /\
      forall a : arithmetic_expression,
        super_refactor (super_refactor_aux ae a) = super_refactor_aux ae (super_refactor a).
Proof.
  intro ae.
  induction ae as [ n
                  | ae1 [IHae1_sr IHae1_sr_aux] ae2 [IHae2_sr IHae2_sr_aux]
                  | ae1 [IHae1_sr IHae1_sr_aux] ae2 [IHae2_sr IHae2_sr_aux] ].
  - split.
    + rewrite ->2 fold_unfold_super_refactor_Literal.
      reflexivity.
    + intro a.
      rewrite ->2 fold_unfold_super_refactor_aux_Literal.
      rewrite -> fold_unfold_super_refactor_Plus.
      rewrite -> fold_unfold_super_refactor_aux_Literal.
      reflexivity.
  - split.
    + rewrite -> fold_unfold_super_refactor_Plus.
      rewrite -> (IHae1_sr_aux (super_refactor ae2)).
      rewrite -> IHae2_sr.
      reflexivity.
    + intro a.
      rewrite ->2 fold_unfold_super_refactor_aux_Plus.
      rewrite -> (IHae1_sr_aux (super_refactor_aux ae2 a)).
      rewrite -> (IHae2_sr_aux a).
      reflexivity.
  - split.
    + rewrite ->2 fold_unfold_super_refactor_Minus.
      rewrite -> IHae1_sr.
      rewrite -> IHae2_sr.
      reflexivity.
    + intro a.
      rewrite ->2 fold_unfold_super_refactor_aux_Minus.
      rewrite -> fold_unfold_super_refactor_Plus.
      rewrite -> fold_unfold_super_refactor_aux_Minus.
      rewrite -> IHae1_sr.
      rewrite -> IHae2_sr.
      reflexivity.
Qed.

Proposition super_refactor_is_idempotent :
  forall ae,
    super_refactor ae = super_refactor (super_refactor ae).
Proof.
  intros ae.
  Check super_refactor_is_idempotent_aux.
  destruct (super_refactor_is_idempotent_aux ae) as [ H_sr H_sr_aux ].
  rewrite -> H_sr.
  reflexivity.
Qed.


(* ********** *)

(* Week 03 *)

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
