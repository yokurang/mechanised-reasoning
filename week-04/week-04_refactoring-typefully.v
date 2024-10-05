(* week-04_refactoring-typefully.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 20 Sep 2024 *)

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
        reflexivity. }
    
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Plus.
      apply sr_aux_ae1.
      left. exact sr_ae2_Plus. }    
    { intros a [H_a_Plus | H_a_OK].
      rewrite -> fold_unfold_super_refactor_right_aux_Plus.
      + Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        apply sr_aux_ae2.
        left. exact H_a_Plus.
      + rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        apply sr_aux_ae2.
        right. exact H_a_OK. }
    
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Plus.
      Check (sr_aux_ae1 (super_refactor_right ae2)).
      apply sr_aux_ae1.
      right. exact sr_ae2_OK. }
    { intros a [H_a_Plus | H_a_OK].
      rewrite -> fold_unfold_super_refactor_right_aux_Plus.
      + Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        Check (sr_aux_ae2 a).
        apply sr_aux_ae2.
        left. exact H_a_Plus.
      + rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        Check (sr_aux_ae2 a).
        apply sr_aux_ae2.
        right. exact H_a_OK. }
    
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Plus.
      apply sr_aux_ae1.
      left. exact sr_ae2_Plus. }
    { intros a [H_a_Plus | H_a_OK].
      + rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        Check (sr_aux_ae2 a).
        apply sr_aux_ae2.
        left. exact H_a_Plus.
      + rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        Check (sr_aux_ae2 a).
        apply sr_aux_ae2.
        right. exact H_a_OK. }
    
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Plus.
      Check (sr_aux_ae1 (super_refactor_right ae2)).
      apply sr_aux_ae1.
      right. exact sr_ae2_OK. }
    { intros a [H_a_Plus | H_a_OK].
      + rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        Check (sr_aux_ae2 a).
        apply sr_aux_ae2.
        left. exact H_a_Plus.
      + rewrite -> fold_unfold_super_refactor_right_aux_Plus.
        Check (sr_aux_ae1 (super_refactor_right_aux ae2 a)).
        apply sr_aux_ae1.
        Check (sr_aux_ae2 a).
        apply sr_aux_ae2.
        right. exact H_a_OK. }
    
  - split.
    { rewrite -> fold_unfold_super_refactor_right_Minus.
      rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
      rewrite -> sr_ae1_Plus.
      rewrite -> sr_ae2_Plus.
      right.
      reflexivity. }
    { intros a [H_a_Plus | H_a_OK].
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_Plus.
        rewrite -> sr_ae2_Plus.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
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
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_Plus.
        rewrite -> sr_ae2_OK.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
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
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_OK.
        rewrite -> sr_ae2_Plus.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
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
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
        rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
        rewrite -> sr_ae1_OK.
        rewrite -> sr_ae2_OK.
        rewrite -> H_a_Plus.
        left.
        reflexivity.
      + rewrite -> fold_unfold_super_refactor_right_aux_Minus.
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
  case (super_refactor_right_yields_super_refactored_rightp_results_aux ae)
    as [[H_ae_Plus | H_ae_OK] _].
  - rewrite  -> H_ae_Plus.
    reflexivity.
  - rewrite -> H_ae_OK.
    reflexivity.
Qed.

(* A typeful take: characterizing refactored expressions with a type. *)

Inductive arithmetic_expression_right : Type :=
  Literal_right : nat -> arithmetic_expression_right
| Plus_right_Literal : nat -> arithmetic_expression_right -> arithmetic_expression_right
| Plus_right_Minus : arithmetic_expression_right -> arithmetic_expression_right -> arithmetic_expression_right -> arithmetic_expression_right
| Minus_right : arithmetic_expression_right -> arithmetic_expression_right -> arithmetic_expression_right.

Fixpoint arithmetic_expression_from_arithmetic_expression_right (aer : arithmetic_expression_right) : arithmetic_expression :=
  match aer with
    Literal_right n =>
    Literal n
  | Plus_right_Literal n1 aer2 =>
    Plus (Literal n1) (arithmetic_expression_from_arithmetic_expression_right aer2)    
  | Plus_right_Minus aer11 aer12 aer2 =>
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

Lemma fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Literal_right :
  forall n : nat,
    arithmetic_expression_from_arithmetic_expression_right (Literal_right n) = Literal n.
Proof.
  fold_unfold_tactic  arithmetic_expression_from_arithmetic_expression_right.
Qed.

Lemma fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Literal :
  forall (n : nat)
    (aer : arithmetic_expression_right),
    arithmetic_expression_from_arithmetic_expression_right (Plus_right_Literal n aer) =
      Plus (Literal n) (arithmetic_expression_from_arithmetic_expression_right aer).
Proof.
  fold_unfold_tactic arithmetic_expression_from_arithmetic_expression_right.
Qed.

Lemma fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus :
  forall (aer11 aer12 aer2 : arithmetic_expression_right),
    arithmetic_expression_from_arithmetic_expression_right (Plus_right_Minus aer11 aer12 aer2) =
    Plus
      (Minus
         (arithmetic_expression_from_arithmetic_expression_right aer11)
         (arithmetic_expression_from_arithmetic_expression_right aer12))
      (arithmetic_expression_from_arithmetic_expression_right aer2).
Proof.
  fold_unfold_tactic arithmetic_expression_from_arithmetic_expression_right.
Qed.

Lemma fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Minus_right :
  forall (aer1 aer2 : arithmetic_expression_right),
    arithmetic_expression_from_arithmetic_expression_right (Minus_right aer1 aer2) =
      Minus
      (arithmetic_expression_from_arithmetic_expression_right aer1)
      (arithmetic_expression_from_arithmetic_expression_right aer2).
Proof.
  fold_unfold_tactic arithmetic_expression_from_arithmetic_expression_right.
Qed.

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
      Plus_right_Minus (super_refactor_right' ae1) (super_refactor_right' ae2) a
    end.

(* soundness of type arithmetic_expression_right *)

Check arithmetic_expression_right_ind.

Proposition soundness_of_arithmetic_expression_right :
  forall aer : arithmetic_expression_right,
    (intermediate_expression_from_arithmetic_expression
       (arithmetic_expression_from_arithmetic_expression_right
          aer) = ExpPlus
     \/
       intermediate_expression_from_arithmetic_expression
         (arithmetic_expression_from_arithmetic_expression_right
            aer) = ExpOK).
Proof.
  intro aer.
  induction aer as [ n | n aer1 [IHaer1 | IHaer1] | aerm1 [IHaerm1 | IHaerm1] aerm2 [IHaerm2 | IHaerm2] aerp [IHaerp| IHaerp] | aer1 [IHaer1 | IHaer1] aer2 [IHaer2 | IHaer2]].

  - right.
    rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Literal_right n).
    rewrite -> (fold_unfold_intermediate_expression_from_arithmetic_expression_Literal n).
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Literal n aer1).
    rewrite -> (fold_unfold_intermediate_expression_from_arithmetic_expression_Plus (Literal n) (arithmetic_expression_from_arithmetic_expression_right aer1)).
    rewrite -> (fold_unfold_intermediate_expression_from_arithmetic_expression_Literal n).
    rewrite -> IHaer1.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Literal n aer1).
    rewrite -> (fold_unfold_intermediate_expression_from_arithmetic_expression_Plus (Literal n) (arithmetic_expression_from_arithmetic_expression_right aer1)).
    rewrite -> (fold_unfold_intermediate_expression_from_arithmetic_expression_Literal n).
    rewrite -> IHaer1.
    left.
    reflexivity.

(* the next 8 cases are all same same *)
    
  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.
    
  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Plus_right_Minus aerm1 aerm2 aerp).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Plus.
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaerm1.
    rewrite -> IHaerm2.
    rewrite -> IHaerp.
    left.
    reflexivity.

(* the last 4 cases are all the same *)
    
  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Minus_right aer1 aer2).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaer1.
    rewrite -> IHaer2.
    right.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Minus_right aer1 aer2).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaer1.
    rewrite -> IHaer2.
    right.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Minus_right aer1 aer2).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaer1.
    rewrite -> IHaer2.
    right.
    reflexivity.

  - rewrite -> (fold_unfold_arithmetic_expression_from_arithmetic_expression_right_Minus_right aer1 aer2).
    rewrite -> fold_unfold_intermediate_expression_from_arithmetic_expression_Minus.
    rewrite -> IHaer1.
    rewrite -> IHaer2.
    right.
    reflexivity.
Qed.

Corollary super_refactor_right_yields_super_refactored_right_results_revisited :
  forall ae : arithmetic_expression,
    super_refactored_rightp (arithmetic_expression_from_arithmetic_expression_right (super_refactor_right' ae)) = true.
Proof.
  intro ae.
  unfold super_refactored_rightp.
  remember (super_refactor_right' ae) as aer.
  Check (soundness_of_arithmetic_expression_right aer).
  destruct (soundness_of_arithmetic_expression_right aer) as [ H_aer| H_aer].

  - rewrite -> H_aer.
    reflexivity.

  - rewrite -> H_aer.
    reflexivity.
Qed.
(* ********** *)

(* end of week-04_refactoring-typefully.v *)
