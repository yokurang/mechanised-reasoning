(* week3_refactoring-left-and-right.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 22 Aug 2024 *)

(* ********** *)

(*
   Members of the group:
   Kwangjoo Park <e0425762@u.nus.edu>
   Nguyen Viet Anh <e0851472@u.nus.edu>
   Sanjay Adhith <sanjay.adhith@u.nus.edu>
 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Nat Arith Bool List String Ascii.

(* ********** *)

Fixpoint list_length (V : Type) (vs : list V) : nat :=
  match vs with
  | nil =>
    0
  | v :: vs' =>
    S (list_length V vs')
  end.

Lemma fold_unfold_list_length_nil :
  forall V : Type,
    list_length V nil = 0.
Proof.
  fold_unfold_tactic list_length.
Qed.

Lemma fold_unfold_list_length_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_length V (v :: vs') = S (list_length V vs').
Proof.
  fold_unfold_tactic list_length.
Qed.

Lemma fold_unfold_app_nil :
  forall (V : Type)
         (v2s : list V),
    nil ++ v2s = v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_app_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    (v1 :: v1s') ++ v2s = v1 :: v1s' ++ v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

(* ********** *)

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
                                in let s3 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                                   in if q3 <? 10
                                      then s3
                                      else "00000".

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

Definition err_msg_underflow_minus (n1 n2 : nat) : string :=
  String.append "numerical underflow: -" (string_of_nat (n2 - n1)).

Fixpoint evaluate_ltr (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus ae1 ae2 =>
    match evaluate_ltr ae1 with
    | Expressible_nat n1 =>
      match evaluate_ltr ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Minus ae1 ae2 =>
    match evaluate_ltr ae1 with
    | Expressible_nat n1 =>
      match evaluate_ltr ae2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (err_msg_underflow_minus n1 n2)
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
    evaluate_ltr (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Plus :
  forall ae1 ae2 : arithmetic_expression,
    evaluate_ltr (Plus ae1 ae2) =
    match evaluate_ltr ae1 with
      Expressible_nat n1 =>
      match evaluate_ltr ae2 with
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
  forall ae1 ae2 : arithmetic_expression,
    evaluate_ltr (Minus ae1 ae2) =
    match evaluate_ltr ae1 with
    | Expressible_nat n1 =>
      match evaluate_ltr ae2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (err_msg_underflow_minus n1 n2)
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

Fixpoint arithmetic_expression_eqb (ae1 ae2 : arithmetic_expression) : bool :=
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
      (arithmetic_expression_eqb ae11 ae21) && (arithmetic_expression_eqb ae12 ae22)
    | _ =>
      false
    end
  | Minus ae11 ae12 =>
    match ae2 with
    | Minus ae21 ae22 =>
      (arithmetic_expression_eqb ae11 ae21) && (arithmetic_expression_eqb ae12 ae22)
    | _ =>
      false
    end
  end.

Proposition Literal_0_is_neutral_for_Plus_on_the_left_ltr :
  forall ae : arithmetic_expression,
    evaluate_ltr (Plus (Literal 0) ae) = evaluate_ltr ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_ltr_Plus.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  destruct (evaluate_ltr ae) as [n | s].
  * rewrite -> plus_O_n.
    reflexivity.
  * reflexivity.
Qed.

Proposition Literal_0_is_neutral_for_Plus_on_the_right_ltr :
  forall ae : arithmetic_expression,
    evaluate_ltr (Plus ae (Literal 0)) = evaluate_ltr ae.
Proof.
  intros ae.
  rewrite -> fold_unfold_evaluate_ltr_Plus.
  rewrite -> fold_unfold_evaluate_ltr_Literal.
  destruct (evaluate_ltr ae) as [n | s].
  * rewrite <- plus_n_O.
    reflexivity.
  * reflexivity.
Qed.

Proposition Plus_is_associative_ltr :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate_ltr (Plus (Plus ae1 ae2) ae3) =
    evaluate_ltr (Plus ae1 (Plus ae2 ae3)).
Proof.
  intros ae1 ae2 ae3.
  rewrite ->4 fold_unfold_evaluate_ltr_Plus.
  destruct (evaluate_ltr ae1) as [n1 | s1].
  - destruct (evaluate_ltr ae2) as [n2 | s2].
    + destruct (evaluate_ltr ae3) as [n3 | s3].
      * rewrite <- Nat.add_assoc.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma necessary_condition_for_Plus_to_return_Expressible_msg_when_evaluating_ltr :
  forall (ae1 ae2 : arithmetic_expression)
         (s : string),
    evaluate_ltr (Plus ae1 ae2) = Expressible_msg s ->
    evaluate_ltr ae1 = Expressible_msg s
    \/ (exists n : nat,
           evaluate_ltr ae1 = Expressible_nat n
           /\ evaluate_ltr ae2 = Expressible_msg s).
Proof.
  intros ae1 ae2 s H.
  rewrite -> fold_unfold_evaluate_ltr_Plus in H.
  destruct (evaluate_ltr ae1) as [n1 | s1].
  - destruct (evaluate_ltr ae2) as [n2 | s2].
    + discriminate H.
    + right.
      exists n1.
      split.
      { reflexivity. }
      { exact H. }
  - left.
    exact H.
Qed.

Lemma necessary_condition_for_Plus_to_return_Expressible_nat_when_evaluating_ltr :
  forall (ae1 ae2 : arithmetic_expression)
         (n : nat),
    evaluate_ltr (Plus ae1 ae2) = Expressible_nat n ->
    (exists n1 n2 : nat,
        evaluate_ltr ae1 = Expressible_nat n1
        /\ evaluate_ltr ae2 = Expressible_nat n2
        /\ n = n1 + n2).
Proof.
  intros ae1 ae2 n H.
  rewrite -> fold_unfold_evaluate_ltr_Plus in H.
  destruct (evaluate_ltr ae1) as [n1 | s1].
  - destruct (evaluate_ltr ae2) as [n2 | s2].
    + exists n1, n2.
      split.
      { reflexivity. }
      split.
      { reflexivity. }
      { injection H as H.
        symmetry.
        exact H. }
    + discriminate H.
  - discriminate H.
Qed.

Lemma necessary_condition_for_Minus_to_return_Expressible_msg_when_evaluating_ltr :
  forall (ae1 ae2 : arithmetic_expression)
         (s : string),
    evaluate_ltr (Minus ae1 ae2) = Expressible_msg s ->
    evaluate_ltr ae1 = Expressible_msg s
    \/ (exists n : nat,
           evaluate_ltr ae1 = Expressible_nat n
           /\ evaluate_ltr ae2 = Expressible_msg s)
    \/ (exists n1 n2 : nat,
           evaluate_ltr ae1 = Expressible_nat n1
           /\ evaluate_ltr ae2 = Expressible_nat n2
           /\ n1 <? n2 = true
           /\ s = err_msg_underflow_minus n1 n2).
Proof.
  intros ae1 ae2 s H.
  rewrite -> fold_unfold_evaluate_ltr_Minus in H.
  destruct (evaluate_ltr ae1) as [n1 | s1].
  - destruct (evaluate_ltr ae2) as [n2 | s2].
    + destruct (n1 <? n2) eqn:H_n1_n2.
      * right. right.
        exists n1, n2.
        split.
        { reflexivity. }
        split.
        { reflexivity. }
        split.
        { exact H_n1_n2. }
        { injection H as H.
          symmetry.
          exact H. }
      * discriminate H.
    + right. left.
      exists n1.
      split.
      { reflexivity. }
      { exact H. }
  - left.
    exact H.
Qed.

Lemma necessary_condition_for_Minus_to_return_Expressible_nat_when_evaluating_ltr :
  forall (ae1 ae2 : arithmetic_expression)
         (n : nat),
    evaluate_ltr (Minus ae1 ae2) = Expressible_nat n ->
    (exists n1 n2 : nat,
        evaluate_ltr ae1 = Expressible_nat n1
        /\ evaluate_ltr ae2 = Expressible_nat n2
        /\ n1 <? n2 = false
        /\ n = n1 - n2).
Proof.
  intros ae1 ae2 s H.
  rewrite -> fold_unfold_evaluate_ltr_Minus in H.
  destruct (evaluate_ltr ae1) as [n1 | s1].
  - destruct (evaluate_ltr ae2) as [n2 | s2].
    + destruct (n1 <? n2) eqn:H_n1_n2.
      * discriminate H.
      * exists n1, n2.
        split.
        { reflexivity. }
        split.
        { reflexivity. }
        split.
        { exact H_n1_n2. }
        { injection H as H.
          symmetry.
          exact H. }
    + discriminate H.
  - discriminate H.
Qed.

(* ********** *)

Fixpoint super_refactor_left (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_left_aux ae2 (super_refactor_left ae1)
  | Minus ae1 ae2 =>
    Minus (super_refactor_left ae1) (super_refactor_left ae2)
  end
  with super_refactor_left_aux (ae a : arithmetic_expression) : arithmetic_expression :=
    match ae with
    | Literal n =>
      Plus a (Literal n)
    | Plus ae1 ae2 =>
      super_refactor_left_aux ae2 (super_refactor_left_aux ae1 a)
    | Minus ae1 ae2 =>
      Plus (Minus (super_refactor_left ae1) (super_refactor_left ae2)) a
    end.

Lemma fold_unfold_super_refactor_left_Literal :
  forall n : nat,
    super_refactor_left (Literal n) = Literal n.
Proof.
  fold_unfold_tactic super_refactor_left.
Qed.

Lemma fold_unfold_super_refactor_left_Plus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_left (Plus ae1 ae2) =
    super_refactor_left_aux ae2 (super_refactor_left ae1).
Proof.
  fold_unfold_tactic super_refactor_left.
Qed.

Lemma fold_unfold_super_refactor_left_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_left (Minus ae1 ae2) =
    Minus (super_refactor_left ae1) (super_refactor_left ae2).
Proof.
  fold_unfold_tactic super_refactor_left.
Qed.

Lemma fold_unfold_super_refactor_left_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    super_refactor_left_aux (Literal n) a = Plus a (Literal n).
Proof.
  fold_unfold_tactic super_refactor_left_aux.
Qed.

Lemma fold_unfold_super_refactor_left_aux_Plus :
  forall ae1 ae2 a : arithmetic_expression,
    super_refactor_left_aux (Plus ae1 ae2) a =
    super_refactor_left_aux ae2 (super_refactor_left_aux ae1 a).
Proof.
  fold_unfold_tactic super_refactor_left_aux.
Qed.

Lemma fold_unfold_super_refactor_left_aux_Minus :
  forall ae1 ae2 a : arithmetic_expression,
    super_refactor_left_aux (Minus ae1 ae2) a =
    Plus (Minus (super_refactor_left ae1) (super_refactor_left ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_left_aux.
Qed.

Definition test_super_refactor_left (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  (let input := (Minus
                   (Plus
                      (Plus
                         (Literal 1)
                         (Literal 5))
                      (Literal 2))
                   (Plus
                      (Literal 3)
                      (Plus
                         (Literal 6)
                         (Literal 7)))) in
   let expected := (Minus
                      (Plus
                         (Plus
                            (Literal 1)
                            (Literal 5))
                         (Literal 2))
                      (Plus
                         (Plus
                            (Literal 3)
                            (Literal 6))
                         (Literal 7))) in
   arithmetic_expression_eqb (candidate input) expected)
  &&
  (arithmetic_expression_eqb
     (candidate (Literal 1))
     (Literal 1))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Literal 1)
           (Literal 2)))
     (Plus
        (Literal 1)
        (Literal 2)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Plus
              (Literal 1)
              (Literal 2))
           (Plus
              (Literal 3)
              (Literal 4))))
     (Plus
        (Plus
           (Plus
              (Literal 1)
              (Literal 2))
           (Literal 3))
        (Literal 4)))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Minus
           (Plus
              (Literal 1)
              (Literal 2))
           (Plus
              (Literal 3)
              (Literal 4))))
     (Minus
        (Plus
           (Literal 1)
           (Literal 2))
        (Plus
           (Literal 3)
           (Literal 4)))).

Compute (test_super_refactor_left super_refactor_left).

(* ********** *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

Fixpoint compile_ltr (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: nil
  | Plus ae1 ae2 =>
    (compile_ltr ae1) ++ (compile_ltr ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
    (compile_ltr ae1) ++ (compile_ltr ae2) ++ (SUB :: nil)
  end.

Lemma fold_unfold_compile_ltr_Literal :
  forall n : nat,
    compile_ltr (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_ltr.
Qed.

Lemma fold_unfold_compile_ltr_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ltr (Plus ae1 ae2) =
    (compile_ltr ae1) ++ (compile_ltr ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_ltr.
Qed.

Lemma fold_unfold_compile_ltr_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ltr (Minus ae1 ae2) =
    (compile_ltr ae1) ++ (compile_ltr ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_ltr.
Qed.

(* ********** *)

Definition data_stack := list nat.

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition decode_execute_ltr (bci : byte_code_instruction) (ds : data_stack) :=
  match bci with
  | PUSH n =>
    OK (n :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO "ADD: stack underflow"
    | n2 :: ds' =>
      match ds' with
      | nil =>
        KO "ADD: stack underflow"
      | n1 :: ds'' =>
        OK ((n1 + n2) :: ds'')
      end
    end
  | SUB =>
    match ds with
    | nil =>
      KO "SUB: stack underflow"
    | n2 :: ds' =>
      match ds' with
      | nil =>
        KO "SUB: stack underflow"
      | n1 :: ds'' =>
        if n1 <? n2
        then KO (err_msg_underflow_minus n1 n2)
        else OK ((n1 - n2) :: ds'')
      end
    end
  end.

Inductive result_of_decoding_and_execution_with_profiling : Type :=
| OK_p : data_stack -> nat -> result_of_decoding_and_execution_with_profiling
| KO_p : string -> result_of_decoding_and_execution_with_profiling.

Fixpoint fetch_decode_execute_loop_ltr_with_profiling (bcis : list byte_code_instruction) (ds : data_stack) :=
  match bcis with
  | nil =>
    OK_p ds 0
  | bci :: bcis' =>
    match decode_execute_ltr bci ds with
    | OK ds' =>
      match fetch_decode_execute_loop_ltr_with_profiling bcis' ds' with
      | OK_p ds'' max_size'' =>
        OK_p ds'' (Nat.max (list_length nat ds') max_size'')
      | KO_p s =>
        KO_p s
      end
    | KO s =>
      KO_p s
    end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil :
  forall (ds : data_stack),
    fetch_decode_execute_loop_ltr_with_profiling nil ds = OK_p ds 0.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_ltr_with_profiling.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop_ltr_with_profiling (bci :: bcis') ds =
    match decode_execute_ltr bci ds with
    | OK ds' =>
      match fetch_decode_execute_loop_ltr_with_profiling bcis' ds' with
      | OK_p ds'' max_size'' =>
        OK_p ds'' (Nat.max (list_length nat ds') max_size'')
      | KO_p s =>
        KO_p s
      end
    | KO s =>
      KO_p s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_ltr_with_profiling.
Qed.

Inductive expressible_value_with_profiling : Type :=
| Expressible_nat_p : nat -> nat -> expressible_value_with_profiling
| Expressible_msg_p : string -> expressible_value_with_profiling.

Definition run_ltr_with_profiling (bcis : list byte_code_instruction) :=
  match fetch_decode_execute_loop_ltr_with_profiling bcis nil with
  | OK_p ds max_size =>
    match ds with
    | nil =>
      Expressible_msg_p "no result on the data stack"
    | result :: ds' =>
      match ds' with
      | nil =>
        Expressible_nat_p result max_size
      | _ :: _ =>
        Expressible_msg_p "too many results on the data stack"
      end
    end
  | KO_p s =>
    Expressible_msg_p s
  end.

(* ********** *)

Fixpoint stack_size_ltr (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal _ =>
    1
  | Plus ae1 ae2 =>
    Nat.max (stack_size_ltr ae1) (S (stack_size_ltr ae2))
  | Minus ae1 ae2 =>
    Nat.max (stack_size_ltr ae1) (S (stack_size_ltr ae2))
  end.

Lemma fold_unfold_stack_size_ltr_Literal :
  forall (n : nat),
    stack_size_ltr (Literal n) = 1.
Proof.
  fold_unfold_tactic stack_size_ltr.
Qed.

Lemma fold_unfold_stack_size_ltr_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    stack_size_ltr (Plus ae1 ae2) =
    Nat.max (stack_size_ltr ae1) (S (stack_size_ltr ae2)).
Proof.
  fold_unfold_tactic stack_size_ltr.
Qed.

Lemma fold_unfold_stack_size_ltr_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    stack_size_ltr (Minus ae1 ae2) =
    Nat.max (stack_size_ltr ae1) (S (stack_size_ltr ae2)).
Proof.
  fold_unfold_tactic stack_size_ltr.
Qed.

(* ********** *)

Lemma necessary_condition_for_cons_to_return_OK_p_when_running_ltr :
  forall (bci : byte_code_instruction)
         (bcis : list byte_code_instruction)
         (ds ds' : data_stack)
         (max_size' : nat),
    fetch_decode_execute_loop_ltr_with_profiling (bci :: bcis) ds = OK_p ds' max_size' ->
    (exists (ds_intermediate : data_stack)
            (max_size_intermediate : nat),
        (decode_execute_ltr bci ds = OK ds_intermediate)
        /\ (fetch_decode_execute_loop_ltr_with_profiling bcis ds_intermediate = OK_p ds' max_size_intermediate)
        /\ (Nat.max (list_length nat ds_intermediate) max_size_intermediate) = max_size').
Proof.
  intros bci bcis ds ds' max_size' H.
  rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons in H.
  destruct (decode_execute_ltr bci ds) as
    [ ds_intermediate
    | s
    ].
  - destruct (fetch_decode_execute_loop_ltr_with_profiling bcis ds_intermediate) as
      [ ds_final max_size_intermediate
      | s
      ] eqn:H_bcis.
    + injection H as H_ds' H_max_size'.
      exists ds_intermediate, max_size_intermediate.
      split.
      { reflexivity. }
      split.
      { rewrite <- H_ds'.
        exact H_bcis. }
      { exact H_max_size'. }
    + discriminate H.
  - discriminate H.
Qed.

Lemma necessary_condition_for_cons_to_return_KO_p_when_running_ltr :
  forall (bci : byte_code_instruction)
         (bcis : list byte_code_instruction)
         (ds : data_stack)
         (s : string),
    fetch_decode_execute_loop_ltr_with_profiling (bci :: bcis) ds = KO_p s ->
    (decode_execute_ltr bci ds = KO s)
    \/ (exists (ds_intermediate : data_stack),
           decode_execute_ltr bci ds = OK ds_intermediate
           /\ fetch_decode_execute_loop_ltr_with_profiling bcis ds_intermediate = KO_p s).
Proof.
  intros bci bcis ds s H.
  rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons in H.
  destruct (decode_execute_ltr bci ds) as
    [ ds_intermediate
    | s'
    ].
  - destruct (fetch_decode_execute_loop_ltr_with_profiling bcis ds_intermediate) as
      [ ds_final max_size_intermediate
      | s'
      ] eqn:H_bcis.
    + discriminate H.
    + right.
      exists ds_intermediate.
      split.
      { reflexivity. }
      { rewrite <- H.
        exact H_bcis. }
  - left.
    injection H as H_s.
    rewrite -> H_s.
    reflexivity.
Qed.

Lemma about_fetch_decode_execute_loop_ltr_with_profiling_and_app :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : data_stack),
    (forall (ds' : data_stack)
            (max_size' : nat),
        fetch_decode_execute_loop_ltr_with_profiling bcis1 ds = OK_p ds' max_size' ->
        (forall (ds'' : data_stack)
                (max_size'' : nat),
            fetch_decode_execute_loop_ltr_with_profiling bcis2 ds' = OK_p ds'' max_size'' ->
            fetch_decode_execute_loop_ltr_with_profiling (bcis1 ++ bcis2) ds = OK_p ds'' (Nat.max max_size' max_size''))
        /\
        (forall (s : string),
            fetch_decode_execute_loop_ltr_with_profiling bcis2 ds' = KO_p s ->
            fetch_decode_execute_loop_ltr_with_profiling (bcis1 ++ bcis2) ds = KO_p s))
    /\
    (forall (s : string),
        fetch_decode_execute_loop_ltr_with_profiling bcis1 ds = KO_p s ->
        fetch_decode_execute_loop_ltr_with_profiling (bcis1 ++ bcis2) ds = KO_p s).
Proof.
  intros bcis1 bcis2.
  induction bcis1 as
    [
    | bci1 bcis1' IHbcis1'
    ]; intros ds; split.
  - intros ds' max_size' H_bcis1.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil in H_bcis1.
    injection H_bcis1 as H_ds' H_max_size'.
    split.
    + intros ds'' max_size'' H_bcis2.
      rewrite -> fold_unfold_app_nil.
      rewrite -> H_ds'.
      rewrite <- H_max_size'.
      rewrite -> Nat.max_0_l.
      exact H_bcis2.
    + intros s H_bcis2.
      rewrite -> fold_unfold_app_nil.
      rewrite -> H_ds'.
      exact H_bcis2.
  - intros s H_bcis1.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil in H_bcis1.
    discriminate H_bcis1.
  - intros ds' max_size' H_bcis1.
    Check (necessary_condition_for_cons_to_return_OK_p_when_running_ltr).
    Check (necessary_condition_for_cons_to_return_OK_p_when_running_ltr bci1).
    Check (necessary_condition_for_cons_to_return_OK_p_when_running_ltr bci1 bcis1').
    Check (necessary_condition_for_cons_to_return_OK_p_when_running_ltr bci1 bcis1' ds).
    Check (necessary_condition_for_cons_to_return_OK_p_when_running_ltr bci1 bcis1' ds ds').
    Check (necessary_condition_for_cons_to_return_OK_p_when_running_ltr bci1 bcis1' ds ds' max_size').
    Check (necessary_condition_for_cons_to_return_OK_p_when_running_ltr bci1 bcis1' ds ds' max_size' H_bcis1).
    destruct (necessary_condition_for_cons_to_return_OK_p_when_running_ltr bci1 bcis1' ds ds' max_size' H_bcis1) as
      [ds_intermediate [max_size_intermediate [H_bci1 [H_bcis1' H_max_size']]]].
    Check (IHbcis1').
    Check (IHbcis1' ds_intermediate).
    assert (IHbcis1' := IHbcis1' ds_intermediate).
    destruct IHbcis1' as [IHbcis1'_ok _].
    Check (IHbcis1'_ok ds').
    Check (IHbcis1'_ok ds' max_size_intermediate).
    Check (IHbcis1'_ok ds' max_size_intermediate H_bcis1').
    assert (IHbcis1'_ok := IHbcis1'_ok ds' max_size_intermediate H_bcis1').
    destruct IHbcis1'_ok as [IHbcis1'_ok_ok IHbcis1'_ok_ko].
    split.
    + intros ds'' max_size'' H_bcis2.
      rewrite -> fold_unfold_app_cons.
      rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
      rewrite -> H_bci1.
      rewrite -> (IHbcis1'_ok_ok ds'' max_size'' H_bcis2).
      rewrite -> Nat.max_assoc.
      rewrite -> H_max_size'.
      reflexivity.
    + intros s H_bcis2.
      rewrite -> fold_unfold_app_cons.
      rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
      rewrite -> H_bci1.
      rewrite -> (IHbcis1'_ok_ko s H_bcis2).
      reflexivity.
  - intros s H_bcis1.
    rewrite -> fold_unfold_app_cons.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
    Check (necessary_condition_for_cons_to_return_KO_p_when_running_ltr).
    Check (necessary_condition_for_cons_to_return_KO_p_when_running_ltr bci1).
    Check (necessary_condition_for_cons_to_return_KO_p_when_running_ltr bci1 bcis1').
    Check (necessary_condition_for_cons_to_return_KO_p_when_running_ltr bci1 bcis1' ds).
    Check (necessary_condition_for_cons_to_return_KO_p_when_running_ltr bci1 bcis1' ds s).
    Check (necessary_condition_for_cons_to_return_KO_p_when_running_ltr bci1 bcis1' ds s H_bcis1).
    destruct (necessary_condition_for_cons_to_return_KO_p_when_running_ltr bci1 bcis1' ds s H_bcis1) as
      [ H_bci1
      | [ds_intermediate [H_bci1 H_bcis1']]
      ].
    + rewrite -> H_bci1.
      reflexivity.
    + rewrite -> H_bci1.
      Check (IHbcis1').
      Check (IHbcis1' ds_intermediate).
      assert (IHbcis1' := IHbcis1' ds_intermediate).
      destruct IHbcis1' as [_ IHbcis1'_ko].
      rewrite -> (IHbcis1'_ko s H_bcis1').
      reflexivity.
Qed.

(* Easier to use *)
Lemma about_fetch_decode_execute_loop_ltr_with_profiling_and_app_ok_ok :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds ds' ds'' : data_stack)
         (max_size' max_size'' : nat),
    fetch_decode_execute_loop_ltr_with_profiling bcis1 ds = OK_p ds' max_size' ->
    fetch_decode_execute_loop_ltr_with_profiling bcis2 ds' = OK_p ds'' max_size'' ->
    fetch_decode_execute_loop_ltr_with_profiling (bcis1 ++ bcis2) ds = OK_p ds'' (Nat.max max_size' max_size'').
Proof.
  intros bcis1 bcis2 ds ds' ds'' max_size' max_size'' H_bcis1 H_bcis2.
  destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_app bcis1 bcis2 ds) as [H_ok _].
  destruct (H_ok ds' max_size' H_bcis1) as [H_ok_ok _].
  exact (H_ok_ok ds'' max_size'' H_bcis2).
Qed.

(* Easier to use *)
Lemma about_fetch_decode_execute_loop_ltr_with_profiling_and_app_ok_ko :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds ds' : data_stack)
         (max_size' : nat)
         (s : string),
    fetch_decode_execute_loop_ltr_with_profiling bcis1 ds = OK_p ds' max_size' ->
    fetch_decode_execute_loop_ltr_with_profiling bcis2 ds' = KO_p s ->
    fetch_decode_execute_loop_ltr_with_profiling (bcis1 ++ bcis2) ds = KO_p s.
Proof.
  intros bcis1 bcis2 ds ds' max_size' s H_bcis1 H_bcis2.
  destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_app bcis1 bcis2 ds) as [H_ok _].
  destruct (H_ok ds' max_size' H_bcis1) as [_ H_ok_ko].
  exact (H_ok_ko s H_bcis2).
Qed.

(* Easier to use *)
Lemma about_fetch_decode_execute_loop_ltr_with_profiling_and_app_ko :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : data_stack)
         (s : string),
    fetch_decode_execute_loop_ltr_with_profiling bcis1 ds = KO_p s ->
    fetch_decode_execute_loop_ltr_with_profiling (bcis1 ++ bcis2) ds = KO_p s.
Proof.
  intros bcis1 bcis2 ds s H_bcis1.
  destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_app bcis1 bcis2 ds) as [_ H_ko].
  exact (H_ko s H_bcis1).
Qed.

Lemma about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop_ltr_with_profiling (bcis1 ++ bcis2) ds =
    match fetch_decode_execute_loop_ltr_with_profiling bcis1 ds with
    | OK_p ds' max_size' =>
      match fetch_decode_execute_loop_ltr_with_profiling bcis2 ds' with
      | OK_p ds'' max_size'' =>
        OK_p ds'' (Nat.max max_size' max_size'')
      | KO_p s =>
        KO_p s
      end
    | KO_p s =>
      KO_p s
    end.
Proof.
  intros bcis1 bcis2.
  induction bcis1 as
    [
    | bci1 bcis1' IHbcis1'
    ]; intros ds.
  - rewrite -> fold_unfold_app_nil.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
    destruct (fetch_decode_execute_loop_ltr_with_profiling bcis2 ds) as [ds'' max_size'' | s].
    + Search (Nat.max).
      rewrite -> Nat.max_0_l.
      reflexivity.
    + reflexivity.
  - rewrite -> fold_unfold_app_cons.
    rewrite ->2 fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
    destruct (decode_execute_ltr bci1 ds) as [ds' | s].
    + rewrite -> (IHbcis1' ds').
      destruct (fetch_decode_execute_loop_ltr_with_profiling bcis1' ds') as [ds'' max_size'' | s].
      * destruct (fetch_decode_execute_loop_ltr_with_profiling bcis2 ds'') as [ds''' max_size''' | s].
        { Search (Nat.max).
          rewrite -> Nat.max_assoc.
          reflexivity. }
        { reflexivity. }
      * reflexivity.
    + reflexivity.
Qed.

Lemma about_fetch_decode_execute_loop_ltr_with_profiling_and_compile_ltr :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (exists (result max_size : nat),
        fetch_decode_execute_loop_ltr_with_profiling (compile_ltr ae) ds = OK_p (result :: ds) max_size)
    \/
    (exists (s : string),
        fetch_decode_execute_loop_ltr_with_profiling (compile_ltr ae) ds = KO_p s).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    ]; intros ds.
  - left.
    rewrite -> fold_unfold_compile_ltr_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
    unfold decode_execute_ltr.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
    rewrite -> fold_unfold_list_length_cons.
    rewrite -> Nat.max_0_r.
    exists n, (S (list_length nat ds)).
    reflexivity.
  - rewrite -> fold_unfold_compile_ltr_Plus.
    rewrite -> app_assoc.
    Check (about_fetch_decode_execute_loop_ltr_with_profiling_and_app).
    Check (about_fetch_decode_execute_loop_ltr_with_profiling_and_app (compile_ltr ae1) (compile_ltr ae2) ds).
    destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_app
                (compile_ltr ae1)
                (compile_ltr ae2)
                ds) as [H_ok H_ko].
    destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_app
                (compile_ltr ae1 ++ compile_ltr ae2)
                (ADD :: nil)
                ds) as [H_ok' H_ko'].
    destruct (IHae1 ds) as
      [ [result1 [max_size1 IHae1_ok]]
      | [s1 IHae1_ko]
      ].
    + Check (H_ok (result1 :: ds)).
      Check (H_ok (result1 :: ds) max_size1).
      Check (H_ok (result1 :: ds) max_size1 IHae1_ok).
      destruct (H_ok (result1 :: ds) max_size1 IHae1_ok) as [H_ok_ok H_ok_ko].
      destruct (IHae2 (result1 :: ds)) as
        [ [result2 [max_size2 IHae2_ok]]
        | [s2 IHae2_ko]].
      * left.
        Check (H_ok_ok (result2 :: result1 :: ds)).
        Check (H_ok_ok (result2 :: result1 :: ds) max_size2).
        Check (H_ok_ok (result2 :: result1 :: ds) max_size2 IHae2_ok).
        assert (H_app := H_ok_ok (result2 :: result1 :: ds) max_size2 IHae2_ok).
        Check (about_fetch_decode_execute_loop_ltr_with_profiling_and_app).
        Check (about_fetch_decode_execute_loop_ltr_with_profiling_and_app (compile_ltr ae1 ++ compile_ltr ae2) (ADD :: nil)).
        Check (about_fetch_decode_execute_loop_ltr_with_profiling_and_app (compile_ltr ae1 ++ compile_ltr ae2) (ADD :: nil)
                 (result2 :: result1 :: ds)).
        Check (H_ok').
        Check (H_ok' (result2 :: result1 :: ds)).
        Check (H_ok' (result2 :: result1 :: ds) (Nat.max max_size1 max_size2)).
        Check (H_ok' (result2 :: result1 :: ds) (Nat.max max_size1 max_size2) H_app).
        destruct (H_ok' (result2 :: result1 :: ds) (Nat.max max_size1 max_size2) H_app) as [H_ok'_ok' _].
        Check (H_ok'_ok').
        Check (H_ok'_ok' (result1 + result2 :: ds)).
        assert (H_add : fetch_decode_execute_loop_ltr_with_profiling (ADD :: nil) (result2 :: result1 :: ds) =
                        OK_p (result1 + result2 :: ds) (S (list_length nat ds))).
        { rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
          unfold decode_execute_ltr.
          rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
          rewrite -> fold_unfold_list_length_cons.
          rewrite -> Nat.max_0_r.
          reflexivity. }
        Check (H_ok'_ok' (result1 + result2 :: ds) (S (list_length nat ds))).
        Check (H_ok'_ok' (result1 + result2 :: ds) (S (list_length nat ds)) H_add).
        rewrite -> (H_ok'_ok' (result1 + result2 :: ds) (S (list_length nat ds)) H_add).
        exists (result1 + result2), (Nat.max (Nat.max max_size1 max_size2) (S (list_length nat ds))).
        reflexivity.
      * right.
        Check (H_ok_ko s2).
        Check (H_ok_ko s2 IHae2_ko).
        assert (H_app := H_ok_ko s2 IHae2_ko).
        Check (H_ko').
        Check (H_ko' s2).
        Check (H_ko' s2 H_app).
        rewrite -> (H_ko' s2 H_app).
        exists s2.
        reflexivity.
    + right.
      Check (H_ko s1).
      Check (H_ko s1 IHae1_ko).
      assert (H_app := H_ko s1 IHae1_ko).
      rewrite -> (H_ko' s1 H_app).
      exists s1.
      reflexivity.
  - rewrite -> fold_unfold_compile_ltr_Minus.
    rewrite -> app_assoc.
    destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_app
                (compile_ltr ae1)
                (compile_ltr ae2)
                ds) as [H_ok H_ko].
    destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_app
                (compile_ltr ae1 ++ compile_ltr ae2)
                (SUB :: nil)
                ds) as [H_ok' H_ko'].
    destruct (IHae1 ds) as
      [ [result1 [max_size1 IHae1_ok]]
      | [s1 IHae1_ko]
      ].
    + destruct (H_ok (result1 :: ds) max_size1 IHae1_ok) as [H_ok_ok H_ok_ko].
      destruct (IHae2 (result1 :: ds)) as
        [ [result2 [max_size2 IHae2_ok]]
        | [s2 IHae2_ko]].
      * assert (H_app := H_ok_ok (result2 :: result1 :: ds) max_size2 IHae2_ok).
        destruct (H_ok' (result2 :: result1 :: ds) (Nat.max max_size1 max_size2) H_app) as [H_ok'_ok' H_ok'_ko'].
        destruct (result1 <? result2) eqn:H_compare.
        { right.
          assert (H_sub : fetch_decode_execute_loop_ltr_with_profiling (SUB :: nil) (result2 :: result1 :: ds) =
                          KO_p (err_msg_underflow_minus result1 result2)).
          { rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
            unfold decode_execute_ltr.
            rewrite -> H_compare.
            reflexivity. }
          rewrite -> (H_ok'_ko' (err_msg_underflow_minus result1 result2) H_sub).
          exists (err_msg_underflow_minus result1 result2).
          reflexivity. }
        { left.
          assert (H_sub : fetch_decode_execute_loop_ltr_with_profiling (SUB :: nil) (result2 :: result1 :: ds) =
                          OK_p (result1 - result2 :: ds) (S (list_length nat ds))).
          { rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
            unfold decode_execute_ltr.
            rewrite -> H_compare.
            rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
            rewrite -> fold_unfold_list_length_cons.
            rewrite -> Nat.max_0_r.
            reflexivity. }
          rewrite -> (H_ok'_ok' (result1 - result2 :: ds) (S (list_length nat ds)) H_sub).
          exists (result1 - result2), (Nat.max (Nat.max max_size1 max_size2) (S (list_length nat ds))).
          reflexivity. }
      * right.
        assert (H_app := H_ok_ko s2 IHae2_ko).
        rewrite -> (H_ko' s2 H_app).
        exists s2.
        reflexivity.
    + right.
      assert (H_app := H_ko s1 IHae1_ko).
      rewrite -> (H_ko' s1 H_app).
      exists s1.
      reflexivity.

  Restart.

  intros ae.
  induction ae as
    [ n
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    ]; intros ds.
  - left.
    rewrite -> fold_unfold_compile_ltr_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
    unfold decode_execute_ltr.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
    rewrite -> fold_unfold_list_length_cons.
    rewrite -> Nat.max_0_r.
    exists n, (S (list_length nat ds)).
    reflexivity.
  - rewrite -> fold_unfold_compile_ltr_Plus.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    destruct (IHae1 ds) as
      [ [result1 [max_size1 IHae1_ok]]
      | [s1 IHae1_ko]
      ].
    + rewrite -> IHae1_ok.
      rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
      destruct (IHae2 (result1 :: ds)) as
        [ [result2 [max_size2 IHae2_ok]]
        | [s2 IHae2_ko]
        ].
      * left.
        rewrite -> IHae2_ok.
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
        unfold decode_execute_ltr.
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
        rewrite -> fold_unfold_list_length_cons.
        rewrite -> Nat.max_0_r.
        exists (result1 + result2), (Nat.max max_size1 (Nat.max max_size2 (S (list_length nat ds)))).
        reflexivity.
      * right.
        rewrite -> IHae2_ko.
        exists s2.
        reflexivity.
    + right.
      rewrite -> IHae1_ko.
      exists s1.
      reflexivity.
  - rewrite -> fold_unfold_compile_ltr_Minus.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    destruct (IHae1 ds) as
      [ [result1 [max_size1 IHae1_ok]]
      | [s1 IHae1_ko]].
    + rewrite -> IHae1_ok.
      rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
      destruct (IHae2 (result1 :: ds)) as
        [ [result2 [max_size2 IHae2_ok]]
        | [s2 IHae2_ko]].
      * rewrite -> IHae2_ok.
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
        unfold decode_execute_ltr.
        destruct (result1 <? result2).
        { right.
          exists (err_msg_underflow_minus result1 result2).
          reflexivity. }
        left.
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
        rewrite -> fold_unfold_list_length_cons.
        rewrite -> Nat.max_0_r.
        exists (result1 - result2), (Nat.max max_size1 (Nat.max max_size2 (S (list_length nat ds)))).
        reflexivity.
      * right.
        rewrite -> IHae2_ko.
        exists s2.
        reflexivity.
    + right.
      rewrite -> IHae1_ko.
      exists s1.
      reflexivity.
Qed.

Proposition about_the_stack_size_required_when_running_ltr_aux :
  forall (ae : arithmetic_expression)
         (ds : data_stack)
         (result max_size : nat),
    fetch_decode_execute_loop_ltr_with_profiling (compile_ltr ae) ds = OK_p (result :: ds) max_size ->
    stack_size_ltr ae + list_length nat ds = max_size.
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    ]; intros ds result max_size H.
  - rewrite -> fold_unfold_stack_size_ltr_Literal.
    rewrite -> fold_unfold_compile_ltr_Literal in H.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons in H.
    unfold decode_execute_ltr in H.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil in H.
    rewrite -> fold_unfold_list_length_cons in H.
    rewrite -> Nat.max_0_r in H.
    injection H as _ H_max_size.
    (* `injection` also does the two previous rewrites if they are missing,
       but better be explicit *)
    rewrite -> Nat.add_1_l.
    exact H_max_size.
  - rewrite -> fold_unfold_stack_size_ltr_Plus.
    rewrite -> fold_unfold_compile_ltr_Plus in H.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt in H.
    destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_compile_ltr ae1 ds) as
      [ [result1 [max_size1 Hae1_ok]]
      | [s1 Hae1_ko]
      ].
    + rewrite -> Hae1_ok in H.
      rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt in H.
      destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_compile_ltr ae2 (result1 :: ds)) as
        [ [result2 [max_size2 Hae2_ok]]
        | [s2 Hae2_ko]
        ].
      * rewrite -> Hae2_ok in H.
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons in H.
        unfold decode_execute_ltr in H.
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil in H.
        rewrite -> fold_unfold_list_length_cons in H.
        rewrite -> Nat.max_0_r in H.
        Check (IHae1 ds result1 max_size1 Hae1_ok).
        assert (IHae1 := IHae1 ds result1 max_size1 Hae1_ok).
        assert (IHae2 := IHae2 (result1 :: ds) result2 max_size2 Hae2_ok).
        rewrite -> fold_unfold_list_length_cons in IHae2.
        assert (H_max_size2 : S (list_length nat ds) <= max_size2).
        { rewrite <- (Nat.add_0_l (S (list_length nat ds))).
          rewrite <- IHae2.
          Search (_ + _ <= _).
          apply Nat.add_le_mono_r.
          Search (0 <= _).
          apply Nat.le_0_l. }
        Search (Nat.max).
        rewrite -> (Nat.max_l _ _ H_max_size2) in H.
        injection H as _ H_max_size.
        rewrite <- Nat.add_max_distr_r.
        rewrite -> Nat.add_succ_comm.
        rewrite -> IHae1.
        rewrite -> IHae2.
        exact H_max_size.
      * rewrite -> Hae2_ko in H.
        discriminate H.
    + rewrite Hae1_ko in H.
      discriminate H.
  - rewrite -> fold_unfold_stack_size_ltr_Minus.
    rewrite -> fold_unfold_compile_ltr_Minus in H.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt in H.
    destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_compile_ltr ae1 ds) as
      [ [result1 [max_size1 Hae1_ok]]
      | [s1 Hae1_ko]
      ].
    + rewrite -> Hae1_ok in H.
      rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt in H.
      destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_compile_ltr ae2 (result1 :: ds)) as
        [ [result2 [max_size2 Hae2_ok]]
        | [s2 Hae2_ko]
        ].
      * rewrite -> Hae2_ok in H.
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons in H.
        unfold decode_execute_ltr in H.
        destruct (result1 <? result2).
        { discriminate H. }
        rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil in H.
        rewrite -> fold_unfold_list_length_cons in H.
        rewrite -> Nat.max_0_r in H.
        assert (IHae1 := IHae1 ds result1 max_size1 Hae1_ok).
        assert (IHae2 := IHae2 (result1 :: ds) result2 max_size2 Hae2_ok).
        rewrite -> fold_unfold_list_length_cons in IHae2.
        assert (H_max_size2 : S (list_length nat ds) <= max_size2).
        { rewrite <- (Nat.add_0_l (S (list_length nat ds))).
          rewrite <- IHae2.
          apply Nat.add_le_mono_r.
          apply Nat.le_0_l. }
        rewrite -> (Nat.max_l _ _ H_max_size2) in H.
        injection H as _ H_max_size.
        rewrite <- Nat.add_max_distr_r.
        rewrite -> Nat.add_succ_comm.
        rewrite -> IHae1.
        rewrite -> IHae2.
        exact H_max_size.
      * rewrite -> Hae2_ko in H.
        discriminate H.
    + rewrite Hae1_ko in H.
      discriminate H.
Qed.

Proposition about_the_stack_size_required_when_running_ltr :
  forall (ae : arithmetic_expression)
         (result max_size : nat),
    run_ltr_with_profiling (compile_ltr ae) = Expressible_nat_p result max_size ->
    stack_size_ltr ae = max_size.
Proof.
  unfold run_ltr_with_profiling.
  intros ae result max_size H.
  Check (about_the_stack_size_required_when_running_ltr_aux ae).
  Check (about_the_stack_size_required_when_running_ltr_aux ae nil).
  Check (about_the_stack_size_required_when_running_ltr_aux ae nil result).
  Check (about_the_stack_size_required_when_running_ltr_aux ae nil result max_size).
  assert (H_aux := about_the_stack_size_required_when_running_ltr_aux ae nil result max_size).
  destruct (about_fetch_decode_execute_loop_ltr_with_profiling_and_compile_ltr ae nil) as
    [ [result' [max_size' Hae_ok]]
    | [s Hae_ko]
    ].
  - rewrite -> Hae_ok in H.
    injection H as H_result H_max_size.
    rewrite -> H_result in Hae_ok.
    rewrite -> H_max_size in Hae_ok.
    assert (H_aux := H_aux Hae_ok).
    rewrite -> fold_unfold_list_length_nil in H_aux.
    rewrite -> Nat.add_0_r in H_aux.
    exact H_aux.
  - rewrite -> Hae_ko in H.
    discriminate H.
Qed.

(* ********** *)

Lemma about_evaluate_ltr_and_fetch_decode_execute_loop_ltr_with_profiling_and_compiler_ltr :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (result : nat),
        evaluate_ltr ae = Expressible_nat result ->
        (exists max_size : nat,
            fetch_decode_execute_loop_ltr_with_profiling (compile_ltr ae) ds = OK_p (result :: ds) max_size))
    /\
    (forall (s : string),
        evaluate_ltr ae = Expressible_msg s ->
        fetch_decode_execute_loop_ltr_with_profiling (compile_ltr ae) ds = KO_p s).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 IHae1 ae2 IHae2
    | ae1 IHae1 ae2 IHae2
    ]; intros ds; split.
  - intros result H_evaluate.
    rewrite -> fold_unfold_evaluate_ltr_Literal in H_evaluate.
    injection H_evaluate as H_result.
    rewrite -> fold_unfold_compile_ltr_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
    unfold decode_execute_ltr.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
    rewrite -> fold_unfold_list_length_cons.
    rewrite -> Nat.max_0_r.
    rewrite -> H_result.
    exists (S (list_length nat ds)).
    reflexivity.
  - intros s H_evaluate.
    rewrite -> fold_unfold_evaluate_ltr_Literal in H_evaluate.
    discriminate H_evaluate.
  - intros result H_evaluate.
    rewrite -> fold_unfold_compile_ltr_Plus.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    (* use 'necessary_condition' lemma *)
    Check (necessary_condition_for_Plus_to_return_Expressible_nat_when_evaluating_ltr).
    Check (necessary_condition_for_Plus_to_return_Expressible_nat_when_evaluating_ltr ae1 ae2 result H_evaluate).
    destruct (necessary_condition_for_Plus_to_return_Expressible_nat_when_evaluating_ltr ae1 ae2 result H_evaluate) as
      [n1 [n2 [H_evaluate1 [H_evaluate2 H_result]]]].
    destruct (IHae1 ds) as [IHae1_ok _].
    Check (IHae1_ok).
    Check (IHae1_ok n1 H_evaluate1).
    destruct (IHae1_ok n1 H_evaluate1) as [max_size1 H_run1].
    rewrite -> H_run1.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    destruct (IHae2 (n1 :: ds)) as [IHae2_ok _].
    destruct (IHae2_ok n2 H_evaluate2) as [max_size2 H_run2].
    rewrite -> H_run2.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
    unfold decode_execute_ltr.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
    rewrite -> fold_unfold_list_length_cons.
    rewrite -> Nat.max_0_r.
    rewrite -> H_result.
    exists (Nat.max max_size1 (Nat.max max_size2 (S (list_length nat ds)))).
    reflexivity.
  - intros s H_evaluate.
    rewrite -> fold_unfold_compile_ltr_Plus.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    destruct (IHae1 ds) as [IHae1_ok IHae1_ko].
    Check (necessary_condition_for_Plus_to_return_Expressible_msg_when_evaluating_ltr).
    Check (necessary_condition_for_Plus_to_return_Expressible_msg_when_evaluating_ltr ae1 ae2 s H_evaluate).
    destruct (necessary_condition_for_Plus_to_return_Expressible_msg_when_evaluating_ltr ae1 ae2 s H_evaluate) as
      [ H_evaluate1
      | [n [H_evaluate1 H_evaluate2]]
      ].
    + rewrite -> (IHae1_ko s H_evaluate1).
      reflexivity.
    + destruct (IHae1_ok n H_evaluate1) as [max_size1 H_run1].
      rewrite -> H_run1.
      rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
      destruct (IHae2 (n :: ds)) as [_ IHae2_ko].
      rewrite -> (IHae2_ko s H_evaluate2).
      reflexivity.
  - intros result H_evaluate.
    rewrite -> fold_unfold_compile_ltr_Minus.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    destruct (necessary_condition_for_Minus_to_return_Expressible_nat_when_evaluating_ltr ae1 ae2 result H_evaluate) as
      [n1 [n2 [H_evaluate1 [H_evaluate2 [H_compare H_result]]]]].
    destruct (IHae1 ds) as [IHae1_ok _].
    destruct (IHae1_ok n1 H_evaluate1) as [max_size1 H_run1].
    rewrite -> H_run1.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    destruct (IHae2 (n1 :: ds)) as [IHae2_ok _].
    destruct (IHae2_ok n2 H_evaluate2) as [max_size2 H_run2].
    rewrite -> H_run2.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
    unfold decode_execute_ltr.
    rewrite -> H_compare.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_nil.
    rewrite -> fold_unfold_list_length_cons.
    rewrite -> Nat.max_0_r.
    rewrite -> H_result.
    exists (Nat.max max_size1 (Nat.max max_size2 (S (list_length nat ds)))).
    reflexivity.
  - intros s H_evaluate.
    rewrite -> fold_unfold_compile_ltr_Minus.
    rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
    destruct (IHae1 ds) as [IHae1_ok IHae1_ko].
    Check (necessary_condition_for_Minus_to_return_Expressible_msg_when_evaluating_ltr ae1 ae2 s H_evaluate).
    destruct (necessary_condition_for_Minus_to_return_Expressible_msg_when_evaluating_ltr ae1 ae2 s H_evaluate) as
      [ H_evaluate1
      | [ [n [H_evaluate1 H_evaluate2]]
        | [n1 [n2 [H_evaluate1 [H_evaluate2 [H_compare H_s]]]]]
        ]
      ].
    + rewrite -> (IHae1_ko s H_evaluate1).
      reflexivity.
    + destruct (IHae1_ok n H_evaluate1) as [max_size1 H_run1].
      rewrite -> H_run1.
      rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
      destruct (IHae2 (n :: ds)) as [_ IHae2_ko].
      rewrite -> (IHae2_ko s H_evaluate2).
      reflexivity.
    + destruct (IHae1_ok n1 H_evaluate1) as [max_size1 H_run1].
      rewrite -> H_run1.
      rewrite -> about_fetch_decode_execute_loop_ltr_with_profiling_and_app_alt.
      destruct (IHae2 (n1 :: ds)) as [IHae2_ok _].
      destruct (IHae2_ok n2 H_evaluate2) as [max_size2 H_run2].
      rewrite -> H_run2.
      rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_with_profiling_cons.
      unfold decode_execute_ltr.
      rewrite -> H_compare.
      rewrite -> H_s.
      reflexivity.
Qed.

Theorem the_commuting_diagram_for_ltr_evaluation :
  forall (ae : arithmetic_expression),
    (exists result max_size : nat,
        evaluate_ltr ae = Expressible_nat result
        /\ run_ltr_with_profiling (compile_ltr ae) = Expressible_nat_p result max_size)
    \/
    (exists s : string,
        evaluate_ltr ae = Expressible_msg s
        /\ run_ltr_with_profiling (compile_ltr ae) = Expressible_msg_p s).
Proof.
  unfold run_ltr_with_profiling.
  intros ae.
  destruct (about_evaluate_ltr_and_fetch_decode_execute_loop_ltr_with_profiling_and_compiler_ltr ae nil) as [H_ok H_ko].
  destruct (evaluate_ltr ae) as [result | s].
  - left.
    destruct (H_ok result eq_refl) as [max_size H_run].
    exists result, max_size.
    split.
    { reflexivity. }
    { rewrite -> H_run.
      reflexivity. }
  - right.
    exists s.
    split.
    { reflexivity. }
    { rewrite -> (H_ko s eq_refl).
      reflexivity. }
Qed.

Lemma about_the_stack_size_required_when_running_ltr_alt_aux :
  forall (ae : arithmetic_expression)
         (ds : data_stack)
         (result : nat),
    evaluate_ltr ae = Expressible_nat result ->
    fetch_decode_execute_loop_ltr_with_profiling (compile_ltr ae) ds =
    OK_p (result :: ds) (stack_size_ltr ae + list_length nat ds).
Proof.
  intros ae ds result H_evaluate.
  destruct (about_evaluate_ltr_and_fetch_decode_execute_loop_ltr_with_profiling_and_compiler_ltr ae ds) as [H_ok _].
  destruct (H_ok result H_evaluate) as [max_size H_run].
  rewrite -> H_run.
  Check (about_the_stack_size_required_when_running_ltr_aux).
  Check (about_the_stack_size_required_when_running_ltr_aux ae ds result max_size).
  Check (about_the_stack_size_required_when_running_ltr_aux ae ds result max_size H_run).
  rewrite -> (about_the_stack_size_required_when_running_ltr_aux ae ds result max_size H_run).
  reflexivity.
Qed.

Proposition about_the_stack_size_required_when_running_ltr_alt :
  forall (ae : arithmetic_expression)
         (result : nat),
    evaluate_ltr ae = Expressible_nat result ->
    run_ltr_with_profiling (compile_ltr ae) =
    Expressible_nat_p result (stack_size_ltr ae).
Proof.
  unfold run_ltr_with_profiling.
  intros ae result H_evaluate.
  Check (about_the_stack_size_required_when_running_ltr_alt_aux ae nil result H_evaluate).
  rewrite -> (about_the_stack_size_required_when_running_ltr_alt_aux ae nil result H_evaluate).
  rewrite -> fold_unfold_list_length_nil.
  rewrite -> Nat.add_0_r.
  reflexivity.
Qed.

(* ********** *)

Fixpoint depth (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal _ =>
    0
  | Plus ae1 ae2 =>
    S (Nat.max (depth ae1) (depth ae2))
  | Minus ae1 ae2 =>
    S (Nat.max (depth ae1) (depth ae2))
  end.

Lemma fold_unfold_depth_Literal :
  forall n : nat,
    depth (Literal n) = 0.
Proof.
  fold_unfold_tactic depth.
Qed.

Lemma fold_unfold_depth_Plus :
  forall ae1 ae2 : arithmetic_expression,
    depth (Plus ae1 ae2) =
    S (Nat.max (depth ae1) (depth ae2)).
Proof.
  fold_unfold_tactic depth.
Qed.

Lemma fold_unfold_depth_Minus :
  forall ae1 ae2 : arithmetic_expression,
    depth (Minus ae1 ae2) =
    S (Nat.max (depth ae1) (depth ae2)).
Proof.
  fold_unfold_tactic depth.
Qed.

Fixpoint depth_after_refactoring_left (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal _ =>
    0
  | Plus ae1 ae2 =>
    depth_after_refactoring_left_aux ae2 (depth_after_refactoring_left ae1)
  | Minus ae1 ae2 =>
    S (Nat.max (depth_after_refactoring_left ae1) (depth_after_refactoring_left ae2))
  end
  with depth_after_refactoring_left_aux (ae : arithmetic_expression) (a : nat) : nat :=
    match ae with
    | Literal _ =>
      S a
    | Plus ae1 ae2 =>
      depth_after_refactoring_left_aux ae2 (depth_after_refactoring_left_aux ae1 a)
    | Minus ae1 ae2 =>
      S (Nat.max (S (Nat.max (depth_after_refactoring_left ae1) (depth_after_refactoring_left ae2))) a)
    end.

Compute
  (let ae := Plus
               (Literal 1)
               (Literal 2)
   in depth (super_refactor_left ae) = depth_after_refactoring_left ae).

Compute
  (let ae := Plus
               (Plus
                  (Literal 1)
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Literal 4))
   in depth (super_refactor_left ae) = depth_after_refactoring_left ae).

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7)))
   in depth (super_refactor_left ae) = depth_after_refactoring_left ae).

Lemma fold_unfold_depth_after_refactoring_left_Literal :
  forall n : nat,
    depth_after_refactoring_left (Literal n) = 0.
Proof.
  fold_unfold_tactic depth_after_refactoring_left.
Qed.

Lemma fold_unfold_depth_after_refactoring_left_Plus :
  forall ae1 ae2 : arithmetic_expression,
    depth_after_refactoring_left (Plus ae1 ae2) =
    depth_after_refactoring_left_aux ae2 (depth_after_refactoring_left ae1).
Proof.
  fold_unfold_tactic depth_after_refactoring_left.
Qed.

Lemma fold_unfold_depth_after_refactoring_left_Minus :
  forall ae1 ae2 : arithmetic_expression,
    depth_after_refactoring_left (Minus ae1 ae2) =
    S (Nat.max (depth_after_refactoring_left ae1) (depth_after_refactoring_left ae2)).
Proof.
  fold_unfold_tactic depth_after_refactoring_left.
Qed.

Lemma fold_unfold_depth_after_refactoring_left_aux_Literal :
  forall (n a : nat),
    depth_after_refactoring_left_aux (Literal n) a = S a.
Proof.
  fold_unfold_tactic depth_after_refactoring_left_aux.
Qed.

Lemma fold_unfold_depth_after_refactoring_left_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : nat),
    depth_after_refactoring_left_aux (Plus ae1 ae2) a =
    depth_after_refactoring_left_aux ae2 (depth_after_refactoring_left_aux ae1 a).
Proof.
  fold_unfold_tactic depth_after_refactoring_left_aux.
Qed.

Lemma fold_unfold_depth_after_refactoring_left_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : nat),
    depth_after_refactoring_left_aux (Minus ae1 ae2) a =
    S (Nat.max (S (Nat.max (depth_after_refactoring_left ae1) (depth_after_refactoring_left ae2))) a).
Proof.
  fold_unfold_tactic depth_after_refactoring_left_aux.
Qed.

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   let ae' := Plus
                (Literal 1)
                (Literal 2) in
   depth (super_refactor_left_aux ae (super_refactor_left ae')) =
   depth_after_refactoring_left_aux ae (depth_after_refactoring_left ae')).

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   let ae' := Minus
                (Plus
                   (Plus
                      (Literal 1)
                      (Literal 5))
                   (Literal 2))
                (Plus
                   (Literal 3)
                   (Plus
                      (Literal 6)
                      (Literal 7))) in
   depth (super_refactor_left_aux ae (super_refactor_left ae')) =
   depth_after_refactoring_left_aux ae (depth_after_refactoring_left ae')).

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   let ae' := Minus
                (Plus
                   (Plus
                      (Plus
                         (Literal 0)
                         (Literal 1))
                      (Literal 5))
                   (Literal 2))
                (Plus
                   (Literal 3)
                   (Plus
                      (Literal 6)
                      (Literal 7))) in
   depth (super_refactor_left_aux ae (super_refactor_left ae')) =
   depth_after_refactoring_left_aux ae (depth_after_refactoring_left ae')).

Lemma depth_after_refactoring_left_equals_depth_composed_with_super_refactor_left_aux :
  forall (ae : arithmetic_expression),
    depth_after_refactoring_left ae = depth (super_refactor_left ae)
    /\
    (forall (ae' : arithmetic_expression),
        depth_after_refactoring_left_aux ae (depth_after_refactoring_left ae') =
        depth (super_refactor_left_aux ae (super_refactor_left ae'))).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite -> fold_unfold_depth_after_refactoring_left_Literal.
    rewrite -> fold_unfold_super_refactor_left_Literal.
    rewrite -> fold_unfold_depth_Literal.
    reflexivity.
  - admit.
  - rewrite -> fold_unfold_depth_after_refactoring_left_Plus.
    rewrite -> fold_unfold_super_refactor_left_Plus.
    rewrite -> (IHae2_aux ae1).
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_depth_after_refactoring_left_aux_Plus.
    rewrite -> fold_unfold_super_refactor_left_aux_Plus.
    rewrite -> (IHae1_aux ae').
    admit.
Abort.

Lemma depth_after_refactoring_left_equals_depth_composed_with_super_refactor_left_aux :
  forall (ae : arithmetic_expression),
    depth_after_refactoring_left ae = depth (super_refactor_left ae)
    /\
    (forall (ae' : arithmetic_expression),
        depth_after_refactoring_left_aux ae (depth (super_refactor_left ae')) =
        depth (super_refactor_left_aux ae (super_refactor_left ae'))).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite -> fold_unfold_depth_after_refactoring_left_Literal.
    rewrite -> fold_unfold_super_refactor_left_Literal.
    rewrite -> fold_unfold_depth_Literal.
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_depth_after_refactoring_left_aux_Literal.
    rewrite -> fold_unfold_super_refactor_left_aux_Literal.
    rewrite -> fold_unfold_depth_Plus.
    rewrite -> fold_unfold_depth_Literal.
    rewrite -> Nat.max_0_r.
    reflexivity.
  - rewrite -> fold_unfold_depth_after_refactoring_left_Plus.
    rewrite -> fold_unfold_super_refactor_left_Plus.
    rewrite -> IHae1.
    rewrite -> (IHae2_aux ae1).
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_depth_after_refactoring_left_aux_Plus.
    rewrite -> fold_unfold_super_refactor_left_aux_Plus.
    rewrite -> (IHae1_aux ae').
    admit.
Abort.

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   let ae' := Plus
                (Literal 1)
                (Literal 2) in
   depth (super_refactor_left_aux ae ae') =
   depth_after_refactoring_left_aux ae (depth ae')).

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   let ae' := Minus
                (Plus
                   (Plus
                      (Literal 1)
                      (Literal 5))
                   (Literal 2))
                (Plus
                   (Literal 3)
                   (Plus
                      (Literal 6)
                      (Literal 7))) in
   depth (super_refactor_left_aux ae ae') =
   depth_after_refactoring_left_aux ae (depth ae')).

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   let ae' := Minus
                (Plus
                   (Plus
                      (Literal 5)
                      (Plus
                         (Literal 0)
                         (Literal 1)))
                   (Literal 2))
                (Plus
                   (Literal 3)
                   (Plus
                      (Literal 6)
                      (Literal 7))) in
   depth (super_refactor_left_aux ae ae') =
   depth_after_refactoring_left_aux ae (depth ae')).

Lemma depth_after_refactoring_left_equals_depth_composed_with_super_refactor_left_aux :
  forall (ae : arithmetic_expression),
    depth_after_refactoring_left ae = depth (super_refactor_left ae)
    /\
    (forall (ae' : arithmetic_expression),
        depth_after_refactoring_left_aux ae (depth ae') =
        depth (super_refactor_left_aux ae ae')).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite -> fold_unfold_depth_after_refactoring_left_Literal.
    rewrite -> fold_unfold_super_refactor_left_Literal.
    rewrite -> fold_unfold_depth_Literal.
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_depth_after_refactoring_left_aux_Literal.
    rewrite -> fold_unfold_super_refactor_left_aux_Literal.
    rewrite -> fold_unfold_depth_Plus.
    rewrite -> fold_unfold_depth_Literal.
    rewrite -> Nat.max_0_r.
    reflexivity.
  - rewrite -> fold_unfold_depth_after_refactoring_left_Plus.
    rewrite -> fold_unfold_super_refactor_left_Plus.
    rewrite -> IHae1.
    rewrite -> (IHae2_aux (super_refactor_left ae1)).
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_depth_after_refactoring_left_aux_Plus.
    rewrite -> fold_unfold_super_refactor_left_aux_Plus.
    rewrite -> (IHae1_aux ae').
    rewrite -> (IHae2_aux (super_refactor_left_aux ae1 ae')).
    reflexivity.
  - rewrite -> fold_unfold_depth_after_refactoring_left_Minus.
    rewrite -> fold_unfold_super_refactor_left_Minus.
    rewrite -> fold_unfold_depth_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_depth_after_refactoring_left_aux_Minus.
    rewrite -> fold_unfold_super_refactor_left_aux_Minus.
    rewrite -> fold_unfold_depth_Plus.
    rewrite -> fold_unfold_depth_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Proposition depth_after_refactoring_left_equals_depth_composed_with_super_refactor_left :
  forall (ae : arithmetic_expression),
    depth_after_refactoring_left ae = depth (super_refactor_left ae).
Proof.
  intros ae.
  destruct (depth_after_refactoring_left_equals_depth_composed_with_super_refactor_left_aux ae) as [ly _].
  exact ly.
Qed.

(* ********** *)

Fixpoint stack_size_ltr_after_refactoring_left (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal _ =>
    1
  | Plus ae1 ae2 =>
    stack_size_ltr_after_refactoring_left_aux ae2 (stack_size_ltr_after_refactoring_left ae1)
  | Minus ae1 ae2 =>
    Nat.max (stack_size_ltr_after_refactoring_left ae1) (S (stack_size_ltr_after_refactoring_left ae2))
  end
  with stack_size_ltr_after_refactoring_left_aux (ae : arithmetic_expression) (a : nat) : nat :=
    match ae with
    | Literal _ =>
      Nat.max a 2
    | Plus ae1 ae2 =>
      stack_size_ltr_after_refactoring_left_aux ae2 (stack_size_ltr_after_refactoring_left_aux ae1 a)
    | Minus ae1 ae2 =>
      Nat.max (Nat.max (stack_size_ltr_after_refactoring_left ae1) (S (stack_size_ltr_after_refactoring_left ae2))) (S a)
    end.

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   let ae' := Plus
                (Literal 1)
                (Literal 2) in
   stack_size_ltr (super_refactor_left ae) =
   stack_size_ltr_after_refactoring_left ae).

Compute
  (let ae := Minus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   stack_size_ltr (super_refactor_left ae) =
   stack_size_ltr_after_refactoring_left ae).

Compute
  (let ae := Plus
               (Plus
                  (Plus
                     (Literal 1)
                     (Literal 5))
                  (Literal 2))
               (Plus
                  (Literal 3)
                  (Plus
                     (Literal 6)
                     (Literal 7))) in
   stack_size_ltr (super_refactor_left ae) =
   stack_size_ltr_after_refactoring_left ae).

Lemma fold_unfold_stack_size_ltr_after_refactoring_left_Literal :
  forall n : nat,
    stack_size_ltr_after_refactoring_left (Literal n) = 1.
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_left.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_left_Plus :
  forall ae1 ae2 : arithmetic_expression,
    stack_size_ltr_after_refactoring_left (Plus ae1 ae2) =
    stack_size_ltr_after_refactoring_left_aux ae2 (stack_size_ltr_after_refactoring_left ae1).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_left.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_left_Minus :
  forall ae1 ae2 : arithmetic_expression,
    stack_size_ltr_after_refactoring_left (Minus ae1 ae2) =
    Nat.max (stack_size_ltr_after_refactoring_left ae1) (S (stack_size_ltr_after_refactoring_left ae2)).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_left.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_left_aux_Literal :
  forall (n a : nat),
    stack_size_ltr_after_refactoring_left_aux (Literal n) a =
    Nat.max a 2.
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_left_aux.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_left_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : nat),
    stack_size_ltr_after_refactoring_left_aux (Plus ae1 ae2) a =
    stack_size_ltr_after_refactoring_left_aux ae2 (stack_size_ltr_after_refactoring_left_aux ae1 a).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_left_aux.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_left_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : nat),
    stack_size_ltr_after_refactoring_left_aux (Minus ae1 ae2) a =
    Nat.max (Nat.max (stack_size_ltr_after_refactoring_left ae1) (S (stack_size_ltr_after_refactoring_left ae2))) (S a).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_left_aux.
Qed.

Lemma stack_size_ltr_after_refactoring_left_equals_stack_size_ltr_composed_with_super_refactor_left_aux :
  forall (ae : arithmetic_expression),
    stack_size_ltr_after_refactoring_left ae =
    stack_size_ltr (super_refactor_left ae)
    /\
    (forall (ae' : arithmetic_expression),
        stack_size_ltr_after_refactoring_left_aux ae (stack_size_ltr ae') =
        stack_size_ltr (super_refactor_left_aux ae ae')).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite -> fold_unfold_stack_size_ltr_after_refactoring_left_Literal.
    rewrite -> fold_unfold_super_refactor_left_Literal.
    rewrite -> fold_unfold_stack_size_ltr_Literal.
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_stack_size_ltr_after_refactoring_left_aux_Literal.
    rewrite -> fold_unfold_super_refactor_left_aux_Literal.
    rewrite -> fold_unfold_stack_size_ltr_Plus.
    rewrite -> fold_unfold_stack_size_ltr_Literal.
    reflexivity.
  - rewrite -> fold_unfold_stack_size_ltr_after_refactoring_left_Plus.
    rewrite -> fold_unfold_super_refactor_left_Plus.
    rewrite -> IHae1.
    rewrite -> (IHae2_aux (super_refactor_left ae1)).
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_stack_size_ltr_after_refactoring_left_aux_Plus.
    rewrite -> fold_unfold_super_refactor_left_aux_Plus.
    rewrite -> (IHae1_aux ae').
    rewrite -> (IHae2_aux (super_refactor_left_aux ae1 ae')).
    reflexivity.
  - rewrite -> fold_unfold_stack_size_ltr_after_refactoring_left_Minus.
    rewrite -> fold_unfold_super_refactor_left_Minus.
    rewrite -> fold_unfold_stack_size_ltr_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_stack_size_ltr_after_refactoring_left_aux_Minus.
    rewrite -> fold_unfold_super_refactor_left_aux_Minus.
    rewrite -> fold_unfold_stack_size_ltr_Plus.
    rewrite -> fold_unfold_stack_size_ltr_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Lemma stack_size_ltr_after_refactoring_left_equals_stack_size_ltr_composed_with_super_refactor_left :
  forall (ae : arithmetic_expression),
    stack_size_ltr_after_refactoring_left ae =
    stack_size_ltr (super_refactor_left ae).
Proof.
  intros ae.
  destruct (stack_size_ltr_after_refactoring_left_equals_stack_size_ltr_composed_with_super_refactor_left_aux ae) as [ly _].
  exact ly.
Qed.

Proposition about_the_stack_size_required_when_running_ltr_after_refactoring_left :
  forall (ae : arithmetic_expression)
         (result max_size : nat),
    run_ltr_with_profiling (compile_ltr (super_refactor_left ae)) = Expressible_nat_p result max_size ->
    stack_size_ltr_after_refactoring_left ae = max_size.
Proof.
  intros ae.
  rewrite -> stack_size_ltr_after_refactoring_left_equals_stack_size_ltr_composed_with_super_refactor_left.
  exact (about_the_stack_size_required_when_running_ltr (super_refactor_left ae)).
Qed.

(* ********** *)

Fixpoint super_refactor_right (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_right_aux ae1 (super_refactor_right ae2)
  | Minus ae1 ae2 =>
    Minus (super_refactor_right ae1) (super_refactor_right ae2)
  end
  with super_refactor_right_aux (ae a : arithmetic_expression) : arithmetic_expression :=
    match ae with
    | Literal n =>
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

Fixpoint stack_size_ltr_after_refactoring_right (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal _ =>
    1
  | Plus ae1 ae2 =>
    stack_size_ltr_after_refactoring_right_aux ae1 (stack_size_ltr_after_refactoring_right ae2)
  | Minus ae1 ae2 =>
    Nat.max (stack_size_ltr_after_refactoring_right ae1) (S (stack_size_ltr_after_refactoring_right ae2))
  end
  with stack_size_ltr_after_refactoring_right_aux (ae : arithmetic_expression) (a : nat) : nat :=
    match ae with
    | Literal _ =>
      Nat.max 1 (S a)
    | Plus ae1 ae2 =>
      stack_size_ltr_after_refactoring_right_aux ae1 (stack_size_ltr_after_refactoring_right_aux ae2 a)
    | Minus ae1 ae2 =>
      Nat.max (Nat.max (stack_size_ltr_after_refactoring_right ae1) (S (stack_size_ltr_after_refactoring_right ae2))) (S a)
    end.

Lemma fold_unfold_stack_size_ltr_after_refactoring_right_Literal :
  forall n : nat,
    stack_size_ltr_after_refactoring_right (Literal n) = 1.
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_right.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_right_Plus :
  forall ae1 ae2 : arithmetic_expression,
    stack_size_ltr_after_refactoring_right (Plus ae1 ae2) =
    stack_size_ltr_after_refactoring_right_aux ae1 (stack_size_ltr_after_refactoring_right ae2).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_right.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_right_Minus :
  forall ae1 ae2 : arithmetic_expression,
    stack_size_ltr_after_refactoring_right (Minus ae1 ae2) =
    Nat.max (stack_size_ltr_after_refactoring_right ae1) (S (stack_size_ltr_after_refactoring_right ae2)).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_right.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_right_aux_Literal :
  forall (n a : nat),
    stack_size_ltr_after_refactoring_right_aux (Literal n) a =
    Nat.max 1 (S a).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_right_aux.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_right_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : nat),
    stack_size_ltr_after_refactoring_right_aux (Plus ae1 ae2) a =
    stack_size_ltr_after_refactoring_right_aux ae1 (stack_size_ltr_after_refactoring_right_aux ae2 a).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_right_aux.
Qed.

Lemma fold_unfold_stack_size_ltr_after_refactoring_right_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : nat),
    stack_size_ltr_after_refactoring_right_aux (Minus ae1 ae2) a =
    Nat.max (Nat.max (stack_size_ltr_after_refactoring_right ae1) (S (stack_size_ltr_after_refactoring_right ae2))) (S a).
Proof.
  fold_unfold_tactic stack_size_ltr_after_refactoring_right_aux.
Qed.

Lemma stack_size_ltr_after_refactoring_right_equals_stack_size_ltr_composed_with_super_refactor_right_aux :
  forall (ae : arithmetic_expression),
    stack_size_ltr_after_refactoring_right ae =
    stack_size_ltr (super_refactor_right ae)
    /\
    (forall (ae' : arithmetic_expression),
        stack_size_ltr_after_refactoring_right_aux ae (stack_size_ltr ae') =
        stack_size_ltr (super_refactor_right_aux ae ae')).
Proof.
  intros ae.
  induction ae as
    [ n
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    | ae1 [IHae1 IHae1_aux] ae2 [IHae2 IHae2_aux]
    ]; split.
  - rewrite -> fold_unfold_stack_size_ltr_after_refactoring_right_Literal.
    rewrite -> fold_unfold_super_refactor_right_Literal.
    rewrite -> fold_unfold_stack_size_ltr_Literal.
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_stack_size_ltr_after_refactoring_right_aux_Literal.
    rewrite -> fold_unfold_super_refactor_right_aux_Literal.
    rewrite -> fold_unfold_stack_size_ltr_Plus.
    rewrite -> fold_unfold_stack_size_ltr_Literal.
    reflexivity.
  - rewrite -> fold_unfold_stack_size_ltr_after_refactoring_right_Plus.
    rewrite -> fold_unfold_super_refactor_right_Plus.
    rewrite -> IHae2.
    rewrite -> (IHae1_aux (super_refactor_right ae2)).
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_stack_size_ltr_after_refactoring_right_aux_Plus.
    rewrite -> fold_unfold_super_refactor_right_aux_Plus.
    rewrite -> (IHae2_aux ae').
    rewrite -> (IHae1_aux (super_refactor_right_aux ae2 ae')).
    reflexivity.
  - rewrite -> fold_unfold_stack_size_ltr_after_refactoring_right_Minus.
    rewrite -> fold_unfold_super_refactor_right_Minus.
    rewrite -> fold_unfold_stack_size_ltr_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - intros ae'.
    rewrite -> fold_unfold_stack_size_ltr_after_refactoring_right_aux_Minus.
    rewrite -> fold_unfold_super_refactor_right_aux_Minus.
    rewrite -> fold_unfold_stack_size_ltr_Plus.
    rewrite -> fold_unfold_stack_size_ltr_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Lemma stack_size_ltr_after_refactoring_right_equals_stack_size_ltr_composed_with_super_refactor_right :
  forall (ae : arithmetic_expression),
    stack_size_ltr_after_refactoring_right ae =
    stack_size_ltr (super_refactor_right ae).
Proof.
  intros ae.
  destruct (stack_size_ltr_after_refactoring_right_equals_stack_size_ltr_composed_with_super_refactor_right_aux ae) as [ly _].
  exact ly.
Qed.

Proposition about_the_stack_size_required_when_running_ltr_after_refactoring_right :
  forall (ae : arithmetic_expression)
         (result max_size : nat),
    run_ltr_with_profiling (compile_ltr (super_refactor_right ae)) = Expressible_nat_p result max_size ->
    stack_size_ltr_after_refactoring_right ae = max_size.
Proof.
  intros ae.
  rewrite -> stack_size_ltr_after_refactoring_right_equals_stack_size_ltr_composed_with_super_refactor_right.
  exact (about_the_stack_size_required_when_running_ltr (super_refactor_right ae)).
Qed.

(* ********** *)

(* end of week3_refactoring-left-and-right.v *)
