(* midterm-project.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Sat 19 Oct 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List String Ascii.

(* ********** *)

(* Abstract syntax of source programs: *)

Definition name : Type := string.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Name : name -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Equality predicates: *)

Definition option_eqb (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
    Some v1 =>
    match ov2 with
     | Some v2 =>
      eqb_V v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
      Some v =>
      false
    | None =>
      true
    end
  end.

Definition String_eqb (s1 s2 : string) : bool :=
  match String.string_dec s1 s2 with
    left _ =>
      true
  | right _ =>
      false
  end.

Definition name_eqb (x1 x2  : name) : bool :=
  String_eqb x1 x2.

Fixpoint arithmetic_expression_eqb (ae1 ae2 : arithmetic_expression) : bool :=
  match ae1 with
    Literal n1 =>
    match ae2 with
      Literal n2 =>
      Nat.eqb n1 n2
    | _ =>
      false
    end
  | Name x1 =>
    match ae2 with 
      Name x2 =>
      name_eqb x1 x2
    | _ =>
      false
    end
  | Plus ae11 ae12 =>
    match ae2 with
      Plus ae21 ae22 =>
      arithmetic_expression_eqb ae11 ae21 && arithmetic_expression_eqb ae12 ae22
    | _ =>
      false
    end
  | Times ae11 ae12 =>
    match ae2 with
      Times ae21 ae22 =>
      arithmetic_expression_eqb ae11 ae21 && arithmetic_expression_eqb ae12 ae22
    | _ =>
      false
    end
  end.

Definition source_program_eqb (sp1 sp2 : source_program) : bool :=
  match sp1 with
    Source_program ae1 =>
    match sp2 with
      Source_program ae2 =>
      arithmetic_expression_eqb ae1 ae2
    end
  end.

(* ********** *)

(* The abstract data type of environments: *)

Definition environment (denotable : Type) : Type :=
  list (name * denotable).

Definition mt (denotable : Type) : environment denotable :=
  nil.

Definition extend (denotable : Type) (x : name) (d : denotable) (e : environment denotable) : environment denotable :=
  (x , d) :: e.

Fixpoint lookup (denotable : Type) (x : name) (e : environment denotable) : option denotable :=
  match e with
    nil =>
    None
  | (x', d) :: e' =>
    if String_eqb x x'
    then Some d
    else lookup denotable x e'
  end.

(* ********** *)

Inductive source_msg : Type :=
  Source_undeclared_name : string -> source_msg.

Inductive source_expressible_value : Type :=
  Source_expressible_nat : nat -> source_expressible_value
| Source_expressible_msg : source_msg -> source_expressible_value.

(* ********** *)

(* The source interpreter: *)

Fixpoint evaluate_ltr (ae : arithmetic_expression) (e : environment nat) : source_expressible_value :=
  match ae with
    Literal n =>
    Source_expressible_nat n
  | Name x =>
    match lookup nat x e with
      Some n =>
      Source_expressible_nat n
    | None =>
      Source_expressible_msg (Source_undeclared_name x)
    end
  | Plus ae1 ae2 =>
    match evaluate_ltr ae1 e with
      Source_expressible_nat n1 =>
      match evaluate_ltr ae2 e with
        Source_expressible_nat n2 =>
        Source_expressible_nat (n1 + n2)
      | Source_expressible_msg s2 =>
        Source_expressible_msg s2
      end
    | Source_expressible_msg s1 =>
      Source_expressible_msg s1
    end
  | Times ae1 ae2 =>
    match evaluate_ltr ae1 e with
      Source_expressible_nat n1 =>
      match evaluate_ltr ae2 e with
        Source_expressible_nat n2 =>
        Source_expressible_nat (n1 * n2)
      | Source_expressible_msg s2 =>
        Source_expressible_msg s2
      end
    | Source_expressible_msg s1 =>
      Source_expressible_msg s1
    end
  end.

Lemma fold_unfold_evaluate_ltr_Literal :
  forall (n : nat) (e : environment nat),
    evaluate_ltr (Literal n) e = Source_expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.
    
Lemma fold_unfold_evaluate_ltr_Name :
  forall (x : string) (e : environment nat),
    evaluate_ltr (Name x) e =
      match lookup nat x e with
        Some n =>
          Source_expressible_nat n
      | None =>
          Source_expressible_msg (Source_undeclared_name x)
      end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Plus :
  forall (ae1 ae2 : arithmetic_expression) (e : environment nat),
    evaluate_ltr (Plus ae1 ae2) e = 
      match evaluate_ltr ae1 e with
        Source_expressible_nat n1 =>
          match evaluate_ltr ae2 e with
            Source_expressible_nat n2 =>
              Source_expressible_nat (n1 + n2)
          | Source_expressible_msg s2 =>
              Source_expressible_msg s2
          end
      | Source_expressible_msg s1 =>
          Source_expressible_msg s1
      end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Times :
  forall (ae1 ae2 : arithmetic_expression) (e : environment nat),
    evaluate_ltr (Times ae1 ae2) e =
      match evaluate_ltr ae1 e with
        Source_expressible_nat n1 =>
          match evaluate_ltr ae2 e with
            Source_expressible_nat n2 =>
              Source_expressible_nat (n1 * n2)
          | Source_expressible_msg s2 =>
              Source_expressible_msg s2
          end
      | Source_expressible_msg s1 =>
          Source_expressible_msg s1
      end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Definition interpret_ltr (sp : source_program) (e : environment nat) : source_expressible_value :=
  match sp with
    Source_program ae =>
    evaluate_ltr ae e
  end.

(* ********** *)

(* Abstract syntax of target programs: *)

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| LOOKUP : string -> byte_code_instruction
| ADD : byte_code_instruction
| MUL : byte_code_instruction.

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

(* ********** *)

(* The compiler: *)

Fixpoint compile_ltr_aux (ae : arithmetic_expression) : list byte_code_instruction :=
    match ae with
      Literal n =>
      PUSH n :: nil
    | Name x =>
      LOOKUP x :: nil
    | Plus ae1 ae2 =>
      compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ ADD :: nil
    | Times ae1 ae2 =>
      compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ MUL :: nil
    end.

Definition compile_ltr (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_ltr_aux ae)
  end.

(* ********** *)

(* The target interpreter (a.k.a. virtual machine): *)

Definition data_stack : Type :=
  list nat.

Inductive result_msg : Type :=
  Result_undeclared_name : string -> result_msg
| Result_stack_underflow : byte_code_instruction -> result_msg.

Inductive result_of_decoding_and_execution : Type :=
  OK : data_stack -> result_of_decoding_and_execution
| KO : result_msg -> result_of_decoding_and_execution.

Definition decode_execute_ltr (bci : byte_code_instruction) (e : environment nat) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
  | PUSH n =>
    OK (n :: ds)
  | LOOKUP x =>
    match lookup nat x e with
      Some n =>
      OK (n :: ds)
    | None =>
      KO (Result_undeclared_name x)
    end
  | ADD =>
      match ds with
        nil =>
        KO (Result_stack_underflow ADD)
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' =>
            OK ((n1 + n2) :: ds'')
          | nil =>
            KO (Result_stack_underflow ADD)
          end
      end
  | MUL =>
      match ds with
      | nil =>
        KO (Result_stack_underflow MUL)
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' =>
            OK ((n1 * n2) :: ds'')
          | nil =>
            KO (Result_stack_underflow MUL)
          end
      end
  end.

Fixpoint fetch_decode_execute_loop_ltr (bcis : list byte_code_instruction) (e : environment nat) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
    nil =>
    OK ds
  | bci :: bcis' =>
    match decode_execute_ltr bci e ds with
    | OK ds' =>
      fetch_decode_execute_loop_ltr bcis' e ds'
    | KO m =>
      KO m
    end
  end.

Inductive target_msg : Type :=
  Target_undeclared_name : string -> target_msg
| Target_stack_underflow : byte_code_instruction -> target_msg
| Target_stack_O : target_msg
| Target_stack_SS : target_msg.

Inductive target_expressible_value : Type :=
  Target_expressible_nat : nat -> target_expressible_value
| Target_expressible_msg : target_msg -> target_expressible_value.

Definition run_ltr (tp : target_program) (e : environment nat) : target_expressible_value :=
  match tp with
    Target_program bcis =>
    match fetch_decode_execute_loop_ltr bcis e nil with
      OK nil =>
      Target_expressible_msg Target_stack_O
    | OK (n :: nil) =>
      Target_expressible_nat n
    | OK (n :: _ :: _) =>
      Target_expressible_msg Target_stack_SS
    | KO (Result_undeclared_name x) =>
      Target_expressible_msg (Target_undeclared_name x)
    | KO (Result_stack_underflow bci) =>
      Target_expressible_msg (Target_stack_underflow bci)
    end
  end.

(* ********** *)

Theorem the_commuting_diagram_ltr :
  forall (sp : source_program)
         (e : environment nat),
    (forall n : nat,
        interpret_ltr sp e = Source_expressible_nat n
        <->
        run_ltr (compile_ltr sp) e = Target_expressible_nat n)
    /\
    (forall s : string,
        interpret_ltr sp e = Source_expressible_msg (Source_undeclared_name s)
        <->
        run_ltr (compile_ltr sp) e = Target_expressible_msg (Target_undeclared_name s)).
Proof.
Admitted.

(* ********** *)

Definition Magritte_data_stack : Type :=
  list arithmetic_expression.

Definition Magritte_result_of_decoding_and_execution : Type :=
  option Magritte_data_stack.

Definition Magritte_decode_execute_ltr (bci : byte_code_instruction) (ds : Magritte_data_stack) : Magritte_result_of_decoding_and_execution :=
  match bci with
  | PUSH n =>
    Some (Literal n :: ds)
  | LOOKUP x =>
    Some (Name x :: ds)
  | ADD =>
      match ds with
        nil =>
        None
      | ae2 :: ds' =>
          match ds' with
          | ae1 :: ds'' =>
            Some (Plus ae1 ae2 :: ds'')
          | nil =>
            None
          end
      end
  | MUL =>
      match ds with
      | nil =>
        None
      | ae2 :: ds' =>
          match ds' with
          | ae1 :: ds'' =>
            Some (Times ae1 ae2 :: ds'')
          | nil =>
            None
          end
      end
  end.

Fixpoint Magritte_fetch_decode_execute_loop_ltr (bcis : list byte_code_instruction) (ds : Magritte_data_stack) : Magritte_result_of_decoding_and_execution :=
  match bcis with
    nil =>
    Some ds
  | bci :: bcis' =>
    match Magritte_decode_execute_ltr bci ds with
    | Some ds' =>
      Magritte_fetch_decode_execute_loop_ltr bcis' ds'
    | None =>
      None
    end
  end.

Definition Magritte_target_expressible_value : Type :=
  option source_program.

Definition Magritte_target_expressible_value_eqb (mtev1 mtev2 : Magritte_target_expressible_value) : bool :=
  option_eqb source_program source_program_eqb mtev1 mtev2.

Definition Magritte_run_ltr (tp : target_program) : Magritte_target_expressible_value :=
  match tp with
    Target_program bcis =>
    match Magritte_fetch_decode_execute_loop_ltr bcis nil with
      Some nil =>
      None
    | Some (ae :: nil) =>
      Some (Source_program ae)
    | Some (ae :: _ :: _) =>
      None
    | None =>
      None
    end
  end.

(* ********** *)

(* Definition:
   A _constant expression_ is an expression that does not contain any names.
   We say that it is "constant" because evaluating it always yields the same expressible nat.
 *)

(* Task 1:
   Formalize a simplifier that replaces all constant expressions by the corresponding literal.
*)

(* This is the inspiration for an intermediate type, will be used in report don't delete ples *)
Fixpoint simplify_ltr_simple (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
    Literal n =>
      Literal n
  | Name x =>
      Name x
  | Plus ae1 ae2 =>
      match ae1 with
        Literal n1 =>
          match ae2 with
            Literal n2 =>
              Literal (n1 + n2)
          | Name x2 =>
              Plus (Literal n1) (Name x2)
          | _ =>
              Plus (simplify_ltr_simple ae1) (simplify_ltr_simple ae2) (* Need to peak *)
          end
      | _ =>
          Name "not implemented"%string
      end
  | _ =>
      Name "not implemented"%string
  end.

(* Task 1a:
   Expand the unit-test function just above with more tests
   and argue that your tests cover all possible cases.
*)

(*
  TODO: Implement a more robust but non-redundant unit test for constant_or_not_constant_from_arithmetic_expression with code coverage.
*)

(* ***** test cases ***** *)

Definition test_ae1 : arithmetic_expression :=
  Plus
    (Literal 1)
    (Literal 10).

Definition expected_ae1 : arithmetic_expression :=
  Literal 11.

Definition test_ae2 : arithmetic_expression :=
  Plus
    (Literal 1)
    (Name "x"%string).

Definition expected_ae2 : arithmetic_expression :=
  Plus
    (Literal 1)
    (Name "x"%string).

Definition test_ae3 : arithmetic_expression :=
  Times
    (Literal 2)
    (Literal 3).

Definition expected_ae3 : arithmetic_expression :=
  Literal 6.

Definition test_ae4 : arithmetic_expression :=
  Times
    (Literal 2)
    (Name "y"%string).

Definition expected_ae4 : arithmetic_expression :=
  Times
    (Literal 2)
    (Name "y"%string).

Definition test_ae5 : arithmetic_expression :=
  Plus
    (Plus
       (Literal 1)
       (Literal 2))
    (Plus
       (Literal 3)
       (Name "x"%string)).

Definition expected_ae5 : arithmetic_expression :=
  Plus
    (Literal 3)
    (Plus
       (Literal 3)
       (Name "x"%string)).

Definition test_ae6 : arithmetic_expression :=
  Plus
    (Times
       (Literal 2)
       (Literal 3))
    (Name "z"%string).

Definition expected_ae6 : arithmetic_expression :=
  Plus
    (Literal 6)
    (Name "z"%string).

Definition test_ae7 : arithmetic_expression :=
  Plus
    (Name "x"%string)
    (Name "y"%string).

Definition expected_ae7 : arithmetic_expression :=
  Plus
    (Name "x"%string)
    (Name "y"%string).

Definition test_ae8 : arithmetic_expression :=
  Times
    (Name "x"%string)
    (Name "y"%string).

Definition expected_ae8 : arithmetic_expression :=
  Times
    (Name "x"%string)
    (Name "y"%string).

Definition test_ae9 : arithmetic_expression :=
  Plus
    (Plus
       (Literal 2)
       (Name "x"%string))
    (Literal 3).

Definition expected_ae9 : arithmetic_expression :=
  Plus
    (Plus
       (Literal 2)
       (Name "x"%string))
    (Literal 3).

Definition test_ae10 : arithmetic_expression :=
  Times
    (Times
       (Literal 4)
       (Name "y"%string))
    (Literal 5).

Definition expected_ae10 : arithmetic_expression :=
  Times
    (Times
       (Literal 4)
       (Name "y"%string))
    (Literal 5).

Definition test_ae11 : arithmetic_expression :=
  Plus
    (Times
       (Literal 2)
       (Name "a"%string))
    (Plus
       (Times
          (Literal 3)
          (Name "b"%string))
       (Literal 5)).

Definition expected_ae11 : arithmetic_expression :=
  Plus
    (Times
       (Literal 2)
       (Name "a"%string))
    (Plus
       (Times
          (Literal 3)
          (Name "b"%string))
       (Literal 5)).

Definition test_ae12 : arithmetic_expression :=
  Times
    (Plus
       (Literal 1)
       (Name "x"%string))
    (Plus
       (Name "y"%string)
       (Literal 2)).

Definition expected_ae12 : arithmetic_expression :=
  Times
    (Plus
       (Literal 1)
       (Name "x"%string))
    (Plus
       (Name "y"%string)
       (Literal 2)).

Definition test_ae13 : arithmetic_expression :=
  (Plus
     (Plus
        (Literal 1)
        (Literal 2))
     (Plus
        (Name "x"%string)
        (Literal 3))).

Definition expected_ae13 : arithmetic_expression :=
  (Plus
     (Literal 3)
     (Plus (Name "x"%string)
        (Literal 3))).

Definition test_ae14 : arithmetic_expression :=
  (Times
     (Times
        (Literal 1)
        (Literal 2))
     (Times
        (Name "x"%string)
        (Literal 3))).

Definition expected_ae14 : arithmetic_expression :=
  (Times
     (Literal 2)
     (Times (Name "x"%string)
        (Literal 3))).
  
Definition test_simplify (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  (arithmetic_expression_eqb (candidate test_ae1) expected_ae1) &&
  (arithmetic_expression_eqb (candidate test_ae2) expected_ae2) &&
  (arithmetic_expression_eqb (candidate test_ae3) expected_ae3) &&
  (arithmetic_expression_eqb (candidate test_ae4) expected_ae4) &&
  (arithmetic_expression_eqb (candidate test_ae5) expected_ae5) &&
  (arithmetic_expression_eqb (candidate test_ae6) expected_ae6) &&
  (arithmetic_expression_eqb (candidate test_ae7) expected_ae7) &&
  (arithmetic_expression_eqb (candidate test_ae8) expected_ae8) &&
  (arithmetic_expression_eqb (candidate test_ae9) expected_ae9) &&
  (arithmetic_expression_eqb (candidate test_ae10) expected_ae10) &&
  (arithmetic_expression_eqb (candidate test_ae11) expected_ae11) &&
  (arithmetic_expression_eqb (candidate test_ae12) expected_ae12) &&
  (arithmetic_expression_eqb (candidate test_ae13) expected_ae13) &&
  (arithmetic_expression_eqb (candidate test_ae14) expected_ae14).

(* Task 1b:
   Implement a simplifier and verify that it satisfies the unit-test function.
 *)

(*
  the simplifier maps a given arithmetic expression either to a nat(a constant arithmetic expression), or to an arithmetic expression that is not a nat (a non-constant arithmetic expression)
*)

Inductive constant_or_not_constant : Type :=
| C : nat -> constant_or_not_constant
| NC : arithmetic_expression -> constant_or_not_constant.

(* simplify_ltr *)

Fixpoint simplify_ltr_aux (ae : arithmetic_expression) : constant_or_not_constant :=
  match ae with
  | Literal n =>
      C n
  | Name x =>
      NC (Name x)
  | Plus ae1 ae2 =>
      match simplify_ltr_aux ae1 with
      | C n1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              C (n1 + n2)
          | NC ae2 =>
              NC (Plus (Literal n1) ae2)
          end
      | NC ae1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              NC (Plus ae1 (Literal n2))
          | NC ae2 =>
              NC (Plus ae1 ae2)
          end
      end
  | Times ae1 ae2 =>
      match simplify_ltr_aux ae1 with
      | C n1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              C (n1 * n2)
          | NC ae2 =>
              NC (Times (Literal n1) ae2)
          end
      | NC ae1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              NC (Times ae1 (Literal n2))
          | NC ae2 =>
              NC (Times ae1 ae2)
          end
      end
  end.
  
Lemma fold_unfold_simplify_ltr_aux_Literal :
  forall n : nat,
    simplify_ltr_aux (Literal n) = C n.
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Lemma fold_unfold_simplify_ltr_aux_Name :
  forall x : string,
    simplify_ltr_aux (Name x) = NC (Name x).
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Lemma fold_unfold_simplify_ltr_aux_Plus :
  forall ae1 ae2 : arithmetic_expression,
    simplify_ltr_aux (Plus ae1 ae2) =
      match simplify_ltr_aux ae1 with
      | C n1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              C (n1 + n2)
          | NC ae2 =>
              NC (Plus (Literal n1) ae2)
          end
      | NC ae1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              NC (Plus ae1 (Literal n2))
          | NC ae2 =>
              NC (Plus ae1 ae2)
          end
      end.
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Lemma fold_unfold_simplify_ltr_aux_Times :
  forall ae1 ae2 : arithmetic_expression,
    simplify_ltr_aux (Times ae1 ae2) =
      match simplify_ltr_aux ae1 with
      | C n1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              C (n1 * n2)
          | NC ae2 =>
              NC (Times (Literal n1) ae2)
          end
      | NC ae1 =>
          match simplify_ltr_aux ae2 with
          | C n2 =>
              NC (Times ae1 (Literal n2))
          | NC ae2 =>
              NC (Times ae1 ae2)
          end
      end.
Proof.
  fold_unfold_tactic simplify_ltr_aux.
Qed.

Definition simplify_ltr (ae : arithmetic_expression) : arithmetic_expression :=
  match simplify_ltr_aux ae with
  | C n =>
      Literal n
  | NC ae' =>
      ae'
  end.

Compute (test_simplify simplify_ltr).

(* Task 1c:
   Argue that your unit tests provide code coverage.
   (And if they don't, expand test_simplify so that they do.)
*)

(* Task 1d:
   Prove that your simplifier is idempotent: Once an expression is simplified, it contains no constant sub-expressions.
 *)

(* simplify ltr *)

Lemma simplify_ltr_is_idempotent_aux :
  forall ae ae' : arithmetic_expression,
    simplify_ltr_aux ae = NC ae' ->
    simplify_ltr_aux ae' = NC ae'.
Proof.
  intro ae.
  induction ae as [ n | x | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ];
    intro a.
  - intro H_absurd.
    rewrite -> fold_unfold_simplify_ltr_aux_Literal in H_absurd.
    discriminate H_absurd.
  - intro H.
    rewrite -> fold_unfold_simplify_ltr_aux_Name in H.
    injection H as H.
    rewrite <- H.
    rewrite -> fold_unfold_simplify_ltr_aux_Name.
    reflexivity.
  - intro H.
    rewrite -> fold_unfold_simplify_ltr_aux_Plus in H.
    case (simplify_ltr_aux ae1) as [c1 | nc1] eqn:C_simplify_ae1.
    + case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
      * discriminate H.
      * injection H as H.
        rewrite <- H.
        rewrite -> fold_unfold_simplify_ltr_aux_Plus.
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        Check (IHae2 nc2 eq_refl).
        rewrite -> (IHae2 nc2 eq_refl).
        reflexivity.
    + case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
      * injection H as H.
        rewrite <- H.
        rewrite -> fold_unfold_simplify_ltr_aux_Plus.
        Check (IHae1 nc1 eq_refl).
        rewrite -> (IHae1 nc1 eq_refl).
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        reflexivity.
      * injection H as H.
        rewrite <- H.
        rewrite -> fold_unfold_simplify_ltr_aux_Plus.
        Check (IHae1 nc1 eq_refl).
        rewrite -> (IHae1 nc1 eq_refl).
        rewrite -> (IHae2 nc2 eq_refl).
        reflexivity.
  - intro H.
    rewrite -> fold_unfold_simplify_ltr_aux_Times in H.
    case (simplify_ltr_aux ae1) as [c1 | nc1] eqn:C_simplify_ae1.
    + case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
      * discriminate H.
      * injection H as H.
        rewrite <- H.
        rewrite -> fold_unfold_simplify_ltr_aux_Times.
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        Check (IHae2 nc2 eq_refl).
        rewrite -> (IHae2 nc2 eq_refl).
        reflexivity.
    + case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
      * injection H as H.
        rewrite <- H.
        rewrite -> fold_unfold_simplify_ltr_aux_Times.
        Check (IHae1 nc1 eq_refl).
        rewrite -> (IHae1 nc1 eq_refl).
        rewrite -> fold_unfold_simplify_ltr_aux_Literal.
        reflexivity.
      * injection H as H.
        rewrite <- H.
        rewrite -> fold_unfold_simplify_ltr_aux_Times.
        Check (IHae1 nc1 eq_refl).
        rewrite -> (IHae1 nc1 eq_refl).
        rewrite -> (IHae2 nc2 eq_refl).
        reflexivity.
Qed.

Theorem simplify_ltr_is_idempotent :
  forall ae : arithmetic_expression,
    simplify_ltr ae = simplify_ltr (simplify_ltr ae).
  Compute (let x := simplify_ltr test_ae5 in
           let y := simplify_ltr (simplify_ltr test_ae5) in
           x = y).
  Compute (let x := simplify_ltr test_ae10 in
           let y := simplify_ltr (simplify_ltr test_ae10) in
           x = y).
  Compute (let x := simplify_ltr test_ae12 in
           let y := simplify_ltr (simplify_ltr test_ae12) in
           x = y).
  Compute (let x := simplify_ltr test_ae14 in
           let y := simplify_ltr (simplify_ltr test_ae14) in
           x = y).
Proof.
  intro ae.
  unfold simplify_ltr.
  assert (H_aux := simplify_ltr_is_idempotent_aux ae).
  case ae as [n | x | ae1 ae2 | ae1 ae2] eqn:C_ae.
  - rewrite ->2 fold_unfold_simplify_ltr_aux_Literal.
    reflexivity.
  - rewrite ->2 fold_unfold_simplify_ltr_aux_Name.
    reflexivity.
  - case (simplify_ltr_aux (Plus ae1 ae2)) as [c | nc].
    + rewrite -> fold_unfold_simplify_ltr_aux_Literal.
      reflexivity.
    + rewrite -> ((H_aux nc) eq_refl).
      reflexivity.
  - case (simplify_ltr_aux (Times ae1 ae2)) as [c | nc].
    + rewrite -> fold_unfold_simplify_ltr_aux_Literal.
      reflexivity.
    + rewrite -> ((H_aux nc) eq_refl).
      reflexivity.
Qed.

(* simplify_rtl *)

(* TODO : Theorem simplify_ltr_is_idempotent *)

(* Task 1e:
   Prove that your simplifier is meaning-preserving,
   i.e., that evaluating an expression and a simplified expression always yield the same expressible value.
 *)
 *)

Lemma simplify_ltr_preserves_evaluation_aux :
  forall (ae : arithmetic_expression) (e : environment nat),
    (forall n : nat,
        simplify_ltr_aux ae = C n ->
        evaluate_ltr ae e = Source_expressible_nat n)
    /\
    (forall a' : arithmetic_expression,
        simplify_ltr_aux ae = NC a' ->
        evaluate_ltr ae e = evaluate_ltr a' e).
Proof.
  intro ae.
  induction ae as [ n | x | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ];
    intro e.
  - split.
    + intros n1 H.
      rewrite -> fold_unfold_simplify_ltr_aux_Literal in H.
      injection H as H.
      rewrite -> fold_unfold_evaluate_ltr_Literal.
      rewrite -> H.
      reflexivity.
    + intros a H.
      rewrite -> fold_unfold_simplify_ltr_aux_Literal in H.
      discriminate H.
  - split.
    + intros n H.
      rewrite -> fold_unfold_simplify_ltr_aux_Name in H.
      discriminate H.
    + intros a H.
      rewrite -> fold_unfold_simplify_ltr_aux_Name in H.
      injection H as H.
      rewrite -> H.
      reflexivity.
  - split.
    + intros n H.
      rewrite -> fold_unfold_simplify_ltr_aux_Plus in H.
      case (simplify_ltr_aux ae1) as [c1 | nc1] eqn:C_simplify_ae1.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- injection H as H.
           rewrite <- H.
           rewrite -> fold_unfold_evaluate_ltr_Plus.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [IHae2_n _].
           assert (IHae2_n := IHae2_n c2 eq_refl).
           rewrite -> IHae2_n.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [IHae1_n _].
           assert (IHae1_n := IHae1_n c1 eq_refl).
           rewrite -> IHae1_n.
           reflexivity.
        -- discriminate H.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- discriminate H.
        -- discriminate H.
    + intros a H.
      rewrite -> fold_unfold_simplify_ltr_aux_Plus in H.
      case (simplify_ltr_aux ae1) as [c1 | nc1] eqn:C_simplify_ae1.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- discriminate H.
        -- injection H as H.
           rewrite <- H.
           rewrite ->2 fold_unfold_evaluate_ltr_Plus.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [IHae1_n _].
           assert (IHae1_n := IHae1_n c1 eq_refl).
           rewrite -> IHae1_n.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [_ IHae2_nc].
           assert (IHae2_nc := IHae2_nc nc2 eq_refl).
           rewrite -> IHae2_nc.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           reflexivity.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- injection H as H.
           rewrite <- H.
           rewrite ->2 fold_unfold_evaluate_ltr_Plus.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [IHae2_n _].
           assert (IHae2_n := IHae2_n c2 eq_refl).
           rewrite -> IHae2_n.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [_ IHae1_nc].
           assert (IHae1_nc := IHae1_nc nc1 eq_refl).
           rewrite -> IHae1_nc.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           reflexivity.
        -- injection H as H.
           rewrite <- H.
           rewrite ->2 fold_unfold_evaluate_ltr_Plus.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [_ IHae2_nc].
           assert (IHae2_nc := IHae2_nc nc2 eq_refl).
           rewrite -> IHae2_nc.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [_ IHae1_nc].
           assert (IHae1_nc := IHae1_nc nc1 eq_refl).
           rewrite -> IHae1_nc.
           reflexivity.
  - split.
    + intros n H.
      rewrite -> fold_unfold_simplify_ltr_aux_Times in H.
      case (simplify_ltr_aux ae1) as [c1 | nc1] eqn:C_simplify_ae1.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- injection H as H.
           rewrite <- H.
           rewrite -> fold_unfold_evaluate_ltr_Times.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [IHae2_n _].
           assert (IHae2_n := IHae2_n c2 eq_refl).
           rewrite -> IHae2_n.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [IHae1_n _].
           assert (IHae1_n := IHae1_n c1 eq_refl).
           rewrite -> IHae1_n.
           reflexivity.
        -- discriminate H.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- discriminate H.
        -- discriminate H.
    + intros a H.
      rewrite -> fold_unfold_simplify_ltr_aux_Times in H.
      case (simplify_ltr_aux ae1) as [c1 | nc1] eqn:C_simplify_ae1.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- discriminate H.
        -- injection H as H.
           rewrite <- H.
           rewrite ->2 fold_unfold_evaluate_ltr_Times.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [IHae1_n _].
           assert (IHae1_n := IHae1_n c1 eq_refl).
           rewrite -> IHae1_n.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [_ IHae2_nc].
           assert (IHae2_nc := IHae2_nc nc2 eq_refl).
           rewrite -> IHae2_nc.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           reflexivity.
      * case (simplify_ltr_aux ae2) as [c2 | nc2] eqn:C_simplify_ae2.
        -- injection H as H.
           rewrite <- H.
           rewrite ->2 fold_unfold_evaluate_ltr_Times.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [IHae2_n _].
           assert (IHae2_n := IHae2_n c2 eq_refl).
           rewrite -> IHae2_n.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [_ IHae1_nc].
           assert (IHae1_nc := IHae1_nc nc1 eq_refl).
           rewrite -> IHae1_nc.
           rewrite -> fold_unfold_evaluate_ltr_Literal.
           reflexivity.
        -- injection H as H.
           rewrite <- H.
           rewrite ->2 fold_unfold_evaluate_ltr_Times.
           assert (IHae2 := IHae2 e).
           destruct IHae2 as [_ IHae2_nc].
           assert (IHae2_nc := IHae2_nc nc2 eq_refl).
           rewrite -> IHae2_nc.
           assert (IHae1 := IHae1 e).
           destruct IHae1 as [_ IHae1_nc].
           assert (IHae1_nc := IHae1_nc nc1 eq_refl).
           rewrite -> IHae1_nc.
           reflexivity.
Qed.

Proposition simplify_ltr_preserves_evaluation :
  forall (ae : arithmetic_expression) (e : environment nat),
    evaluate_ltr (simplify_ltr ae) e = evaluate_ltr ae e.
Proof.
  intros ae e.
  unfold simplify_ltr.
  Check (simplify_ltr_preserves_evaluation_aux ae e).
  destruct (simplify_ltr_preserves_evaluation_aux ae e) as [H_C H_NC].
  destruct (simplify_ltr_aux ae) as [c | nc].
  - assert (H_C := H_C c eq_refl).
    rewrite -> H_C.
    rewrite -> fold_unfold_evaluate_ltr_Literal.
    reflexivity.
  - assert (H_NC := H_NC nc eq_refl).
    rewrite -> H_NC.
    reflexivity.
Qed.

(* ********** *)

(* task 2:
   Each of the following "optimizing" compilers exploits a semantic property of arithmetic expressions.
   Your task is to identify this property for each compiler.

   You should proceed in two separate ways:
   - take a "black box" approach and figure out what the compiler does by feeding it with appropriate source programs and then analyzing the corresponding target programs;
   - take a "white box" approach and figure out what the compiler does by reading its code.

   Unless you absolutely want to, no theorems and no proofs are required here, just examples and narrative clarity.
*)

(* Relevant quote:
   "It is not forbidden to think."
   -- Carmen
*)

(* For example, if the optimization is a transformation (e.g., simplifying "1 * e" into "e"),
   for source programs where the transformation has been done already (here, source programs with no occurrence of "1 * e"),
   then the optimizing compiler gives the same result as the standard compiler.
*)

(* ***** *)

(* Here is a worked-out example for compile_peculiar, which is defined just below. *)

Fixpoint compile_peculiar_aux (ae : arithmetic_expression) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    PUSH n :: a
  | Name x =>
    LOOKUP x :: a
  | Plus ae1 ae2 =>
    compile_peculiar_aux ae2 (compile_peculiar_aux ae1 (ADD :: a))
  | Times ae1 ae2 =>
    compile_peculiar_aux ae2 (compile_peculiar_aux ae1 (MUL :: a))
  end.

Definition compile_peculiar (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_peculiar_aux ae nil)
  end.

(* Both the black-box approach and the white-box approach suggest that
   compile_peculiar commutes additions and multiplications.
   However, this commutation is not semantically correct for left-to-right evaluation,
   and therefore this optimizing compiler is incorrect.
*)

(* Counter-example: *)

Compute (let sp1 := Source_program (Plus (Name "x"%string) (Name "y"%string)) in
         let tp1 := compile_peculiar sp1 in
         (interpret_ltr sp1 nil, run_ltr tp1 nil)).

(* In words,
   interpreting sp1 yields Source_expressible_msg (Source_undeclared_name "x")
   whereas
   interpreting tp1 yields Target_expressible_msg (Target_undeclared_name "y"),
   which are not the same error messages. *)

(* This worked-out example illustrates
   that you also need to assess the correctness each optimizing compiler.
*)

(* ***** *)

(* compile_bizarre *)

Fixpoint compile_bizarre_aux_Plus (ae : arithmetic_expression) (k : list byte_code_instruction -> list byte_code_instruction -> list byte_code_instruction) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    k (PUSH n :: nil) a
  | Name x =>
    k (LOOKUP x :: nil) a
  | Plus ae1 ae2 =>
    compile_bizarre_aux_Plus ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Plus ae2 k a1) (ADD :: a)
  | Times ae1 ae2 =>
    k (compile_bizarre_aux_Times ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Times ae2 (fun bcis2 a2 => bcis2 ++ a2) a1) (MUL :: nil)) a
  end
with compile_bizarre_aux_Times (ae : arithmetic_expression) (k : list byte_code_instruction -> list byte_code_instruction -> list byte_code_instruction) (a : list byte_code_instruction) : list byte_code_instruction :=
       match ae with
         Literal n =>
         k (PUSH n :: nil) a
       | Name x =>
         k (LOOKUP x :: nil) a
       | Plus ae1 ae2 =>
         k (compile_bizarre_aux_Plus ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Plus ae2 (fun bcis2 a2 => bcis2 ++ a2) a1) (ADD :: nil)) a
       | Times ae1 ae2 =>
         compile_bizarre_aux_Times ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Times ae2 k a1) (MUL :: a)
       end.

Fixpoint compile_bizarre_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
    Literal n =>
    PUSH n :: nil
  | Name x =>
    LOOKUP x :: nil
  | Plus ae1 ae2 =>
    compile_bizarre_aux_Plus ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Plus ae2 (fun bcis2 a2 => bcis2 ++ a2) a1) (ADD :: nil)
  | Times ae1 ae2 =>
    compile_bizarre_aux_Times ae1 (fun bcis1 a1 => bcis1 ++ compile_bizarre_aux_Times ae2 (fun bcis2 ae2 => bcis2 ++ ae2) a1) (MUL :: nil)
  end.

Definition compile_bizarre (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_bizarre_aux ae)
  end.

(* ***** *)

(* compile_quaint *)

Fixpoint compile_quaint_aux (ae : arithmetic_expression) (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_quaint_aux ae1 k ++ compile_quaint_aux ae2 k ++ ADD :: nil
  | Times ae1 ae2 =>
    compile_quaint_aux ae1 (fun bcis1 => compile_quaint_aux ae2 (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_quaint (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_quaint_aux ae (fun bcis => bcis))
  end.

(* ***** *)

(* compile_curious *)

Fixpoint compile_curious_aux (ae : arithmetic_expression) (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_curious_aux ae1 k ++ compile_curious_aux ae2 k ++ ADD :: nil
  | Times ae1 ae2 =>
    compile_curious_aux ae2 (fun bcis2 => compile_curious_aux ae1 (fun bcis1 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_curious (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_curious_aux ae (fun bcis => bcis))
  end.

(* ***** *)

(* compile_surprising *)

Fixpoint compile_surprising_aux (ae : arithmetic_expression) (k0 k1 : unit -> list byte_code_instruction) (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal 0 =>
    k0 tt
  | Literal 1 =>
    k1 tt
  | Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_surprising_aux ae1 (fun _ => compile_surprising_aux ae2 k0 k1 k) (fun _ => compile_surprising_aux ae2 k1 (fun _ => k (PUSH 1 :: PUSH 1 :: ADD :: nil)) (fun bcis2 => k (PUSH 1 :: bcis2 ++ ADD :: nil))) (fun bcis1 => compile_surprising_aux ae2 (fun _ => k bcis1) (fun _ => k (bcis1 ++ PUSH 1 :: ADD :: nil)) (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))
  | Times ae1 ae2 =>
    compile_surprising_aux ae1 k0 (fun _ => compile_surprising_aux ae2 k0 k1 k) (fun bcis1 => compile_surprising_aux ae2 k0 (fun _ => k bcis1) (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_surprising (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_surprising_aux ae (fun _ => PUSH 0 :: nil) (fun _ => PUSH 1 :: nil) (fun bcis => bcis))
  end.

(* ***** *)

(* compile_unexpected *)

Fixpoint compile_unexpected_aux (ae : arithmetic_expression) (k0 k1 : unit -> list byte_code_instruction) (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal 0 =>
    k0 tt
  | Literal 1 =>
    k1 tt
  | Literal n =>
    k (PUSH n :: nil)
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_unexpected_aux ae1 (fun _ => compile_unexpected_aux ae2 k0 k1 k) (fun _ => compile_unexpected_aux ae2 k1 (fun _ => k (PUSH 1 :: PUSH 1 :: ADD :: nil)) (fun bcis2 => k (PUSH 1 :: bcis2 ++ ADD :: nil))) (fun bcis1 => compile_unexpected_aux ae2 (fun _ => k bcis1) (fun _ => k (bcis1 ++ PUSH 1 :: ADD :: nil)) (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))
  | Times ae1 ae2 =>
    compile_unexpected_aux ae1 (fun _ => compile_unexpected_aux ae2 (fun _ => k (PUSH 0 :: nil)) (fun _ => k (PUSH 0 :: nil)) (fun bcis2 => k (PUSH 0 :: bcis2 ++ MUL :: nil))) (fun _ => compile_unexpected_aux ae2 (fun _ => k (PUSH 0 :: nil)) k1 k) (fun bcis1 => compile_unexpected_aux ae2 (fun _ => bcis1 ++ PUSH 0 :: MUL :: nil) (fun _ => k bcis1) (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_unexpected (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_unexpected_aux ae (fun _ => PUSH 0 :: nil) (fun _ => PUSH 1 :: nil) (fun bcis => bcis))
  end.

(* ***** *)

(* compile_curiouser *)

Fixpoint compile_curiouser_aux (ae : arithmetic_expression) (c : nat -> list byte_code_instruction) (k : list byte_code_instruction -> list byte_code_instruction) : list byte_code_instruction :=
  match ae with
    Literal n =>
    c n
  | Name x =>
    k (LOOKUP x :: nil)
  | Plus ae1 ae2 =>
    compile_curiouser_aux ae1 (fun n1 => compile_curiouser_aux ae2 (fun n2 => c (n1 + n2)) (fun bcis2 => match n1 with O => k bcis2 | _ => k (PUSH n1 :: bcis2 ++ ADD :: nil) end)) (fun bcis1 => compile_curiouser_aux ae2 (fun n2 => match n2 with O => k bcis1 | _ => k (bcis1 ++ PUSH n2 :: ADD :: nil) end) (fun bcis2 => k (bcis1 ++ bcis2 ++ ADD :: nil)))
  | Times ae1 ae2 =>
    compile_curiouser_aux ae1 (fun n1 => compile_curiouser_aux ae2 (fun n2 => c (n1 * n2)) (fun bcis2 => match n1 with 1 => k bcis2 | _ => k (PUSH n1 :: bcis2 ++ MUL :: nil) end)) (fun bcis1 => compile_curiouser_aux ae2 (fun n2 => match n2 with 1 => k bcis1 | _ => k (bcis1 ++ PUSH n2 :: MUL :: nil) end) (fun bcis2 => k (bcis1 ++ bcis2 ++ MUL :: nil)))
  end.

Definition compile_curiouser (sp : source_program) : target_program :=
  match sp with
    Source_program ae =>
    Target_program (compile_curiouser_aux ae (fun n => PUSH n :: nil) (fun bcis => bcis))
  end.

(* ********** *)

(* end of midterm-project.v *)
