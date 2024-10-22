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


Definition test_simplify (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  (arithmetic_expression_eqb
     (candidate (Plus
                   (Literal 1)
                   (Literal 10)))
     (Literal 11))
  &&
  (arithmetic_expression_eqb
     (candidate (Plus
                   (Times
                      (Literal 2)
                      (Literal 3))
                   (Name "x"%string)))
     (Plus
        (Literal 6)
        (Name "x"%string)))
  &&
  (arithmetic_expression_eqb
     (candidate (Plus
                   (Name "y"%string)
                   (Times
                      (Literal 2)
                      (Literal 0))))
     (Plus
        (Name "y"%string)
        (Literal 0)))
  &&
  (arithmetic_expression_eqb
     (candidate (Plus
                   (Plus
                      (Literal 1)
                      (Literal 2))
                   (Plus
                      (Literal 3)
                      (Name "x"%string))))
     (Plus
        (Literal 3)
        (Plus
           (Literal 3)
           (Name "x"%string))))
  &&
  (arithmetic_expression_eqb
     (candidate
        (Plus
           (Plus
              (Literal 1)
              (Literal 2))
           (Plus
              (Name "x"%string)
              (Literal 3))))
     (Plus
        (Literal 3)
        (Plus (Name "x"%string)
           (Literal 3)))).

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
    (Literal 2)
    (Plus
       (Name "x"%string)
       (Literal 3)).

Definition test_ae10 : arithmetic_expression :=
  Times
    (Times
       (Literal 4)
       (Name "y"%string))
    (Literal 5).

Definition expected_ae10 : arithmetic_expression :=
  Times
    (Literal 4)
    (Times
       (Name "y"%string)
       (Literal 5)).

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

(* Task 1b:
   Implement a simplifier and verify that it satisfies the unit-test function.
 *)

(*
  the simplifier maps a given arithmetic expression either to a nat(a constant arithmetic expression), or to an arithmetic expression that is not a nat (a non-constant arithmetic expression)
*)

Inductive constant_or_not_constant : Type :=
| C : nat -> constant_or_not_constant
| NC : arithmetic_expression -> constant_or_not_constant.

Fixpoint constant_or_not_constant_from_arithmetic_expression (ae : arithmetic_expression) :
  constant_or_not_constant :=
  match ae with
  | Literal n =>
      C n
  | Name x =>
      NC (Name x)
  | Plus ae1 ae2 =>
      match constant_or_not_constant_from_arithmetic_expression ae1 with
      | C n1 =>
          match constant_or_not_constant_from_arithmetic_expression ae2 with
          | C n2 =>
              C (n1 + n2)
          | NC ae2 =>
              NC (Plus (Literal n1) ae2)
          end
      | NC ae1 =>
          match constant_or_not_constant_from_arithmetic_expression ae2 with
          | C n2 =>
              NC (Plus ae1 (Literal n2))
          | NC ae2 =>
              NC (Plus ae1 ae2)
          end
      end
  | Times ae1 ae2 =>
      match constant_or_not_constant_from_arithmetic_expression ae1 with
      | C n1 =>
          match constant_or_not_constant_from_arithmetic_expression ae2 with
          | C n2 =>
              C (n1 * n2)
          | NC ae2 =>
              NC (Times (Literal n1) ae2)
          end
      | NC ae1 =>
          match constant_or_not_constant_from_arithmetic_expression ae2 with
          | C n2 =>
              NC (Times ae1 (Literal n2))
          | NC ae2 =>
              NC (Times ae1 ae2)
          end
      end
  end.

Definition simplify_ltr (ae : arithmetic_expression) : arithmetic_expression :=
  match constant_or_not_constant_from_arithmetic_expression ae with
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

(* Task 1e:
   Prove that your simplifier is meaning-preserving,
   i.e., that evaluating an expression and a simplified expression always yield the same expressible value.
*)

(* ********** *)

(* Task 2:
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
