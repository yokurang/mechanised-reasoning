(* week3_stack_height_v2.v *)

(* MR 2024 - YSC 2024-2025, Sem1 *)
(* Continued from FPP 2023 - YSC 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2024 *)

(* ********** *)

(* Three language processors for arithmetic expressions. *)

(* ********** *)

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

Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 *)
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

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
      match v2s with
      | nil =>
          true
      | v2 :: v2s' =>
          false
      end
  | v1 :: v1s' =>
      match v2s with
      | nil =>
          false
      | v2 :: v2s' =>
          eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
      end
  end.

Definition eqb_list_nat (v1s v2s : list nat) : bool :=
  eqb_list nat Nat.eqb v1s v2s.

Fixpoint list_length (V : Type) (vs : list V) : nat :=
  match vs with
    | nil =>
      0
    | v :: vs' =>
      S (list_length V vs')
  end.

Lemma fold_unfold_list_length_nil :
  forall V : Type,
    list_length V nil =
    0.
Proof.
  fold_unfold_tactic list_length.
Qed.

Lemma fold_unfold_list_length_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_length V (v :: vs') =
    S (list_length V vs').
Proof.
  fold_unfold_tactic list_length.
Qed.

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

Definition String_eqb (s1 s2 : string) : bool :=
  match String.string_dec s1 s2 with
    left _ =>
      true
  | right _ =>
      false
  end.

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
          String_eqb s1 s2
      end
  end.

(* ********** *)

(*** Evaluate and Interpret ***)

(* evaluate_ltr *)

Definition test_evaluate_ltr (candidate : arithmetic_expression -> expressible_value) : bool :=
  (expressible_value_eqb (candidate (Minus (Minus (Literal 1) (Literal 5)) (Minus (Literal 1) (Literal 4)))) (Expressible_msg "numerical underflow: -4"))
  && (expressible_value_eqb (candidate (Literal 5)) (Expressible_nat 5))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Literal 5))) (Expressible_nat 10))
  && (expressible_value_eqb (candidate (Plus (Plus (Literal 1) (Literal 2)) (Literal 3))) (Expressible_nat 6))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 5))) (Expressible_nat 0))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 4))) (Expressible_nat 1))
  && (expressible_value_eqb (candidate (Minus (Literal 4) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1")).

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
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          | Expressible_msg s2 =>
              Expressible_msg s2
          end
      | Expressible_msg s1 =>
          Expressible_msg s1
      end
  end.

Compute (test_evaluate_ltr evaluate_ltr = true).

Lemma fold_unfold_evaluate_ltr_Literal :
  forall (n : nat),
    evaluate_ltr (Literal n) =
      Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_ltr (Plus ae1 ae2) =
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
      end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_ltr (Minus ae1 ae2) =
       match evaluate_ltr ae1 with
      | Expressible_nat n1 =>
          match evaluate_ltr ae2 with
          | Expressible_nat n2 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
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

(* evaluate_rtl *)

Definition test_evaluate_rtl (candidate : arithmetic_expression -> expressible_value) : bool :=
  (expressible_value_eqb (candidate (Minus (Minus (Literal 1) (Literal 5)) (Minus (Literal 1) (Literal 4)))) (Expressible_msg "numerical underflow: -3"))
  && (expressible_value_eqb (candidate (Literal 5)) (Expressible_nat 5))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Literal 5))) (Expressible_nat 10))
  && (expressible_value_eqb (candidate (Plus (Plus (Literal 1) (Literal 2)) (Literal 3))) (Expressible_nat 6))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 5))) (Expressible_nat 0))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 4))) (Expressible_nat 1))
  && (expressible_value_eqb (candidate (Minus (Literal 4) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1")).

Fixpoint evaluate_rtl (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate_rtl ae2 with
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_nat n1 =>
              Expressible_nat (n1 + n2)
          | Expressible_msg s1 =>
              Expressible_msg s1
          end
      | Expressible_msg s2 =>
          Expressible_msg s2
      end
  | Minus ae1 ae2 =>
      match evaluate_rtl ae2 with
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_nat n1 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          | Expressible_msg s1 =>
              Expressible_msg s1
          end
      | Expressible_msg s2 =>
          Expressible_msg s2
      end
  end.

Compute (test_evaluate_rtl evaluate_rtl = true).

Lemma fold_unfold_evaluate_rtl_Literal :
  forall (n : nat),
    evaluate_rtl (Literal n) =
      Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_rtl.
Qed.

Lemma fold_unfold_evaluate_rtl_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_rtl (Plus ae1 ae2) =
       match evaluate_rtl ae2 with
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_nat n1 =>
              Expressible_nat (n1 + n2)
          | Expressible_msg s1 =>
              Expressible_msg s1
          end
      | Expressible_msg s2 =>
          Expressible_msg s2
      end.
Proof.
  fold_unfold_tactic evaluate_rtl.
Qed.

Lemma fold_unfold_evaluate_rtl_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_rtl (Minus ae1 ae2) =
      match evaluate_rtl ae2 with
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_nat n1 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          | Expressible_msg s1 =>
              Expressible_msg s1
          end
      | Expressible_msg s2 =>
          Expressible_msg s2
      end.
Proof.
  fold_unfold_tactic evaluate_rtl.
Qed.

(* ********** *)

(* Interpret *)

(*** interpret_ltr ***)

Definition test_interpret_ltr (candidate : source_program -> expressible_value) : bool :=
  test_evaluate_ltr (fun ae => candidate (Source_program ae)).

Definition interpret_ltr (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => evaluate_ltr ae
  end.

Compute (test_interpret_ltr interpret_ltr = true).

(*** interpret_rtl ***)

Definition test_interpret_rtl (candidate : source_program -> expressible_value) : bool :=
  test_evaluate_rtl (fun ae => candidate (Source_program ae)).

Definition interpret_rtl (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => evaluate_rtl ae
  end.

Compute (test_interpret_rtl interpret_rtl = true).

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

(* DE, FDEL, Run *)

(* Result of decoding and executing: *)

Inductive result_of_decoding_and_execution : Type :=
  OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition eqb_result_of_decoding_and_execution (rde1 rde2 : result_of_decoding_and_execution) : bool :=
  match rde1 with
  | OK vs1 =>
      match rde2 with
      | OK vs2 =>
          eqb_list_nat vs1 vs2
      | KO s2 =>
          false
      end
  | KO s1 =>
      match rde2 with
      | OK vs2 =>
          false
      | KO s2 =>
          String_eqb s1 s2
      end
  end.

Definition test_decode_execute_ltr (candidate : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) : bool :=
  (eqb_result_of_decoding_and_execution (candidate (PUSH 42) (1 :: 2 :: 3 :: nil)) (OK (42 :: 1 :: 2 :: 3 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (1 :: 5 :: nil)) (OK (4 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (5 :: 1 :: nil)) (KO "numerical underflow: -4"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (1 :: nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (nil)) (KO "SUB: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (4 :: 3 :: 2 :: 1 :: nil)) (OK (7 :: 2 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (3 :: 4 :: 2 :: 5 :: nil)) (OK (1 :: 2 :: 5 :: nil))).

Definition decode_execute_ltr (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
  | PUSH n => OK (n :: ds)
  | ADD =>
      match ds with
      | nil => KO "ADD: stack underflow"
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' => OK ((n1 + n2) :: ds'')
          | nil => KO "ADD: stack underflow"
          end
      end
  | SUB =>
      match ds with
      | nil => KO "SUB: stack underflow"
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' =>
              match n1 <? n2 with
              | true =>
                  KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  OK ((n1 - n2) :: ds'')
              end
          | nil => KO "SUB: stack underflow"
          end
      end
  end.

Compute (test_decode_execute_ltr decode_execute_ltr = true).

Inductive result_of_decoding_and_execution_height : Type :=
  OK_h : data_stack -> nat -> result_of_decoding_and_execution_height
| KO_h : string -> result_of_decoding_and_execution_height.

Definition eqb_result_of_decoding_and_execution_height (rde1 rde2 : result_of_decoding_and_execution_height) : bool :=
  match rde1 with
  | OK_h ds1 mh1 =>
      match rde2 with
      | OK_h ds2 mh2 =>
          (eqb_list_nat ds1 ds2) &&
            (Nat.eqb mh1 mh2)
      | KO_h s2 =>
          false
      end
  | KO_h s1 =>
      match rde2 with
      | OK_h vs2 mh2 =>
          false
      | KO_h s2 =>
          String_eqb s1 s2
      end
  end.

Definition test_fetch_decode_execute_loop_height_ltr (candidate : (list byte_code_instruction) -> data_stack -> result_of_decoding_and_execution_height) :=
  (eqb_result_of_decoding_and_execution_height
     (candidate (PUSH 42 :: PUSH 21 :: nil) (1 :: 2 :: 3 :: nil))
     (OK_h (21 :: 42 :: 1 :: 2 :: 3 :: nil) 5))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (ADD :: ADD :: nil) (1 :: 2 :: 3 :: nil))
       (OK_h (6 :: nil) 3))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (SUB :: nil) (2 :: 3 :: nil))
       (OK_h (1 :: nil) 2))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (SUB :: SUB :: nil) (4 :: 3 :: 2 :: nil))
       (KO_h "numerical underflow: -1"))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate
          (PUSH 1 :: PUSH 2 :: ADD :: PUSH 3 :: ADD :: PUSH 4 :: ADD :: nil) nil)
       (OK_h (10 :: nil) 2)).

Fixpoint fetch_decode_execute_loop_height_ltr (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution_height :=
  match bcis with
  | nil => OK_h ds (list_length nat ds)
  | bci :: bcis' =>
      match decode_execute_ltr bci ds with
      | OK ds' =>
          match fetch_decode_execute_loop_height_ltr bcis' ds' with
          | OK_h ds'' mh'' =>
              OK_h ds'' (max (max (list_length nat ds) (list_length nat ds')) mh'')
          | KO_h s =>
              KO_h s
          end
      | KO s => KO_h s
      end
  end.

Compute (test_fetch_decode_execute_loop_height_ltr fetch_decode_execute_loop_height_ltr).

Lemma fold_unfold_fetch_decode_execute_loop_height_ltr_nil :
  forall (ds: data_stack),
    fetch_decode_execute_loop_height_ltr nil ds =
      OK_h ds (list_length nat ds).
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_height_ltr.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_height_ltr_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop_height_ltr (bci :: bcis') ds =
     match decode_execute_ltr bci ds with
      | OK ds' =>
          match fetch_decode_execute_loop_height_ltr bcis' ds' with
          | OK_h ds'' mh'' =>
              OK_h ds'' (max (max (list_length nat ds) (list_length nat ds')) mh'')
          | KO_h s =>
              KO_h s
          end
      | KO s => KO_h s
      end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_height_ltr.
Qed.

Definition test_run_height_ltr (candidate : target_program -> expressible_value * nat) : bool :=
  (let (ev1, h1) := (candidate (Target_program (PUSH 42 :: nil))) in
   (expressible_value_eqb ev1 (Expressible_nat 42)) &&
     (Nat.eqb h1 1))
  &&
    (let (ev2, h2) := (candidate (Target_program (PUSH 42 :: PUSH 1 :: ADD :: PUSH 100 :: ADD :: nil))) in
     (expressible_value_eqb ev2 (Expressible_nat 143)) &&
       (Nat.eqb h2 2))
  &&
    (let (ev3, h3) := (candidate (Target_program (PUSH 42 :: ADD :: SUB :: nil))) in
     (expressible_value_eqb ev3 (Expressible_msg "ADD: stack underflow")) &&
       (Nat.eqb h3 0))
  &&
    (let (ev4, h4) := (candidate (Target_program (PUSH 20 :: PUSH 42 :: ADD :: PUSH 20 :: PUSH 30 :: PUSH 40 :: nil))) in
     (expressible_value_eqb ev4 (Expressible_msg "too many results on the data stack")) &&
       (Nat.eqb h4 0)).

Definition run_height_ltr (tp : target_program) : expressible_value * nat :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop_height_ltr bcis nil with
    | OK_h ds mh =>
        match ds with
        | nil => (Expressible_msg "no result on the data stack", 0)
        | (n :: ds') =>
            match ds' with
            | nil => ((Expressible_nat n), mh)
            | (n' :: ds'') => ((Expressible_msg "too many results on the data stack"), 0)
            end
        end
    | KO_h s => ((Expressible_msg s), 0)
    end
  end.

Compute (test_run_height_ltr run_height_ltr).

(* Right-to-left *)

Definition test_decode_execute_rtl (candidate : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) : bool :=
  (eqb_result_of_decoding_and_execution (candidate (PUSH 42) (1 :: 2 :: 3 :: nil)) (OK (42 :: 1 :: 2 :: 3 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (5 :: 1 :: nil)) (OK (4 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (1 :: 5 :: nil)) (KO "numerical underflow: -4"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (1 :: nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (nil)) (KO "SUB: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (4 :: 3 :: 2 :: 1 :: nil)) (OK (7 :: 2 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (4 :: 3 :: 2 :: 5 :: nil)) (OK (1 :: 2 :: 5 :: nil))).

Definition decode_execute_rtl (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
  | PUSH n => OK (n :: ds)
  | ADD =>
      match ds with
      | nil => KO "ADD: stack underflow"
      | n1 :: ds' =>
          match ds' with
          | n2 :: ds'' => OK ((n1 + n2) :: ds'')
          | nil => KO "ADD: stack underflow"
          end
      end
  | SUB =>
      match ds with
      | nil => KO "SUB: stack underflow"
      | n1 :: ds' =>
          match ds' with
          | n2 :: ds'' =>
              match n1 <? n2 with
              | true =>
                  KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  OK ((n1 - n2) :: ds'')
              end
          | nil => KO "SUB: stack underflow"
          end
      end
  end.

Compute (test_decode_execute_ltr decode_execute_ltr = true).

Definition test_fetch_decode_execute_loop_height_rtl (candidate : (list byte_code_instruction) -> data_stack  -> result_of_decoding_and_execution_height) :=
  (eqb_result_of_decoding_and_execution_height
     (candidate (PUSH 42 :: PUSH 21 :: nil) (1 :: 2 :: 3 :: nil))
     (OK_h (21 :: 42 :: 1 :: 2 :: 3 :: nil) 5))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (ADD :: ADD :: nil) (1 :: 2 :: 3 :: nil))
       (OK_h (6 :: nil) 3))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (SUB :: nil) (3 :: 2 :: nil))
       (OK_h (1 :: nil) 2 ))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (SUB :: SUB :: nil) (4 :: 3 :: 2 :: nil))
       (KO_h "numerical underflow: -1"))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate
          (PUSH 1 :: PUSH 2 :: ADD :: PUSH 3 :: ADD :: PUSH 4 :: ADD :: nil) nil)
       (OK_h (10 :: nil) 2)).

Fixpoint fetch_decode_execute_loop_height_rtl (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution_height :=
  match bcis with
  | nil => OK_h ds (list_length nat ds)
  | bci :: bcis' =>
      match decode_execute_rtl bci ds with
      | OK ds' =>
          match fetch_decode_execute_loop_height_rtl bcis' ds' with
          | OK_h ds'' mh'' =>
              OK_h ds'' (max (max (list_length nat ds) (list_length nat ds')) mh'')
          | KO_h s =>
              KO_h s
          end
      | KO s => KO_h s
      end
  end.

Compute (test_fetch_decode_execute_loop_height_rtl fetch_decode_execute_loop_height_rtl).

Lemma fold_unfold_fetch_decode_execute_loop_height_rtl_nil :
  forall (ds: data_stack),
    fetch_decode_execute_loop_height_rtl nil ds =
    OK_h ds (list_length nat ds).
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_height_rtl.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_height_rtl_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop_height_rtl (bci :: bcis') ds =
    match decode_execute_rtl bci ds with
    | OK ds' =>
        match fetch_decode_execute_loop_height_rtl bcis' ds' with
        | OK_h ds'' mh'' =>
            OK_h ds'' (max (max (list_length nat ds) (list_length nat ds')) mh'')
        | KO_h s =>
            KO_h s
        end
    | KO s => KO_h s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_height_rtl.
Qed.

Definition test_run_height_rtl (candidate : target_program -> expressible_value * nat) : bool :=
  (let (ev1, h1) := (candidate (Target_program (PUSH 42 :: nil))) in
   (expressible_value_eqb ev1 (Expressible_nat 42)) &&
     (Nat.eqb h1 1))
  &&
    (let (ev2, h2) := (candidate (Target_program (PUSH 42 :: PUSH 1 :: ADD :: PUSH 100 :: ADD :: nil))) in
     (expressible_value_eqb ev2 (Expressible_nat 143)) &&
       (Nat.eqb h2 2))
  &&
    (let (ev3, h3) := (candidate (Target_program (PUSH 42 :: ADD :: SUB :: nil))) in
     (expressible_value_eqb ev3 (Expressible_msg "ADD: stack underflow")) &&
       (Nat.eqb h3 0))
  &&
    (let (ev4, h4) := (candidate (Target_program (PUSH 20 :: PUSH 42 :: ADD :: PUSH 20 :: PUSH 30 :: PUSH 40 :: nil))) in
     (expressible_value_eqb ev4 (Expressible_msg "too many results on the data stack")) &&
       (Nat.eqb h4 0)).

Definition run_height_rtl (tp : target_program) : expressible_value * nat :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop_height_rtl bcis nil with
    | OK_h ds mh =>
        match ds with
        | nil => (Expressible_msg "no result on the data stack", 0)
        | (n :: ds') =>
            match ds' with
            | nil => ((Expressible_nat n), mh)
            | (n' :: ds'') => ((Expressible_msg "too many results on the data stack"), 0)
            end
        end
    | KO_h s => ((Expressible_msg s), 0)
    end
  end.

Compute (test_run_height_rtl run_height_rtl).

(* Compile *)

Definition test_eqb_byte_code_instruction (candidate : byte_code_instruction -> byte_code_instruction -> bool) :=
  (Bool.eqb (candidate ADD ADD) true)
  && (Bool.eqb (candidate ADD SUB) false)
  && (Bool.eqb (candidate ADD (PUSH 1)) false)
  && (Bool.eqb (candidate SUB ADD) false)
  && (Bool.eqb (candidate SUB SUB) true)
  && (Bool.eqb (candidate SUB (PUSH 1)) false)
  && (Bool.eqb (candidate (PUSH 1) (PUSH 1)) true)
  && (Bool.eqb (candidate (PUSH 2) (PUSH 1)) false).

Definition eqb_byte_code_instruction (bci1 bci2 : byte_code_instruction) :=
  match bci1 with
  | PUSH n1 =>
      match bci2 with
      | PUSH n2 =>
          Nat.eqb n1 n2
      | _ =>
          false
      end
  | ADD =>
      match bci2 with
      | ADD =>
          true
      | _ =>
          false
      end
  | SUB =>
      match bci2 with
      | SUB =>
          true
      | _ =>
          false
      end
  end.

Compute (test_eqb_byte_code_instruction eqb_byte_code_instruction).

Definition eqb_list_byte_code_instruction (bcis1 bcis2 : list byte_code_instruction) : bool :=
  eqb_list byte_code_instruction eqb_byte_code_instruction bcis1 bcis2.

Definition eqb_target_program (tp1 tp2 : target_program) : bool :=
  match tp1 with
  | Target_program bcis1 =>
      match tp2 with
      | Target_program bcis2 =>
          eqb_list_byte_code_instruction bcis1 bcis2
      end
  end.

Compute (eqb_target_program (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil))
           (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil))).
Compute (eqb_target_program (Target_program (PUSH 3 :: PUSH 10 :: ADD :: nil))
           (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil))).

(*** compile_ltr ***)

Definition test_compile_ltr_aux (candidate : arithmetic_expression -> (list byte_code_instruction)) :=
  (eqb_list_byte_code_instruction (candidate (Literal 2))
     (PUSH 2 :: nil))
  && (eqb_list_byte_code_instruction (candidate (Plus (Literal 5) (Literal 2)))
        (PUSH 5 :: PUSH 2 :: ADD :: nil))
  && (eqb_list_byte_code_instruction (candidate (Minus (Literal 5) (Literal 2)))
        (PUSH 5 :: PUSH 2 :: SUB :: nil)).

Fixpoint compile_ltr_aux (ae : arithmetic_expression) : list byte_code_instruction :=
    match ae with
    | Literal n => PUSH n :: nil
    | Plus ae1 ae2 => compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ (ADD :: nil)
    | Minus ae1 ae2 => compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ (SUB :: nil)
    end.

Compute (test_compile_ltr_aux compile_ltr_aux = true).

Lemma fold_unfold_compile_ltr_aux_Literal :
  forall (n : nat),
    compile_ltr_aux (Literal n) =
      PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Lemma fold_unfold_compile_ltr_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ltr_aux (Plus ae1 ae2) =
       compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Lemma fold_unfold_compile_ltr_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ltr_aux (Minus ae1 ae2) =
       compile_ltr_aux ae1 ++ compile_ltr_aux ae2 ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Definition test_compile_ltr (candidate : source_program -> target_program) : bool :=
  (eqb_target_program
     (candidate (Source_program (Minus (Literal 3) (Literal 10))))
     (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil)))
  && (eqb_target_program
        (candidate (Source_program (Minus (Minus (Literal 3) (Literal 1)) (Plus (Literal 3) (Literal 2)))))
        (Target_program (PUSH 3 :: PUSH 1 :: SUB :: PUSH 3 :: PUSH 2 :: ADD :: SUB :: nil))).

Definition compile_ltr (sp : source_program) : target_program :=
  match sp with
  | Source_program ae => Target_program (compile_ltr_aux ae)
  end.

Compute (test_compile_ltr compile_ltr = true).

(*** compile_rtl ***)

Definition test_compile_rtl_aux (candidate : arithmetic_expression -> (list byte_code_instruction)) :=
  (eqb_list_byte_code_instruction (candidate (Literal 2))
     (PUSH 2 :: nil))
  && (eqb_list_byte_code_instruction (candidate (Plus (Literal 5) (Literal 2)))
        (PUSH 2 :: PUSH 5 :: ADD :: nil))
  && (eqb_list_byte_code_instruction (candidate (Minus (Literal 5) (Literal 2)))
        (PUSH 2 :: PUSH 5 :: SUB :: nil)).

Fixpoint compile_rtl_aux (ae : arithmetic_expression) : list byte_code_instruction :=
    match ae with
    | Literal n => PUSH n :: nil
    | Plus ae1 ae2 => compile_rtl_aux ae2 ++ compile_rtl_aux ae1 ++ (ADD :: nil)
    | Minus ae1 ae2 => compile_rtl_aux ae2 ++ compile_rtl_aux ae1 ++ (SUB :: nil)
    end.

Compute (test_compile_rtl_aux compile_rtl_aux = true).

Lemma fold_unfold_compile_rtl_aux_Literal :
  forall (n : nat),
    compile_rtl_aux (Literal n) =
      PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_rtl_aux.
Qed.

Lemma fold_unfold_compile_rtl_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_rtl_aux (Plus ae1 ae2) =
       compile_rtl_aux ae2 ++ compile_rtl_aux ae1 ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_rtl_aux.
Qed.

Lemma fold_unfold_compile_rtl_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_rtl_aux (Minus ae1 ae2) =
       compile_rtl_aux ae2 ++ compile_rtl_aux ae1 ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_rtl_aux.
Qed.

Definition test_compile_rtl (candidate : source_program -> target_program) : bool :=
  (eqb_target_program
     (candidate (Source_program (Minus (Literal 3) (Literal 10))))
     (Target_program (PUSH 10 :: PUSH 3 :: SUB :: nil)))
  && (eqb_target_program
        (candidate (Source_program (Minus (Minus (Literal 3) (Literal 1)) (Plus (Literal 3) (Literal 2)))))
        (Target_program (PUSH 2 :: PUSH 3 :: ADD :: PUSH 1 :: PUSH 3 :: SUB :: SUB :: nil))).

Definition compile_rtl (sp : source_program) : target_program :=
  match sp with
  | Source_program ae => Target_program (compile_rtl_aux ae)
  end.

Compute (test_compile_rtl compile_rtl = true).

(* Super Refactor *)

(*** super_refactor_ltr ***)

Fixpoint super_refactor_ltr (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_ltr_aux ae1 (super_refactor_ltr ae2)
  | Minus ae1 ae2 =>
    Minus (super_refactor_ltr ae1) (super_refactor_ltr ae2)
  end
  with super_refactor_ltr_aux (ae1 a : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
    | Literal n =>
      Plus (Literal n) a
    | Plus ae1 ae2 =>
      super_refactor_ltr_aux ae1 (super_refactor_ltr_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus (Minus (super_refactor_ltr ae1) (super_refactor_ltr ae2)) a
    end.

(* ***** *)

Lemma fold_unfold_super_refactor_ltr_Literal :
  forall (n : nat),
    super_refactor_ltr (Literal n) =
      (Literal n).
Proof.
  fold_unfold_tactic super_refactor_ltr.
Qed.

Lemma fold_unfold_super_refactor_ltr_Plus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_ltr (Plus ae1 ae2) =
      super_refactor_ltr_aux ae1 (super_refactor_ltr ae2).
Proof.
  fold_unfold_tactic super_refactor_ltr.
Qed.

Lemma fold_unfold_super_refactor_ltr_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_ltr (Minus ae1 ae2) =
      Minus (super_refactor_ltr ae1) (super_refactor_ltr ae2).
Proof.
  fold_unfold_tactic super_refactor_ltr.
Qed.

Lemma fold_unfold_super_refactor_ltr_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    super_refactor_ltr_aux (Literal n) a =
      Plus (Literal n) a.
Proof.
  fold_unfold_tactic super_refactor_ltr_aux.
Qed.

Lemma fold_unfold_super_refactor_ltr_aux_Plus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_ltr_aux (Plus ae1 ae2) a =
      super_refactor_ltr_aux ae1 (super_refactor_ltr_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_ltr_aux.
Qed.

Lemma fold_unfold_super_refactor_ltr_aux_Minus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_ltr_aux (Minus ae1 ae2) a =
      Plus (Minus (super_refactor_ltr ae1) (super_refactor_ltr ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_ltr_aux.
Qed.

(*** super_refactor_rtl ***)

Fixpoint super_refactor_rtl (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_rtl_aux (super_refactor_rtl ae1) ae2
  | Minus ae1 ae2 =>
    Minus (super_refactor_rtl ae1) (super_refactor_rtl ae2)
  end
  with super_refactor_rtl_aux (a ae1 : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
    | Literal n =>
      Plus a (Literal n)
    | Plus ae1 ae2 =>
      super_refactor_rtl_aux (super_refactor_rtl_aux a ae1) ae2
    | Minus ae1 ae2 =>
      Plus a (Minus (super_refactor_rtl ae1) (super_refactor_rtl ae2))
    end.

(* ***** *)

Lemma fold_unfold_super_refactor_rtl_Literal :
  forall (n : nat),
    super_refactor_rtl (Literal n) =
      (Literal n).
Proof.
  fold_unfold_tactic super_refactor_rtl.
Qed.

Lemma fold_unfold_super_refactor_rtl_Plus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_rtl (Plus ae1 ae2) =
      super_refactor_rtl_aux (super_refactor_rtl ae1) ae2.
Proof.
  fold_unfold_tactic super_refactor_rtl.
Qed.

Lemma fold_unfold_super_refactor_rtl_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_rtl (Minus ae1 ae2) =
      Minus (super_refactor_rtl ae1) (super_refactor_rtl ae2).
Proof.
  fold_unfold_tactic super_refactor_rtl.
Qed.

Lemma fold_unfold_super_refactor_rtl_aux_Literal :
  forall (n : nat)
         (a : arithmetic_expression),
    super_refactor_rtl_aux a (Literal n) =
      Plus a (Literal n).
Proof.
  fold_unfold_tactic super_refactor_rtl_aux.
Qed.

Lemma fold_unfold_super_refactor_rtl_aux_Plus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_rtl_aux a (Plus ae1 ae2) =
      super_refactor_rtl_aux (super_refactor_rtl_aux a ae1) ae2.
Proof.
  fold_unfold_tactic super_refactor_rtl_aux.
Qed.

Lemma fold_unfold_super_refactor_rtl_aux_Minus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_rtl_aux a (Minus ae1 ae2) =
      Plus a (Minus (super_refactor_rtl ae1) (super_refactor_rtl ae2)).
Proof.
  fold_unfold_tactic super_refactor_rtl_aux.
Qed.

(* ********** *)

(* Depth *)

(*** depth_left ***)

Definition test_depth_left (candidate : arithmetic_expression -> nat) : bool :=
  let ae1 := (Literal 1) in
  let ae1 := (Literal 1) in
  let ae2 := (Plus
                (Plus (Literal 1) (Literal 2))
                (Plus (Literal 3) (Literal 4))) in
  let ae3 := (Plus (Literal 1)
                (Plus
                   (Plus
                      (Plus (Literal 4) (Literal 5))
                      (Literal 3))
                   (Literal 2))) in
  (Nat.eqb (candidate ae1) 0) &&
    (Nat.eqb (candidate ae2) 2) &&
    (Nat.eqb (candidate ae3) 3).

Fixpoint depth_left (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal n => 0
  | Plus ae1 ae2 =>
      let n1 := depth_left ae1 in
      let n2 := depth_left ae2 in
      max (S n1) n2
  | Minus ae1 ae2 =>
      let n1 := depth_left ae1 in
      let n2 := depth_left ae2 in
      max (S n1) n2
end.

Compute (test_depth_left depth_left).

Lemma fold_unfold_depth_left_Literal :
  forall (n : nat),
    depth_left (Literal n) = 0.
Proof.
  fold_unfold_tactic depth_left.
Qed.

Lemma fold_unfold_depth_left_Plus :
  forall (ae1 ae2: arithmetic_expression),
    depth_left (Plus ae1 ae2) = max (S (depth_left ae1)) (depth_left ae2).
Proof.
  fold_unfold_tactic depth_left.
Qed.

Lemma fold_unfold_depth_left_Minus :
  forall (ae1 ae2: arithmetic_expression),
    depth_left (Minus ae1 ae2) = max (S (depth_left ae1)) (depth_left ae2).
Proof.
  fold_unfold_tactic depth_left.
Qed.

(*** depth_right ***)

Definition test_depth_right (candidate : arithmetic_expression -> nat) : bool :=
  let ae1 := (Literal 1) in
  let ae1 := (Literal 1) in
  let ae2 := (Plus
                (Plus (Literal 1) (Literal 2))
                (Plus (Literal 3) (Literal 4))) in
  let ae3 := (Plus (Literal 1)
                (Plus
                   (Plus
                      (Plus (Literal 4) (Literal 5))
                      (Literal 3))
                   (Literal 2))) in
  (Nat.eqb (candidate ae1) 0) &&
    (Nat.eqb (candidate ae2) 2) &&
    (Nat.eqb (candidate ae3) 2).

Fixpoint depth_right (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal n => 0
  | Plus ae1 ae2 =>
      let n1 := depth_right ae1 in
      let n2 := depth_right ae2 in
      max n1 (S n2)
  | Minus ae1 ae2 =>
      let n1 := depth_right ae1 in
      let n2 := depth_right ae2 in
      max n1 (S n2)
end.

Compute (test_depth_right depth_right).

Lemma fold_unfold_depth_right_Literal :
  forall (n : nat),
    depth_right (Literal n) = 0.
Proof.
  fold_unfold_tactic depth_right.
Qed.

Lemma fold_unfold_depth_right_Plus :
  forall (ae1 ae2: arithmetic_expression),
    depth_right (Plus ae1 ae2) = max (depth_right ae1) (S (depth_right ae2)).
Proof.
  fold_unfold_tactic depth_right.
Qed.

Lemma fold_unfold_depth_right_Minus :
  forall (ae1 ae2: arithmetic_expression),
    depth_right (Minus ae1 ae2) = max (depth_right ae1) (S (depth_right ae2)).
Proof.
  fold_unfold_tactic depth_right.
Qed.

(* ********** *)

(*** Proving time ***)

Compute (let ae := (Plus (Minus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1))) (Minus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1)))) in
         let ds := (42 :: nil) in
         match evaluate_ltr ae with
         | Expressible_nat n =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               OK_h (n :: ds) (list_length nat ds + S (depth_right (super_refactor_ltr ae)))
         | Expressible_msg s =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               KO_h s
        end).

Compute (let ae := (Plus (Minus (Plus (Minus (Literal 5) (Literal 4)) (Literal 4)) (Literal 4)) (Literal 4)) in
         let ds := (42 :: nil) in
         match evaluate_ltr ae with
         | Expressible_nat n =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               OK_h (n :: ds) (list_length nat ds + S (depth_right (super_refactor_ltr ae)))
         | Expressible_msg s =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               KO_h s
        end).

Compute (let ae := (Plus (Literal 4) (Minus (Literal 30) (Plus (Literal 2) (Plus (Literal 1) (Literal 0))))) in
         let ds := (42 :: nil) in
         match evaluate_ltr ae with
         | Expressible_nat n =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               OK_h (n :: ds) (list_length nat ds + S (depth_right (super_refactor_ltr ae)))
         | Expressible_msg s =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               KO_h s
        end).

Compute (let ae := (Minus (Literal 1) (Literal 2)) in
         let ds := (42 :: nil) in
         match evaluate_ltr ae with
         | Expressible_nat n =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               OK_h (n :: ds) (list_length nat ds + S (depth_right (super_refactor_ltr ae)))
         | Expressible_msg s =>
             fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
               KO_h s
        end).

Lemma main_theorem_aux :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate_ltr ae = Expressible_nat n ->
        fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
          OK_h (n :: ds) (list_length nat ds + S (depth_right (super_refactor_ltr ae))))
    /\
      (forall (s : string),
        evaluate_ltr ae = Expressible_msg s ->
        fetch_decode_execute_loop_height_ltr (compile_ltr_aux (super_refactor_ltr ae)) ds =
          KO_h s).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].
  - intro ds.
    rewrite -> fold_unfold_evaluate_ltr_Literal.
    rewrite -> fold_unfold_super_refactor_ltr_Literal.
    rewrite -> fold_unfold_compile_ltr_aux_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_ltr_cons.
    unfold decode_execute_ltr.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_ltr_nil.
    split.
    + intros n' H_eq_n_n'.
      injection H_eq_n_n' as H_eq_n_n'.
      rewrite -> H_eq_n_n'.
      simpl.
      admit.
    + intros s H_absurd.
      discriminate H_absurd.
  - intro ds.
    rewrite -> fold_unfold_evaluate_ltr_Plus.
    rewrite -> fold_unfold_super_refactor_ltr_Plus.
    case (evaluate_ltr ae1) as [ n1' | s1' ] eqn:H_e_ae1.
    + case (evaluate_ltr ae2) as [ n2' | s2' ] eqn:H_e_ae2.
      * split.
        -- intros n H_eq_n1'n2'_n.
           injection H_eq_n1'n2'_n as H_eq_n1'n2'_n.
           destruct (IHae1 ds) as [H_OK_ae1 _].
           destruct (IHae2 ds) as [H_OK_ae2 _].
           Check (H_OK_ae1 n1' (eq_refl)).
Admitted.

Lemma about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds ds' ds'' : data_stack)
         (mh1 mh2 : nat),
    fetch_decode_execute_loop_height_ltr bci1s ds = OK_h ds' mh1 ->
    fetch_decode_execute_loop_height_ltr bci2s ds' = OK_h ds'' mh2 ->
    fetch_decode_execute_loop_height_ltr (bci1s ++ bci2s) ds = OK_h ds'' (max mh1 mh2).
Admitted.
(* [od] no need for refactoring yet: prove the theorem in general: *)

Lemma main_theorem_aux' :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate_ltr ae = Expressible_nat n ->
        fetch_decode_execute_loop_height_ltr (compile_ltr_aux ae) ds =
          OK_h (n :: ds) (list_length nat ds + S (depth_right ae)))
    /\
      (forall (s : string),
        evaluate_ltr ae = Expressible_msg s ->
        fetch_decode_execute_loop_height_ltr (compile_ltr_aux ae) ds =
          KO_h s).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro ds.
  - rewrite -> fold_unfold_evaluate_ltr_Literal.
    rewrite -> fold_unfold_compile_ltr_aux_Literal.
    rewrite -> fold_unfold_depth_right_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_ltr_cons.
    unfold decode_execute_ltr.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_ltr_nil.
    split.
    + (* [od] this subgoal is simple to prove, esp. if you first re-associate max *)
      intros n' H_eq_n_n'.
      injection H_eq_n_n' as H_eq_n_n'.
      rewrite -> H_eq_n_n'.
      rewrite -> fold_unfold_list_length_cons.
      Search (_ + 1 = S _).
      rewrite -> Nat.add_1_r.
      Search (max _ _).
      (* max_r: forall n m : nat, n <= m -> Init.Nat.max n m = m *)
      Search (_ <= _).
      (* Nat.le_succ_diag_r: forall n : nat, n <= S n *)
      Check (max_r (list_length nat ds) (S (list_length nat ds)) (Nat.le_succ_diag_r (list_length nat ds))).
      rewrite -> (max_r (list_length nat ds) (S (list_length nat ds)) (Nat.le_succ_diag_r (list_length nat ds))).
      rewrite -> Nat.max_id.
      reflexivity.
    + intros s H_absurd.
      discriminate H_absurd.
  - rewrite -> fold_unfold_evaluate_ltr_Plus.
    rewrite -> fold_unfold_compile_ltr_aux_Plus.
    rewrite -> fold_unfold_depth_right_Plus.
    case (evaluate_ltr ae1) as [ n1' | s1' ] eqn:H_e_ae1.
    + case (evaluate_ltr ae2) as [ n2' | s2' ] eqn:H_e_ae2.
      * split.
        -- intros n' H_eq_n1_n2_n'.
           injection H_eq_n1_n2_n' as H_eq_n1_n2_n'.
           Check (IHae1 ds).
           destruct (IHae1 ds) as [IHae1_OK _].
           clear IHae1.
           Check (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK).
           Check (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK (compile_ltr_aux ae1) (compile_ltr_aux ae1 ++ ADD :: nil) ds (n1' :: ds) (n' :: ds)).
           Check (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK (compile_ltr_aux ae1) (compile_ltr_aux ae1 ++ ADD :: nil) ds (n1' :: ds) (n' :: ds) (list_length nat ds + S (depth_right ae1)) (list_length nat ds + S (Init.Nat.max (depth_right ae1) (S (depth_right ae2))))).
           Check (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK (compile_ltr_aux ae1) (compile_ltr_aux ae2 ++ ADD :: nil) ds (n1' :: ds) (n' :: ds) (list_length nat ds + S (depth_right ae1)) (list_length nat ds + S (Init.Nat.max (depth_right ae1) (S (depth_right ae2))))
                 (IHae1_OK n1' (eq_refl (Expressible_nat n1')))).
           destruct (IHae2 (n1' :: ds)) as [IHae2_OK _].
           Check (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK
                    (compile_ltr_aux ae1)
                    (compile_ltr_aux ae2 ++ ADD :: nil)
                    ds (n1' :: ds) (n2' :: n1' :: ds)
                    (list_length nat ds + S (depth_right ae1))
                    (list_length nat ds + S (Init.Nat.max (depth_right ae1) (S (depth_right ae2))))
                    (IHae1_OK n1' (eq_refl (Expressible_nat n1')))
                 ).
           Check (IHae2_OK n2' (eq_refl (Expressible_nat n2'))).

           destruct (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK
                       (compile_ltr_aux ae1)
                       (compile_ltr_aux ae2 ++ ADD :: nil) ds
                       ds
                       (n1' :: ds)
                       (n2' :: n1' :: ds)
             as [H_fdel_ae1_OK H_fdel_ae1_KO].
           destruct (IHae1 ds) as [IHae1_OK IHae1_KO].

        -- intros n H_eq_n1'n2'_n.
           injection H_eq_n1'n2'_n as H_eq_n1'n2'_n.
           rewrite <- H_eq_n1'n2'_n.
           rewrite -> fold_unfold_compile_ltr_aux_Plus.
           rewrite -> fold_unfold_depth_right_Plus.
           destruct (IHae1 ds) as [IHae1_OK _].
           clear IHae1.
           destruct (IHae2 (n1' ::ds)) as [IHae2_OK _].
           clear IHae2.
           Check (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK
                    (compile_ltr_aux ae1)
                    (compile_ltr_aux ae2)
                    ds
                    (n1' :: ds)
                    (n2' :: n1' :: ds)
                    (list_length nat ds + S (depth_right ae1))
                    (list_length nat (n1' :: ds) + S (depth_right ae2))
                    (IHae1_OK n1' eq_refl)
                    (IHae2_OK n2' eq_refl)
                 ).
           remember (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK
                    (compile_ltr_aux ae1)
                    (compile_ltr_aux ae2)
                    ds
                    (n1' :: ds)
                    (n2' :: n1' :: ds)
                    (list_length nat ds + S (depth_right ae1))
                    (list_length nat (n1' :: ds) + S (depth_right ae2))
                    (IHae1_OK n1' eq_refl)
                    (IHae2_OK n2' eq_refl)
                    ) as H_concat_ae1_ae2.
           clear HeqH_concat_ae1_ae2.
           Check (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK
                    (compile_ltr_aux ae1 ++ compile_ltr_aux ae2)
                    (ADD :: nil)
                    ds
                    (n2' :: n1' :: ds)
                    (n1' + n2' :: ds)
                    (Init.Nat.max (list_length nat ds + S (depth_right ae1))
                       (list_length nat (n1' :: ds) + S (depth_right ae2)))
                    (Init.Nat.max (list_length nat ds + S (depth_right ae1))
                       (list_length nat (n1' :: ds) + S (depth_right ae2)))
                    H_concat_ae1_ae2
                 ).
           remember (about_fetch_decode_execute_loop_height_ltr_concatenation_OK_OK
                    (compile_ltr_aux ae1 ++ compile_ltr_aux ae2)
                    (ADD :: nil)
                    ds
                    (n2' :: n1' :: ds)
                    (n1' + n2' :: ds)
                    (Init.Nat.max (list_length nat ds + S (depth_right ae1))
                       (list_length nat (n1' :: ds) + S (depth_right ae2)))
                    (Init.Nat.max (list_length nat ds + S (depth_right ae1))
                       (list_length nat (n1' :: ds) + S (depth_right ae2)))
                    H_concat_ae1_ae2
                    ) as H_concat_ae1_ae2_ADD.
           clear HeqH_concat_ae1_ae2_ADD.
           clear H_concat_ae1_ae2.
           unfold fetch_decode_execute_loop_height_ltr in H_concat_ae1_ae2_ADD at 1.
           unfold decode_execute_ltr in H_concat_ae1_ae2_ADD.
           rewrite ->3 fold_unfold_list_length_cons in H_concat_ae1_ae2_ADD.
           
           Check H_concat_ae1_ae2_ADD.

           (list_length nat ds + S (depth_right ae2))).
           (* [od] and here you need the theorem about applying fetch_decode_execute_loop_height_ltr to the concatenation of byte-code instructions *)
           destruct (IHae1 ds) as [H_OK_ae1 _].
           destruct (IHae2 ds) as [H_OK_ae2 _].
           Check (H_OK_ae1 n1' (eq_refl)).
Admitted.

(* ***** *)

Compute (
    let ae := (Plus (Minus (Plus (Minus (Literal 5) (Literal 4)) (Literal 4)) (Literal 4)) (Literal 4)) in
    match (interpret_ltr (Source_program ae)) with
    | Expressible_nat n =>
        run_height_ltr (compile_ltr (Source_program (super_refactor_ltr ae))) =
          (Expressible_nat n, S (depth_right (super_refactor_ltr ae)))
    | Expressible_msg s =>
        (Expressible_msg s, 0) = (Expressible_msg s, 0)
    end).

Compute (
    let ae := (Plus (Literal 4) (Minus (Literal 30) (Plus (Literal 2) (Plus (Literal 1) (Literal 0))))) in
    match (interpret_ltr (Source_program ae)) with
    | Expressible_nat n =>
        run_height_ltr (compile_ltr (Source_program (super_refactor_ltr ae))) =
          (Expressible_nat n, S (depth_right (super_refactor_ltr ae)))
    | Expressible_msg s =>
        (Expressible_msg s, 0) = (Expressible_msg s, 0)
    end).

Compute (
    let ae := (Plus (Minus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1))) (Minus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1)))) in
    match (interpret_ltr (Source_program ae)) with
    | Expressible_nat n =>
        run_height_ltr (compile_ltr (Source_program (super_refactor_ltr ae))) =
          (Expressible_nat n, S (depth_right (super_refactor_ltr ae)))
    | Expressible_msg s =>
        (Expressible_msg s, 0) = (Expressible_msg s, 0)
    end).

Theorem main_theorem :
  forall (ae : arithmetic_expression),
    (forall n : nat,
        interpret_ltr (Source_program ae) = Expressible_nat n ->
        run_height_ltr (compile_ltr (Source_program (super_refactor_ltr ae))) =
          (Expressible_nat n, S (depth_right (super_refactor_ltr ae))))
    /\
      (forall s : string,
        interpret_ltr (Source_program ae) = Expressible_msg s ->
        run_height_ltr (compile_ltr (Source_program (super_refactor_ltr ae))) =
          (Expressible_msg s, 0)).
(* [od] this statement is off because all occurrences of ae should be super-refactored, including the ones in the premiss:

        interpret_ltr (Source_program (super_refactor_ltr ae)) = Expressible_nat n ->
*)
Proof.
  intro ae.
  unfold interpret_ltr, run_height_ltr, compile_ltr.
  split.
  - intros n H_e_ae.
    destruct (main_theorem_aux' ae nil) as [H_OK _].
    Check (H_OK n H_e_ae).
    rewrite -> (H_OK n H_e_ae).
    rewrite -> fold_unfold_list_length_nil.
    rewrite -> Nat.add_0_l.
    reflexivity.
  - intros s H_e_ae.
    destruct (main_theorem_aux ae nil) as [_ H_KO].
    rewrite -> (H_KO s H_e_ae).
    reflexivity.
Qed.

(* [od] 
   Anyway, the main theorem should not involve refactoring.
   And then it should have corollaries where ae is actually the result of refactoring.
   A simple way would be to quantify ae to be not an arithmetic_expression
   but an arithmetic_expression_right (or _left)
   and then adjust interpret_ltr and compile_ltr to operate on arithmetic_expression_right:

Theorem main_theorem_ltr_right :
  forall (aer : arithmetic_expression_right),
    (forall n : nat,
        interpret_ltr_right (Source_program_right aer) = Expressible_nat n ->
        run_height_ltr (compile_ltr_right (Source_program_right aer)) =
          (Expressible_nat n, S (depth_right_right aer)))
    /\
      (forall s : string,
        interpret_ltr_right (Source_program_right aer) = Expressible_msg s ->
        run_height_ltr (compile_ltr_right (Source_program_right aer)) =
          (Expressible_msg s, 0)).

Theorem main_theorem_ltr_left :
  forall (ael : arithmetic_expression_left),
    (forall n : nat,
        interpret_ltr_left (Source_program_left ael) = Expressible_nat n ->
        run_height_ltr (compile_ltr_left (Source_program_left ael)) =
          (Expressible_nat n, S (depth_right_left ael)))
    /\
      (forall s : string,
        interpret_ltr_left (Source_program_left ael) = Expressible_msg s ->
        run_height_ltr (compile_ltr_left (Source_program_left ael)) =
          (Expressible_msg s, 0)).

Theorem main_theorem_rtl_right :
  forall (aer : arithmetic_expression_right),
    (forall n : nat,
        interpret_rtl_right (Source_program_right aer) = Expressible_nat n ->
        run_height_rtl (compile_rtl_right (Source_program_right aer)) =
          (Expressible_nat n, S (depth_right_right aer)))
    /\
      (forall s : string,
        interpret_rtl_right (Source_program_right aer) = Expressible_msg s ->
        run_height_rtl (compile_rtl_right (Source_program_right aer)) =
          (Expressible_msg s, 0)).

Theorem main_theorem_rtl_left :
  forall (ael : arithmetic_expression_left),
    (forall n : nat,
        interpret_rtl_left (Source_program_left ael) = Expressible_nat n ->
        run_height_rtl (compile_rtl_left (Source_program_left ael)) =
          (Expressible_nat n, S (depth_right_left ael)))
    /\
      (forall s : string,
        interpret_rtl_left (Source_program_left ael) = Expressible_msg s ->
        run_height_rtl (compile_rtl_left (Source_program_left ael)) =
          (Expressible_msg s, 0)).

These are the four cases, and, e.g.,

   Definition depth_right_right (aer : arithmetic_expression_right) : nat :=
     depth_right (super_refactor_right (arithmetic_expression_from_arithmetic_expression_right)).

etc.

But these four theorems are too much work.
So for your handin, just consider one version per evaluation order:

Theorem main_theorem_ltr_right :
  forall (ae : arithmetic_expression),
    (forall n : nat,
        interpret_ltr (Source_program ae) = Expressible_nat n ->
        run_height_ltr (compile_ltr (Source_program ae)) =
          (Expressible_nat n, S (depth_ltr ae)))
    /\
      (forall s : string,
        interpret_ltr (Source_program ae) = Expressible_msg s ->
        run_height_ltr (compile_ltr (Source_program ae)) =
          (Expressible_msg s, 0)).

for a suitable definition of depth_ltr (maybe / probably either depth_left or depth_right; run some tests).

This is a simple variation on what you did in your term project.

Mutatis mutandis:

Theorem main_theorem_rtl_right :
  forall (ae : arithmetic_expression),
    (forall n : nat,
        interpret_rtl (Source_program ae) = Expressible_nat n ->
        run_height_rtl (compile_rtl (Source_program ae)) =
          (Expressible_nat n, S (depth_rtl ae)))
    /\
      (forall s : string,
        interpret_rtl (Source_program ae) = Expressible_msg s ->
        run_height_rtl (compile_rtl (Source_program ae)) =
          (Expressible_msg s, 0)).

for a suitable definition of depth_rtl (maybe / probably either depth_right or depth_left; run some tests).


And then you can, by hand (no theorem and no proofs), characterize the result of depth_ltr and of depth_rtl
when the input is left-refactored and when it is right-refactored.

Hopefully your characterization can explain why

* refactoring the source expression on the left is a good idea when using ltr evaluation (it requires a smaller stack at run time)

* refactoring the source expression on the right is a bad idea when using ltr evaluation (it requires a bigger stack at run time)

* refactoring the source expression on the left is a bad idea when using rtl evaluation (it requires a bigger stack at run time)

* refactoring the source expression on the right is a good idea when using rtl evaluation (it requires a smaller stack at run time)

since that is the point of this handin.

*)

(* ********** *)

(* end of week3_stack_height_v2.v *)
