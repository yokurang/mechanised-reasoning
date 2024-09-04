(* week3_stack_height.v *)

(* MR 2024 - YSC 2024-2025, Sem1 *)
(* Continued from FPP 2023 - YSC 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 29 Aug 2024 *)

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

(* ********** *)

Lemma fold_unfold_list_append_nil :
  forall (V : Type)
         (v2s : list V),
    nil ++ v2s = v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_list_append_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    (v1 :: v1s') ++ v2s = v1 :: v1s' ++ v2s.
Proof.
  fold_unfold_tactic List.app.
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

(* ********** *)

(* evaluate: *)

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

Definition test_evaluate (candidate : arithmetic_expression -> expressible_value) : bool :=
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

Fixpoint evaluate_rtl (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate_rtl ae2 with
      | Expressible_msg s2 =>
          Expressible_msg s2
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_msg s1 =>
              Expressible_msg s1
          | Expressible_nat n1 =>
              Expressible_nat (n1 + n2)
          end
      end
  | Minus ae1 ae2 =>
      match evaluate_rtl ae2 with
      | Expressible_msg s2 =>
          Expressible_msg s2
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_msg s1 =>
              Expressible_msg s1
          | Expressible_nat n1 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          end
      end
  end.

Compute (test_evaluate evaluate = true).

Compute (test_evaluate evaluate_rtl = false).

Compute (test_evaluate_rtl evaluate = false).

Compute (test_evaluate_rtl evaluate_rtl = true).

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

(* Task 1b interpret *)

Definition test_interpret (candidate : source_program -> expressible_value) : bool :=
  (expressible_value_eqb (candidate (Source_program (Literal 5))) (Expressible_nat 5))
  && (expressible_value_eqb (candidate (Source_program (Plus (Literal 5) (Literal 5)))) (Expressible_nat 10))
  && (expressible_value_eqb (candidate (Source_program (Plus (Plus (Literal 1) (Literal 2)) (Literal 3)))) (Expressible_nat 6))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 5) (Literal 5)))) (Expressible_nat 0))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 5) (Literal 4)))) (Expressible_nat 1))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Minus (Minus (Literal 4) (Literal 5)) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Plus (Minus (Literal 4) (Literal 5)) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 5) (Minus (Literal 4)(Literal 5))))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Plus (Literal 5) (Minus (Literal 4) (Literal 5))))) (Expressible_msg "numerical underflow: -1")).

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => evaluate ae
  end.

Compute (test_interpret interpret = true).

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

Inductive result_of_decoding_and_execution : Type :=
  OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

(* decode_execute *)

Definition test_eqb_list_nat (candidate : list nat -> list nat -> bool) : bool :=
  (Bool.eqb (candidate nil nil) true)
  && (Bool.eqb (candidate (1 :: nil) (1 :: nil)) true)
  && (Bool.eqb (candidate (2 :: 1 :: nil) (2 :: 1 :: nil)) true)
  && (Bool.eqb (candidate (2 :: 1 :: nil) (1 :: 1 :: nil)) false).

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

Compute (test_eqb_list_nat eqb_list_nat = true).

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
          String.eqb s1 s2
      end
  end.

Definition test_decode_execute (candidate : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) : bool :=
  (eqb_result_of_decoding_and_execution (candidate (PUSH 42) (1 :: 2 :: 3 :: nil)) (OK (42 :: 1 :: 2 :: 3 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (1 :: 5 :: nil)) (OK (4 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (5 :: 1 :: nil)) (KO "numerical underflow: -4"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (1 :: nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (nil)) (KO "SUB: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (4 :: 3 :: 2 :: 1 :: nil)) (OK (7 :: 2 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (3 :: 4 :: 2 :: 5 :: nil)) (OK (1 :: 2 :: 5 :: nil))).

Definition decode_execute (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
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

Compute (test_decode_execute decode_execute = true).

(* fdel *)

Definition test_fetch_decode_execute_loop (candidate : (list byte_code_instruction) -> data_stack -> result_of_decoding_and_execution) :=
  (eqb_result_of_decoding_and_execution (candidate (PUSH 42 :: PUSH 21 :: nil) (2 :: 4 :: nil)) (OK (21 :: 42 :: 2 :: 4 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (PUSH 42 :: PUSH 21 :: nil) (nil)) (OK (21 :: 42 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (ADD :: SUB :: nil) (nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (PUSH 3 :: PUSH 10 :: SUB :: nil) nil) (KO "numerical underflow: -7"))
  && (eqb_result_of_decoding_and_execution (candidate (PUSH 3 :: PUSH 1 :: SUB :: PUSH 3 :: PUSH 2 :: ADD :: SUB :: nil) nil) (KO "numerical underflow: -3")).

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | nil => OK ds
  | bci :: bcis' =>
    match decode_execute bci ds with
    | OK ds' => fetch_decode_execute_loop bcis' ds'
    | KO s => KO s
    end
  end.

Compute (test_fetch_decode_execute_loop fetch_decode_execute_loop).

Lemma fold_unfold_fetch_decode_execute_loop_nil :
  forall (ds: data_stack),
    fetch_decode_execute_loop nil ds =
      OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction) (bcis' : list byte_code_instruction) (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
      match decode_execute bci ds with
      | OK ds' => fetch_decode_execute_loop bcis' ds'
      | KO s => KO s
      end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

(* ********** *)

(* This is more operational (v1), but it's better to write something more logical (v2) *)

Theorem fetch_decode_execute_loop_concatenation_v1 :
  forall (bci1s bci2s : list byte_code_instruction) (ds : data_stack),
    fetch_decode_execute_loop (bci1s ++ bci2s) ds =
    match fetch_decode_execute_loop bci1s ds with
    | OK ds' => fetch_decode_execute_loop bci2s ds'
    | KO s => KO s
    end.
Proof.
  (* Let's test first *)
  Compute (let bci1s := (PUSH 42 :: PUSH 23 :: nil) in
           let bci2s :=  (ADD :: SUB :: nil) in
           let ds := (2 :: 1 :: nil) in
           fetch_decode_execute_loop (bci1s ++ bci2s) ds =
             match fetch_decode_execute_loop bci1s ds with
             | OK ds' => fetch_decode_execute_loop bci2s ds'
             | KO s => KO s
             end).
  Compute (let bci1s := (ADD :: SUB :: nil)  in
           let bci2s := (PUSH 42 :: PUSH 23 :: nil)  in
           let ds := (nil) in
           fetch_decode_execute_loop (bci1s ++ bci2s) ds =
             match fetch_decode_execute_loop bci1s ds with
             | OK ds' => fetch_decode_execute_loop bci2s ds'
             | KO s => KO s
             end).
  intros bci1s.
  induction bci1s as [ | bci1 bci1s' IHbci1s'].
  - intros bci2s ds.
    rewrite -> fold_unfold_list_append_nil.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  - intros [ | bci2 bci2s'].
    + intro ds.
      Search (_ ++ nil = _).
      Check (app_nil_r).
      rewrite -> (app_nil_r).
      Check (fold_unfold_fetch_decode_execute_loop_cons).
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      destruct (decode_execute bci1 ds) as [ds1' | s1].
      * Check (IHbci1s' nil ds1').
        rewrite <- (app_nil_r bci1s') at 1.
        Check (IHbci1s' nil ds1').
        exact (IHbci1s' nil ds1').
      * reflexivity.
    + intro ds.
      Check (fold_unfold_fetch_decode_execute_loop_cons).
      rewrite -> fold_unfold_list_append_cons.
      rewrite -> 2 fold_unfold_fetch_decode_execute_loop_cons.
      destruct (decode_execute bci1 ds) as [ds1' | s1].
      * Check (IHbci1s').
        Check (IHbci1s' (bci2 :: bci2s')).
        exact (IHbci1s' (bci2 :: bci2s') ds1').
      * reflexivity.
Qed.

(* This is more logical *)

Theorem fetch_decode_execute_loop_concatenation_v2 :
  forall (bci1s bci2s : list byte_code_instruction) (ds : data_stack),
    (forall ds1 : data_stack,
       fetch_decode_execute_loop bci1s ds = OK ds1 ->
       fetch_decode_execute_loop (bci1s ++ bci2s) ds =
       fetch_decode_execute_loop bci2s ds1)
    /\
    (forall s1 : string,
       fetch_decode_execute_loop bci1s ds = KO s1 ->
       fetch_decode_execute_loop (bci1s ++ bci2s) ds =
       KO s1).
Proof.
  intros bci1s.
  induction bci1s as [ | bci bci1s' IHbci1s'].
  - intros [ | bci2 bci2s'].
    + intro ds.
      split.
      * intro ds1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        rewrite -> S_fde_nil.
        rewrite <- fold_unfold_fetch_decode_execute_loop_nil.
        reflexivity.
      * intro s1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        exact S_fde_nil.
    + intro ds.
      split.
      * intro ds1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        rewrite -> (fold_unfold_fetch_decode_execute_loop_nil) in S_fde_nil.
        injection S_fde_nil as S_fde_nil.
        rewrite -> S_fde_nil.
        reflexivity.
      * intro s1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil in S_fde_nil.
        discriminate S_fde_nil.
  - intros [ | bci2 bci2s'].
    + intro ds.
      split.
      * intro ds1.
        intro S_nil.
        Search (_ ++ nil).
        rewrite -> app_nil_r.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        exact S_nil.
      * intro s1.
        intro S_KO.
        rewrite -> app_nil_r.
        exact S_KO.
    + intro ds.
      split.
      * intro ds1.
        intro S_OK.
        rewrite -> fold_unfold_list_append_cons.
        destruct (decode_execute bci ds) as [ds' | s'] eqn:H_decode.
        -- destruct (IHbci1s' (bci2 :: bci2s') ds') as [S_ds _].
           Check (fold_unfold_fetch_decode_execute_loop_cons).
           Check (fold_unfold_fetch_decode_execute_loop_cons bci (bci1s' ++ bci2 :: bci2s')).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_OK.
           rewrite -> H_decode in S_OK.
           Check (S_ds ds1).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           Check (S_ds ds1 S_OK).
           exact (S_ds ds1 S_OK).
        -- destruct (IHbci1s' (bci2 :: bci2s') ds) as [S_ds _].
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_OK.
           rewrite -> H_decode in S_OK.
           discriminate S_OK.
      * intro s1.
        intro S_KO.
        rewrite -> fold_unfold_list_append_cons.
        destruct (decode_execute bci ds) as [ds' | s'] eqn:H_decode.
        -- destruct (IHbci1s' (bci2 :: bci2s') ds') as [_ S_s].
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_KO.
           rewrite -> H_decode in S_KO.
           Check (S_s s1 S_KO).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           exact (S_s s1 S_KO).
        -- destruct (IHbci1s' (bci2 :: bci2s') ds) as [_ S_s].
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_KO.
           rewrite -> H_decode in S_KO.
           exact S_KO.
Qed.

(* ********** *)

(* run *)

Definition test_run (candidate : target_program -> expressible_value) : bool :=
  (expressible_value_eqb
     (candidate (Target_program (PUSH 42 :: nil)))
     (Expressible_nat 42))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 42 :: ADD :: SUB :: nil)))
        (Expressible_msg "ADD: stack underflow"))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 42 :: ADD :: SUB :: PUSH 20 :: PUSH 10 :: PUSH 5 :: nil)))
        (Expressible_msg "ADD: stack underflow"))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 20 :: PUSH 42 :: ADD :: PUSH 20 :: PUSH 30 :: PUSH 40 :: nil)))
        (Expressible_msg "too many results on the data stack"))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 42 :: PUSH 1 :: ADD :: PUSH 100 :: ADD :: nil)))
        (Expressible_nat 143)).

Definition run (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | OK nil => Expressible_msg "no result on the data stack"
    | OK (n :: nil) => Expressible_nat n
    | OK (n :: _ :: _) => Expressible_msg "too many results on the data stack"
    | KO s => Expressible_msg s
    end
  end.

Compute (test_run run = true).

(* A more verbose version,
reflects the structure of the there is at most one run function proof *)
Definition run_v2 (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | OK ds =>
        match ds with
        | nil => Expressible_msg "no result on the data stack"
        | (n :: ds') =>
            match ds' with
            | nil =>  Expressible_nat n
            | (n' :: ds'') => Expressible_msg "too many results on the data stack"
            end
        end
    | KO s => Expressible_msg s
    end
  end.

Compute (test_run run_v2 = true).

(* compile aux *)

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
    match ae with
    | Literal n => PUSH n :: nil
    | Plus ae1 ae2 => compile_aux ae1 ++ compile_aux ae2 ++ (ADD :: nil)
    | Minus ae1 ae2 => compile_aux ae1 ++ compile_aux ae2 ++ (SUB :: nil)
    end.

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

Definition test_compile_aux (candidate : arithmetic_expression -> (list byte_code_instruction)) :=
  (eqb_list_byte_code_instruction (candidate (Literal 2))
     (PUSH 2 :: nil))
  && (eqb_list_byte_code_instruction (candidate (Plus (Literal 5) (Literal 2)))
        (PUSH 5 :: PUSH 2 :: ADD :: nil))
  && (eqb_list_byte_code_instruction (candidate (Minus (Literal 5) (Literal 2)))
        (PUSH 5 :: PUSH 2 :: SUB :: nil)).

Compute (test_compile_aux compile_aux = true).

(* Task 6c *)

Lemma fold_unfold_compile_aux_Literal :
  forall (n : nat),
    compile_aux (Literal n) =
      PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Plus ae1 ae2) =
       compile_aux ae1 ++ compile_aux ae2 ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Minus ae1 ae2) =
       compile_aux ae1 ++ compile_aux ae2 ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

(*********)

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

Definition test_compile (candidate : source_program -> target_program) : bool :=
  (eqb_target_program
     (candidate (Source_program (Minus (Literal 3) (Literal 10))))
     (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil)))
  && (eqb_target_program
        (candidate (Source_program (Minus (Minus (Literal 3) (Literal 1)) (Plus (Literal 3) (Literal 2)))))
        (Target_program (PUSH 3 :: PUSH 1 :: SUB :: PUSH 3 :: PUSH 2 :: ADD :: SUB :: nil))).

Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae => Target_program (compile_aux ae)
  end.

Compute (test_compile compile = true).

(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
 *)

Fixpoint compile_alt_aux_aux (ae : arithmetic_expression) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
  | Literal n => PUSH n :: a
  | Plus ae1 ae2 => compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (ADD :: a))
  | Minus ae1 ae2 => compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (SUB :: a))
  end.

Lemma fold_unfold_compile_alt_aux_aux_Literal :
  forall (n : nat)
         (a : list byte_code_instruction),
    compile_alt_aux_aux (Literal n) a =
      PUSH n :: a.
Proof.
  fold_unfold_tactic compile_alt_aux_aux.
Qed.

Lemma fold_unfold_compile_alt_aux_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_alt_aux_aux (Plus ae1 ae2) a =
      compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (ADD :: a)).
Proof.
  fold_unfold_tactic compile_alt_aux_aux.
Qed.

Lemma fold_unfold_compile_alt_aux_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_alt_aux_aux (Minus ae1 ae2) a =
      compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (SUB :: a)).
Proof.
  fold_unfold_tactic compile_alt_aux_aux.
Qed.

Lemma about_compile_alt_aux_aux :
  forall (ae : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_alt_aux_aux ae a = (compile_alt_aux_aux ae nil) ++ a.
Proof.
  Compute (let ae := (Plus (Literal 5) (Literal 2)) in
           let a := (PUSH 50 :: PUSH 20 :: nil) in
           compile_alt_aux_aux ae a = (compile_alt_aux_aux ae nil) ++ a).
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro a.
  - rewrite -> 2(fold_unfold_compile_alt_aux_aux_Literal).
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - Check (fold_unfold_compile_alt_aux_aux_Plus).
    rewrite -> 2fold_unfold_compile_alt_aux_aux_Plus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: a))).
    Search ((_ ++ _) ++ _ = _).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (ADD :: a)).
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - rewrite -> 2fold_unfold_compile_alt_aux_aux_Minus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: a))).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (SUB :: a)).
    rewrite -> (IHae2 (SUB :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
Qed.

Definition make_Eureka_lemma (A : Type) (id_A : A) (combine_A : A -> A -> A) (c : A -> A) (a : A) : Prop :=
  c a = combine_A (c id_A) a.

Lemma about_compile_alt_aux_aux_alt :
  (* expressed using make_Eureka_lemma *)
  forall (ae : arithmetic_expression) (a : list byte_code_instruction),
    make_Eureka_lemma (list byte_code_instruction) nil (fun x y => x ++ y) (compile_alt_aux_aux ae) a.
Proof.
  unfold make_Eureka_lemma.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro a.
  - rewrite -> 2(fold_unfold_compile_alt_aux_aux_Literal).
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - Check (fold_unfold_compile_alt_aux_aux_Plus).
    rewrite -> 2fold_unfold_compile_alt_aux_aux_Plus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: a))).
    Search ((_ ++ _) ++ _ = _).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (ADD :: a)).
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - rewrite -> 2fold_unfold_compile_alt_aux_aux_Minus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: a))).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (SUB :: a)).
    rewrite -> (IHae2 (SUB :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
Qed.

Definition compile_alt_aux (ae : arithmetic_expression) : list byte_code_instruction :=
   (compile_alt_aux_aux ae nil).

Compute (test_compile_aux compile_alt_aux = true).

Definition compile_alt (sp : source_program) : target_program :=
  match sp with
  | Source_program ae => Target_program (compile_alt_aux ae)
  end.

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)

Lemma about_ae_OK :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate ae = Expressible_nat n -> fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds)).
Proof.
  intro ae.
  induction ae as [ n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intros ds n H_ae.
  - rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    unfold decode_execute.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    rewrite -> fold_unfold_evaluate_Literal in H_ae.
    injection H_ae as eq_n'_n.
    rewrite -> eq_n'_n.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Plus.
    Check (fetch_decode_execute_loop_concatenation_v1).
    rewrite -> fetch_decode_execute_loop_concatenation_v1.
    rewrite -> fold_unfold_evaluate_Plus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + Check (IHae1 ds n1 eq_refl).
       rewrite -> (IHae1 ds n1 eq_refl).
       rewrite -> fetch_decode_execute_loop_concatenation_v1.
       Check (IHae2 (n1 :: ds) n2 eq_refl).
       rewrite -> (IHae2 (n1 :: ds) n2 eq_refl).
       rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
       unfold decode_execute.
       rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
       injection H_ae as eq_sum_n1_n2_n.
       rewrite -> eq_sum_n1_n2_n.
       reflexivity.
    + discriminate H_ae.
    + discriminate H_ae.
  - rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> fetch_decode_execute_loop_concatenation_v1.
    rewrite -> fold_unfold_evaluate_Minus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + case (n1 <? n2) as [ | ] eqn:H_n1_n2.
      * discriminate H_ae.
      * Check (IHae1 ds n1 eq_refl).
        rewrite -> (IHae1 ds n1 eq_refl).
        rewrite -> fetch_decode_execute_loop_concatenation_v1.
        Check (IHae2 (n1 :: ds) n2 eq_refl).
        rewrite -> (IHae2 (n1 :: ds) n2 eq_refl).
        rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
        unfold decode_execute.
        rewrite -> H_n1_n2.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        injection H_ae as eq_sub_n1_n2_n.
        rewrite -> eq_sub_n1_n2_n.
        reflexivity.
    + discriminate H_ae.
    + discriminate H_ae.
Qed.

Lemma about_ae_KO :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (s : string),
        evaluate ae = Expressible_msg s -> fetch_decode_execute_loop (compile_aux ae) ds = KO s).
Proof.
  intro ae.
  induction ae as [ n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intros ds s H_ae.
  - rewrite -> fold_unfold_evaluate_Literal in H_ae.
    discriminate H_ae.
  - rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> fetch_decode_execute_loop_concatenation_v1.
    rewrite -> fold_unfold_evaluate_Plus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + discriminate H_ae.
    + Check (about_ae_OK).
      Check (about_ae_OK ae1 ds n1).
      Check (about_ae_OK ae1 ds n1 H_ev_ae1).
      rewrite -> (about_ae_OK ae1 ds n1 H_ev_ae1).
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      Check (IHae2 (n1 :: ds) s H_ae).
      rewrite -> (IHae2 (n1 :: ds) s H_ae).
      reflexivity.
    + Check (IHae1 ds s H_ae).
      rewrite -> (IHae1 ds s H_ae).
      reflexivity.
  - rewrite -> fold_unfold_evaluate_Minus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + case (n1 <? n2) as [ | ] eqn:H_n1_n2.
      * rewrite -> fold_unfold_compile_aux_Minus.
        rewrite -> fetch_decode_execute_loop_concatenation_v1.
        Check (about_ae_OK).
        Check (about_ae_OK ae1 ds n1).
        Check (about_ae_OK ae1 ds n1 H_ev_ae1).
        rewrite -> (about_ae_OK ae1 ds n1 H_ev_ae1).
        rewrite -> fetch_decode_execute_loop_concatenation_v1.
        Check (about_ae_OK ae2 (n1 :: ds) n2 H_ev_ae2).
        rewrite -> (about_ae_OK ae2 (n1 :: ds) n2 H_ev_ae2).
        rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
        unfold decode_execute.
        rewrite -> H_n1_n2.
        injection H_ae as H_s.
        rewrite <- H_s.
        reflexivity.
      * discriminate H_ae.
    + rewrite -> fold_unfold_compile_aux_Minus.
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      rewrite -> (about_ae_OK ae1 ds n1 H_ev_ae1).
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      rewrite -> (IHae2 (n1 :: ds) s H_ae).
      reflexivity.
    + rewrite -> fold_unfold_compile_aux_Minus.
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      rewrite -> (IHae1 ds s1 eq_refl).
      injection H_ae as eq_s1_s.
      rewrite -> eq_s1_s.
      reflexivity.
Qed.

Theorem the_commuting_diagram :
  forall sp : source_program,
    interpret sp = run (compile sp).
Proof.
  intro sp.
  destruct sp as [ae].
  unfold compile.
  unfold run.
  unfold interpret.
  case (evaluate ae) as [n' | s] eqn:H_ae.
  - rewrite -> (about_ae_OK ae nil n' H_ae).
    reflexivity.
  - rewrite -> (about_ae_KO ae nil s H_ae).
    reflexivity.
Qed.

Lemma the_commuting_diagram'_aux :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall n' : nat,
        evaluate ae = Expressible_nat n' ->
        fetch_decode_execute_loop (compile_aux ae) ds =
          OK (n' :: ds))
    /\
      (forall s : string,
          evaluate ae = Expressible_msg s ->
          fetch_decode_execute_loop (compile_aux ae) ds =
            KO s).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds; split.
  - intros n' H_n.
    rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    unfold decode_execute.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    rewrite -> fold_unfold_evaluate_Literal in H_n.
    injection H_n as H_eq_n_n'.
    rewrite -> H_eq_n_n'.
    reflexivity.
  - intros s H_s.
    rewrite -> fold_unfold_evaluate_Literal in H_s.
    discriminate H_s.
    
  - intros n' H_n'.
    rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> fold_unfold_evaluate_Plus in H_n'.
    destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae1_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
      case (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      * destruct (IHae2 (n1 :: ds)) as [IHae2_OK IHae2_KO].
        rewrite -> (H_fdel_ae2_OK (n2 :: n1 :: ds) (IHae2_OK n2 (eq_refl (Expressible_nat n2)))).
        rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
        unfold decode_execute.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        injection H_n' as H_n1_n2.
        rewrite -> H_n1_n2.
        reflexivity.
      * discriminate H_n'.
    + discriminate H_n'.
  - intros s H_s.
    rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> fold_unfold_evaluate_Plus in H_s.
    destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae1_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
      case (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      * discriminate H_s.
      * destruct (IHae2 (n1 ::ds)) as [IHae2_OK IHae2_KO].
        rewrite -> (H_fdel_ae2_KO s2 (IHae2_KO s2 (eq_refl (Expressible_msg s2)))).
        injection H_s as H_s_s2.
        rewrite -> H_s_s2.
        reflexivity.        
    + destruct (IHae1 ds) as [_ IHae1_KO].
      rewrite -> (H_fdel_ae1_KO s1 (IHae1_KO s1 (eq_refl (Expressible_msg s1)))).
      injection H_s as H_s1.
      rewrite -> H_s1.
      reflexivity.
      
  - intros n' H_n'.
    rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> fold_unfold_evaluate_Minus in H_n'.
    destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae2_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
      case (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      * destruct (IHae2 (n1 :: ds)) as [IHae2_OK IHHae2_KO].
        case (n1 <? n2) eqn: H_n1_lt_n2.
        { discriminate H_n'. }
        rewrite -> (H_fdel_ae2_OK (n2 :: n1 :: ds) (IHae2_OK n2 (eq_refl (Expressible_nat n2)))).
        rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
        unfold decode_execute.
        rewrite -> H_n1_lt_n2.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        injection H_n' as H_n1_n2.
        rewrite -> H_n1_n2.
        reflexivity. 
      * discriminate H_n'.
    + discriminate H_n'.
  - intros s H_s.
    rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> fold_unfold_evaluate_Minus in H_s.
    destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae1_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (fetch_decode_execute_loop_concatenation_v2 (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
      case (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      * destruct (IHae2 (n1 :: ds)) as [IHae2_OK IHHae2_KO].
        case (n1 <? n2) eqn: H_n1_lt_n2.
        { rewrite -> (H_fdel_ae2_OK (n2 :: n1 :: ds) (IHae2_OK n2 (eq_refl (Expressible_nat n2)))).
        rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
        unfold decode_execute.
        rewrite -> H_n1_lt_n2.
        remember (String.append ("numerical underflow: -") (string_of_nat (n2 - n1))) as msg eqn:H_msg.
        injection H_s as H_s'.
        rewrite -> H_s'.
        reflexivity. }
        discriminate H_s.
      * destruct (IHae2 (n1 ::ds)) as [IHae2_OK IHae2_KO].
        rewrite -> (H_fdel_ae2_KO s2 (IHae2_KO s2 (eq_refl (Expressible_msg s2)))).
        injection H_s as H_s_s2.
        rewrite -> H_s_s2.
        reflexivity.   
    + destruct (IHae1 ds) as [_ IHae1_KO].
      rewrite -> (H_fdel_ae1_KO s1 (IHae1_KO s1 (eq_refl (Expressible_msg s1)))).
      injection H_s as H_s1.
      rewrite -> H_s1.
      reflexivity.
Qed.
  
Theorem the_commuting_diagram' :
  forall sp : source_program,
    interpret sp = run (compile sp).
Proof.
  intros [ae].
  unfold interpret, run, compile.
  destruct (the_commuting_diagram'_aux ae nil) as [H_fdel_OK H_fdel_KO].
  destruct (evaluate ae) as [n | s] eqn: H_ae.
  - rewrite -> (H_fdel_OK n (eq_refl (Expressible_nat n))).
    reflexivity.
  - rewrite -> (H_fdel_KO s (eq_refl (Expressible_msg s))).
    reflexivity.
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
  with super_refactor_right_aux (ae1 a : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
    | Literal n =>
      Plus (Literal n) a
    | Plus ae1 ae2 =>
      super_refactor_right_aux ae1 (super_refactor_right_aux ae2 a)
    | Minus ae1 ae2 =>
      Plus (Minus (super_refactor_right ae1) (super_refactor_right ae2)) a
    end.

(* ***** *)

Lemma fold_unfold_super_refactor_right_Literal :
  forall (n : nat),
    super_refactor_right (Literal n) =
      (Literal n).
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
    super_refactor_right_aux (Literal n) a =
      Plus (Literal n) a.
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Plus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_right_aux (Plus ae1 ae2) a =
      super_refactor_right_aux ae1 (super_refactor_right_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

Lemma fold_unfold_super_refactor_right_aux_Minus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_right_aux (Minus ae1 ae2) a =
      Plus (Minus (super_refactor_right ae1) (super_refactor_right ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

(* ***** *)

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

Compute (super_refactor_right
  (Plus
    (Plus (Literal 1) (Literal 2))
    (Plus (Literal 3) (Literal 4)))).

Definition test_super_refactor_left (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  let ae1 := (Plus
               (Plus (Literal 1) (Literal 2))
               (Plus (Literal 3) (Literal 4))) in
  let ae2 := (Minus
                (Plus (Literal 15) (Plus (Literal 4) (Literal 5)))
                (Plus (Literal 1) (Literal 2))) in
  (eqb_arithmetic_expression
     (candidate ae1)
     (Plus (Plus (Plus (Literal 1) (Literal 2)) (Literal 3)) (Literal 4))) &&
    (eqb_arithmetic_expression
       (candidate ae2)
       (Minus
          (Plus (Plus (Literal 15) (Literal 4)) (Literal 5))
          (Plus (Literal 1) (Literal 2)))).

Fixpoint super_refactor_left (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    super_refactor_aux_left (super_refactor_left ae1) ae2
  | Minus ae1 ae2 =>
    Minus (super_refactor_left ae1) (super_refactor_left ae2)
  end
  with super_refactor_aux_left (a ae1 : arithmetic_expression) : arithmetic_expression :=
    match ae1 with
    | Literal n =>
      Plus a (Literal n)
    | Plus ae1 ae2 =>
      super_refactor_aux_left (super_refactor_aux_left a ae1) ae2
    | Minus ae1 ae2 =>
      Plus a (Minus (super_refactor_left ae1) (super_refactor_left ae2))
    end.

Compute (test_super_refactor_left super_refactor_left).

(* ***** *)

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

(* ***** *)

(* *** Start of List Length *** *)

Definition test_list_length (candidate : forall V : Type, list V -> nat) :=
  (candidate nat nil =? 0) &&
    (candidate bool nil =? 0) &&
    (candidate nat (1 :: nil) =? 1) &&
    (candidate bool (true :: nil) =? 1) &&
    (candidate nat (2 :: 1 :: nil) =? 2) &&
    (candidate bool (false :: true :: nil) =? 2) &&
    (candidate nat (3 :: 2 :: 1 :: nil) =? 3) &&
    (candidate bool (false :: false :: true :: nil) =? 3) &&
    (candidate nat (5 :: 4 :: 3 :: 2 :: 1 :: nil) =? 5) &&
    (candidate bool (true :: true :: false :: false :: true :: nil) =? 5).

Fixpoint list_length (V : Type) (vs : list V) : nat :=
  match vs with
    | nil =>
      0
    | v :: vs' =>
      S (list_length V vs')
  end.

Compute (test_list_length list_length).

(* Associated fold-unfold lemmas: *)

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


Fixpoint list_length_acc (V : Type) (ls : list V) (a : nat) : nat :=
  match ls with
  | nil =>
      a
  | v :: vs' =>
      list_length_acc V vs' (S a)
  end.


Definition list_length_alt (V : Type) (vs : list V) : nat :=
  list_length_acc V vs 0.

Compute (test_list_length list_length_alt).

Lemma fold_unfold_list_length_acc_nil :
  forall (V : Type)
         (acc : nat),
    list_length_acc V nil acc =
      acc.
Proof.
  fold_unfold_tactic list_length_acc.
Qed.

Lemma fold_unfold_list_length_acc_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (acc : nat),
    list_length_acc V (v :: vs') acc =
      list_length_acc V vs' (S acc).
Proof.
  fold_unfold_tactic list_length_acc.
Qed.

(* *** End of List Length *** *)

(* Start of depth functions *)

Definition test_depth (candidate : arithmetic_expression -> nat) : bool :=
  let ae1 := (Literal 1) in
  let ae2 := (Plus
                (Plus (Literal 1) (Literal 2))
                (Plus (Literal 3) (Literal 4))) in
  let ae3 := (Minus
                (Minus
                   (Minus
                      (Minus (Literal 4) (Literal 3))
                      (Literal 0))
                   (Literal 0))
                (Literal 0)) in
  let ae4 := (Plus (Literal 1)
                (Plus (Literal 3) (Literal 4))) in
  let ae5 := (Plus (Plus (Literal 1) (Literal 2))
                (Literal 4)) in
  let ae6 := (Plus (Literal 1)
                 (Plus (Literal 3)
                    (Plus (Literal 4)(Literal 5)))) in
  let ae7 := (Plus
                 (Plus
                    (Plus (Literal 3)
                       (Literal 4))
                    (Literal 4))
                (Literal 4)) in
  let ae8 := (Minus (Literal 1) (Literal 2)) in
  let ae9 := (Plus (Minus (Literal 1) (Literal 2)) (Literal 3)) in
  let ae10 := (Minus
                 (Plus (Literal 1) (Literal 2))
                 (Minus (Literal 3) (Literal 4))) in
  let ae11 := (Plus
                 (Plus
                    (Plus
                       (Plus (Literal 1) (Literal 2))
                       (Literal 3))
                    (Literal 4))
                 (Literal 5)) in
  let ae12 := (Minus
                 (Minus (Literal 1)
                    (Minus (Literal 2)
                       (Minus
                       (Literal 3) (Literal 4))))
                 (Literal 5)) in
  (Nat.eqb (candidate ae1) 0) &&
    (Nat.eqb (candidate ae2) 2) &&
    (Nat.eqb (candidate ae3) 4) &&
    (Nat.eqb (candidate ae4) 2) &&
    (Nat.eqb (candidate ae5) 2) &&
    (Nat.eqb (candidate ae6) 3) &&
    (Nat.eqb (candidate ae7) 3) &&
    (Nat.eqb (candidate ae8) 1) &&
    (Nat.eqb (candidate ae9) 2) &&
    (Nat.eqb (candidate ae10) 2) &&
    (Nat.eqb (candidate ae11) 4) &&
    (Nat.eqb (candidate ae12) 4).

Fixpoint depth (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal n => 0
  | Plus ae1 ae2 =>
      let n1 := depth ae1 in
      let n2 := depth ae2 in
      S (max n1 n2)
  | Minus ae1 ae2 =>
      let n1 := depth ae1 in
      let n2 := depth ae2 in
      S (max n1 n2)
end.

Compute (test_depth depth).

Lemma fold_unfold_depth_Literal :
  forall (n : nat),
    depth (Literal n) = 0.
Proof.
  fold_unfold_tactic depth.
Qed.

Lemma fold_unfold_depth_Plus :
  forall (ae1 ae2: arithmetic_expression),
    depth (Plus ae1 ae2) = max (S (depth ae1)) (S (depth ae2)).
Proof.
  fold_unfold_tactic depth.
Qed.

Lemma fold_unfold_depth_Minus :
  forall (ae1 ae2: arithmetic_expression),
    depth (Minus ae1 ae2) = max (S (depth ae1)) (S (depth ae2)).
Proof.
  fold_unfold_tactic depth.
Qed.

(* End of depth functions *)

(* Start of depth left functions *)

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

(* End of depth left functions *)

(* Start of depth right functions *)

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


(* End of depth right functions *)

(* Start of fetch_decode_execute with height ltr functions *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
  | Some v1 =>
      match ov2 with
      | Some v2 =>
          eqb_V v1 v2
      | None =>
          false
      end
  | None =>
      match ov2 with
      | Some v =>
          false
      | None =>
          true
      end
  end.

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
          String.eqb s1 s2
      end
  end.

(* ***** *)

Definition test_decode_execute_height_ltr (candidate : byte_code_instruction -> data_stack -> result_of_decoding_and_execution_height) : bool :=
  (eqb_result_of_decoding_and_execution_height
     (candidate (PUSH 42) (1 :: 2 :: 3 :: nil))
     (OK_h (42 :: 1 :: 2 :: 3 :: nil) 4))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (PUSH 42) (1 :: 2 :: 3 :: nil))
       (OK_h (42 :: 1 :: 2 :: 3 :: nil) 4))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate ADD (1 :: 2 :: 3 :: nil))
       (OK_h (3 :: 3 :: nil) 3))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate SUB (2 :: 3 :: 3 :: nil))
       (OK_h (1 :: 3 :: nil) 3))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate SUB (3 :: 2 :: 3 :: nil))
       (KO_h "numerical underflow: -1")).

Definition decode_execute_height_ltr (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution_height :=
  match bci with
    (* current height depends on ds *)
  | PUSH n => OK_h (n :: ds) (S (list_length nat ds))
  | ADD =>
      match ds with
      | nil => KO_h "ADD: stack underflow"
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' => OK_h ((n1 + n2) :: ds'') (list_length nat ds)
          | nil => KO_h "ADD: stack underflow"
          end
      end
  | SUB =>
      match ds with
      | nil => KO_h "SUB: stack underflow"
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' =>
              match n1 <? n2 with
              | true =>
                  KO_h (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  OK_h ((n1 - n2) :: ds'') (list_length nat ds)
              end
          | nil => KO_h "SUB: stack underflow"
          end
      end
  end.

Compute test_decode_execute_height_ltr decode_execute_height_ltr.

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
      match decode_execute_height_ltr bci ds with
      | OK_h ds' mh' =>
          match fetch_decode_execute_loop_height_ltr bcis' ds' with
          | OK_h ds'' mh'' =>
              OK_h ds'' (max (list_length nat ds) mh'')
          | KO_h s =>
              KO_h s
          end
      | KO_h s => KO_h s
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
      match decode_execute_height_ltr bci ds with
      | OK_h ds' mh' =>
          match fetch_decode_execute_loop_height_ltr bcis' ds'  with
          | OK_h ds'' mh'' =>
              OK_h ds'' (max (list_length nat ds) mh'')
          | KO_h s =>
              KO_h s
          end
      | KO_h s =>
          KO_h s
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

(* End of fetch_decode_execute with height ltr functions *)

(* Start of fetch_decode_execute with height rtl functions *)

Definition test_decode_execute_height_rtl (candidate : byte_code_instruction -> data_stack  -> result_of_decoding_and_execution_height) : bool :=
  (eqb_result_of_decoding_and_execution_height
     (candidate (PUSH 42) (1 :: 2 :: 3 :: nil))
     (OK_h (42 :: 1 :: 2 :: 3 :: nil) 4))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate (PUSH 42) (1 :: 2 :: 3 :: nil))
       (OK_h (42 :: 1 :: 2 :: 3 :: nil) 4))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate ADD (1 :: 2 :: 3 :: nil))
       (OK_h (3 :: 3 :: nil) 3 ))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate SUB (2 :: 3 :: 3 :: nil))
       (KO_h "numerical underflow: -1"))
  &&
    (eqb_result_of_decoding_and_execution_height
       (candidate SUB (3 :: 2 :: 3 :: nil))
       (OK_h (1 :: 3 :: nil) 3)).

Definition decode_execute_height_rtl (bci : byte_code_instruction)
  (ds : data_stack) : result_of_decoding_and_execution_height :=
  match bci with
  | PUSH n => OK_h (n :: ds) (S (list_length nat ds))
  | ADD =>
      match ds with
      | nil => KO_h "ADD: stack underflow"
      | n1 :: ds' =>
          match ds' with
          | n2 :: ds'' => OK_h ((n1 + n2) :: ds'') (list_length nat ds)
          | nil => KO_h "ADD: stack underflow"
          end
      end
  | SUB =>
      match ds with
      | nil => KO_h "SUB: stack underflow"
      | n1 :: ds' =>
          match ds' with
          | n2 :: ds'' =>
              match n1 <? n2 with
              | true =>
                  KO_h (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  OK_h ((n1 - n2) :: ds'') (list_length nat ds)
              end
          | nil => KO_h "SUB: stack underflow"
          end
      end
  end.

Compute test_decode_execute_height_rtl decode_execute_height_rtl.

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
      match decode_execute_height_rtl bci ds with
      | OK_h ds' mh' =>
          match fetch_decode_execute_loop_height_rtl bcis' ds' with
          | OK_h ds'' mh'' =>
              OK_h ds'' (max (list_length nat ds) mh'')
          | KO_h s =>
              KO_h s
          end                 
      | KO_h s => KO_h s
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
    match decode_execute_height_rtl bci ds with
    | OK_h ds' mh' =>
        match fetch_decode_execute_loop_height_rtl bcis' ds' with
        | OK_h ds'' mh'' =>
            OK_h ds'' (max (list_length nat ds) mh'')
        | KO_h s =>
            KO_h s
        end                 
    | KO_h s => KO_h s
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

(* End of fetch_decode_execute with height rtl functions *)

(* Sanity check that run_height_ltr works for balanced trees of Plus operators *)

Compute (let ae1 := (Plus
                       (Plus (Literal 1) (Literal 2))
                       (Plus (Literal 1) (Literal 2))) in
         let ae2 := (Plus
                       (Plus (Literal 1) (Literal 2))
                       (Plus (Literal 1) (Literal 2))) in
         (run_height_ltr (Target_program (compile_aux (Plus ae1 ae2)))) =
           (match run_height_ltr (Target_program (compile_aux ae1)) with
            | (Expressible_nat n1, h1) =>
                (match run_height_ltr (Target_program (compile_aux ae2)) with
                 | (Expressible_nat n2, h2) =>
                     (Expressible_nat (n1 + n2), (max h1 h2) + 1)
                 | (Expressible_msg s, _) => (Expressible_msg s, 0)
                 end)
            | (Expressible_msg s, _) => (Expressible_msg s, 0)
            end)).

Theorem about_fetch_decode_execute_loop_height_concatenation_ltr :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds : data_stack),
    (* PUSH case  *)
    (forall (ds1 : data_stack)
            (mh : nat),
        fetch_decode_execute_loop_height_ltr bci1s ds =
          OK_h ds1 mh ->
        fetch_decode_execute_loop_height_ltr (bci1s ++ bci2s) ds =
          fetch_decode_execute_loop_height_ltr bci2s ds1)
    /\
      (forall s : string,
          fetch_decode_execute_loop_height_ltr bci1s ds = KO_h s ->
          fetch_decode_execute_loop_height_ltr (bci1s ++ bci2s) ds  =
            KO_h s).
Proof.
Admitted.
(*   intros bci1s. *)
(*   induction bci1s as [ | bci bci1s' IHbci1s']. *)
(*   - unfold fetch_decode_execute_loop_height_ltr at 1 4. *)
(*     intros bci2s ds. *)
(*     + split. *)
(*       { intros ds1. *)
(*         rewrite -> fold_unfold_list_append_nil. *)
(*         intro H_fdel. *)
(*         injection H_fdel as H_fdel. *)
(*         rewrite -> H_fdel. *)
(*         reflexivity. *)
(*       }       *)
(*       { intro s1. *)
(*         intro H_absurd. *)
(*         discriminate H_absurd. *)
(*       } *)
(*   - intros [ | bci2 bci2s'] ds. *)
(*     + split. *)
(*       { intro ds1. *)
(*         rewrite -> fold_unfold_list_append_cons. *)
(*         rewrite ->2 fold_unfold_fetch_decode_execute_loop_height_ltr_cons. *)
(*         rewrite -> fold_unfold_fetch_decode_execute_loop_height_ltr_nil. *)
(*         intro H_fdel. *)
(*         rewrite -> app_nil_r. *)
(*         exact H_fdel. *)
(*       } *)
(*       { intro s1. *)
(*         intro H_fdel. *)
(*         rewrite -> app_nil_r. *)
(*         exact H_fdel. *)
(*       } *)
(*     + split. *)
(*       { intro ds1. *)
(*         intro H_fdel. *)
(*         rewrite -> fold_unfold_list_append_cons. *)
(*         case (decode_execute_height_ltr bci ds) as [ ds' | s' ] eqn:H_decode. *)
(*         * destruct (IHbci1s' (bci2 :: bci2s') ds') as [ S_ds _ ]. *)
(*           rewrite -> fold_unfold_fetch_decode_execute_loop_height_ltr_cons in H_fdel. *)
(*           rewrite -> H_decode in H_fdel. *)
(*           rewrite -> fold_unfold_fetch_decode_execute_loop_height_ltr_cons. *)
(*           rewrite -> H_decode. *)
(*           case (fetch_decode_execute_loop_height_ltr bci1s' ds') as [ ds'' mh'' | s ] eqn:C_fdel. *)
(*           -- *)
(*           admit. *)
(* Admitted. *)

(* Start of running_and_compiling_ltr_guves_mh_S_depth_right_ae tests *)

Compute (let ae := Plus (Plus (Plus (Literal 1) (Literal 2)) (Literal 3))(Literal 4) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := Plus (Literal 1) (Minus (Literal 20) (Plus (Literal 3)(Literal 4))) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Literal 1) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Plus (Plus (Literal 1)(Literal 2))(Literal 3)) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Plus
                     (Plus
                        (Plus
                           (Literal 1)
                           (Literal 2))
                           (Literal 3))
                           (Literal 4)) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Plus (Minus (Literal 2) (Literal 1))(Literal 2)) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Plus (Literal 1) (Plus (Literal 2) (Literal 3))) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Plus (Literal 1) (Plus (Literal 2) (Plus (Literal 3) (Literal 4)))) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Plus (Literal 2) (Plus (Plus (Literal 3) (Literal 2)) (Literal 1))) in
         let ds := nil in
         match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

Compute (let ae := (Minus (Literal 2) (Literal 3)) in
         let ds := nil in
match run_height_ltr (compile (Source_program ae)) with
         | (Expressible_nat n, mh) =>
             run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
             mh = S (depth_right ae)
         | (Expressible_msg s, n) => s = s
         end).

(* End of running_and_compiling_ltr_guves_mh_S_depth_right_ae *)

Lemma about_height_and_depth_of_ae_ltr_eureka :
  forall (ae : arithmetic_expression)
         (ds : data_stack)
         (mh : nat),

Theorem running_and_compiling_ltr_gives_mh_S_depth_right_ae_aux :
  forall (ae : arithmetic_expression)
         (n mh : nat),
         run_height_ltr (Target_program (compile_aux ae)) = (Expressible_nat n, mh) ->
         mh = S (depth_right ae).
Proof.
  intros ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].
  - intros n' mh.
    rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_depth_right_Literal.
    unfold run_height_ltr.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_height_ltr_cons (PUSH n)).
    unfold decode_execute_height_ltr.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_height_ltr_nil (n :: nil)).
    rewrite -> (fold_unfold_list_length_cons nat n nil).
    rewrite -> (fold_unfold_list_length_nil nat).
    Search (Init.Nat.max _ _).
    rewrite -> (Nat.max_0_l 1).
    intro H_n_mh_inject.
    injection H_n_mh_inject as _ H_eq_mh.
    rewrite -> H_eq_mh.
    reflexivity.
  - intros n mh.
    rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> fold_unfold_depth_right_Plus.
    unfold run_height_ltr.
    case (compile_aux ae1) as [ | bci1' bci1s' ] eqn:C_ae1.
    + admit.
    + Check (about_fetch_decode_execute_loop_height_concatenation_ltr).
      case (fetch_decode_execute_loop_height_ltr (bci1' :: bci1s') nil) as [ds1 mh1 | s1] eqn:H_fdel_ae1.
      * Check (about_fetch_decode_execute_loop_height_concatenation_ltr (bci1' :: bci1s')
        (compile_aux ae2 ++ ADD :: nil) nil).
        destruct (about_fetch_decode_execute_loop_height_concatenation_ltr (bci1' :: bci1s')
        (compile_aux ae2 ++ ADD :: nil) nil) as [H_fdel_OK H_fdel_KO].
        Check (H_fdel_OK ds1 mh1 H_fdel_ae1).
        rewrite -> (H_fdel_OK ds1 mh1 H_fdel_ae1).
        unfold run_height_ltr in IHae2.
        Check (about_fetch_decode_execute_loop_height_concatenation_ltr).
        case (compile_aux ae2) as [ | bci2' bci2s' ] eqn:C_ae2.
        -- admit.
        -- case (fetch_decode_execute_loop_height_ltr (bci2' :: bci2s') ds1) as [ds2 mh2 | s2] eqn:H_fdel_ae2.
           ++ Check (about_fetch_decode_execute_loop_height_concatenation_ltr (bci2' :: bci2s')
           (ADD :: nil) ds1).
           destruct (about_fetch_decode_execute_loop_height_concatenation_ltr (bci2' :: bci2s')
           (ADD :: nil) ds1) as [H_fdel_OK2 _].
           Check (H_fdel_OK2 ds2 mh2 H_fdel_ae2).
           rewrite -> (H_fdel_OK2 ds2 mh2 H_fdel_ae2).
           unfold fetch_decode_execute_loop_height_ltr.
           unfold decode_execute_height_ltr.
Admitted.

(*
fetch_decode_execute_loop_height_ltr (compile_aux ae1) nil = OK_h ds1 mh1 ->
      fetch_decode_execute_loop_height_ltr (compile_aux ae1) nil =
                                               OK_h ds1 (list_length nat ds1)
*)

(*
fetch_decode_execute_loop_height_ltr (compile_aux ae1) ds = OK_h ds1 mh1 ->
fetch_decode_execute_loop_height_ltr (compile_aux ae1) ds =
                                         OK_h ds1 (list_length nat ds1)
 *)
(*
fetch_decode_execute_loop_height_ltr (compile_aux ae1) ds = OK_h ds mh1 ->
fetch_decode_execute_loop_height_ltr (compile_aux ae1) ds =
                                         OK_h ds1 (list_length nat ds)
 *)

Admitted.

Theorem running_and_compiling_ltr_gives_mh_S_depth_right_ae :
  forall (ae : arithmetic_expression)
         (n mh : nat),
    run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
    mh = S (depth_right ae).
Proof.
  intros ae n mh.
  unfold compile.
  exact (running_and_compiling_ltr_guves_mh_S_depth_right_ae_aux ae n mh).

(* Computes for the theorem below:

Compute (
      let ae := (Literal 1) in
      let h := 1 in
      let n := 1 in
      run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
      S (depth ae) = h).
Compute (
      let ae := (Plus (Plus (Literal 1)(Literal 2))(Literal 3)) in
      let h := 2 in
      let n := 6 in
      compile_aux ae = nil ->
      run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
      S (depth ae) = h). (* Wrong case *)
Compute (
    let ae := (Plus
                 (Plus
                    (Plus
                       (Literal 1)
                       (Literal 2))
                       (Literal 3))
                       (Literal 4)) in
      let h := 2 in
      let n := 10 in
      run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
      S (depth ae) = h). (* Wrong case *)
Compute (
      let ae := (Plus (Minus (Literal 2) (Literal 1))(Literal 2)) in
      let h := 2 in
      let n := 3 in
      run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
      S (depth ae) = h). (* Take care here *)
Compute (
      let ae := (Plus (Literal 1) (Plus (Literal 2) (Literal 3))) in
      let h := 3 in
      let n := 5 in
      run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
      S (depth ae) = h).
Compute (
      let ae := (Plus (Literal 1) (Plus (Literal 2) (Plus (Literal 3) (Literal 4)))) in
      let h := 4 in
      let n := 10 in
      run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
      S (depth ae) = h).
Compute (
      let ae := (Plus (Literal 2) (Plus (Plus (Literal 3) (Literal 2)) (Literal 1))) in
      let h := 3 in
      let n := 8 in
      run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
      S (depth ae) = h). (* Wrong case *)
 *)

Compute (let ae := Plus (Plus (Plus (Literal 1) (Literal 2)) (Literal 3))(Literal 4) in
         let ds := nil in
         fetch_decode_execute_loop_height_ltr (compile_aux (super_refactor_right ae)) ds).

Compute (let ae := Plus (Plus (Plus (Literal 1) (Literal 2)) (Literal 3))(Literal 4) in
         S (depth_right (super_refactor_right ae))).

Compute (let ae := Plus (Literal 1) (Minus (Literal 20) (Plus (Literal 3)(Literal 4))) in
         let ds := nil in
         fetch_decode_execute_loop_height_ltr (compile_aux (super_refactor_right ae)) ds).

Compute (let ae := Plus (Literal 1) (Minus (Literal 20) (Plus (Literal 3)(Literal 4))) in
         S (depth_right (super_refactor_right ae))).

Check (run_height_ltr).
Compute (run_height_ltr (compile (Source_program (Literal 1))) = (Expressible_nat 1, 1)).
Check (fetch_decode_execute_loop_height_ltr (compile_aux (Literal 1)) nil).

Theorem about_runnning :
  forall (ae : arithmetic_expression)
         (n mh : nat),
    run_height_ltr (compile (Source_program ae)) = (Expressible_nat n, mh) ->
    mh = S (depth_left ae).

Lemma about_height_and_depth_of_ae_eureka :
  forall (ae : arithmetic_expression)
         (ds : data_stack)
         (mh : nat),
    (forall n' : nat,
        evaluate ae = Expressible_nat n' ->
        fetch_decode_execute_loop_height (compile_aux ae) ds mh (list_length nat ds) =
          OK_h (n' :: ds) (max mh (S (depth ae))) (Some (S (depth ae))))
    /\
    (forall s : string,
        evaluate ae = Expressible_msg s ->
        fetch_decode_execute_loop_height (compile_aux ae) ds mh (list_length nat ds) =
          KO_h s).
Proof.
  intros ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intros ds mh.
  split.
  - intros n' H_n.
    rewrite ->  fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_cons.
    unfold decode_execute_height.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_nil.
    rewrite -> fold_unfold_evaluate_Literal in H_n.
    injection H_n as H_eq_n_n'.
    rewrite -> H_eq_n_n'.
    rewrite -> fold_unfold_depth_Literal.
Admitted.

Theorem about_height_and_depth_of_ae_aux :
  forall (ae : arithmetic_expression)
         (h n : nat),
    run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
    S (depth ae) = h.
Proof.
  intros ae h n H_run.
  unfold run_height in H_run.
  destruct (about_height_and_depth_of_ae_eureka ae nil 0) as [H_OK H_KO].
  destruct (evaluate ae) as [n' | s] eqn:Eval_ae.
  - specialize (H_OK n' eq_refl).
    rewrite -> fold_unfold_list_length_nil in H_OK.
    rewrite H_OK in H_run.
    injection H_run as _ H_h.
    rewrite H_h.
    reflexivity.
  - specialize (H_KO s eq_refl).
    rewrite -> fold_unfold_list_length_nil in H_KO.
    rewrite H_KO in H_run.
    discriminate H_run.
Qed.

Theorem about_height_and_depth_of_ae :
  forall (ae : arithmetic_expression)
         (h n : nat),
    run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
    S (depth ae) = h.
Proof.
  intros ae h n'.
  unfold compile.
  exact (about_height_and_depth_of_ae_aux ae h n').
Qed.

Theorem compiling_and_running_super_refacored_left_gives_S_depth_right :
  forall (ae : arithmetic_expression)
         (n h: nat),
    run_height (Target_program (compile_aux (super_refactor_left ae))) =
      (Expressible_nat n, h) ->
    S (depth_right (super_refactor_left ae)) = h.
Compute (let ae := (Literal 1) in
         let h := 1 in
         let n := 1 in
         run_height (Target_program (compile_aux (super_refactor_left ae))) =
           (Expressible_nat n, h) ->
         S (depth_right (super_refactor_left ae)) = h).
Compute (let ae := (Plus (Plus (Literal 1) (Literal 2))
                      (Plus (Literal 3) (Literal 4))) in
         let h := 2 in
         let n := 10 in
         run_height (Target_program (compile_aux (super_refactor_left ae))) =
           (Expressible_nat n, h) ->
         S (depth_right (super_refactor_left ae)) = h).
Compute (let ae := (Plus
                      (Plus
                         (Plus
                            (Literal 1)
                            (Literal 2))
                         (Literal 3))
                      (Literal 4)) in
         let h := 2 in
         let n := 10 in
         run_height (Target_program (compile_aux (super_refactor_left ae))) =
           (Expressible_nat n, h) ->
         S (depth_right (super_refactor_left ae)) = h).
Compute (let ae := (Minus
                      (Minus
                         (Minus
                            (Literal 10)
                            (Literal 5))
                         (Literal 2))
                      (Literal 1)) in
         let h := 2 in
         let n := 2 in
         run_height (Target_program (compile_aux (super_refactor_left ae))) =
           (Expressible_nat n, h) ->
         S (depth_right (super_refactor_left ae)) = h).
Compute (let ae := (Plus (Literal 1)
                      (Plus (Literal 2)
                         (Plus (Literal 3) (Literal 4)))) in
         let h := 2 in
         let n := 10 in
         run_height (Target_program (compile_aux (super_refactor_left ae))) =
           (Expressible_nat n, h) ->
             S (depth_right (super_refactor_left ae)) = h).
Compute (let ae := (Minus (Literal 10)
                      (Minus (Literal 5)
                         (Minus (Literal 2) (Literal 1)))) in
         let h := 4 in
         let n := 6 in
         run_height (Target_program (compile_aux (super_refactor_left ae))) =
           (Expressible_nat n, h) ->
         S (depth_right (super_refactor_left ae)) = h).
Proof.
Admitted.

Lemma about_compiling_and_running_ltr_gives_S_depth_right :
  forall (ae : arithmetic_expression)
         (n h: nat),
    run_height (Target_program (compile_aux ae)) = (Expressible_nat n, h) ->
    S (depth_right ae) = h.
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].
  (*case ae as [ n | ae1 ae2 | ae1 ae2 ].*)
  - intros n' h.
    intro H_run.
    rewrite -> fold_unfold_depth_right_Literal.
    rewrite -> fold_unfold_compile_aux_Literal in H_run.
    unfold run_height in H_run.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_cons in H_run.
    unfold decode_execute_height in H_run.
    rewrite -> fold_unfold_fetch_decode_execute_loop_height_nil in H_run.
    injection H_run as _ H_eq_1.
    exact H_eq_1.
  - intros n' h.
    rewrite -> fold_unfold_compile_aux_Plus.
    unfold run_height.
    rewrite -> fetch_decode_execute_loop_concatenation_height.
    unfold run_height in IHae1, IHae2.
    case (compile_aux ae1) as [ | bci1' bci1s' ].
    + rewrite -> fold_unfold_fetch_decode_execute_loop_height_nil.
      case (compile_aux ae2) as [ | bci2' bci2s' ].
      * rewrite -> fold_unfold_list_append_nil.
        rewrite -> fold_unfold_fetch_decode_execute_loop_height_cons.
        unfold decode_execute_height.
        intro H_absurd.
        injection H_absurd as H_absurd _.
        discriminate H_absurd.
      * rewrite -> fold_unfold_list_append_cons.
        rewrite -> fold_unfold_fetch_decode_execute_loop_height_cons.
        unfold decode_execute_height.
        case bci2' as [ n2' | | ] eqn:C_bci2'.
        -- rewrite -> fetch_decode_execute_loop_concatenation_height.
           unfold fetch_decode_execute_loop_height at 1.
           unfold decode_execute_height.
Admitted.

Theorem compiling_and_running_ltr_gives_S_depth_right :
  forall (ae : arithmetic_expression)
         (n h: nat),
    run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
    h = S (depth_right ae).
Compute (let ae := (Literal 1) in
         let h := 1 in
         let n := 1 in
         run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
         h = S (depth_right ae)).

Compute (let ae := (Plus (Plus (Literal 1) (Literal 2))
                      (Plus (Literal 3) (Literal 4))) in
         let h := 3 in
         let n := 10 in
         run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
         h = S (depth_right ae)).

Compute (let ae := (Plus
                      (Plus
                         (Plus
                            (Literal 1)
                            (Literal 2))
                         (Literal 3))
                      (Literal 4)) in
         let h := 2 in
         let n := 10 in
         run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
         h = S (depth_right ae)).

Compute (let ae := (Minus
                      (Minus
                         (Minus
                            (Literal 10)
                            (Literal 5))
                         (Literal 2))
                      (Literal 1)) in
         let h := 2 in
         let n := 2 in
         run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
         h = S (depth_right ae)).

Compute (let ae := (Plus (Literal 1)
                      (Plus (Literal 2)
                         (Plus (Literal 3) (Literal 4)))) in
         let h := 4 in
         let n := 10 in
         run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
         h = S (depth_right ae)).

Compute (let ae := (Minus (Literal 10)
                      (Minus (Literal 5)
                         (Minus (Literal 2) (Literal 1)))) in
         let h := 4 in
         let n := 6 in
         run_height (compile (Source_program ae)) = (Expressible_nat n, h) ->
         h = S (depth_right ae)).
Proof.
Admitted.

(* end of week3_stack_height.v *)
