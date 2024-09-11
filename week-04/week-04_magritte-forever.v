(* week-04_magritte-forever.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Inspired by Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 05 Sep 2024 *)

(* student name: Kim Young Il
   e-mail address: youngil.kim@u.yale-nus.edu.sg
   student ID number: A0207809Y
 *)

(* student name: Vibilan Jayanth
   e-mail address: vibilan@u.yale-nus.edu.sg
   student ID number: A0242417L
 *)

(* student name: Alan Matthew Anggara
   e-mail address: alan.matthew@u.yale-nus.edu.sg
   student ID number: A0242417L
 *)

(* Start of Paraphernalia *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
      PUSH n :: nil
  | Plus ae1 ae2 =>
      (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
      (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)
  end.

Lemma fold_unfold_compile_aux_Literal :
  forall n : nat,
    compile_aux (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Plus ae1 ae2) =
      (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.
  
Lemma fold_unfold_compile_aux_Minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Minus ae1 ae2) =
      (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
      Target_program (compile_aux ae)
  end.

(* End of Paraphernalia *)

(* Start of Magritte Paraphernalia *)

Definition Magritte_expressible_value := arithmetic_expression.

Definition Magritte_data_stack := list Magritte_expressible_value .

(* 1. Implement this Magritte target interpreter. *)

Inductive Magritte_result_of_decoding_and_execution : Type :=
  OK : Magritte_data_stack -> Magritte_result_of_decoding_and_execution.

Fixpoint Magritte_evaluate (ae : Magritte_expressible_value ) : Magritte_expressible_value :=
  match ae with
  | Literal n =>
      Literal n
  | Plus ae1 ae2 =>
      Plus (Magritte_evaluate ae1) (Magritte_evaluate ae2)
  | Minus ae1 ae2 =>
      Minus (Magritte_evaluate ae1) (Magritte_evaluate ae2)
  end.

Definition Magritte_decode_execute
  (bci : byte_code_instruction)
  (ds : Magritte_data_stack) :
  Magritte_result_of_decoding_and_execution :=
  match bci with
  | PUSH n =>
      OK (Literal n :: ds)
  | ADD =>
      match ds with
      | nil =>
          OK nil
      | ae2 :: ds' =>
          match ds' with
          | nil =>
              OK nil
          | ae1 :: ds'' =>
              OK (Plus ae1 ae2 :: ds'')
          end
      end
  | SUB =>
      match ds with
      | nil =>
          OK nil
      | ae2 :: ds' =>
          match ds' with
          | nil =>
              OK nil
          | ae1 :: ds'' =>
              OK (Minus ae1 ae2 :: ds'')
          end
      end
  end.

Lemma fold_unfold_Magritte_evaluate_Literal :
  forall n : nat,
    Magritte_evaluate (Literal n) = Literal n.
Proof.
  fold_unfold_tactic Magritte_evaluate.
Qed.

Lemma fold_unfold_Magritte_evaluate_Plus :
  forall ae1 ae2 : Magritte_expressible_value ,
    Magritte_evaluate (Plus ae1 ae2) =
      Plus (Magritte_evaluate ae1) (Magritte_evaluate ae2).
Proof.
  fold_unfold_tactic Magritte_evaluate.
Qed.

Lemma fold_unfold_Magritte_evaluate_Minus :
  forall ae1 ae2 : Magritte_expressible_value ,
    Magritte_evaluate (Minus ae1 ae2) =
      Minus (Magritte_evaluate ae1) (Magritte_evaluate ae2).
Proof.
  fold_unfold_tactic Magritte_evaluate.
Qed.

(* Look for the aha *)
Theorem about_Magritte_evaluate :
  forall ae : Magritte_expressible_value,
    Magritte_evaluate ae = ae.
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 | ae2 IHae2 ].
  - exact (fold_unfold_Magritte_evaluate_Literal n).
  - rewrite -> fold_unfold_Magritte_evaluate_Plus.
    rewrite -> IHae1, IHae2.
    reflexivity.
  - rewrite -> fold_unfold_Magritte_evaluate_Minus.
    rewrite -> IHae1, IHae2.
    reflexivity.
Qed.

Fixpoint Magritte_fetch_decode_execute_loop
  (bcis : list byte_code_instruction)
  (ds : Magritte_data_stack) :
  Magritte_result_of_decoding_and_execution :=
  match bcis with
  | nil =>
      OK ds
  | bci :: bcis' =>
      match Magritte_decode_execute bci ds with
      | OK ds' =>
          Magritte_fetch_decode_execute_loop bcis' ds'
      end
  end.

Lemma fold_unfold_Magritte_fetch_decode_execute_loop_nil :
  forall (ds : Magritte_data_stack),
    Magritte_fetch_decode_execute_loop nil ds = OK ds.
Proof.
  fold_unfold_tactic Magritte_fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_Magritte_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : Magritte_data_stack),
    Magritte_fetch_decode_execute_loop (bci :: bcis') ds =
      match Magritte_decode_execute bci ds with
      | OK ds' =>
          Magritte_fetch_decode_execute_loop bcis' ds'
      end. 
Proof.
  fold_unfold_tactic Magritte_fetch_decode_execute_loop.
Qed.

Definition Magritte_run (t : target_program) : option source_program :=
  match t with
    Target_program bcis =>
      match Magritte_fetch_decode_execute_loop bcis nil with
        OK nil => None
      | OK (ae :: nil) => Some (Source_program ae)
      | OK (ae :: ae'' :: ds'') => None
      end
  end.

(*
  2. Likewise, implement a Magritte source interpreter
  so that its result is not a natural number or an error message,
  it is the syntactic representation of a natural number.
 *)

Definition Magritte_interpret (sp : source_program) : source_program :=
  match sp with
    Source_program ae =>
      Source_program (Magritte_evaluate ae)
  end.

Theorem about_Magritte_interpret :
  forall sp : source_program,
    Magritte_interpret sp = sp.
Proof.
  intros [ae].
  unfold Magritte_interpret.
  rewrite -> about_Magritte_evaluate.
  reflexivity.
Qed.

(* Start proving *)

(* Tests *)

Definition test_ae_Literal := (Literal 0).

Definition test_ae_Plus_left := (Plus
                                   (Plus
                                      (Plus
                                         (Literal 0)
                                         (Literal 1))
                                      (Literal 2))
                                   (Literal 3)).
Definition test_ae_Plus_right := (Plus
                                   (Literal 0)
                                   (Plus
                                      (Literal 1)
                                      (Plus
                                         (Literal 2)
                                         (Literal 3)))).
Definition test_ae_Plus_balanced := (Plus
                                       (Plus
                                          (Literal 0)
                                          (Literal 1))
                                       (Plus
                                          (Literal 2)
                                          (Literal 3))).
Definition test_ae_Minus_left := (Minus
                                   (Minus
                                      (Minus
                                         (Literal 20)
                                         (Literal 10))
                                      (Literal 5))
                                   (Literal 1)).
Definition test_ae_Minus_right := (Minus
                                   (Literal 20)
                                   (Minus
                                      (Literal 10)
                                      (Minus
                                         (Literal 5)
                                         (Literal 1)))).
Definition test_ae_Minus_balanced := (Minus
                                       (Minus
                                          (Literal 20)
                                          (Literal 10))
                                       (Minus
                                          (Literal 5)
                                          (Literal 1))).
Definition test_ae_Minus_error := (Minus (Literal 0) (Literal 1)).

Theorem about_Magritte_fetch_decode_execute_loop_concat :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds : Magritte_data_stack)
         (ds' : Magritte_data_stack),
             Magritte_fetch_decode_execute_loop bci1s ds = OK ds' ->
             Magritte_fetch_decode_execute_loop (bci1s ++ bci2s) ds =
               Magritte_fetch_decode_execute_loop bci2s ds'.
Proof.
  intro bci1s.
  induction bci1s as [ | [n | | ] bci1s' IHbci1s']; intros bci2s ds.
  - intros ds' H_fdel_nil_OK.
    unfold Magritte_fetch_decode_execute_loop in H_fdel_nil_OK.
    injection H_fdel_nil_OK as H_eq_ds_ds'.
    rewrite -> H_eq_ds_ds'.
    rewrite -> app_nil_l.
    reflexivity.
  - intros ds' H_fdel_PUSH.
    rewrite <- app_comm_cons.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons in H_fdel_PUSH.
    unfold Magritte_decode_execute in H_fdel_PUSH.
    unfold Magritte_decode_execute.
    Check (IHbci1s' bci2s (Literal n :: ds) ds' H_fdel_PUSH).
    rewrite -> (IHbci1s' bci2s (Literal n :: ds) ds' H_fdel_PUSH).
    reflexivity.
  - intros ds' H_fdel_ADD.
    rewrite <- app_comm_cons.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons in H_fdel_ADD.
    unfold Magritte_decode_execute in H_fdel_ADD.
    unfold Magritte_decode_execute.
    case ds as [ | ae1 ds1'].
    { Check (IHbci1s' bci2s nil ds' H_fdel_ADD).
      exact (IHbci1s' bci2s nil ds' H_fdel_ADD).
    }
    case ds1' as [ | ae2 ds2'].
    { Check (IHbci1s' bci2s nil ds' H_fdel_ADD).
      exact (IHbci1s' bci2s nil ds' H_fdel_ADD).
    }
    Check (IHbci1s' bci2s (Plus ae2 ae1 :: ds2') ds' H_fdel_ADD).
    exact (IHbci1s' bci2s (Plus ae2 ae1 :: ds2') ds' H_fdel_ADD).
  - intros ds' H_fdel_SUB. (* Mutatis Mutandis, now that it is without bugs *)
    rewrite <- app_comm_cons.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons in H_fdel_SUB.
    unfold Magritte_decode_execute in H_fdel_SUB.
    unfold Magritte_decode_execute.
    case ds as [ | ae1 ds1'].
    { Check (IHbci1s' bci2s nil ds' H_fdel_SUB).
      exact (IHbci1s' bci2s nil ds' H_fdel_SUB).
    }
    case ds1' as [ | ae2 ds2'].
    { Check (IHbci1s' bci2s nil ds' H_fdel_SUB).
      exact (IHbci1s' bci2s nil ds' H_fdel_SUB).
    }
    Check (IHbci1s' bci2s (Minus ae2 ae1 :: ds2') ds' H_fdel_SUB).
    exact (IHbci1s' bci2s (Minus ae2 ae1 :: ds2') ds' H_fdel_SUB).
Qed.

Lemma about_Magritte_fetch_decode_execute_loop :
  forall (ae : Magritte_expressible_value )
         (ds : Magritte_data_stack),
  exists ae' :Magritte_expressible_value ,
    Magritte_fetch_decode_execute_loop (compile_aux ae) ds = OK (ae' :: ds).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds.
  - rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    unfold Magritte_decode_execute.   
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_nil.
    exists (Literal n).
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Plus.
    Check about_Magritte_fetch_decode_execute_loop_concat.
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae1)
             (compile_aux ae2 ++ ADD :: nil)
             ds).
    destruct (IHae1 ds) as [ae1' H_ae1'].
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae1)
                  (compile_aux ae2 ++ ADD :: nil)
                  ds
                  (ae1' :: ds)
                  H_ae1').
    destruct (IHae2 (ae1' :: ds)) as [ae2' H_ae2'].
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae2)
             (ADD :: nil)
             (ae1' :: ds)
             (ae2' :: ae1' :: ds)
             H_ae2').
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae2)
                  (ADD :: nil)
                  (ae1' :: ds)
                  (ae2' :: ae1' :: ds)
                  H_ae2').
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    unfold Magritte_decode_execute.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_nil.
    exists (Plus ae1' ae2').
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Minus.
    Check about_Magritte_fetch_decode_execute_loop_concat.
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae1)
             (compile_aux ae2 ++ SUB :: nil)
             ds).
    destruct (IHae1 ds) as [ae1' H_ae1'].
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae1)
                  (compile_aux ae2 ++ SUB :: nil)
                  ds
                  (ae1' :: ds)
                  H_ae1').
    destruct (IHae2 (ae1' :: ds)) as [ae2' H_ae2'].
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae2)
             (SUB :: nil)
             (ae1' :: ds)
             (ae2' :: ae1' :: ds)
             H_ae2').
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae2)
                  (SUB :: nil)
                  (ae1' :: ds)
                  (ae2' :: ae1' :: ds)
                  H_ae2').
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    unfold Magritte_decode_execute.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_nil.
    exists (Minus ae1' ae2').
    reflexivity.
Qed.

(* Look for the aha *)
Lemma about_Magritte_run_aux :
  forall (ae : Magritte_expressible_value )
         (ds : Magritte_data_stack),
    Magritte_fetch_decode_execute_loop (compile_aux ae) ds =
      OK (ae :: ds).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds.
  - rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    unfold Magritte_decode_execute.   
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Plus.
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae1)
             (compile_aux ae2 ++ ADD :: nil)
             ds
             (ae1 :: ds)
             (IHae1 ds)).
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae1)
                  (compile_aux ae2 ++ ADD :: nil)
                  ds
                  (ae1 :: ds)
                  (IHae1 ds)).
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae2)
             (ADD :: nil)
             (ae1 :: ds)
             (ae2 :: ae1 :: ds)
             (IHae2 (ae1 :: ds))).
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae2)
                  (ADD :: nil)
                  (ae1 :: ds)
                  (ae2 :: ae1 :: ds)
                  (IHae2 (ae1 :: ds))).
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    unfold Magritte_decode_execute.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Minus.
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae1)
             (compile_aux ae2 ++ SUB :: nil)
             ds
             (ae1 :: ds)
             (IHae1 ds)).
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae1)
                  (compile_aux ae2 ++ SUB :: nil)
                  ds
                  (ae1 :: ds)
                  (IHae1 ds)).
    Check (about_Magritte_fetch_decode_execute_loop_concat
             (compile_aux ae2)
             (SUB :: nil)
             (ae1 :: ds)
             (ae2 :: ae1 :: ds)
             (IHae2 (ae1 :: ds))).
    rewrite -> (about_Magritte_fetch_decode_execute_loop_concat
                  (compile_aux ae2)
                  (SUB :: nil)
                  (ae1 :: ds)
                  (ae2 :: ae1 :: ds)
                  (IHae2 (ae1 :: ds))).
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_cons.
    unfold Magritte_decode_execute.
    rewrite -> fold_unfold_Magritte_fetch_decode_execute_loop_nil.
    reflexivity.
Qed.  

Corollary about_Magritte_run :
  forall (sp : source_program)
         (ae : Magritte_expressible_value ),
  exists ae' : Magritte_expressible_value ,
    Magritte_run (compile (Source_program ae)) = Some (Source_program ae').
Proof.
  intros [ae] sp.
  unfold Magritte_run, compile.
  Check (about_Magritte_run_aux sp nil).
  rewrite -> (about_Magritte_run_aux sp nil).
  exists sp.
  reflexivity.
Qed.

(*
  3. A commuting diagram also holds about Magritte_interpret,
  compile, and Magritte_run. State and prove the Magritte
  analogue of the capstone theorem.
 *)

Theorem the_Magritte_commuting_diagram :
  forall (ae : arithmetic_expression)
         (ae' : Magritte_expressible_value),
    Magritte_run (compile (Source_program ae)) = Some (Source_program ae') <->
    Magritte_interpret (Source_program ae) = Source_program ae'.
Proof.
  intros ae ae'.
  unfold Magritte_run, compile.    
  split.
  - rewrite -> (about_Magritte_run_aux ae nil).
    intro H_injection.
    injection H_injection as H_eq_ae_ae'.
    rewrite -> H_eq_ae_ae'.
    rewrite -> about_Magritte_interpret.
    reflexivity.
  - rewrite -> (about_Magritte_run_aux ae nil).
    intro H_injection.
    rewrite -> about_Magritte_interpret in H_injection.
    injection H_injection as H_eq_ae_ae'.    
    rewrite -> H_eq_ae_ae'.
    reflexivity.
Qed.
