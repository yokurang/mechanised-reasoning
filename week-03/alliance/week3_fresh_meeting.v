(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* Type Definitions*)

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

Definition data_stack := list nat.

Inductive result_of_decoding_and_execution : Type :=
  OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Inductive result_of_fetch_decode_execute_loop : Type :=
  OK' : data_stack -> nat -> result_of_fetch_decode_execute_loop
| KO' : string -> result_of_fetch_decode_execute_loop.


(* ********** *)

(* Helper functions *)

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


(* List length and its fold unfold lemmas *)

Fixpoint list_length (T: Type) (ls: list T): nat :=
  match ls with
  | nil => 0
  | l :: ls' => 1 + (list_length T ls')
  end.

Lemma fold_unfold_list_length_nil:
  forall (V : Type),
    list_length V nil = 0.
Proof.
  fold_unfold_tactic list_length.
Qed.

Lemma fold_unfold_list_length_cons:
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_length V (v :: vs') = 1 + (list_length V vs').
Proof.
  fold_unfold_tactic list_length.
Qed.

(* Fold unfold lemmas for list append *)

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

(* Equality functions *)

Definition eqb_string (s1 s2 : string) : bool :=
  match String.string_dec s1 s2 with
  | left _ =>
      true
  | right _ =>
      false
  end.


Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
      match v2s with
      | nil =>
          true
      | _ :: _ =>
          false
      end
  | v1 :: v1s' =>
      match v2s with
      | nil =>
          false
      | v2 :: v2s' =>
          (eqb_V v1 v2) && (eqb_list V eqb_V v1s' v2s')
      end
  end.

Definition eqb_pair (A : Type)
  (eqb_A : A -> A -> bool)
  (B : Type)
  (eqb_B : B -> B -> bool)
  (p1 p2 : A * B) : bool :=
  match p1 with
  |(a1, b1) =>
     match p2 with
     |(a2 , b2) =>
        (eqb_A a1 a2) && (eqb_B b1 b2)
     end
  end.

Definition eqb_expressible_value (ev1 ev2: expressible_value) : bool :=
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

Fixpoint eqb_ae (ae1 ae2: arithmetic_expression) : bool :=
  match ae1 with
  | Literal n1 =>
      match ae2 with
        | Literal n2 =>
          Nat.eqb n1 n2
        | Plus _ _ =>
            false
        | Minus _ _ =>
            false
      end
  | Plus ae1_1 ae1_2 =>
      match ae2 with
      | Literal _ =>
          false
      | Plus ae2_1 ae2_2 =>
          (eqb_ae ae1_1 ae2_1) && (eqb_ae ae1_2 ae2_2)
      | Minus ae2_1 ae2_2 =>
          (eqb_ae ae1_1 ae2_1) && (eqb_ae ae1_2 ae2_2)
      end
  | Minus ae1_1 ae1_2 =>
      match ae2 with
      | Literal _ =>
          false
      | Plus ae2_1 ae2_2 =>
          (eqb_ae ae1_1 ae2_1) && (eqb_ae ae1_2 ae2_2)
      | Minus ae2_1 ae2_2 =>
          (eqb_ae ae1_1 ae2_1) && (eqb_ae ae1_2 ae2_2)
      end
  end.

Definition eqb_pair_of_expressible_value_and_nat (p1 p2 : (expressible_value * nat)) : bool :=
  eqb_pair expressible_value eqb_expressible_value nat Nat.eqb p1 p2.


Definition eqb_bci (bci1 bci2 : byte_code_instruction) : bool :=
  match bci1 with
  | PUSH n1 =>
      match bci2 with
      | PUSH n2 =>
          n1 =? n2
      | ADD =>
          false
      | SUB =>
          false
      end
  | ADD =>
      match bci2 with
      | PUSH _ =>
          false
      | ADD =>
          true
      | SUB =>
          false
      end
  | SUB =>
      match bci2 with
      | PUSH _ =>
          false
      | ADD =>
          false
      | SUB =>
          true
      end
  end.

(* ********** *)

(* evaluate ltr and its fold unfold lemmas *)

Fixpoint evaluate_ltr (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate_ltr ae1  with
      | Expressible_nat n1 =>
          match evaluate_ltr ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          end
      | Expressible_msg s1 =>
          Expressible_msg s1
      end
  | Minus ae1 ae2 =>
      match evaluate_ltr ae1 with
      | Expressible_nat n1 =>
          match evaluate_ltr ae2  with
          | Expressible_nat n2 =>
              match (n1 <? n2) with
              | true =>
                  Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  Expressible_nat (n1 - n2)
              end
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
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_ltr (Plus ae1 ae2) =
      match evaluate_ltr ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate_ltr ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          end
      end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

Lemma fold_unfold_evaluate_ltr_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_ltr (Minus ae1 ae2) =
      match evaluate_ltr ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate_ltr ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              match (n1 <? n2) with
              | true =>
                  Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  Expressible_nat (n1 - n2)
              end
          end
      end.
Proof.
  fold_unfold_tactic evaluate_ltr.
Qed.

(* ********** *)

(* interpret ltr *)

Definition interpret_ltr (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
      evaluate_ltr ae
  end.


(* ********** *)

(* decode execute ltr *)

Definition decode_execute_ltr (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
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
              OK (n1 + n2 :: ds'')
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
              then KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else OK (n1 - n2 :: ds'')
          end
      end
  end.

(* ********** *)

(* fdel ltr and its fold unfold lemmas*)

Fixpoint fetch_decode_execute_loop_ltr (bcis : list byte_code_instruction) (ds : data_stack) : result_of_fetch_decode_execute_loop :=
  match bcis with
  | nil =>
      OK' ds (list_length nat ds)
  | bci :: bcis' =>
      match decode_execute_ltr bci ds with
      | OK ds' =>
          match fetch_decode_execute_loop_ltr bcis' ds' with
          | OK' ds'' mh'' =>
              OK' ds'' (Nat.max (list_length nat ds) (Nat.max (list_length nat ds') mh''))
          | KO' s =>
              KO' s
          end
      | KO s =>
          KO' s
      end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_ltr_nil :
  forall (ds : data_stack),
    fetch_decode_execute_loop_ltr nil ds = OK' ds (list_length nat ds).
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_ltr.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_ltr_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop_ltr (bci :: bcis') ds =
      match decode_execute_ltr bci ds with
      | OK ds' =>
          match fetch_decode_execute_loop_ltr bcis' ds' with
          | OK' ds'' mh'' =>
              OK' ds'' (Nat.max (list_length nat ds) (Nat.max (list_length nat ds') mh''))
          | KO' s =>
              KO' s
          end
      | KO s =>
          KO' s
      end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_ltr.
Qed.

(* ********** *)

(* compile ltr, compile ltr aux, and its fold unfold lemmas *)

Fixpoint compile_ltr_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
      PUSH n :: nil
  | Plus ae1 ae2 =>
      (compile_ltr_aux ae1) ++ (compile_ltr_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
      (compile_ltr_aux ae1) ++ (compile_ltr_aux ae2) ++ (SUB :: nil)
  end.

Lemma fold_unfold_compile_ltr_aux_Literal :
  forall n : nat,
    compile_ltr_aux (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Lemma fold_unfold_compile_ltr_aux_Plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_ltr_aux (Plus ae1 ae2) = (compile_ltr_aux ae1) ++ (compile_ltr_aux ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Lemma fold_unfold_compile_ltr_aux_Minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_ltr_aux (Minus ae1 ae2) = (compile_ltr_aux ae1) ++ (compile_ltr_aux ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_ltr_aux.
Qed.

Definition compile_ltr (source_program : source_program) : target_program :=
  match source_program with
  | Source_program ae =>
      Target_program (compile_ltr_aux ae)
  end.

(* ********** *)

(* run ltr *)

Definition run_ltr (target : target_program) : (expressible_value * nat) :=
  match target with
    | Target_program bcis =>
        match fetch_decode_execute_loop_ltr bcis nil with
        | OK' ds mh =>
            match ds with
            | nil =>
                (Expressible_msg "no result on the data stack", 0)
            | d :: nil =>
                (Expressible_nat d, mh)
            | d :: d' :: ds'' =>
                (Expressible_msg "too many results on the data stack", 0)
            end
        | KO' s =>
            (Expressible_msg s, 0)
        end
    end.


(* ********** *)

(* super refactor right, super refactor right aux, and their fold unfold lemmas*)

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

Lemma fold_unfold_super_refactor_right_Literal :
  forall n : nat,
    super_refactor_right (Literal n) = Literal n.
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_Plus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_right (Plus ae1 ae2) = super_refactor_right_aux ae1 (super_refactor_right ae2).
Proof.
  fold_unfold_tactic super_refactor_right.
Qed.

Lemma fold_unfold_super_refactor_right_Minus :
  forall ae1 ae2 : arithmetic_expression,
    super_refactor_right (Minus ae1 ae2) = Minus (super_refactor_right ae1) (super_refactor_right ae2).
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
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_right_aux (Plus ae1 ae2) a = super_refactor_right_aux ae1 (super_refactor_right_aux ae2 a).
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

Lemma fold_unfold_super_refactor_aux_Minus :
  forall (ae1 ae2 a : arithmetic_expression),
    super_refactor_right_aux (Minus ae1 ae2) a = Plus (Minus (super_refactor_right ae1) (super_refactor_right ae2)) a.
Proof.
  fold_unfold_tactic super_refactor_right_aux.
Qed.

(* ********** *)

(* Exercise 1 *)

(* Exploring the behaviour of super_refactor_right *)

Definition test_case1 : arithmetic_expression :=
  Plus (Plus (Literal 0)
             (Literal 1))
       (Plus (Literal 2)
             (Literal 3)).

Definition test_case2 : arithmetic_expression :=
  Plus (Plus (Literal 4)
             (Literal 5))
       (Plus (Literal 6)
             (Literal 7)).

Definition test_case3 : arithmetic_expression :=
  Minus (test_case2)
    (test_case1).

Definition test_case4 : arithmetic_expression :=
  Minus (test_case3)
        (Plus (test_case3)
              (test_case3)).

Compute eqb_ae
  (super_refactor_right test_case1)
  (Plus (Literal 0)
     (Plus (Literal 1)
        (Plus (Literal 2) (Literal 3)))).

Definition test_super_refactor_left (candidate : arithmetic_expression -> arithmetic_expression) : bool :=
  eqb_ae (candidate test_case1) (Plus (Plus (Plus (Literal 0)
                                                  (Literal 1))
                                            (Literal 2))
                                      (Literal 3))
  && eqb_ae (candidate test_case2) (Plus (Plus (Plus (Literal 4)
                                                     (Literal 5))
                                               (Literal 6))
                                         (Literal 7))
  && eqb_ae (candidate test_case3) (Minus (Plus (Plus (Plus (Literal 4)
                                                            (Literal 5))
                                                      (Literal 6))
                                                (Literal 7))
                                          (Plus (Plus (Plus (Literal 0)
                                                            (Literal 1))
                                                      (Literal 2))
                                                (Literal 3)))
  && eqb_ae (candidate test_case4) (Minus (Minus (Plus (Plus (Plus (Literal 4)
                                                                   (Literal 5))
                                                             (Literal 6))
                                                       (Literal 7))
                                                 (Plus (Plus (Plus (Literal 0)
                                                                   (Literal 1))
                                                             (Literal 2))
                                                       (Literal 3)))
                                          (Plus (Minus (Plus (Plus (Plus (Literal 4)
                                                                         (Literal 5))
                                                                   (Literal 6))
                                                             (Literal 7))
                                                       (Plus (Plus (Plus (Literal 0)
                                                                         (Literal 1))
                                                                   (Literal 2))
                                                             (Literal 3)))
                                                (Minus (Plus (Plus (Plus (Literal 4)
                                                                         (Literal 5))
                                                                   (Literal 6))
                                                             (Literal 7))
                                                       (Plus (Plus (Plus (Literal 0)
                                                                         (Literal 1))
                                                                   (Literal 2))
                                                             (Literal 3))))).

Fixpoint super_refactor_left (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
      Literal n
  | Plus ae1 ae2 =>
      super_refactor_left_aux (super_refactor_left ae1) ae2
  | Minus ae1 ae2 =>
      Minus (super_refactor_left ae1) (super_refactor_left ae2)
  end
with super_refactor_left_aux (a ae1 : arithmetic_expression) : arithmetic_expression :=
       match ae1 with
       | Literal n =>
           Plus a (Literal n)
       | Plus ae1 ae2 =>
           super_refactor_left_aux (super_refactor_left_aux a ae1) ae2
       | Minus ae1 ae2 =>
           Plus a (Minus (super_refactor_left ae1) (super_refactor_left ae2))
       end.

(* ********** *)

(* Exercise 2 *)

(* Reasoning about the depth of trees *)

(* depth function and its fold unfold lemmas *)

Definition test_depth (candidate : arithmetic_expression -> nat) : bool :=
  Nat.eqb (candidate (super_refactor_right test_case1)) 3
  && Nat.eqb (candidate (super_refactor_left test_case1)) 3
  && Nat.eqb (candidate (super_refactor_right test_case2)) 3
  && Nat.eqb (candidate (super_refactor_left test_case2)) 3
  && Nat.eqb (candidate (super_refactor_right test_case3)) 4
  && Nat.eqb (candidate (super_refactor_left test_case3)) 4
  && Nat.eqb (candidate (super_refactor_right test_case4)) 6
  && Nat.eqb (candidate (super_refactor_left test_case4)) 6.

Fixpoint depth (ae : arithmetic_expression) : nat :=
  match ae with
  | Literal n =>
      0
  | Plus ae1 ae2 =>
      Nat.max (S (depth ae1)) (S (depth ae2))
  | Minus ae1 ae2 =>
      Nat.max (S (depth ae1)) (S (depth ae2))
  end.

Lemma fold_unfold_depth_Literal:
  forall n: nat,
    depth (Literal n) = 0.
Proof.
  fold_unfold_tactic depth.
Qed.

Lemma fold_unfold_depth_Plus:
  forall ae1 ae2: arithmetic_expression,
    depth (Plus ae1 ae2) = Nat.max (S (depth ae1)) (S (depth ae2)).
Proof.
  fold_unfold_tactic depth.
Qed.

Lemma fold_unfold_depth_Minus:
  forall ae1 ae2: arithmetic_expression,
    depth (Minus ae1 ae2) = Nat.max (S (depth ae1)) (S (depth ae2)).
Proof.
  fold_unfold_tactic depth.
Qed.

Compute (test_depth depth).

(* depth right and its fold unfold lemmas *)

Definition test_depth_right (candidate : arithmetic_expression -> nat) : bool :=
  Nat.eqb (candidate (super_refactor_right test_case1)) 1
  && Nat.eqb (candidate (super_refactor_left test_case1)) 3
  && Nat.eqb (candidate (super_refactor_right test_case2)) 1
  && Nat.eqb (candidate (super_refactor_left test_case2)) 3
  && Nat.eqb (candidate (super_refactor_right test_case3)) 2
  && Nat.eqb (candidate (super_refactor_left test_case3)) 4
  && Nat.eqb (candidate (super_refactor_right test_case4)) 3
  && Nat.eqb (candidate (super_refactor_left test_case4)) 5.


Fixpoint depth_right (ae : arithmetic_expression) : nat :=
    match ae with
    | Literal _ =>
        0
    | Plus ae1 ae2 =>
        Nat.max (S (depth_right ae1)) (depth_right ae2)
    | Minus ae1 ae2 =>
        Nat.max (S (depth_right ae1)) (depth_right ae2)
    end.

Lemma fold_unfold_depth_right_Literal:
  forall n: nat,
    depth_right (Literal n) = 0.
Proof.
  fold_unfold_tactic depth_right.
Qed.

Lemma fold_unfold_depth_right_Plus:
  forall ae1 ae2: arithmetic_expression,
    depth_right (Plus ae1 ae2) =  Nat.max (S (depth_right ae1)) (depth_right ae2).
Proof.
  fold_unfold_tactic depth_right.
Qed.

Lemma fold_unfold_depth_right_Minus:
  forall ae1 ae2: arithmetic_expression,
    depth_right (Minus ae1 ae2) =  Nat.max (S (depth_right ae1)) (depth_right ae2).
Proof.
  fold_unfold_tactic depth_right.
Qed.

Compute (test_depth_right depth_right).

(* depth left and its fold unfold lemmas *)

Definition test_depth_left (candidate : arithmetic_expression -> nat) : bool :=
  Nat.eqb (candidate (super_refactor_right test_case1)) 3
  && Nat.eqb (candidate (super_refactor_left test_case1)) 1
  && Nat.eqb (candidate (super_refactor_right test_case2)) 3
  && Nat.eqb (candidate (super_refactor_left test_case2)) 1
  && Nat.eqb (candidate (super_refactor_right test_case3)) 4
  && Nat.eqb (candidate (super_refactor_left test_case3)) 2
  && Nat.eqb (candidate (super_refactor_right test_case4)) 6
  && Nat.eqb (candidate (super_refactor_left test_case4)) 4.

Fixpoint depth_left (ae : arithmetic_expression) : nat :=
    match ae with
    | Literal _ =>
        0
    | Plus ae1 ae2 =>
        Nat.max (depth_left ae1) (S (depth_left ae2))
    | Minus ae1 ae2 =>
        Nat.max (depth_left ae1) (S (depth_left ae2))
    end.

Lemma fold_unfold_depth_left_Literal:
  forall n: nat,
    depth_left (Literal n) = 0.
Proof.
  fold_unfold_tactic depth_left.
Qed.

Lemma fold_unfold_depth_left_Plus:
  forall ae1 ae2: arithmetic_expression,
    depth_left (Plus ae1 ae2) =  Nat.max (depth_left ae1) (S (depth_left ae2)).
Proof.
  fold_unfold_tactic depth_left.
Qed.

Lemma fold_unfold_depth_left_Minus:
  forall ae1 ae2: arithmetic_expression,
    depth_left (Minus ae1 ae2) =  Nat.max (depth_left ae1) (S (depth_left ae2)).
Proof.
  fold_unfold_tactic depth_left.
Qed.

Compute (test_depth_left depth_left).

(* Exercise 3 *)

(* On Compiling Right to Left *)

(* evaluate rtl and its fold unfold lemmas *)

Fixpoint evaluate_rtl (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate_rtl ae2  with
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_msg s1 =>
              Expressible_msg s1
          | Expressible_nat n1 =>
              Expressible_nat (n1 + n2)
          end
      | Expressible_msg s2 =>
          Expressible_msg s2
      end
  | Minus ae1 ae2 =>
      match evaluate_rtl ae2 with
      | Expressible_nat n2 =>
          match evaluate_rtl ae1  with
          | Expressible_nat n1 =>
              match (n1 <? n2) with
              | true =>
                  Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  Expressible_nat (n1 - n2)
              end
          | Expressible_msg s2 =>
              Expressible_msg s2
          end

      | Expressible_msg s1 =>
          Expressible_msg s1
      end
  end.

Lemma fold_unfold_evaluate_rtl_Literal :
  forall n : nat,
    evaluate_rtl (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_rtl.
Qed.

Lemma fold_unfold_evaluate_rtl_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_rtl (Plus ae1 ae2) =
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
      end.
Proof.
  fold_unfold_tactic evaluate_rtl.
Qed.

Lemma fold_unfold_evaluate_rtl_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_rtl (Minus ae1 ae2) =
      match evaluate_rtl ae2 with
      | Expressible_msg s2 =>
          Expressible_msg s2
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_msg s1 =>
              Expressible_msg s1
          | Expressible_nat n1 =>
              match (n1 <? n2) with
              | true =>
                  Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  Expressible_nat (n1 - n2)
              end
          end
      end.
Proof.
  fold_unfold_tactic evaluate_rtl.
Qed.

(* compile rtl, compile rtl aux and its fold unfold lemmas *)

Fixpoint compile_rtl_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
      PUSH n :: nil
  | Plus ae1 ae2 =>
      (compile_rtl_aux ae2) ++ (compile_rtl_aux ae1) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
      (compile_rtl_aux ae2) ++ (compile_rtl_aux ae1) ++ (SUB :: nil)
  end.

Definition compile_rtl (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
      Target_program (compile_rtl_aux ae)
  end.

Lemma fold_unfold_compile_rtl_aux_Literal :
  forall n : nat,
    compile_rtl_aux (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_rtl_aux.
Qed.

Lemma fold_unfold_compile_rtl_aux_Plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_rtl_aux (Plus ae1 ae2) = (compile_rtl_aux ae2) ++ (compile_rtl_aux ae1) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_rtl_aux.
Qed.

Lemma fold_unfold_compile_rtl_aux_Minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_rtl_aux (Minus ae1 ae2) = (compile_rtl_aux ae2) ++ (compile_rtl_aux ae1) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_rtl_aux.
Qed.

(* decode execute rtl *)

Definition decode_execute_rtl (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
  | PUSH n =>
      OK (n :: ds)
  | ADD =>
      match ds with
      | nil =>
          KO "ADD: stack underflow"
      | n1 :: ds' =>
          match ds' with
          | nil =>
              KO "ADD: stack underflow"
          | n2 :: ds'' =>
              OK (n1 + n2 :: ds'')
          end
      end
  | SUB =>
      match ds with
      | nil =>
          KO "SUB: stack underflow"
      | n1 :: ds' =>
          match ds' with
          | nil =>
              KO "SUB: stack underflow"
          | n2 :: ds'' =>
              if n1 <? n2
              then KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else OK (n1 - n2 :: ds'')
          end
      end
  end.

(* fetch decode execute rtl and its fold unfold lemmas*)

Fixpoint fetch_decode_execute_loop_rtl (bcis : list byte_code_instruction) (ds : data_stack) : result_of_fetch_decode_execute_loop :=
  match bcis with
  | nil =>
      OK' ds (list_length nat ds)
  | bci :: bcis' =>
      match decode_execute_rtl bci ds with
      | OK ds' =>
          match fetch_decode_execute_loop_rtl bcis' ds' with
          | KO' s =>
              KO' s
          | OK' ds'' mh'' =>
              OK' ds'' (Nat.max (list_length nat ds) (Nat.max (list_length nat ds') mh''))
          end
      | KO s =>
          KO' s
      end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_rtl_nil :
  forall (ds : data_stack),
    fetch_decode_execute_loop_rtl nil ds = OK' ds (list_length nat ds).
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_rtl.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_rtl_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop_rtl (bci :: bcis') ds =
      match decode_execute_rtl bci ds with
      | OK ds' =>
          match fetch_decode_execute_loop_rtl bcis' ds' with
          | OK' ds'' mh'' =>
               OK' ds'' (Nat.max (list_length nat ds) (Nat.max (list_length nat ds') mh''))
          | KO' s =>
              KO' s
          end
      | KO s =>
          KO' s
      end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_rtl.
Qed.

(* run rtl *)

Definition run_rtl (target : target_program) : (expressible_value * nat) :=
  match target with
    | Target_program bcis =>
        match fetch_decode_execute_loop_rtl bcis nil with
        | OK' ds mh =>
            match ds with
            | nil =>
                (Expressible_msg "no result on the data stack", 0)
            | d :: nil =>
                (Expressible_nat d, mh)
            | d :: d' :: ds'' =>
                (Expressible_msg "too many results on the data stack", 0)
            end
        | KO' s =>
            (Expressible_msg s, 0)
        end
    end.

(* interpret rtl *)

Definition interpret_rtl (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
      evaluate_rtl ae
  end.

Lemma about_fde_loop_rtl_stepping :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    (forall (ds1 : data_stack)
            (mh1 : nat),
        fetch_decode_execute_loop_rtl (bci :: bcis') ds = OK' ds1 mh1 ->
        (exists (ds2 : data_stack)
                (mh2 : nat),
            (decode_execute_rtl bci ds = OK ds2)
            /\ (fetch_decode_execute_loop_rtl bcis' ds2 = OK' ds1 mh2)
            /\ (mh1 = Nat.max (list_length nat ds) (Nat.max (list_length nat ds2) mh2)))).
Proof.
  intros bci bcis ds ds1 mh1 H_run_bcis_ds.
  rewrite -> fold_unfold_fetch_decode_execute_loop_rtl_cons in H_run_bcis_ds.
  case (decode_execute_rtl bci ds) as [ds2 | s] eqn:H_bci.
  - case (fetch_decode_execute_loop_rtl bcis ds2) as [ ds3 mh2 | s ] eqn:H_run_bcis'_ds2.
    + injection H_run_bcis_ds as H_ds1 H_mh1.
      exists ds2, mh2.
      split.
      * reflexivity.
      * split.
        { rewrite <- H_ds1. exact H_run_bcis'_ds2. }
        { symmetry. exact H_mh1. }
    + discriminate H_run_bcis_ds.
  - discriminate H_run_bcis_ds.
Qed.

Lemma about_fde_rtl_errors :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds : data_stack)
         (s : string),
        fetch_decode_execute_loop_rtl bci1s ds = KO' s ->
        fetch_decode_execute_loop_rtl (bci1s ++ bci2s) ds = KO' s.
Proof.
  intro bci1s.
  induction bci1s as [ | bci1 bci1s' IHbci1s ].
  - intros bci2s ds s H_absurd.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_nil ds) in H_absurd.
    discriminate H_absurd.
  - intros [ | bci2 bci2s'].
    + intros ds s H_KO.
      rewrite -> app_nil_r.
      exact H_KO.
    + intros ds s H_KO.
      rewrite -> (fold_unfold_list_append_cons byte_code_instruction bci1 bci1s' (bci2 :: bci2s')).
      Check (fold_unfold_fetch_decode_execute_loop_rtl_cons).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons bci1 (bci1s' ++ bci2 :: bci2s') ds).
      destruct (decode_execute_rtl bci1 ds) as [ds' | s'] eqn:H_de_bci1.
      * rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons bci1 bci1s' ds) in H_KO.
        rewrite -> H_de_bci1 in H_KO.
        case (fetch_decode_execute_loop_rtl bci1s' ds') as [ ds'' mh'' | s'' ] eqn:H_fdel_bci1s'_ds'.
        --- discriminate H_KO.
        --- Check (IHbci1s (bci2 :: bci2s') ds' s'' H_fdel_bci1s'_ds').
            rewrite -> (IHbci1s (bci2 :: bci2s') ds' s'' H_fdel_bci1s'_ds').
            exact H_KO.
      * rewrite -> fold_unfold_fetch_decode_execute_loop_rtl_cons in H_KO.
        rewrite -> H_de_bci1 in H_KO.
        exact H_KO.
Qed.

Theorem about_fde_loop_rtl_concatenation :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds: data_stack),
    (forall (ds1 : data_stack)
            (h1 : nat),
        fetch_decode_execute_loop_rtl bci1s ds = OK' ds1 h1 ->
        (forall (ds2 : data_stack)
                (h2 : nat),
            fetch_decode_execute_loop_rtl bci2s ds1 = OK' ds2 h2 ->
            fetch_decode_execute_loop_rtl (bci1s ++ bci2s) ds = OK' ds2 (Nat.max h1 h2))
        /\
        (forall (s2 : string),
            fetch_decode_execute_loop_rtl bci2s ds1 = KO' s2 ->
            fetch_decode_execute_loop_rtl (bci1s ++ bci2s) ds = KO' s2))
    /\
    (forall s1 : string,
        fetch_decode_execute_loop_rtl bci1s ds = KO' s1 ->
        fetch_decode_execute_loop_rtl (bci1s ++ bci2s) ds = KO' s1).
Proof.
  intro bci1s.
  induction bci1s as [ | bci1 bci1s' IH_bci1s].
  - intros bci2s ds.
    rewrite -> fold_unfold_list_append_nil.
    rewrite -> fold_unfold_fetch_decode_execute_loop_rtl_nil.
    split.
    + intros ds1 h1 H_OK'_nil.
      split.
      * intros ds2 h2 H_OK'_bci2s.
        injection H_OK'_nil as H_ds1 H_h1.
        case bci2s as [ | bci2 bci2s'].
        -- rewrite -> fold_unfold_fetch_decode_execute_loop_rtl_nil.
           rewrite -> fold_unfold_fetch_decode_execute_loop_rtl_nil in H_OK'_bci2s.
           injection H_OK'_bci2s as H_ds2 H_h2.
           rewrite -> H_ds1 in H_h1.
           rewrite <- H_h1.
           rewrite <- H_h2.
           rewrite -> Nat.max_id.
           rewrite -> H_ds1.
           rewrite -> H_ds2.
           reflexivity.
        -- rewrite <- H_ds1 in H_OK'_bci2s.
           destruct (about_fde_loop_rtl_stepping bci2 bci2s' ds ds2 h2
                       H_OK'_bci2s) as [ds' [mh' [_ [_ H_h2]]]].
           rewrite -> H_h2.
           rewrite -> H_h2 in H_OK'_bci2s.
           rewrite <- H_h1.
           rewrite -> Nat.max_assoc.
           rewrite -> Nat.max_id.
           exact H_OK'_bci2s.
      * intros s2 H_KO'_s2.
        injection H_OK'_nil as H_ds H_h1.
        rewrite -> H_ds.
        Check (app_nil_l).
        exact H_KO'_s2.
    + intros s1 H_KO'_s1.
      discriminate H_KO'_s1.
  - intros bci2s ds.
    split.
    + intros ds1 h1 H_run_bcis.
      split.
      * intros ds2 h2 H_run_bci2s.
        Check (about_fde_loop_rtl_stepping bci1 bci1s' ds ds1 h1 H_run_bcis).
        destruct (about_fde_loop_rtl_stepping bci1 bci1s' ds ds1 h1 H_run_bcis) as [ds1' [h1' [H_de_bci1 [H_fde H_max]]]].
        rewrite <- (app_comm_cons bci1s' bci2s).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons bci1 (bci1s' ++ bci2s) ds).
        rewrite -> H_de_bci1.
        destruct (IH_bci1s bci2s ds1') as [IH_bci1s_OK _].
        Check (IH_bci1s_OK ds1 h1' H_fde).
        destruct (IH_bci1s_OK ds1 h1' H_fde) as [IH_bci1s_OK_OK _].
        Check (IH_bci1s_OK_OK ds2 h2 H_run_bci2s).
        case  (list_length nat ds1' <=? h1') eqn: le_ds1'_h1'.
        { Search (_ <=? _ = true).
          Check (leb_complete (list_length nat ds1') h1' le_ds1'_h1').
          Check (Nat.max_r (list_length nat ds1') h1' (leb_complete (list_length nat ds1') h1' le_ds1'_h1')).
          rewrite -> (Nat.max_r (list_length nat ds1') h1' (leb_complete (list_length nat ds1') h1' le_ds1'_h1')) in H_max.
          rewrite -> H_max.
          rewrite -> (IH_bci1s_OK_OK ds2 h2 H_run_bci2s).
          Search (Nat.max).
          rewrite -> (Nat.max_assoc (list_length nat ds1') h1' h2).
          rewrite -> (Nat.max_r (list_length nat ds1') h1' (leb_complete (list_length nat ds1') h1' le_ds1'_h1')).
          rewrite -> (Nat.max_assoc (list_length nat ds) h1' h2).
          reflexivity. }
        { rewrite -> (IH_bci1s_OK_OK ds2 h2 H_run_bci2s).
          rewrite -> (Nat.max_assoc (list_length nat ds1') h1' h2).
          Check (Nat.max_assoc (list_length nat ds) (Nat.max (list_length nat ds1') h1') h2).
          rewrite -> (Nat.max_assoc (list_length nat ds) (Nat.max (list_length nat ds1') h1') h2).
          rewrite <- H_max.
          reflexivity. }
      * intros s2 H_s2.
        destruct (about_fde_loop_rtl_stepping bci1 bci1s' ds ds1 h1 H_run_bcis) as [ds1' [h1' [H_de_bci1 [H_fde H_max]]]].
        rewrite -> (fold_unfold_list_append_cons byte_code_instruction bci1 bci1s' bci2s).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons bci1 (bci1s' ++ bci2s) ds).
        rewrite -> H_de_bci1.
        destruct (IH_bci1s bci2s ds1') as [IH_bci1s_OK _].
        destruct (IH_bci1s_OK ds1 h1' H_fde) as [_ IH_bci1s_OK_KO].
        rewrite -> (IH_bci1s_OK_KO s2 H_s2).
        reflexivity.
    + intros s1 H_s1.
      Check (about_fde_rtl_errors (bci1 :: bci1s') bci2s ds s1 H_s1).
      exact (about_fde_rtl_errors (bci1 :: bci1s') bci2s ds s1 H_s1).
Qed.

Lemma about_fde_loop_rtl_and_evaluating:
  forall ae : arithmetic_expression,
    (forall (n : nat)
            (ds : data_stack),
        evaluate_rtl ae = Expressible_nat n ->
        fetch_decode_execute_loop_rtl (compile_rtl_aux ae) ds =
          OK' (n :: ds) (S (depth_right ae) + list_length nat ds))
    /\
      (forall (s : string)
              (ds : data_stack),
          evaluate_rtl ae = Expressible_msg s ->
          fetch_decode_execute_loop_rtl (compile_rtl_aux ae) ds =
            KO' s).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - split.
    + rewrite -> (fold_unfold_evaluate_rtl_Literal n).
      intros n' ds n_equals_n'.
      rewrite -> (fold_unfold_compile_rtl_aux_Literal n).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons (PUSH n) nil ds).
      unfold decode_execute_rtl.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_nil (n :: ds)).
      rewrite -> (fold_unfold_list_length_cons nat n ds).
      Search (Nat.max _ _).
      rewrite -> (Nat.max_id (1 + list_length nat ds)).
      rewrite -> (fold_unfold_depth_right_Literal n).
      injection n_equals_n' as nat_n_equals_n'.
      rewrite -> nat_n_equals_n'.
      Search (_ < S _).
      assert (H := Nat.lt_succ_diag_r (list_length nat ds)).
      Search (1 + _ = S _).
      rewrite -> (Nat.add_1_l (list_length nat ds)).
      Search (Nat.max _ _).
      Search (_ < _ -> _ <= _).
      rewrite -> (Nat.max_r (list_length nat ds) (S (list_length nat ds)) (Nat.lt_le_incl (list_length nat ds) (S (list_length nat ds)) H)).
      reflexivity.
    + intros s ds H_absurd.
      rewrite -> (fold_unfold_evaluate_rtl_Literal n) in H_absurd.
      discriminate H_absurd.
  - split.
    + intros n ds H_ae.
      rewrite -> (fold_unfold_compile_rtl_aux_Plus ae1 ae2).
      case (evaluate_rtl ae2) as [n2| s2] eqn: H_ae2.
      * rewrite -> (fold_unfold_depth_right_Plus ae1 ae2).
        case (evaluate_rtl ae1) as [n1 | s1] eqn: H_ae1.
        -- rewrite -> (fold_unfold_evaluate_rtl_Plus ae1 ae2) in H_ae.
           rewrite -> H_ae2 in H_ae.
           rewrite -> H_ae1 in H_ae.
           injection H_ae as H_ae.
           rewrite <- H_ae.
           destruct IHae1 as [IHae1_n _].
           destruct IHae2 as [IHae2_n _].
           Check (IHae2_n n2 nil (eq_refl (Expressible_nat n2))).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1 ++ ADD :: nil) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1) ds) as [H_eureka _].
           Check (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))).
           destruct (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))) as [H_run_ae2 _].
           Check (H_run_ae2 (n1 :: n2 :: ds) (S (depth_right ae1) + list_length nat (n2 :: ds))).
           Check (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1))).
           Check (H_run_ae2
                    (n1 :: n2 :: ds)
                    (S (depth_right ae1) + list_length nat (n2 :: ds))
                    (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1)))).
           assert (H_run_ae2_ae1 :=
                     (H_run_ae2
                        (n1 :: n2 :: ds)
                        (S (depth_right ae1) + list_length nat (n2 :: ds))
                        (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1))))).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (ADD :: nil) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (ADD :: nil) ds) as [H_eureka' _].
           Check (H_eureka' (n1 :: n2 :: ds) (Nat.max (S (depth_right ae2) + list_length nat ds) (S (depth_right ae1) + list_length nat (n2 :: ds))) H_run_ae2_ae1).
           destruct (H_eureka' (n1 :: n2 :: ds) (Nat.max (S (depth_right ae2) + list_length nat ds) (S (depth_right ae1) + list_length nat (n2 :: ds))) H_run_ae2_ae1) as [H_eureka'' _].
           rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons ADD nil (n1 :: n2 :: ds)) in H_eureka''.
           unfold decode_execute_rtl in H_eureka''.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_nil (n1 + n2 :: ds)) in H_eureka''.
           Check (H_eureka'' (n1 + n2 :: ds) (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 + n2 :: ds))
                                                                                            (list_length nat (n1 + n2 :: ds))))).
           Check H_eureka''.
           Check (H_eureka''
                    (n1 + n2 :: ds)
                    (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 + n2 :: ds)) (list_length nat (n1 + n2 :: ds))))
                    (eq_refl
                       (OK' (n1 + n2 :: ds)
                          (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 + n2 :: ds)) (list_length nat (n1 + n2 :: ds))))))).
           rewrite -> (app_assoc (compile_rtl_aux ae2) (compile_rtl_aux ae1) (ADD :: nil)).
           rewrite -> (H_eureka''
                         (n1 + n2 :: ds)
                         (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 + n2 :: ds)) (list_length nat (n1 + n2 :: ds))))
                         (eq_refl
                            (OK' (n1 + n2 :: ds)
                               (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 + n2 :: ds)) (list_length nat (n1 + n2 :: ds))))))).
           rewrite -> (Nat.max_id (list_length nat (n1 + n2 :: ds))).
           rewrite -> (fold_unfold_list_length_cons nat n1 (n2 :: ds)).
           rewrite -> (fold_unfold_list_length_cons nat n2 ds).
           rewrite -> (fold_unfold_list_length_cons nat (n1 + n2) ds).
           rewrite -> (Nat.add_1_l (list_length nat ds)).
           rewrite -> (Nat.add_1_l (S (list_length nat ds))).
           Search (_ < S _).
           Check (Nat.lt_succ_diag_r (S (list_length nat ds))).
           Search (_ < _ -> _ <= _).
           Check (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds)))).
           Check (Nat.max_r (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds))))).
           Check (Nat.max_l).
           rewrite -> (Nat.max_l (S (S (list_length nat ds))) (S (list_length nat ds)) (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds))))).
           Search (Nat.max (S _) (S _)).
           Search (S _ + _).
           rewrite -> Nat.add_succ_l.
           rewrite -> Nat.add_succ_l.
           rewrite <- Nat.succ_max_distr.
           rewrite <- Nat.succ_max_distr.
           Search (_ + S _).
           rewrite <- Nat.add_succ_comm.
           Search (Nat.max (_ + _) (_ + _)).
           rewrite -> Nat.add_max_distr_r.
           rewrite <- (Nat.add_1_l (list_length nat ds)).
           rewrite -> Nat.add_max_distr_r.
           rewrite -> (Nat.max_comm (S (depth_right ae1)) (depth_right ae2)).
           case (depth_right ae1) as [ | h_ae1]; case (depth_right ae2) as [ | h_ae2].
           { rewrite -> (Nat.max_0_l).
             rewrite -> (Nat.max_id).
             Search (1 + 1).
             rewrite -> BinInt.ZL0.
             rewrite <- Nat.add_1_l.
             rewrite -> (Nat.add_assoc).
             reflexivity.}
           { rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             Search (S (_) + _ ).
             rewrite <- Nat.add_succ_l.
             reflexivity.
           }
           { rewrite -> Nat.max_0_l.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.
           }
           { rewrite <-2 Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.
           }

        -- rewrite -> (fold_unfold_evaluate_rtl_Plus ae1 ae2) in H_ae.
           rewrite -> H_ae2 in H_ae.
           rewrite -> H_ae1 in H_ae.
           discriminate H_ae.

      * rewrite -> (fold_unfold_evaluate_rtl_Plus ae1 ae2) in H_ae.
        rewrite -> H_ae2 in H_ae.
        discriminate H_ae.

    + intros s ds H_ae.
      case (evaluate_rtl ae2) as [n2 | s2] eqn: H_ae2.

      * rewrite -> (fold_unfold_evaluate_rtl_Plus ae1 ae2) in H_ae.
        rewrite -> H_ae2 in H_ae.
        case (evaluate_rtl ae1) as [n1 | s1] eqn: H_ae1.
        -- discriminate H_ae.
        -- rewrite -> (fold_unfold_compile_rtl_aux_Plus ae1 ae2).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1) ds) as [H_eureka _].
           Check (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds)).
           destruct IHae2 as [IHae2_n _].
           Check (IHae2_n n2 ds (eq_refl (Expressible_nat n2))).
           Check (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))).
           destruct (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))) as [_ IHae2'].
           destruct IHae1 as [_ IHae1_s].
           Check (IHae1_s s1 (n2 :: ds) (eq_refl (Expressible_msg s1))).
           Check (IHae2' s1 (IHae1_s s1 (n2 :: ds) (eq_refl (Expressible_msg s1)))).
           assert (H_run_ae2_ae1 := (IHae2' s1 (IHae1_s s1 (n2 :: ds) (eq_refl (Expressible_msg s1))))).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (ADD :: nil) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (ADD :: nil) ds) as [_ H_eureka'].
           Check (H_eureka' s1 H_run_ae2_ae1).
           rewrite -> (app_assoc (compile_rtl_aux ae2) (compile_rtl_aux ae1) (ADD :: nil)).
           injection H_ae as H_ae.
           rewrite <- H_ae.
           exact (H_eureka' s1 H_run_ae2_ae1).
      * rewrite -> (fold_unfold_evaluate_rtl_Plus ae1 ae2) in H_ae.
        rewrite -> H_ae2 in H_ae.
        injection H_ae as H_ae.
        rewrite -> (fold_unfold_compile_rtl_aux_Plus ae1 ae2).
        destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1 ++ ADD :: nil) ds) as [_ H_eureka].
        Check (H_eureka s2).
        destruct IHae2 as [_ IHae2_s].
        Check (IHae2_s s2 ds (eq_refl (Expressible_msg s2))).
        Check (H_eureka s2 (IHae2_s s2 ds (eq_refl (Expressible_msg s2)))).
        rewrite <- H_ae.
        exact (H_eureka s2 (IHae2_s s2 ds (eq_refl (Expressible_msg s2)))).
  - split.
    + intros n ds H_ae.
      rewrite -> (fold_unfold_compile_rtl_aux_Minus ae1 ae2).
      case (evaluate_rtl ae2) as [n2| s2] eqn: H_ae2.
      * rewrite -> (fold_unfold_depth_right_Minus ae1 ae2).
        case (evaluate_rtl ae1) as [n1 | s1] eqn: H_ae1.
        -- rewrite -> (fold_unfold_evaluate_rtl_Minus ae1 ae2) in H_ae.
           rewrite -> H_ae2 in H_ae.
           rewrite -> H_ae1 in H_ae.
           case (n1 <? n2) eqn: n1_lt_n2.
           {discriminate H_ae.}
           injection H_ae as H_ae.
           rewrite <- H_ae.
           destruct IHae1 as [IHae1_n _].
           destruct IHae2 as [IHae2_n _].
           Check (IHae2_n n2 nil (eq_refl (Expressible_nat n2))).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1 ++ ADD :: nil) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1) ds) as [H_eureka _].
           Check (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))).
           destruct (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))) as [H_run_ae2 _].
           Check (H_run_ae2 (n1 :: n2 :: ds) (S (depth_right ae1) + list_length nat (n2 :: ds))).
           Check (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1))).
           Check (H_run_ae2
                    (n1 :: n2 :: ds)
                    (S (depth_right ae1) + list_length nat (n2 :: ds))
                    (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1)))).
           assert (H_run_ae2_ae1 :=
                     (H_run_ae2
                        (n1 :: n2 :: ds)
                        (S (depth_right ae1) + list_length nat (n2 :: ds))
                        (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1))))).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (ADD :: nil) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (SUB :: nil) ds) as [H_eureka' _].
           Check (H_eureka' (n1 :: n2 :: ds) (Nat.max (S (depth_right ae2) + list_length nat ds) (S (depth_right ae1) + list_length nat (n2 :: ds))) H_run_ae2_ae1).
           destruct (H_eureka' (n1 :: n2 :: ds) (Nat.max (S (depth_right ae2) + list_length nat ds) (S (depth_right ae1) + list_length nat (n2 :: ds))) H_run_ae2_ae1) as [H_eureka'' _].
           rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons SUB nil (n1 :: n2 :: ds)) in H_eureka''.
           unfold decode_execute_rtl in H_eureka''.
           rewrite -> n1_lt_n2 in H_eureka''.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_nil (n1 - n2 :: ds)) in H_eureka''.
           Check (H_eureka'' (n1 - n2 :: ds) (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 - n2 :: ds))
                                                                                            (list_length nat (n1 - n2 :: ds))))).
           Check H_eureka''.
           Check (H_eureka''
                    (n1 - n2 :: ds)
                    (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 - n2 :: ds)) (list_length nat (n1 - n2 :: ds))))
                    (eq_refl
                       (OK' (n1 - n2 :: ds)
                          (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 - n2 :: ds)) (list_length nat (n1 - n2 :: ds))))))).
           rewrite -> (app_assoc (compile_rtl_aux ae2) (compile_rtl_aux ae1) (SUB :: nil)).
           rewrite -> (H_eureka''
                         (n1 - n2 :: ds)
                         (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 - n2 :: ds)) (list_length nat (n1 - n2 :: ds))))
                         (eq_refl
                            (OK' (n1 - n2 :: ds)
                               (Nat.max (list_length nat (n1 :: n2 :: ds)) (Nat.max (list_length nat (n1 - n2 :: ds)) (list_length nat (n1 - n2 :: ds))))))).
           rewrite -> (Nat.max_id (list_length nat (n1 - n2 :: ds))).
           rewrite -> (fold_unfold_list_length_cons nat n1 (n2 :: ds)).
           rewrite -> (fold_unfold_list_length_cons nat n2 ds).
           rewrite -> (fold_unfold_list_length_cons nat (n1 - n2) ds).
           rewrite -> (Nat.add_1_l (list_length nat ds)).
           rewrite -> (Nat.add_1_l (S (list_length nat ds))).
           Search (_ < S _).
           Check (Nat.lt_succ_diag_r (S (list_length nat ds))).
           Search (_ < _ -> _ <= _).
           Check (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds)))).
           Check (Nat.max_r (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds))))).
           Check (Nat.max_l).
           rewrite -> (Nat.max_l (S (S (list_length nat ds))) (S (list_length nat ds)) (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds))))).
           Search (Nat.max (S _) (S _)).
           Search (S _ + _).
           rewrite -> Nat.add_succ_l.
           rewrite -> Nat.add_succ_l.
           rewrite <- Nat.succ_max_distr.
           rewrite <- Nat.succ_max_distr.
           Search (_ + S _).
           rewrite <- Nat.add_succ_comm.
           Search (Nat.max (_ + _) (_ + _)).
           rewrite -> Nat.add_max_distr_r.
           rewrite <- (Nat.add_1_l (list_length nat ds)).
           rewrite -> Nat.add_max_distr_r.
           rewrite -> (Nat.max_comm (S (depth_right ae1)) (depth_right ae2)).
           case (depth_right ae1) as [ | h_ae1]; case (depth_right ae2) as [ | h_ae2].
           { rewrite -> (Nat.max_0_l).
             rewrite -> (Nat.max_id).
             Search (1 + 1).
             rewrite -> BinInt.ZL0.
             rewrite <- Nat.add_1_l.
             rewrite -> (Nat.add_assoc).
             reflexivity.}
           { rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             Search (S (_) + _ ).
             rewrite <- Nat.add_succ_l.
             reflexivity.
           }
           { rewrite -> Nat.max_0_l.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.
           }
           { rewrite <-2 Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.
           }
        -- rewrite -> (fold_unfold_evaluate_rtl_Minus ae1 ae2) in H_ae.
           rewrite -> H_ae2 in H_ae.
           rewrite -> H_ae1 in H_ae.
           discriminate H_ae.
      * rewrite -> (fold_unfold_evaluate_rtl_Minus ae1 ae2) in H_ae.
        rewrite -> H_ae2 in H_ae.
        discriminate H_ae.
    + intros s ds H_ae.
      case (evaluate_rtl ae2) as [n2 | s2] eqn: H_ae2.
      * rewrite -> (fold_unfold_evaluate_rtl_Minus ae1 ae2) in H_ae.
        rewrite -> H_ae2 in H_ae.
        case (evaluate_rtl ae1) as [n1 | s1] eqn: H_ae1.
        -- case (n1 <? n2) eqn : n1_lt_n2.
           {
             destruct IHae1 as [IHae1_n _].
             destruct IHae2 as [IHae2_n _].
             Check (IHae2_n n2 nil (eq_refl (Expressible_nat n2))).
             Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1 ++ SUB :: nil) ds).
             destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1) ds) as [H_eureka _].
             Check (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))).
             destruct (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))) as [H_run_ae2 _].
             Check (H_run_ae2 (n1 :: n2 :: ds) (S (depth_right ae1) + list_length nat (n2 :: ds))).
             Check (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1))).
             Check (H_run_ae2
                      (n1 :: n2 :: ds)
                      (S (depth_right ae1) + list_length nat (n2 :: ds))
                      (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1)))).
             assert (H_run_ae2_ae1 :=
                       (H_run_ae2
                          (n1 :: n2 :: ds)
                          (S (depth_right ae1) + list_length nat (n2 :: ds))
                          (IHae1_n n1 (n2 :: ds) (eq_refl (Expressible_nat n1))))).
             Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (SUB :: nil) ds).
             destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (SUB :: nil) ds) as [H_eureka' _].
             Check (H_eureka' (n1 :: n2 :: ds) (Nat.max (S (depth_right ae2) + list_length nat ds) (S (depth_right ae1) + list_length nat (n2 :: ds))) H_run_ae2_ae1).
             destruct (H_eureka' (n1 :: n2 :: ds) (Nat.max (S (depth_right ae2) + list_length nat ds) (S (depth_right ae1) + list_length nat (n2 :: ds))) H_run_ae2_ae1) as [_ H_eureka''].
             rewrite -> (fold_unfold_fetch_decode_execute_loop_rtl_cons SUB nil (n1 :: n2 :: ds)) in H_eureka''.
             unfold decode_execute_rtl in H_eureka''.
             rewrite -> n1_lt_n2 in H_eureka''.
             injection H_ae as H_ae.
             assert (H_s_eq_err : KO' ("numerical underflow: -" ++
                                         string_of_nat (n2 - n1)) = KO' s).
             { rewrite <- H_ae.
               reflexivity. }
             Check (H_eureka'' s H_s_eq_err).
             rewrite -> (fold_unfold_compile_rtl_aux_Minus ae1 ae2).
             rewrite -> (app_assoc (compile_rtl_aux ae2) (compile_rtl_aux ae1) (SUB :: nil)).
             exact (H_eureka'' s H_s_eq_err).
           }
           { discriminate H_ae. }

        -- rewrite -> (fold_unfold_compile_rtl_aux_Minus ae1 ae2).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1) ds) as [H_eureka _].
           Check (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds)).
           destruct IHae2 as [IHae2_n _].
           Check (IHae2_n n2 ds (eq_refl (Expressible_nat n2))).
           Check (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))).
           destruct (H_eureka (n2 :: ds) (S (depth_right ae2) + list_length nat ds) (IHae2_n n2 ds (eq_refl (Expressible_nat n2)))) as [_ IHae2'].
           destruct IHae1 as [_ IHae1_s].
           Check (IHae1_s s1 (n2 :: ds) (eq_refl (Expressible_msg s1))).
           Check (IHae2' s1 (IHae1_s s1 (n2 :: ds) (eq_refl (Expressible_msg s1)))).
           assert (H_run_ae2_ae1 := (IHae2' s1 (IHae1_s s1 (n2 :: ds) (eq_refl (Expressible_msg s1))))).
           Check (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (SUB :: nil) ds).
           destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2 ++ compile_rtl_aux ae1) (SUB :: nil) ds) as [_ H_eureka'].
           Check (H_eureka' s1 H_run_ae2_ae1).
           rewrite -> (app_assoc (compile_rtl_aux ae2) (compile_rtl_aux ae1) (SUB :: nil)).
           injection H_ae as H_ae.
           rewrite <- H_ae.
           exact (H_eureka' s1 H_run_ae2_ae1).
      * rewrite -> (fold_unfold_evaluate_rtl_Minus ae1 ae2) in H_ae.
        rewrite -> H_ae2 in H_ae.
        injection H_ae as H_ae.
        rewrite -> (fold_unfold_compile_rtl_aux_Minus ae1 ae2).
        destruct (about_fde_loop_rtl_concatenation (compile_rtl_aux ae2) (compile_rtl_aux ae1 ++ SUB :: nil) ds) as [_ H_eureka].
        Check (H_eureka s2).
        destruct IHae2 as [_ IHae2_s].
        Check (IHae2_s s2 ds (eq_refl (Expressible_msg s2))).
        Check (H_eureka s2 (IHae2_s s2 ds (eq_refl (Expressible_msg s2)))).
        rewrite <- H_ae.
        exact (H_eureka s2 (IHae2_s s2 ds (eq_refl (Expressible_msg s2)))).
Qed.

Definition depth_right_sp (sp : source_program) : nat :=
  match sp with
  | Source_program ae =>
      depth_right ae
  end.

Theorem compiling_and_running_rtl_gives_S_depth_right:
  forall sp : source_program,
    (forall n mh: nat,
        run_rtl (compile_rtl sp) = (Expressible_nat n, mh) ->
        interpret_rtl sp = Expressible_nat n /\ (S (depth_right_sp sp) = mh))
    /\
    (forall s : string,
        run_rtl (compile_rtl sp) = (Expressible_msg s, 0) ->
        interpret_rtl sp = Expressible_msg s).
Proof.
  intros [ae].
  Check (about_fde_loop_rtl_and_evaluating ae).
  destruct (about_fde_loop_rtl_and_evaluating ae) as [H_n H_s].
  unfold run_rtl; unfold compile_rtl.
  unfold interpret_rtl.
  case (evaluate_rtl ae) as [n | s] eqn: H_ae.

  - Check (H_n n nil (eq_refl (Expressible_nat n))).
    rewrite -> (H_n n nil (eq_refl (Expressible_nat n))).
    split.

    + intros n' mh H_eval.
      injection H_eval as H_n' H_mh.
      rewrite -> H_n'.
      rewrite <- H_mh.
      unfold depth_right_sp.
      split.

      * reflexivity.

      * rewrite -> (Nat.add_0_r (depth_right ae)).
        reflexivity.

    + intros s H_absurd.
      discriminate H_absurd.

  - Check (H_s s nil (eq_refl (Expressible_msg s))).
    rewrite -> (H_s s nil (eq_refl (Expressible_msg s))).
    split.

    + intros n mh H_absurd.
      discriminate H_absurd.

    + intros s' H_s'.
      injection H_s' as s_equals_s'.
      rewrite -> s_equals_s'.
      reflexivity.
Qed.

(* ***** *)

Lemma about_fde_loop_ltr_stepping :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    (forall (ds1 : data_stack)
            (mh1 : nat),
        fetch_decode_execute_loop_ltr (bci :: bcis') ds = OK' ds1 mh1 ->
        (exists (ds2 : data_stack)
                (mh2 : nat),
            (decode_execute_ltr bci ds = OK ds2)
            /\ (fetch_decode_execute_loop_ltr bcis' ds2 = OK' ds1 mh2)
            /\ (mh1 = Nat.max (list_length nat ds) (Nat.max (list_length nat ds2) mh2)))).
Proof.
  intros bci bcis ds ds1 mh1 H_run_bcis_ds.
  rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_cons in H_run_bcis_ds.
  case (decode_execute_ltr bci ds) as [ds2 | s] eqn:H_bci.
  - case (fetch_decode_execute_loop_ltr bcis ds2) as [ ds3 mh2 | s ] eqn:H_run_bcis'_ds2.
    + injection H_run_bcis_ds as H_ds1 H_mh1.
      exists ds2, mh2.
      split.
      * reflexivity.
      * split.
        { rewrite <- H_ds1. exact H_run_bcis'_ds2. }
        { symmetry. exact H_mh1. }
    + discriminate H_run_bcis_ds.
  - discriminate H_run_bcis_ds.
Qed.

Lemma about_fde_ltr_errors :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds : data_stack)
         (s : string),
    fetch_decode_execute_loop_ltr bci1s ds = KO' s ->
    fetch_decode_execute_loop_ltr (bci1s ++ bci2s) ds = KO' s.
Proof.
  intro bci1s.
  induction bci1s as [ | bci1 bci1s' IHbci1s ].
  - intros bci2s ds s H_absurd.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_nil ds) in H_absurd.
    discriminate H_absurd.
  - intros [ | bci2 bci2s'].
    + intros ds s H_KO.
      rewrite -> app_nil_r.
      exact H_KO.
    + intros ds s H_KO.
      rewrite -> (fold_unfold_list_append_cons byte_code_instruction bci1 bci1s' (bci2 :: bci2s')).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons bci1 (bci1s' ++ bci2 :: bci2s') ds).
      destruct (decode_execute_ltr bci1 ds) as [ds' | s'] eqn:H_de_bci1.
      * rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons bci1 bci1s' ds) in H_KO.
        rewrite -> H_de_bci1 in H_KO.
        case (fetch_decode_execute_loop_ltr bci1s' ds') as [ ds'' mh'' | s'' ] eqn:H_fdel_bci1s'_ds'.
        -- discriminate H_KO.
        -- rewrite -> (IHbci1s (bci2 :: bci2s') ds' s'' H_fdel_bci1s'_ds').
           exact H_KO.
      * rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_cons in H_KO.
        rewrite -> H_de_bci1 in H_KO.
        exact H_KO.
Qed.

Theorem about_fde_loop_ltr_concatenation :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds: data_stack),
    (forall (ds1 : data_stack)
            (h1 : nat),
        fetch_decode_execute_loop_ltr bci1s ds = OK' ds1 h1 ->
        (forall (ds2 : data_stack)
                (h2 : nat),
            fetch_decode_execute_loop_ltr bci2s ds1 = OK' ds2 h2 ->
            fetch_decode_execute_loop_ltr (bci1s ++ bci2s) ds = OK' ds2 (Nat.max h1 h2))
        /\
          (forall (s2 : string),
            fetch_decode_execute_loop_ltr bci2s ds1 = KO' s2 ->
            fetch_decode_execute_loop_ltr (bci1s ++ bci2s) ds = KO' s2))
    /\
      (forall s1 : string,
          fetch_decode_execute_loop_ltr bci1s ds = KO' s1 ->
          fetch_decode_execute_loop_ltr (bci1s ++ bci2s) ds = KO' s1).
Proof.
  intro bci1s.
  induction bci1s as [ | bci1 bci1s' IH_bci1s].
  - intros bci2s ds.
    rewrite -> fold_unfold_list_append_nil.
    rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_nil.
    split.
    + intros ds1 h1 H_OK'_nil.
      split.
      * intros ds2 h2 H_OK'_bci2s.
        injection H_OK'_nil as H_ds1 H_h1.
        case bci2s as [ | bci2 bci2s'].
        -- rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_nil.
           rewrite -> fold_unfold_fetch_decode_execute_loop_ltr_nil in H_OK'_bci2s.
           injection H_OK'_bci2s as H_ds2 H_h2.
           rewrite -> H_ds1 in H_h1.
           rewrite <- H_h1.
           rewrite <- H_h2.
           rewrite -> Nat.max_id.
           rewrite -> H_ds1.
           rewrite -> H_ds2.
           reflexivity.
        -- rewrite <- H_ds1 in H_OK'_bci2s.
           destruct (about_fde_loop_ltr_stepping bci2 bci2s' ds ds2 h2
                       H_OK'_bci2s) as [ds' [mh' [_ [_ H_h2]]]].
           rewrite -> H_h2.
           rewrite -> H_h2 in H_OK'_bci2s.
           rewrite <- H_h1.
           rewrite -> Nat.max_assoc.
           rewrite -> Nat.max_id.
           exact H_OK'_bci2s.
      * intros s2 H_KO'_s2.
        injection H_OK'_nil as H_ds H_h1.
        rewrite -> H_ds.
        Check (app_nil_l).
        exact H_KO'_s2.
    + intros s1 H_KO'_s1.
      discriminate H_KO'_s1.
  - intros bci2s ds.
    split.
    + intros ds1 h1 H_run_bcis.
      split.
      * intros ds2 h2 H_run_bci2s.
        destruct (about_fde_loop_ltr_stepping bci1 bci1s' ds ds1 h1 H_run_bcis) as [ds1' [h1' [H_de_bci1 [H_fde H_max]]]].
        rewrite <- (app_comm_cons bci1s' bci2s).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons bci1 (bci1s' ++ bci2s) ds).
        rewrite -> H_de_bci1.
        destruct (IH_bci1s bci2s ds1') as [IH_bci1s_OK _].
        destruct (IH_bci1s_OK ds1 h1' H_fde) as [IH_bci1s_OK_OK _].
        case  (list_length nat ds1' <=? h1') eqn: le_ds1'_h1'.
        { rewrite -> (Nat.max_r (list_length nat ds1') h1' (leb_complete (list_length nat ds1') h1' le_ds1'_h1')) in H_max.
          rewrite -> H_max.
          rewrite -> (IH_bci1s_OK_OK ds2 h2 H_run_bci2s).
          rewrite -> (Nat.max_assoc (list_length nat ds1') h1' h2).
          rewrite -> (Nat.max_r (list_length nat ds1') h1' (leb_complete (list_length nat ds1') h1' le_ds1'_h1')).
          rewrite -> (Nat.max_assoc (list_length nat ds) h1' h2).
          reflexivity. }
        { rewrite -> (IH_bci1s_OK_OK ds2 h2 H_run_bci2s).
          rewrite -> (Nat.max_assoc (list_length nat ds1') h1' h2).
          rewrite -> (Nat.max_assoc (list_length nat ds) (Nat.max (list_length nat ds1') h1') h2).
          rewrite <- H_max.
          reflexivity. }
      * intros s2 H_s2.
        destruct (about_fde_loop_ltr_stepping bci1 bci1s' ds ds1 h1 H_run_bcis) as [ds1' [h1' [H_de_bci1 [H_fde H_max]]]].
        rewrite -> (fold_unfold_list_append_cons byte_code_instruction bci1 bci1s' bci2s).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons bci1 (bci1s' ++ bci2s) ds).
        rewrite -> H_de_bci1.
        destruct (IH_bci1s bci2s ds1') as [IH_bci1s_OK _].
        destruct (IH_bci1s_OK ds1 h1' H_fde) as [_ IH_bci1s_OK_KO].
        rewrite -> (IH_bci1s_OK_KO s2 H_s2).
        reflexivity.
    + intros s1 H_s1.
      exact (about_fde_ltr_errors (bci1 :: bci1s') bci2s ds s1 H_s1).
Qed.
      
Lemma about_fde_loop_ltr_and_evaluating:
  forall ae : arithmetic_expression,
    (forall (n : nat)
            (ds : data_stack),
        evaluate_ltr ae = Expressible_nat n ->
          fetch_decode_execute_loop_ltr (compile_ltr_aux ae) ds =
            OK' (n :: ds) (S (depth_left ae) + list_length nat ds))
    /\
      (forall (s : string)
              (ds : data_stack),
        evaluate_ltr ae = Expressible_msg s ->
        fetch_decode_execute_loop_ltr (compile_ltr_aux ae) ds =
          KO' s).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].

  - split.

    + rewrite -> (fold_unfold_evaluate_ltr_Literal n).
      intros n' ds n_equals_n'.
      rewrite -> (fold_unfold_compile_ltr_aux_Literal n).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons (PUSH n) nil ds).
      unfold decode_execute_ltr.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_nil (n :: ds)).
      rewrite -> (fold_unfold_list_length_cons nat n ds).
      rewrite -> (Nat.max_id (1 + list_length nat ds)).
      rewrite -> (fold_unfold_depth_left_Literal n).
      injection n_equals_n' as nat_n_equals_n'.
      rewrite -> nat_n_equals_n'.
      assert (H := Nat.lt_succ_diag_r (list_length nat ds)).
      rewrite -> (Nat.add_1_l (list_length nat ds)).
      rewrite -> (Nat.max_r (list_length nat ds) (S (list_length nat ds)) (Nat.lt_le_incl (list_length nat ds) (S (list_length nat ds)) H)).
      reflexivity.

    + intros s ds H_absurd.
      rewrite -> (fold_unfold_evaluate_ltr_Literal n) in H_absurd.
      discriminate H_absurd.

  - split.

    + intros n ds H_ae.
      rewrite -> (fold_unfold_compile_ltr_aux_Plus ae1 ae2).
      case (evaluate_ltr ae1) as [n1 | s1] eqn: H_ae1.

      * rewrite -> (fold_unfold_depth_left_Plus ae1 ae2).
        case (evaluate_ltr ae2) as [n2 | s2] eqn: H_ae2.

        -- rewrite -> (fold_unfold_evaluate_ltr_Plus ae1 ae2) in H_ae.
           rewrite -> H_ae2 in H_ae.
           rewrite -> H_ae1 in H_ae.
           injection H_ae as H_ae.
           rewrite <- H_ae.
           destruct IHae1 as [IHae1_n _].
           destruct IHae2 as [IHae2_n _].
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2) ds) as [H_eureka _].
           destruct (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))) as [H_run_ae1 _].
           Check (H_run_ae1
                    (n2 :: n1 :: ds)
                    (S (depth_left ae2) + list_length nat (n1 :: ds))
                    (IHae2_n n2 (n1 :: ds) (eq_refl (Expressible_nat n2)))).
           assert (H_run_ae1_ae2 :=
                     (H_run_ae1
                        (n2 :: n1 :: ds)
                        (S (depth_left ae2) + list_length nat (n1 :: ds))
                        (IHae2_n n2 (n1 :: ds) (eq_refl (Expressible_nat n2))))).
           Check (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (ADD :: nil) ds).
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (ADD :: nil) ds) as [H_eureka' _].
           Check (H_eureka' (n2 :: n1 :: ds) (Nat.max (S (depth_left ae1) + list_length nat ds) (S (depth_left ae2) + list_length nat (n1 :: ds))) H_run_ae1_ae2).
           destruct (H_eureka' (n2 :: n1 :: ds) (Nat.max (S (depth_left ae1) + list_length nat ds) (S (depth_left ae2) + list_length nat (n1 :: ds))) H_run_ae1_ae2) as [H_eureka'' _].
           rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons ADD nil (n2 :: n1 :: ds)) in H_eureka''.
           unfold decode_execute_ltr in H_eureka''.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_nil (n1 + n2 :: ds)) in H_eureka''.
           rewrite -> (app_assoc (compile_ltr_aux ae1) (compile_ltr_aux ae2) (ADD :: nil)).
           rewrite -> (H_eureka''
                         (n1 + n2 :: ds)
                         (Nat.max (list_length nat (n2 :: n1 :: ds)) (Nat.max (list_length nat (n1 + n2 :: ds)) (list_length nat (n1 + n2 :: ds))))
                         (eq_refl
                            (OK' (n1 + n2 :: ds)
                               (Nat.max (list_length nat (n2 :: n1 :: ds)) (Nat.max (list_length nat (n1 + n2 :: ds)) (list_length nat (n1 + n2 :: ds))))))).
           rewrite -> (Nat.max_id (list_length nat (n1 + n2 :: ds))).
           rewrite -> (fold_unfold_list_length_cons nat n2 (n1 :: ds)).
           rewrite -> (fold_unfold_list_length_cons nat n1 ds).
           rewrite -> (fold_unfold_list_length_cons nat (n1 + n2) ds).
           rewrite -> (Nat.add_1_l (list_length nat ds)).
           rewrite -> (Nat.add_1_l (S (list_length nat ds))).
           rewrite -> (Nat.max_l (S (S (list_length nat ds))) (S (list_length nat ds)) (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds))))).
           rewrite -> Nat.add_succ_l.
           rewrite -> Nat.add_succ_l.
           rewrite <- Nat.succ_max_distr.
           rewrite <- Nat.succ_max_distr.
           rewrite <- Nat.add_succ_comm.
           rewrite -> Nat.add_max_distr_r.
           rewrite <- (Nat.add_1_l (list_length nat ds)).
           rewrite -> Nat.add_max_distr_r.
           rewrite -> (Nat.max_comm (depth_left ae1) (S (depth_left ae2))).
           case (depth_left ae2) as [ | h_ae2]; case (depth_left ae1) as [ | h_ae1].
           { rewrite -> (Nat.max_0_r).
             rewrite -> (Nat.max_id).
             Search (1 + 1).
             rewrite -> BinInt.ZL0.
             rewrite <- Nat.add_1_l.
             rewrite -> (Nat.add_assoc).
             reflexivity.}
           { rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_l.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             Search (S (_) + _ ).
             rewrite <- Nat.add_succ_l.
             reflexivity.}
           { rewrite -> Nat.max_0_r.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.}
           { rewrite <-2 Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.}
        -- rewrite -> (fold_unfold_evaluate_ltr_Plus ae1 ae2) in H_ae.
           rewrite -> H_ae2 in H_ae.
           rewrite -> H_ae1 in H_ae.
           discriminate H_ae.
      * rewrite -> (fold_unfold_evaluate_ltr_Plus ae1 ae2) in H_ae.
        rewrite -> H_ae1 in H_ae.
        discriminate H_ae.
    + intros s ds H_ae.
      case (evaluate_ltr ae1) as [n1 | s1] eqn: H_ae1.
      * rewrite -> (fold_unfold_evaluate_ltr_Plus ae1 ae2) in H_ae.
        rewrite -> H_ae1 in H_ae.
        case (evaluate_ltr ae2) as [n2 | s2] eqn: H_ae2.
        -- discriminate H_ae.
        -- rewrite -> (fold_unfold_compile_ltr_aux_Plus ae1 ae2).
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2) ds) as [H_eureka _].
           destruct IHae1 as [IHae1_n _].
           Check (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))).
           destruct (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))) as [_ IHae1'].
           destruct IHae2 as [_ IHae2_s].
           assert (H_run_ae1_ae2 := (IHae1' s2 (IHae2_s s2 (n1 :: ds) (eq_refl (Expressible_msg s2))))).
           Check (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (ADD :: nil) ds).
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (ADD :: nil) ds) as [_ H_eureka'].
           rewrite -> (app_assoc (compile_ltr_aux ae1) (compile_ltr_aux ae2) (ADD :: nil)).
           injection H_ae as H_ae.
           rewrite <- H_ae.
           exact (H_eureka' s2 H_run_ae1_ae2).
      * rewrite -> (fold_unfold_evaluate_ltr_Plus ae1 ae2) in H_ae.
        rewrite -> H_ae1 in H_ae.
        injection H_ae as H_ae.
        rewrite -> (fold_unfold_compile_ltr_aux_Plus ae1 ae2).
        destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2 ++ ADD :: nil) ds) as [_ H_eureka].
        destruct IHae1 as [_ IHae1_s].
        rewrite <- H_ae.
        exact (H_eureka s1 (IHae1_s s1 ds (eq_refl (Expressible_msg s1)))).
  - split.
    + intros n ds H_ae.
      rewrite -> (fold_unfold_compile_ltr_aux_Minus ae1 ae2).
      case (evaluate_ltr ae1) as [n1 | s1] eqn: H_ae1.
      * rewrite -> (fold_unfold_depth_left_Minus ae1 ae2).
        case (evaluate_ltr ae2) as [n2 | s2] eqn: H_ae2.
        -- rewrite -> (fold_unfold_evaluate_ltr_Minus ae1 ae2) in H_ae.
           rewrite -> H_ae1 in H_ae.
           rewrite -> H_ae2 in H_ae.
           case (n1 <? n2) eqn: n1_lt_n2.
           { discriminate H_ae. }
           injection H_ae as H_ae.
           rewrite <- H_ae.
           destruct IHae1 as [IHae1_n _].
           destruct IHae2 as [IHae2_n _].
           Check (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2 ++ ADD :: nil) ds).
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2) ds) as [H_eureka _].
           Check (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))).
           destruct (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))) as [H_run_ae1 _].
           assert (H_run_ae1_ae2 :=
                     (H_run_ae1
                        (n2 :: n1 :: ds)
                        (S (depth_left ae2) + list_length nat (n1 :: ds))
                        (IHae2_n n2 (n1 :: ds) (eq_refl (Expressible_nat n2))))).
           Check (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (SUB :: nil) ds).
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (SUB :: nil) ds) as [H_eureka' _].
           Check (H_eureka' (n2 :: n1 :: ds) (Nat.max (S (depth_left ae1) + list_length nat ds) (S (depth_left ae2) + list_length nat (n1 :: ds))) H_run_ae1_ae2).
           destruct (H_eureka' (n2 :: n1 :: ds) (Nat.max (S (depth_left ae1) + list_length nat ds) (S (depth_left ae2) + list_length nat (n1 :: ds))) H_run_ae1_ae2) as [H_eureka'' _].
           rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons SUB nil (n2 :: n1 :: ds)) in H_eureka''.
           unfold decode_execute_ltr in H_eureka''.
           rewrite -> n1_lt_n2 in H_eureka''.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_nil (n1 - n2 :: ds)) in H_eureka''.
           rewrite -> (app_assoc (compile_ltr_aux ae1) (compile_ltr_aux ae2) (SUB :: nil)).
           rewrite -> (H_eureka''
                         (n1 - n2 :: ds)
                         (Nat.max (list_length nat (n2 :: n1 :: ds)) (Nat.max (list_length nat (n1 - n2 :: ds)) (list_length nat (n1 - n2 :: ds))))
                         (eq_refl
                            (OK' (n1 - n2 :: ds)
                               (Nat.max (list_length nat (n2 :: n1 :: ds)) (Nat.max (list_length nat (n1 - n2 :: ds)) (list_length nat (n1 - n2 :: ds))))))).
           rewrite -> (Nat.max_id (list_length nat (n1 - n2 :: ds))).
           rewrite -> (fold_unfold_list_length_cons nat n2 (n1 :: ds)).
           rewrite -> (fold_unfold_list_length_cons nat n1 ds).
           rewrite -> (fold_unfold_list_length_cons nat (n1 - n2) ds).
           rewrite -> (Nat.add_1_l (list_length nat ds)).
           rewrite -> (Nat.add_1_l (S (list_length nat ds))).
           rewrite -> (Nat.max_l (S (S (list_length nat ds))) (S (list_length nat ds)) (Nat.lt_le_incl (S (list_length nat ds)) (S (S (list_length nat ds))) (Nat.lt_succ_diag_r (S (list_length nat ds))))).
           rewrite -> Nat.add_succ_l.
           rewrite -> Nat.add_succ_l.
           rewrite <- Nat.succ_max_distr.
           rewrite <- Nat.succ_max_distr.
           rewrite <- Nat.add_succ_comm.
           rewrite -> Nat.add_max_distr_r.
           rewrite <- (Nat.add_1_l (list_length nat ds)).
           rewrite -> Nat.add_max_distr_r.
           rewrite -> (Nat.max_comm (depth_left ae1) (S (depth_left ae2))).
           case (depth_left ae2) as [ | h_ae2]; case (depth_left ae1) as [ | h_ae1].
           { rewrite -> (Nat.max_0_r).
             rewrite -> (Nat.max_id).
             Search (1 + 1).
             rewrite -> BinInt.ZL0.
             rewrite <- Nat.add_1_l.
             rewrite -> (Nat.add_assoc).
             reflexivity.}
           { rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_l.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             Search (S (_) + _ ).
             rewrite <- Nat.add_succ_l.
             reflexivity.}
           { rewrite -> Nat.max_0_r.
             rewrite <- Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.}
           { rewrite <-2 Nat.succ_max_distr.
             rewrite -> Nat.max_0_r.
             rewrite <- Nat.add_succ_l.
             reflexivity.
           }
        -- rewrite -> (fold_unfold_evaluate_ltr_Minus ae1 ae2) in H_ae.
           rewrite -> H_ae2 in H_ae.
           rewrite -> H_ae1 in H_ae.
           discriminate H_ae.
      * rewrite -> (fold_unfold_evaluate_ltr_Minus ae1 ae2) in H_ae.
        rewrite -> H_ae1 in H_ae.
        discriminate H_ae.
    + intros s ds H_ae.
      case (evaluate_ltr ae1) as [n1 | s1] eqn: H_ae1.
      * rewrite -> (fold_unfold_evaluate_ltr_Minus ae1 ae2) in H_ae.
        rewrite -> H_ae1 in H_ae.
        case (evaluate_ltr ae2) as [n2 | s2] eqn: H_ae2.
        -- case (n1 <? n2) eqn : n1_lt_n2.
           { destruct IHae1 as [IHae1_n _].
             destruct IHae2 as [IHae2_n _].
             Check (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2 ++ SUB :: nil) ds).
             destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2) ds) as [H_eureka _].
             Check (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))).
             destruct (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))) as [H_run_ae1 _].
             assert (H_run_ae1_ae2 :=
                       (H_run_ae1
                          (n2 :: n1 :: ds)
                          (S (depth_left ae2) + list_length nat (n1 :: ds))
                          (IHae2_n n2 (n1 :: ds) (eq_refl (Expressible_nat n2))))).
             Check (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (SUB :: nil) ds).
             destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (SUB :: nil) ds) as [H_eureka' _].
             Check (H_eureka' (n2 :: n1 :: ds) (Nat.max (S (depth_left ae1) + list_length nat ds) (S (depth_left ae2) + list_length nat (n1 :: ds))) H_run_ae1_ae2).
             destruct (H_eureka' (n2 :: n1 :: ds) (Nat.max (S (depth_left ae1) + list_length nat ds) (S (depth_left ae2) + list_length nat (n1 :: ds))) H_run_ae1_ae2) as [_ H_eureka''].
             rewrite -> (fold_unfold_fetch_decode_execute_loop_ltr_cons SUB nil (n2 :: n1 :: ds)) in H_eureka''.
             unfold decode_execute_ltr in H_eureka''.
             rewrite -> n1_lt_n2 in H_eureka''.
             injection H_ae as H_ae.
             assert (H_s_eq_err : KO' ("numerical underflow: -" ++
                                         string_of_nat (n2 - n1)) = KO' s).
             { rewrite <- H_ae.
               reflexivity. }
             Check (H_eureka'' s H_s_eq_err).
             rewrite -> (fold_unfold_compile_ltr_aux_Minus ae1 ae2).
             rewrite -> (app_assoc (compile_ltr_aux ae1) (compile_ltr_aux ae2) (SUB :: nil)).
             exact (H_eureka'' s H_s_eq_err). }
           { discriminate H_ae. }
        -- rewrite -> (fold_unfold_compile_ltr_aux_Minus ae1 ae2).
           Check (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2) ds).
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2) ds) as [H_eureka _].
           destruct IHae1 as [IHae1_n _].
           destruct (H_eureka (n1 :: ds) (S (depth_left ae1) + list_length nat ds) (IHae1_n n1 ds (eq_refl (Expressible_nat n1)))) as [_ IHae1'].
           destruct IHae2 as [_ IHae2_s].
           assert (H_run_ae1_ae2 := (IHae1' s2 (IHae2_s s2 (n1 :: ds) (eq_refl (Expressible_msg s2))))).
           destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1 ++ compile_ltr_aux ae2) (SUB :: nil) ds) as [_ H_eureka'].
           rewrite -> (app_assoc (compile_ltr_aux ae1) (compile_ltr_aux ae2) (SUB :: nil)).
           injection H_ae as H_ae.
           rewrite <- H_ae.
           exact (H_eureka' s2 H_run_ae1_ae2).
      * rewrite -> (fold_unfold_evaluate_ltr_Minus ae1 ae2) in H_ae.
        rewrite -> H_ae1 in H_ae.
        injection H_ae as H_ae.
        rewrite -> (fold_unfold_compile_ltr_aux_Minus ae1 ae2).
        destruct (about_fde_loop_ltr_concatenation (compile_ltr_aux ae1) (compile_ltr_aux ae2 ++ SUB :: nil) ds) as [_ H_eureka].
        destruct IHae1 as [_ IHae1_s].
        rewrite <- H_ae.
        exact (H_eureka s1 (IHae1_s s1 ds (eq_refl (Expressible_msg s1)))).
Qed.

Definition depth_left_sp (sp : source_program) : nat :=
  match sp with
  | Source_program ae =>
      depth_left ae
  end.

Theorem compiling_and_running_ltr_gives_S_depth_left :
  forall sp : source_program,
    (forall n mh: nat,
        run_ltr (compile_ltr sp) = (Expressible_nat n, mh) ->
        interpret_ltr sp = Expressible_nat n /\ (S (depth_left_sp sp) = mh))
    /\
    (forall s : string,
        run_ltr (compile_ltr sp) = (Expressible_msg s, 0) ->
        interpret_ltr sp = Expressible_msg s).
Proof.
  intros [ae].
  destruct (about_fde_loop_ltr_and_evaluating ae) as [H_n H_s].
  unfold run_ltr, compile_ltr, interpret_ltr.
  case (evaluate_ltr ae) as [n | s] eqn:H_ae.
  - rewrite -> (H_n n nil (eq_refl (Expressible_nat n))).
    split.
    + intros n' mh H_eval.
      injection H_eval as H_n' H_mh.
      rewrite -> H_n'.
      rewrite <- H_mh.
      unfold depth_left_sp.
      split.
      * reflexivity.
      * rewrite -> (Nat.add_0_r (depth_left ae)).
        reflexivity.
    + intros s H_absurd.
      discriminate H_absurd.
  - rewrite -> (H_s s nil (eq_refl (Expressible_msg s))).
    split.
    + intros n mh H_absurd.
      discriminate H_absurd.
    + intros s' H_s'.
      injection H_s' as s_equals_s'.
      rewrite -> s_equals_s'.
      reflexivity.
Qed.

(* The capstone *)

(* effects of super_refactor_left and super_refactor_right on ltr evaluation *)

(* case 1: left-skewed ae *)
Compute(
    let ae := (Plus
                 (Plus
                    (Plus
                       (Plus
                          (Literal 1)
                          (Literal 2))
                       (Literal 3))
                    (Literal 4))
                 (Literal 5))in
    let ael := super_refactor_left ae in
    let aer := super_refactor_right ae in
    let spl := Source_program ael in
    let spr := Source_program aer in
    match run_ltr (compile_ltr spl) with
      (_, mhl) =>
        match run_ltr (compile_ltr spr) with
          (_, mhr) =>
            mhl <= mhr
        end
    end).

(* case 2: right-skewed ae *)
Compute(
    let ae := (Plus
                 (Literal 1)
                 (Plus
                    (Literal 2)
                    (Plus
                       (Literal 3)
                       (Plus (Literal 4)
                             (Literal 5))))) in
    let ael := super_refactor_left ae in
    let aer := super_refactor_right ae in
    let spl := Source_program ael in
    let spr := Source_program aer in
    match run_ltr (compile_ltr spl) with
      (_, mhl) =>
        match run_ltr (compile_ltr spr) with
          (_, mhr) =>
            mhl <= mhr
        end
    end).

(* case 3: complex ae *)
Compute(
    let ae := (Minus
                 (Plus
                    (Literal 1)
                    (Plus
                       (Plus
                          (Literal 4)
                          (Literal 0))
                       (Literal 20)))
                 (Plus
                    (Literal 3)
                    (Plus
                       (Literal 4)
                       (Minus
                          (Literal 2)
                          (Literal 0))))) in
    let ael := super_refactor_left ae in
    let aer := super_refactor_right ae in
    let spl := Source_program ael in
    let spr := Source_program aer in
    match run_ltr (compile_ltr spl) with
      (_, mhl) =>
        match run_ltr (compile_ltr spr) with
          (_, mhr) =>
            mhl <= mhr
        end
    end).

(* for ltr evaluation (compared to each other) :
   refactoring the sp on the left requires less memory allocation for the stack
   refactoring the sp on the right requires more memory allocation for the stack *)

(* effects of super_refactor_left and super_refactor_right on rtl evaluation *)

(* case 1: left-skewed ae *)
Compute(
    let ae := (Plus
                 (Plus
                    (Plus
                       (Plus
                          (Literal 1)
                          (Literal 2))
                       (Literal 3))
                    (Literal 4))
                 (Literal 5))in
    let ael := super_refactor_left ae in
    let aer := super_refactor_right ae in
    let spl := Source_program ael in
    let spr := Source_program aer in
    match run_rtl (compile_rtl spl) with
      (_, mhl) =>
        match run_rtl (compile_rtl spr) with
          (_, mhr) =>
            mhr <= mhl
        end
    end).

(* case 2: right-skewed ae *)
Compute(
    let ae := (Plus
                 (Literal 1)
                 (Plus
                    (Literal 2)
                    (Plus
                       (Literal 3)
                       (Plus (Literal 4)
                             (Literal 5))))) in
    let ael := super_refactor_left ae in
    let aer := super_refactor_right ae in
    let spl := Source_program ael in
    let spr := Source_program aer in
    match run_rtl (compile_rtl spl) with
      (_, mhl) =>
        match run_rtl (compile_rtl spr) with
          (_, mhr) =>
            mhr <= mhl
        end
    end).

(* case 3: complex ae *)
Compute(
    let ae := (Minus
                 (Plus
                    (Literal 1)
                    (Plus
                       (Plus
                          (Literal 4)
                          (Literal 0))
                       (Literal 20)))
                 (Plus
                    (Literal 3)
                    (Plus
                       (Literal 4)
                       (Minus
                          (Literal 2)
                          (Literal 0))))) in
    let ael := super_refactor_left ae in
    let aer := super_refactor_right ae in
    let spl := Source_program ael in
    let spr := Source_program aer in
    match run_rtl (compile_rtl spl) with
      (_, mhl) =>
        match run_rtl (compile_rtl spr) with
          (_, mhr) =>
            mhr <= mhl
        end
    end).

(* for rtl evaluation (compared to each other) :
   refactoring the sp on the left requires more memory allocation for the stack
   refactoring the sp on the right requires less memory allocation for the stack *)
