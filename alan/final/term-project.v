(* term-project.v *)
(* FPP 2023 - YSC 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 07 Nov 2023 *)

(* ********** *)

(* Three language processors for arithmetic expressions. *)

(*
   Group names:

   Student name: Alan Matthew
   E-mail address: alan.matthew@u.yale-nus.edu.sg
   Student ID number: A0224197B

   Student name: Jingyi Hou
   E-mail address: jingyi.hou@u.yale-nus.edu.sg
   Student ID number: A0242429E

   Student name: Zhu Wentao
   E-mail address: zhu.wentao@u.yale-nus.edu.sg
   Student ID number: A0224190N
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

Definition make_Eureka_lemma (A : Type) (id_A : A) (combine_A : A -> A -> A) (c : A -> A) (a : A) : Prop :=
  c a = combine_A (c id_A) a.

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

Proposition list_append_is_associative :
  forall (V : Type)
         (v1s v2s v3s : list V),
    (v1s ++ v2s) ++ v3s = v1s ++ (v2s ++ v3s).
Proof.
  intros V v1s v2s v3s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - rewrite ->2 fold_unfold_list_append_nil.
    reflexivity.
  - rewrite ->3 fold_unfold_list_append_cons.
    rewrite -> IHv1s'.
    reflexivity.
Qed.

Definition eqb_nat := Nat.eqb.

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

Definition eqb_string (s1 s2 : string) : bool :=
  match String.string_dec s1 s2 with
    left _ =>
      true
  | right _ =>
      false
  end.

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

Definition eqb_expressible_value (ev1 ev2 : expressible_value) : bool :=
  match ev1 with
  | Expressible_nat n1 =>
      match ev2 with
      | Expressible_nat n2 =>
          eqb_nat n1 n2
      | Expressible_msg s2 =>
          false
      end
  | Expressible_msg s1 =>
      match ev2 with
      | Expressible_nat n2 =>
          false
      | Expressible_msg s2 =>
          eqb_string s1 s2
      end
  end.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1: 
   a. time permitting, prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
*)

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate ae1 with
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          | Expressible_msg s2 =>
              Expressible_msg s2
          end
      | Expressible_msg s1 =>
          Expressible_msg s1
      end
  | Minus ae1 ae2 =>
      match evaluate ae1 with
      | Expressible_nat n1 =>
          match evaluate ae2 with
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

Definition test_evaluate candidate :=
  (eqb_expressible_value (candidate (Literal 10)) (Expressible_nat 10))
  && (eqb_expressible_value (candidate (Plus (Literal 5) (Literal 3))) (Expressible_nat 8))
  && (eqb_expressible_value (candidate (Plus (Literal 3) (Minus (Literal 5) (Literal 8)))) (Expressible_msg "numerical underflow: -3"))
  && (eqb_expressible_value (candidate (Plus (Minus (Literal 5) (Literal 8)) (Literal 3))) (Expressible_msg "numerical underflow: -3"))
  && (eqb_expressible_value (candidate (Minus (Literal 8) (Literal 3))) (Expressible_nat 5))
  && (eqb_expressible_value (candidate (Minus (Literal 5) (Literal 8))) (Expressible_msg "numerical underflow: -3"))
  && (eqb_expressible_value (candidate (Minus (Literal 3) (Minus (Literal 5) (Literal 8)))) (Expressible_msg "numerical underflow: -3"))
  && (eqb_expressible_value (candidate (Minus (Minus (Literal 5) (Literal 8)) (Literal 3))) (Expressible_msg "numerical underflow: -3")).

Compute (test_evaluate evaluate = true).
          
Lemma fold_unfold_evaluate_Literal :
  forall (n : nat),
    evaluate (Literal n) =
      Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall ae1 ae2: arithmetic_expression,
    evaluate (Plus ae1 ae2) =
      match evaluate ae1 with
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          | Expressible_msg s =>
              Expressible_msg s
          end
      | Expressible_msg s =>
          Expressible_msg s
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Minus :
  forall ae1 ae2: arithmetic_expression,
    evaluate (Minus ae1 ae2) = 
      match evaluate ae1 with
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_nat n2 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          | Expressible_msg s =>
              Expressible_msg s
          end
      | Expressible_msg s =>
          Expressible_msg s
      end.
Proof.
   fold_unfold_tactic evaluate.
Qed.

Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate.
  split.
  { intro n.
    exact (fold_unfold_evaluate_Literal n). }
  split.
  { split.
    { intros ae1 ae2 s1 S_evaluate.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> S_evaluate.
      reflexivity. }
    split.
    { intros ae1 ae2 n1 s2 S_evaluate SS_evaluate.
      rewrite -> fold_unfold_evaluate_Plus.
      rewrite -> S_evaluate.
      rewrite -> SS_evaluate.
      reflexivity. }
    intros ae1 ae2 n1 n2 S_evaluate SS_evaluate.
    rewrite -> fold_unfold_evaluate_Plus.
    rewrite -> S_evaluate.
    rewrite -> SS_evaluate.
    reflexivity. }
  split.
  { intros ae1 ae2 s1 S_evaluate.
    rewrite -> fold_unfold_evaluate_Minus.
    rewrite -> S_evaluate.
    reflexivity. }
  { split.
    { intros ae1 ae2 n1 s2 S_evaluate SS_evaluate.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> S_evaluate.
      rewrite -> SS_evaluate.
      reflexivity. }
    split.
    { intros ae1 ae2 n1 n2 S_evaluate SS_evaluate.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> S_evaluate.
      rewrite -> SS_evaluate.
      intro H_true.
      rewrite -> H_true.
      reflexivity. }
    intros ae1 ae2 n1 n2 S_evaluate SS_evaluate.
    rewrite -> fold_unfold_evaluate_Minus.
    rewrite -> S_evaluate.
    rewrite -> SS_evaluate.
    intro H_false.
    rewrite -> H_false.
    reflexivity. }
Qed.
        
Definition interpret (sp : source_program) : expressible_value :=
  match sp with
    Source_program ae =>
      evaluate ae
  end.

Definition test_interpret candidate :=
  (eqb_expressible_value (candidate (Source_program (Literal 10))) (Expressible_nat 10))
  && (eqb_expressible_value (candidate (Source_program (Plus (Literal 1) (Literal 10)))) (Expressible_nat 11))
  && (eqb_expressible_value (candidate (Source_program (Plus (Literal 1) (Minus (Literal 9) (Literal 10))))) (Expressible_msg "numerical underflow: -1"))
  && (eqb_expressible_value (candidate (Source_program (Plus (Minus (Literal 9) (Literal 10)) (Literal 1)))) (Expressible_msg "numerical underflow: -1"))
  && (eqb_expressible_value (candidate (Source_program (Minus (Literal 10) (Literal 1)))) (Expressible_nat 9))
  && (eqb_expressible_value (candidate (Source_program (Minus (Literal 1) (Literal 10)))) (Expressible_msg "numerical underflow: -9"))
  && (eqb_expressible_value (candidate (Source_program (Minus (Literal 1) (Minus (Literal 9) (Literal 10))))) (Expressible_msg "numerical underflow: -1"))
  && (eqb_expressible_value (candidate (Source_program (Minus (Minus (Literal 9) (Literal 10)) (Literal 1)))) (Expressible_msg "numerical underflow: -1")).

Compute (test_interpret interpret = true).

Theorem there_is_at_most_one_evaluate_function :
  forall (evaluate0 evaluate1 : arithmetic_expression -> expressible_value),
    specification_of_evaluate evaluate0 ->
    specification_of_evaluate evaluate1 ->
    forall ae : arithmetic_expression,
      evaluate0 ae = evaluate1 ae.
Proof.
  intros evaluate1 evaluate2.
  intros S_evaluate1 S_evaluate2.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  + unfold specification_of_evaluate in S_evaluate1.
    destruct S_evaluate1 as [fold_unfold_evaluate1_Literal _].
    unfold specification_of_evaluate in S_evaluate2.
    destruct S_evaluate2 as [fold_unfold_evaluate2_Literal _].
    rewrite -> (fold_unfold_evaluate1_Literal n).
    rewrite -> (fold_unfold_evaluate2_Literal n).
    reflexivity.
  + case (evaluate1 ae1) as [n11 | s11] eqn:E1_ae1;
      case (evaluate2 ae1) as [n21 | s21] eqn:E2_ae1;
      case (evaluate1 ae2) as [n12 | s12] eqn:E1_ae2;
      case (evaluate2 ae2) as [n22 | s22] eqn:E2_ae2.
    ++ destruct S_evaluate1 as [_ [[_ [_ fold_unfold_evaluate1_Plus]] _]].
       destruct S_evaluate2 as [_ [[_ [_ fold_unfold_evaluate2_Plus]] _]].
       Check (fold_unfold_evaluate1_Plus ae1 ae2 n11 n12).
       Check (fold_unfold_evaluate1_Plus ae1 ae2 n11 n12 E1_ae1 E1_ae2).
       rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 n11 n12 E1_ae1 E1_ae2).
       Check (fold_unfold_evaluate2_Plus ae1 ae2).
       Check (fold_unfold_evaluate2_Plus ae1 ae2 n21 n22).
       Check (fold_unfold_evaluate2_Plus ae1 ae2 n21 n22 E2_ae1 E2_ae2).
       rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 n21 n22 E2_ae1 E2_ae2).
       injection IHae1 as H_eq_n11_n21.
       rewrite -> H_eq_n11_n21.
       injection IHae2 as H_eq_n12_n22.
       rewrite -> H_eq_n12_n22.
       reflexivity.
    ++ discriminate IHae2.
    ++ discriminate IHae2.
    ++ unfold specification_of_evaluate in S_evaluate1.
       destruct S_evaluate1 as [_ [[_ [fold_unfold_evaluate1_Plus _]] _]].
       destruct S_evaluate2 as [_ [[_ [fold_unfold_evaluate2_Plus _]] _]].
       Check (fold_unfold_evaluate1_Plus ae1 ae2 n11 s12 E1_ae1 E1_ae2).
       rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 n11 s12 E1_ae1 E1_ae2).
       Check (fold_unfold_evaluate2_Plus ae1 ae2 n21 s22 E2_ae1 E2_ae2).
       rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 n21 s22 E2_ae1 E2_ae2).
       injection IHae2 as H_eq_s12_s22.
       Check (f_equal Expressible_msg H_eq_s12_s22).
       exact (f_equal Expressible_msg H_eq_s12_s22).
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ unfold specification_of_evaluate in S_evaluate1.
       destruct S_evaluate1 as [_ [[fold_unfold_evaluate1_Plus _] _]].
       destruct S_evaluate2 as [_ [[fold_unfold_evaluate2_Plus _] _]].
       Check (fold_unfold_evaluate1_Plus ae1 ae2 s11 E1_ae1).
       rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 s11 E1_ae1).
       Check (fold_unfold_evaluate2_Plus ae1 ae2 s21 E2_ae1).
       rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 s21 E2_ae1).
       injection IHae1 as H_eq_s11_s21.
       rewrite -> H_eq_s11_s21.
       reflexivity.
    ++ discriminate IHae2.
    ++ discriminate IHae2.
    ++ unfold specification_of_evaluate in S_evaluate1.
       destruct S_evaluate1 as [_ [[fold_unfold_evaluate1_Plus _] _]].
       destruct S_evaluate2 as [_ [[fold_unfold_evaluate2_Plus _] _]].
       rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 s11 E1_ae1).
       rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 s21 E2_ae1).
       injection IHae1 as H_eq_s11_s21.
       rewrite -> H_eq_s11_s21.
       reflexivity.
  + case (evaluate1 ae1) as [n11 | s11] eqn:E1_ae1;
      case (evaluate2 ae1) as [n21 | s21] eqn:E2_ae1;
      case (evaluate1 ae2) as [n12 | s12] eqn:E1_ae2;
      case (evaluate2 ae2) as [n22 | s22] eqn:E2_ae2.
    ++ case (n11 <? n12) eqn: H_n11_lt_n12;
         case (n21 <? n22) eqn: H_n21_lt_n22.
       +++ destruct S_evaluate1 as [_ [_ [_ [_ [fold_unfold_evaluate1_Minus_lt _]]]]].
           destruct S_evaluate2 as [_ [_ [_ [_ [fold_unfold_evaluate2_Minus_lt _]]]]].
           Check (fold_unfold_evaluate1_Minus_lt ae1 ae2 n11 n12 E1_ae1 E1_ae2).
           Check (fold_unfold_evaluate1_Minus_lt ae1 ae2 n11 n12 E1_ae1 E1_ae2 H_n11_lt_n12).
           rewrite -> (fold_unfold_evaluate1_Minus_lt ae1 ae2 n11 n12 E1_ae1 E1_ae2 H_n11_lt_n12).
           rewrite -> (fold_unfold_evaluate2_Minus_lt ae1 ae2 n21 n22 E2_ae1 E2_ae2 H_n21_lt_n22).
           injection IHae1 as H_eq_n11_n21.
           rewrite -> H_eq_n11_n21.
           injection IHae2 as H_eq_n21_n22.
           rewrite -> H_eq_n21_n22.
           reflexivity.
       +++ injection IHae1 as H_eq_n11_n21.
           injection IHae2 as H_eq_n12_n22.
           rewrite -> H_eq_n11_n21 in H_n11_lt_n12.
           rewrite <- H_eq_n12_n22 in H_n21_lt_n22.
           rewrite -> H_n11_lt_n12 in H_n21_lt_n22.
           discriminate H_n21_lt_n22.
       +++ injection IHae1 as H_eq_n11_n21.
           injection IHae2 as H_eq_n12_n22.
           rewrite -> H_eq_n11_n21 in H_n11_lt_n12.
           rewrite <- H_eq_n12_n22 in H_n21_lt_n22.
           rewrite -> H_n11_lt_n12 in H_n21_lt_n22.
           discriminate H_n21_lt_n22.
       +++ destruct S_evaluate1 as [_ [_ [_ [_ [_ fold_unfold_evaluate1_Minus_gt]]]]].
           destruct S_evaluate2 as [_ [_ [_ [_ [_ fold_unfold_evaluate2_Minus_gt]]]]].
           Check (fold_unfold_evaluate1_Minus_gt ae1 ae2 n11 n12 E1_ae1 E1_ae2 H_n11_lt_n12).
           rewrite -> (fold_unfold_evaluate1_Minus_gt ae1 ae2 n11 n12 E1_ae1 E1_ae2 H_n11_lt_n12).
           rewrite -> (fold_unfold_evaluate2_Minus_gt ae1 ae2 n21 n22 E2_ae1 E2_ae2 H_n21_lt_n22).
           injection IHae1 as H_eq_n11_n21.
           injection IHae2 as H_eq_n12_n22.
           rewrite -> H_eq_n11_n21.
           rewrite -> H_eq_n12_n22.
           reflexivity.
    ++ discriminate IHae2.
    ++ discriminate IHae2.
    ++ destruct S_evaluate1 as [_ [_ [_ [fold_unfold_evaluate1_Minus _]]]].
       destruct S_evaluate2 as [_ [_ [_ [fold_unfold_evaluate2_Minus _]]]].
       Check (fold_unfold_evaluate1_Minus ae1 ae2 n11 s12 E1_ae1 E1_ae2).
       rewrite -> (fold_unfold_evaluate1_Minus ae1 ae2 n11 s12 E1_ae1 E1_ae2).
       rewrite -> (fold_unfold_evaluate2_Minus ae1 ae2 n21 s22 E2_ae1 E2_ae2).
       injection IHae2 as H_eq_s12_s22.
       rewrite -> H_eq_s12_s22.
       reflexivity.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ discriminate IHae1.
    ++ destruct S_evaluate1 as [_ [_ [fold_unfold_evaluate1_Minus _]]].
       destruct S_evaluate2 as [_ [_ [fold_unfold_evaluate2_Minus _]]].
       Check (fold_unfold_evaluate1_Minus ae1 ae2 s11 E1_ae1).
       rewrite -> (fold_unfold_evaluate1_Minus ae1 ae2 s11 E1_ae1).
       rewrite -> (fold_unfold_evaluate2_Minus ae1 ae2 s21 E2_ae1).
       injection IHae1 as H_eq_s11_s21.
       rewrite -> H_eq_s11_s21.
       reflexivity.
    ++ discriminate IHae2.
    ++ discriminate IHae2.
    ++ destruct S_evaluate1 as [_ [_ [fold_unfold_evaluate1_Minus _]]].
       destruct S_evaluate2 as [_ [_ [fold_unfold_evaluate2_Minus _]]].
       Check (fold_unfold_evaluate1_Minus ae1 ae2 s11 E1_ae1).
       rewrite -> (fold_unfold_evaluate1_Minus ae1 ae2 s11 E1_ae1).
       rewrite -> (fold_unfold_evaluate2_Minus ae1 ae2 s21 E2_ae1).
       injection IHae1 as H_eq_s11_s21.
       rewrite -> H_eq_s11_s21.
       reflexivity.
Qed.
  
Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros eval S_eval ae.
  Check (there_is_at_most_one_evaluate_function evaluate eval evaluate_satisfies_the_specification_of_evaluate S_eval ae).
  exact (there_is_at_most_one_evaluate_function evaluate eval evaluate_satisfies_the_specification_of_evaluate S_eval ae).
Qed.

Theorem there_is_at_most_one_interpret_function :
  forall interpret1 interpret2 : source_program -> expressible_value,
    specification_of_interpret interpret1 ->
    specification_of_interpret interpret2 ->
    forall sp : source_program,
      interpret1 sp = interpret2 sp.
Proof.
  intros interpret1 interpret2 S_interpret1 S_interpret2.
  unfold specification_of_interpret in S_interpret1.
  unfold specification_of_interpret in S_interpret2.
  case sp as [ae].
  Check (S_interpret1 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  rewrite -> (S_interpret1 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  rewrite -> (S_interpret2 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  reflexivity.
Qed.
  
(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

Definition eqb_bci (bci1 bci2 : byte_code_instruction) : bool :=
  match bci1 with
  | PUSH n =>
      match bci2 with
      | PUSH m =>
          eqb_nat n m
      | ADD =>
          false
      | SUB =>
          false
      end
  | ADD =>
      match bci2 with
      | PUSH m =>
          false
      | ADD =>
          true
      | SUB =>
          false
      end
  | SUB =>
      match bci2 with
      | PUSH m =>
          false
      | ADD =>
          false
      | SUB =>
          true
      end
  end.

Fixpoint eqb_bci_list (bci1s bci2s : list byte_code_instruction) : bool :=
  match bci1s with
  | nil =>
    match bci2s with
    | nil =>
      true
    | bci2 :: bci2s' =>
        false
    end
  | bci1 :: bci1s' =>
    match bci2s with
    | nil =>
        false
    | bci2 :: bci2s' =>
        eqb_bci bci1 bci2 && eqb_bci_list bci1s' bci2s'
    end
  end.

(* Target programs: *)

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

Definition eqb_tp (tp1 tp2 : target_program) : bool :=
  match tp1 with
  | Target_program bci1s =>
      match tp2 with
      | Target_program bci2s =>
          eqb_bci_list bci1s bci2s
      end
  end.

(* Data stack: *)

Definition data_stack := list nat.

Definition eqb_data_stack (ds1 ds2 : list nat) : bool :=
  eqb_list nat eqb_nat ds1 ds2.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
  OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition eqb_result_of_decoding_and_execution (res1 res2 : result_of_decoding_and_execution) : bool :=
  match res1 with
  | OK ds1 =>
      match res2 with
      | OK ds2 =>
          eqb_data_stack ds1 ds2
      | KO msg2 =>
          false
      end
  | KO msg1 =>
      match res2 with
      | OK ds2 =>
          false
      | KO msg2 =>
          eqb_string msg1 msg2
      end
  end.

(* Informal specification of decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution

 * given a nat n and a data_stack ds,
   evaluating
     decode_execute (PUSH n) ds
   should successfully return a stack where n is pushed on ds

 * given a data stack ds that contains at least 2 nats,
   evaluating
     decode_execute ADD ds
   should
   - pop these 2 nats off the data stack,
   - add them,
   - push the result of the addition on the data stack, and
   - successfully return the resulting data stack

   if the data stack does not contain at least 2 nats,
   evaluating
     decode_execute ADD ds
   should return the error message "ADD: stack underflow"

 * given a data stack ds that contains at least 2 nats,
   evaluating
     decode_execute SUB ds
   should
   - pop these 2 nats off the data stack,
   - subtract one from the other if the result is non-negative,
   - push the result of the subtraction on the data stack, and
   - successfully return the resulting data stack

   if the data stack does not contain at least 2 nats
   evaluating
     decode_execute SUB ds
   should return the error message "SUB: stack underflow"

   if the data stack contain at least 2 nats
   and
   if subtracting one nat from the other gives a negative result, 
   evaluating
     decode_execute SUB ds
   should return the same error message as the evaluator
*)

(* Task 2:
   implement decode_execute
*)

Definition decode_execute (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
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
              then KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else OK ((n1 - n2) :: ds'')
          end
      end
  end.

Definition test_decode_execute candidate :=
  (eqb_result_of_decoding_and_execution (candidate (PUSH 4) (3 :: 2 :: 1 :: nil)) (OK (4 :: 3 :: 2 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate ADD nil) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate ADD (1 :: nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate ADD (2 :: 1 :: nil)) (OK (3 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate ADD (3 :: 2 :: 1 :: nil)) (OK (5 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate SUB nil) (KO "SUB: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate SUB (1 :: nil)) (KO "SUB: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate SUB (2 :: 1 :: nil)) (KO "numerical underflow: -1"))
  && (eqb_result_of_decoding_and_execution (candidate SUB (1 :: 2 :: nil)) (OK (1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate SUB (1 :: 2 :: 3 :: 4 :: nil)) (OK (1 :: 3 :: 4 :: nil))).

Compute (test_decode_execute decode_execute = true).

(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall ds : data_stack,
      fetch_decode_execute_loop nil ds = OK ds)
  /\
  (forall (bci : byte_code_instruction)
          (bcis' : list byte_code_instruction)
          (ds ds' : data_stack),
      decode_execute bci ds = OK ds' ->
      fetch_decode_execute_loop (bci :: bcis') ds =
      fetch_decode_execute_loop bcis' ds')
  /\
  (forall (bci : byte_code_instruction)
          (bcis' : list byte_code_instruction)
          (ds : data_stack)
          (s : string),
      decode_execute bci ds = KO s ->
      fetch_decode_execute_loop (bci :: bcis') ds =
      KO s).

(* Task 3:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Theorem there_is_at_most_one_fetch_decode_execute_loop :
  forall
    (fdel1 fdel2 : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution)
    (bcis : list byte_code_instruction)
    (ds : data_stack),
    specification_of_fetch_decode_execute_loop fdel1 ->
    specification_of_fetch_decode_execute_loop fdel2 ->
    fdel1 bcis ds = fdel2 bcis ds.
Proof.
  intros fdel1 fdel2 bcis.
  induction bcis as [ | bci bcis' IHbcis' ]; intro ds.
  + unfold specification_of_fetch_decode_execute_loop.
    intros S_fdel1 S_fdel2.
    destruct S_fdel1 as [H_fdel1_nil_OK _].
    destruct S_fdel2 as [H_fdel2_nil_OK _].
    rewrite -> H_fdel1_nil_OK.
    rewrite -> H_fdel2_nil_OK.
    reflexivity.
  + intros S_fdel1 S_fdel2.
    assert (H_fdel1 := S_fdel1).
    assert (H_fdel2 := S_fdel2).
    unfold specification_of_fetch_decode_execute_loop in H_fdel1.
    unfold specification_of_fetch_decode_execute_loop in H_fdel2.
    destruct H_fdel1 as [_ [H_fdel1_OK H_fdel1_KO]].
    destruct H_fdel2 as [_ [H_fdel2_OK H_fdel2_KO]].
    Check (decode_execute bci ds).
    case (decode_execute bci ds) as [OK_ds | KO_s] eqn: H_de_OK_ds.
   { Check (H_fdel1_OK bci bcis' ds).
       Check (H_fdel1_OK bci bcis' ds OK_ds H_de_OK_ds).
       rewrite -> (H_fdel1_OK bci bcis' ds OK_ds H_de_OK_ds).
       rewrite -> (H_fdel2_OK bci bcis' ds OK_ds H_de_OK_ds).
       Check (IHbcis' OK_ds S_fdel1 S_fdel2).
       exact (IHbcis' OK_ds S_fdel1 S_fdel2). }
   { Check (H_fdel1_KO bci bcis' ds).
       Check (H_fdel1_KO bci bcis' ds KO_s H_de_OK_ds).
       rewrite -> (H_fdel1_KO bci bcis' ds KO_s H_de_OK_ds).
       rewrite -> (H_fdel2_KO bci bcis' ds KO_s H_de_OK_ds).
       reflexivity. }
Qed.

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | nil =>
      OK ds
  | bci :: bcis' =>
      match decode_execute bci ds with
      | OK ds' =>
          fetch_decode_execute_loop bcis' ds'
      | KO s =>
          KO s
      end
  end.

Definition test_fetch_decode_execute_loop candidate :=
  (eqb_result_of_decoding_and_execution (candidate nil (3 :: 2 :: 1 :: nil)) (OK (3 :: 2 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate ((PUSH 3) :: (PUSH 4) :: nil) (2 :: 1 :: nil)) (OK (4 :: 3 :: 2 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (ADD :: (PUSH 2) :: nil) nil) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD :: (PUSH 2) :: nil) (1 :: nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (SUB :: (PUSH 2) :: nil) (1 :: nil)) (KO "SUB: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (SUB :: (PUSH 3) :: nil) (2 :: 1 :: nil)) (KO "numerical underflow: -1"))
  && (eqb_result_of_decoding_and_execution (candidate (SUB :: (PUSH 10) :: nil) (1 :: 2 :: nil)) (OK (10 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB :: (PUSH 10) :: nil) (1 :: 2 :: 100 :: nil)) (OK (10 :: 1 :: 100 :: nil))).

Compute (test_fetch_decode_execute_loop fetch_decode_execute_loop = true).

Lemma fold_unfold_fetch_decode_execute_nil:
  forall (ds : data_stack),
    fetch_decode_execute_loop nil ds =
      OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_cons:
  forall (ds : data_stack)
         (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction),
    fetch_decode_execute_loop (bci :: bcis') ds =
      match decode_execute bci ds with
      | OK ds' =>
          fetch_decode_execute_loop bcis' ds'
      | KO s =>
          KO s
      end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Theorem fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  split.
  { exact fold_unfold_fetch_decode_execute_nil. }
  split.
    { intros bci bcis' ds ds' S_decode_execute_loop.
      rewrite -> fold_unfold_fetch_decode_execute_cons.
      rewrite -> S_decode_execute_loop.
      reflexivity. }
    intros bci bcis' ds s S_decode_execute_loop.
    rewrite -> fold_unfold_fetch_decode_execute_cons.
    rewrite -> S_decode_execute_loop.
    reflexivity. 
Qed.

(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bci1s and bci2s,
   and for any data stack ds,
   executing the concatenation of bci1s and bci2s (i.e., bci1s ++ bci2s) with ds
   gives the same result as
   (1) executing bci1s with ds, and then
   (2) executing bci2s with the resulting data stack, if there exists one.
*)

Theorem about_fetch_decode_execute_loop :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds : data_stack),
    (forall ds1 : data_stack,
        fetch_decode_execute_loop bci1s ds = OK ds1 ->
        fetch_decode_execute_loop (bci1s ++ bci2s) ds =
          fetch_decode_execute_loop bci2s ds1)
    /\
      (forall s : string,
          fetch_decode_execute_loop bci1s ds = KO s ->
          fetch_decode_execute_loop (bci1s ++ bci2s) ds =
            KO s).
Proof.
  intros bci1s bci2s.
  induction bci1s as [ | [n | | ]  bci1s' IHbci1s']; intro ds.
  + split.
    ++ intros ds' H_ds_inject.
       rewrite -> fold_unfold_fetch_decode_execute_nil in H_ds_inject.
       injection H_ds_inject as H_eq_ds_ds'.
       rewrite -> H_eq_ds_ds'.
       rewrite -> fold_unfold_list_append_nil.
       reflexivity.
    ++ intros s H_absurd.
       rewrite -> fold_unfold_fetch_decode_execute_nil in H_absurd.
       discriminate H_absurd.
  + split.
    ++ intros ds' H_fdel_cons_OK.
       rewrite -> fold_unfold_list_append_cons.
       Check (IHbci1s' (n :: ds)).
       destruct (IHbci1s' (n :: ds)) as [IHbci1s'_OK _].
       rewrite -> fold_unfold_fetch_decode_execute_cons.
       unfold decode_execute.
       Check (IHbci1s'_OK ds' H_fdel_cons_OK).
       exact (IHbci1s'_OK ds' H_fdel_cons_OK).
    ++ intros s H_fdel_cons_KO.
       rewrite -> fold_unfold_list_append_cons.
       Check (IHbci1s' (n :: ds)).
       destruct (IHbci1s' (n :: ds)) as [_ IHbci1s'_KO].
       rewrite -> fold_unfold_fetch_decode_execute_cons.
       unfold decode_execute.
       Check (IHbci1s'_KO s H_fdel_cons_KO).
       exact (IHbci1s'_KO s H_fdel_cons_KO).
  + split.
    ++ intros ds1 H_fdel_cons_OK.
       rewrite -> fold_unfold_list_append_cons.
       rewrite -> fold_unfold_fetch_decode_execute_cons.
       unfold decode_execute.
       case ds as [ | n2 ds'].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_OK.
         unfold decode_execute in H_fdel_cons_OK.
         discriminate H_fdel_cons_OK. }
       case ds' as [ | n1 ds''].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_OK.
         unfold decode_execute in H_fdel_cons_OK.
         discriminate H_fdel_cons_OK. }
       rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_OK.
       unfold decode_execute in H_fdel_cons_OK.
       Check (IHbci1s' (n1 + n2 :: ds'')).
       destruct (IHbci1s' (n1 + n2 :: ds'')) as [IHbci1s'_OK _].
       Check (IHbci1s'_OK ds1).
       Check (IHbci1s'_OK ds1 H_fdel_cons_OK).
       exact (IHbci1s'_OK ds1 H_fdel_cons_OK).
    ++ intros s H_fdel_cons_KO.
       rewrite -> fold_unfold_list_append_cons.
       rewrite -> fold_unfold_fetch_decode_execute_cons.
       unfold decode_execute.
       case ds as [ | n2 ds'].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         exact H_fdel_cons_KO. }
       case ds' as [ | n1 ds''].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         exact H_fdel_cons_KO. }
       rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
       unfold decode_execute in H_fdel_cons_KO.
       Check (IHbci1s' (n1 + n2 :: ds'')).
       destruct (IHbci1s' (n1 + n2 :: ds'')) as [_ IHbci1s'_KO].
       Check (IHbci1s'_KO s).
       Check (IHbci1s'_KO s H_fdel_cons_KO).
       exact (IHbci1s'_KO s H_fdel_cons_KO).
  + split.
    ++ intros ds1 H_fdel_cons_KO.
       rewrite -> fold_unfold_list_append_cons.
       rewrite -> fold_unfold_fetch_decode_execute_cons.
       unfold decode_execute.
       case ds as [ | n2 ds'].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         discriminate H_fdel_cons_KO. }
       case ds' as [ | n1 ds''].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         discriminate H_fdel_cons_KO. }
       case (n1 <? n2) eqn: H_n1_lt_n2.
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         rewrite -> H_n1_lt_n2 in H_fdel_cons_KO.
         discriminate H_fdel_cons_KO. }
       rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
       unfold decode_execute in H_fdel_cons_KO.
       rewrite -> H_n1_lt_n2 in H_fdel_cons_KO.
       Check (IHbci1s' (n1 - n2 :: ds'')).
       destruct (IHbci1s' (n1 - n2 :: ds'')) as [IHbci1s'_OK _].
       Check (IHbci1s'_OK ds1 H_fdel_cons_KO).
       exact (IHbci1s'_OK ds1 H_fdel_cons_KO).
    ++ intros s H_fdel_cons_KO.
       rewrite -> fold_unfold_list_append_cons.
       rewrite -> fold_unfold_fetch_decode_execute_cons.
       unfold decode_execute.
       case ds as [ | n2 ds'].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         exact H_fdel_cons_KO. }
       case ds' as [ | n1 ds''].
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         exact H_fdel_cons_KO. }
       case (n1 <? n2) eqn: H_n1_lt_n2.
       { rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
         unfold decode_execute in H_fdel_cons_KO.
         rewrite -> H_n1_lt_n2 in H_fdel_cons_KO.
         exact H_fdel_cons_KO. }
       rewrite -> fold_unfold_fetch_decode_execute_cons in H_fdel_cons_KO.
       unfold decode_execute in H_fdel_cons_KO.
       rewrite -> H_n1_lt_n2 in H_fdel_cons_KO.
       Check (IHbci1s' (n1 - n2 :: ds'')).
       destruct (IHbci1s' (n1 - n2 :: ds'')) as [_ IHbci1s'_KO].
       Check (IHbci1s'_KO s H_fdel_cons_KO).
       exact (IHbci1s'_KO s H_fdel_cons_KO).
Qed.

(* ********** *)
      
Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).

(* Task 5:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Theorem there_is_at_most_one_run :
  forall (run1 run2 : target_program -> expressible_value),
    specification_of_run run1 ->
    specification_of_run run2 ->
    forall bcis : list byte_code_instruction,
      run1 (Target_program bcis) = run2 (Target_program bcis).
Proof.
  intros run1 run2 S_run1 S_run2 bcis.
  induction bcis as [ | bci bcis' IHbcis' ].
  + unfold specification_of_run in S_run1.
    unfold specification_of_run in S_run2.
    Check (S_run1 fetch_decode_execute_loop).
    Check (S_run1 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop).
    destruct (S_run1 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop) as [fold_unfold_run1_OK_nil _].
    destruct (S_run2 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop) as [fold_unfold_run2_OK_nil _].
    Check (fold_unfold_run1_OK_nil nil).
    Check (fold_unfold_run1_OK_nil nil (fold_unfold_fetch_decode_execute_nil nil)).
    rewrite -> (fold_unfold_run1_OK_nil nil (fold_unfold_fetch_decode_execute_nil nil)).
    Check (fold_unfold_run2_OK_nil nil (fold_unfold_fetch_decode_execute_nil nil)).
    rewrite -> (fold_unfold_run2_OK_nil nil (fold_unfold_fetch_decode_execute_nil nil)).
    reflexivity.
  + unfold specification_of_run in S_run1.
    unfold specification_of_run in S_run2.
    destruct (S_run1 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop) as [fold_unfold_run1_OK_nil [fold_unfold_run1_OK [fold_unfold_run1_OK_too_many fold_unfold_run1_KO]]].
    destruct (S_run2 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop) as [fold_unfold_run2_OK_nil [fold_unfold_run2_OK [fold_unfold_run2_OK_too_many fold_unfold_run2_KO]]].
    Check (Target_program (bci :: bcis')).
    Check (fetch_decode_execute_loop (bci :: bcis') nil).
    case (fetch_decode_execute_loop (bci :: bcis') nil) as [[ | d [ | d' ds'']] | s] eqn: res_of_fdel.
    { Check (fold_unfold_run1_OK_nil (bci :: bcis') res_of_fdel).
       rewrite -> (fold_unfold_run1_OK_nil (bci :: bcis') res_of_fdel).
       Check (fold_unfold_run2_OK_nil (bci :: bcis') res_of_fdel).
       rewrite -> (fold_unfold_run2_OK_nil (bci :: bcis') res_of_fdel).
       reflexivity. }
    { Check (fold_unfold_run1_OK (bci :: bcis') d res_of_fdel).
       rewrite -> (fold_unfold_run1_OK (bci :: bcis') d res_of_fdel).
       Check (fold_unfold_run2_OK (bci :: bcis') d res_of_fdel).
       rewrite -> (fold_unfold_run2_OK (bci :: bcis') d res_of_fdel).
       reflexivity. }
    { Check (fold_unfold_run1_OK_too_many (bci :: bcis') d d' ds'' res_of_fdel).
       rewrite -> (fold_unfold_run1_OK_too_many (bci :: bcis') d d' ds'' res_of_fdel).
       Check (fold_unfold_run2_OK_too_many (bci :: bcis') d d' ds'' res_of_fdel).
       rewrite -> (fold_unfold_run2_OK_too_many (bci :: bcis') d d' ds'' res_of_fdel).
       reflexivity. }
    { Check (fold_unfold_run1_KO (bci :: bcis') s res_of_fdel).
       rewrite -> (fold_unfold_run1_KO (bci :: bcis') s res_of_fdel).
       Check (fold_unfold_run2_KO (bci :: bcis') s res_of_fdel).
       rewrite -> (fold_unfold_run2_KO (bci :: bcis') s res_of_fdel).
       reflexivity. }
Qed.

Definition run (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
      match fetch_decode_execute_loop bcis nil with
      | OK nil =>
          Expressible_msg "no result on the data stack"
      | OK (n :: nil) =>
          Expressible_nat n
      | OK (n :: n' :: ds'') =>
          Expressible_msg "too many results on the data stack"
      | KO s =>
          Expressible_msg s
      end
  end.

Definition test_run candidate :=
  (eqb_expressible_value (candidate (Target_program nil)) (Expressible_msg "no result on the data stack"))
  && (eqb_expressible_value (candidate (Target_program (PUSH 4 :: nil))) (Expressible_nat 4))
  && (eqb_expressible_value (candidate (Target_program (PUSH 4 :: PUSH 3 :: PUSH 2 :: nil))) (Expressible_msg "too many results on the data stack"))
  && (eqb_expressible_value (candidate (Target_program (PUSH 3 :: PUSH 2 :: nil))) (Expressible_msg "too many results on the data stack"))
  && (eqb_expressible_value (candidate (Target_program (ADD :: PUSH 4 :: nil))) (Expressible_msg "ADD: stack underflow"))
  && (eqb_expressible_value (candidate (Target_program (SUB :: PUSH 4 :: nil))) (Expressible_msg "SUB: stack underflow"))
  && (eqb_expressible_value (candidate (Target_program (PUSH 4 :: PUSH 5 :: SUB :: nil))) (Expressible_msg "numerical underflow: -1")).

Compute (test_run run = true).

Theorem run_satisfies_the_specification_of_run :
  specification_of_run run.
Proof.
  unfold specification_of_run.
  intros fdel S_fdel.
  split.
  { intro bcis.
    Check (there_is_at_most_one_fetch_decode_execute_loop).
    Check (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel).
    Check (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis).
    Check (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis nil).
    Check (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis nil fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop).
    Check (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis nil fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop S_fdel).
    rewrite <- (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis nil fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop S_fdel).
    intro H_fdel_bcis_OK_nil.
    unfold run.
    rewrite -> H_fdel_bcis_OK_nil.
    reflexivity. }
  split.
  { intros bcis n.
    rewrite <- (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis nil fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop S_fdel).
    intro H_fdel_bcis_OK_n.
    unfold run.
    rewrite -> H_fdel_bcis_OK_n.
    reflexivity. }
  split.
  { intros bcis n n' ds'.
    rewrite <- (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis nil fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop S_fdel).
    intro H_fdel_OK_n_n'.
    unfold run.
    rewrite -> H_fdel_OK_n_n'.
    reflexivity. }
  intros bcis s.
  rewrite <- (there_is_at_most_one_fetch_decode_execute_loop fetch_decode_execute_loop fdel bcis nil fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop S_fdel).
  intro H_fdel_KO_s.
  unfold run.
  rewrite -> H_fdel_KO_s.
  reflexivity.
Qed.
   
(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

(* Task 6:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
 *)

Theorem there_is_at_most_one_compile_aux_function:
  forall (compile_aux1 compile_aux2 : arithmetic_expression -> list byte_code_instruction),
    specification_of_compile_aux compile_aux1 ->
    specification_of_compile_aux compile_aux2 ->
    forall (ae : arithmetic_expression),
      compile_aux1 ae = compile_aux2 ae. 
Proof.
  intros compile_aux1 compile_aux2 S_compile_aux1 S_compile_aux2.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - unfold specification_of_compile_aux in S_compile_aux1.
    destruct S_compile_aux1 as [fold_unfold_compile_aux1_Literal _].
    unfold specification_of_compile_aux in S_compile_aux2.
    destruct S_compile_aux2 as [fold_unfold_compile_aux2_Literal _].
    rewrite -> (fold_unfold_compile_aux1_Literal n).
    rewrite -> (fold_unfold_compile_aux2_Literal n).
    reflexivity.
  - assert (S_compile_aux1_tmp := S_compile_aux1).
    assert (S_compile_aux2_tmp := S_compile_aux2).
    unfold specification_of_compile_aux in S_compile_aux1_tmp.
    destruct S_compile_aux1_tmp as [_ [fold_unfold_compile_aux1_Plus _]].
    unfold specification_of_compile_aux in S_compile_aux2_tmp.
    destruct S_compile_aux2_tmp as [_ [fold_unfold_compile_aux2_Plus _]].
    Check (fold_unfold_compile_aux1_Plus ae1 ae2).
    rewrite -> (fold_unfold_compile_aux1_Plus ae1 ae2).
    rewrite -> (fold_unfold_compile_aux2_Plus ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - assert (S_compile_aux1_tmp := S_compile_aux1).
    assert (S_compile_aux2_tmp := S_compile_aux2).
    unfold specification_of_compile_aux in S_compile_aux1_tmp.
    destruct S_compile_aux1_tmp as [_ [_ fold_unfold_compile_aux1_Minus]].
    unfold specification_of_compile_aux in S_compile_aux2_tmp.
    destruct S_compile_aux2_tmp as [_ [_ fold_unfold_compile_aux2_Minus]].
    Check (fold_unfold_compile_aux1_Minus ae1 ae2).
    rewrite -> (fold_unfold_compile_aux1_Minus ae1 ae2).
    rewrite -> (fold_unfold_compile_aux2_Minus ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
      PUSH n :: nil
  | Plus ae1 ae2 =>
      (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
      (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)
  end.

Definition test_compile_aux candidate :=
  (eqb_bci_list (candidate (Literal 1)) (PUSH 1 :: nil))
  && (eqb_bci_list (candidate (Plus (Literal 1) (Literal 1))) (PUSH 1 :: PUSH 1 :: ADD :: nil))
  && (eqb_bci_list (candidate (Plus (Plus (Literal 1) (Literal 1)) (Literal 1))) (PUSH 1:: PUSH 1 :: ADD :: PUSH 1 :: ADD :: nil))
  && (eqb_bci_list (candidate (Plus (Literal 1) (Plus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: PUSH 1 :: ADD :: ADD :: nil))
  && (eqb_bci_list (candidate (Plus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: ADD :: PUSH 1 :: PUSH 1 :: ADD :: ADD :: nil))
  && (eqb_bci_list (candidate (Plus (Literal 1) (Minus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: PUSH 1 :: SUB :: ADD :: nil))
  && (eqb_bci_list (candidate (Plus (Minus (Literal 1) (Literal 1)) (Literal 1))) (PUSH 1 :: PUSH 1 :: SUB :: PUSH 1 :: ADD :: nil))
  && (eqb_bci_list (candidate (Plus (Minus (Literal 1) (Literal 1)) (Minus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: SUB :: PUSH 1 :: PUSH 1 :: SUB :: ADD :: nil))
  && (eqb_bci_list (candidate (Minus (Literal 1) (Plus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: PUSH 1 :: ADD :: SUB :: nil))
  && (eqb_bci_list (candidate (Minus (Plus (Literal 1) (Literal 1)) (Literal 1))) (PUSH 1 :: PUSH 1 :: ADD :: PUSH 1 :: SUB :: nil))
  && (eqb_bci_list (candidate (Minus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: ADD :: PUSH 1 :: PUSH 1 :: ADD :: SUB :: nil))
  && (eqb_bci_list (candidate (Minus (Literal 1) (Literal 1))) (PUSH 1 :: PUSH 1 :: SUB :: nil))
  && (eqb_bci_list (candidate (Minus (Minus (Literal 1) (Literal 1)) (Literal 1))) (PUSH 1:: PUSH 1 :: SUB :: PUSH 1 :: SUB :: nil))
  && (eqb_bci_list (candidate (Minus (Literal 1) (Minus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: PUSH 1 :: SUB :: SUB :: nil))
  && (eqb_bci_list (candidate (Minus (Minus (Literal 1) (Literal 1)) (Minus (Literal 1) (Literal 1)))) (PUSH 1 :: PUSH 1 :: SUB :: PUSH 1 :: PUSH 1 :: SUB :: SUB :: nil)).

Compute (test_compile_aux compile_aux).

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

Theorem compile_aux_satisfies_the_specification_of_compile_aux :
  specification_of_compile_aux compile_aux.
Proof.
  unfold specification_of_compile_aux.
  split.
  { intro n.
    rewrite -> fold_unfold_compile_aux_Literal.
    reflexivity. }
  split; intros ae1 ae2.
  { rewrite -> fold_unfold_compile_aux_Plus.
    reflexivity. }
  rewrite -> fold_unfold_compile_aux_Minus.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Theorem there_is_at_most_one_compile_function :
  forall (compile1 compile2 : source_program -> target_program),
    specification_of_compile compile1 ->
    specification_of_compile compile2 ->
    forall (ae : arithmetic_expression),
      compile1 (Source_program ae) = compile2 (Source_program ae).
Proof.
  intros compile1 compile2 S_compile1 S_compile2 ae.
  unfold specification_of_compile in S_compile1.
  Check (S_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  rewrite -> (S_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  unfold specification_of_compile in S_compile2.
  rewrite -> (S_compile2 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  reflexivity.
Qed.

Definition test_compile candidate :=
  (eqb_tp (candidate (Source_program (Literal 1))) (Target_program (PUSH 1 :: nil)))
  && (eqb_tp (candidate (Source_program (Plus (Literal 1) (Literal 1)))) (Target_program (PUSH 1 :: PUSH 1 :: ADD :: nil)))
  && (eqb_tp (candidate (Source_program (Plus (Plus (Literal 1) (Literal 1)) (Literal 1)))) (Target_program (PUSH 1 :: PUSH 1 :: ADD :: PUSH 1 :: ADD :: nil)))
  && (eqb_tp (candidate (Source_program (Plus (Literal 1) (Plus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: PUSH 1 :: ADD :: ADD :: nil)))
  && (eqb_tp (candidate (Source_program (Plus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: ADD :: PUSH 1 :: PUSH 1 :: ADD :: ADD :: nil)))
  && (eqb_tp (candidate (Source_program (Plus (Literal 1) (Minus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: PUSH 1 :: SUB :: ADD :: nil)))
  && (eqb_tp (candidate (Source_program (Plus (Minus (Literal 1) (Literal 1)) (Literal 1)))) (Target_program (PUSH 1 :: PUSH 1 :: SUB :: PUSH 1 :: ADD :: nil)))
  && (eqb_tp (candidate (Source_program (Plus (Minus (Literal 1) (Literal 1)) (Minus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: SUB :: PUSH 1 :: PUSH 1 :: SUB :: ADD :: nil)))
  && (eqb_tp (candidate (Source_program (Minus (Literal 1) (Plus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: PUSH 1 :: ADD :: SUB :: nil)))
  && (eqb_tp (candidate (Source_program (Minus (Plus (Literal 1) (Literal 1)) (Literal 1)))) (Target_program (PUSH 1 :: PUSH 1 :: ADD :: PUSH 1 :: SUB :: nil)))
  && (eqb_tp (candidate (Source_program (Minus (Plus (Literal 1) (Literal 1)) (Plus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: ADD :: PUSH 1 :: PUSH 1 :: ADD :: SUB :: nil)))
  && (eqb_tp (candidate (Source_program (Minus (Literal 1) (Literal 1)))) (Target_program (PUSH 1 :: PUSH 1 :: SUB :: nil)))
  && (eqb_tp (candidate (Source_program (Minus (Minus (Literal 1) (Literal 1)) (Literal 1)))) (Target_program (PUSH 1 :: PUSH 1 :: SUB :: PUSH 1 :: SUB :: nil)))
  && (eqb_tp (candidate (Source_program (Minus (Literal 1) (Minus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: PUSH 1 :: SUB :: SUB :: nil)))
  && (eqb_tp (candidate (Source_program (Minus (Minus (Literal 1) (Literal 1)) (Minus (Literal 1) (Literal 1))))) (Target_program (PUSH 1 :: PUSH 1 :: SUB :: PUSH 1 :: PUSH 1 :: SUB :: SUB :: nil))).

Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
      Target_program (compile_aux ae)
  end.

Compute (test_compile compile).

Theorem compile_satisfies_the_specification_of_compile :
  specification_of_compile compile.
Proof.
  unfold specification_of_compile, compile.
  intros compile_aux1 S_compile_aux1 ae.
  Check (there_is_at_most_one_compile_aux_function compile_aux compile_aux1 compile_aux_satisfies_the_specification_of_compile_aux S_compile_aux1 ae).
  rewrite -> (there_is_at_most_one_compile_aux_function compile_aux compile_aux1 compile_aux_satisfies_the_specification_of_compile_aux S_compile_aux1 ae).
  reflexivity.
Qed.

      
(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
*)

Fixpoint compile_acc_aux (ae : arithmetic_expression) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
  | Literal n =>
      PUSH n :: a
  | Plus ae1 ae2 =>
      compile_acc_aux ae1 (compile_acc_aux ae2 (ADD :: a))
  | Minus ae1 ae2 =>
      compile_acc_aux ae1 (compile_acc_aux ae2 (SUB :: a))
  end.

Lemma fold_unfold_compile_acc_aux_Literal :
  forall (n : nat)
         (a : list byte_code_instruction),
    compile_acc_aux (Literal n) a = PUSH n :: a.
Proof.
  fold_unfold_tactic compile_acc_aux.
Qed.

Lemma fold_unfold_compile_acc_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_acc_aux (Plus ae1 ae2) a = compile_acc_aux ae1 (compile_acc_aux ae2 (ADD :: a)).
Proof.
  fold_unfold_tactic compile_acc_aux.
Qed.

Lemma fold_unfold_compile_acc_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_acc_aux (Minus ae1 ae2) a = compile_acc_aux ae1 (compile_acc_aux ae2 (SUB :: a)).
Proof.
  fold_unfold_tactic compile_acc_aux.
Qed.

Definition compile_acc (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
      Target_program (compile_acc_aux ae nil)
  end.

Compute (test_compile compile_acc).

Lemma about_compile_acc_aux :
  forall (ae : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_acc_aux ae a = compile_acc_aux ae nil ++ a.
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro a.
  - rewrite -> 2 fold_unfold_compile_acc_aux_Literal.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - rewrite -> 2 fold_unfold_compile_acc_aux_Plus.
    rewrite -> (IHae2 (ADD :: a)).
    rewrite -> (IHae1 (compile_acc_aux ae2 nil ++ ADD :: a)).
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite -> (IHae1 (compile_acc_aux ae2 nil ++ ADD :: nil)).
    rewrite -> 2 list_append_is_associative.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - rewrite -> 2 fold_unfold_compile_acc_aux_Minus.
    rewrite -> (IHae2 (SUB :: a)).
    rewrite -> (IHae1 (compile_acc_aux ae2 nil ++ SUB :: a)).
    rewrite -> (IHae2 (SUB :: nil)).
    rewrite -> (IHae1 (compile_acc_aux ae2 nil ++ SUB :: nil)).
    rewrite -> 2 list_append_is_associative.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
Qed. 

Lemma about_compile_acc_aux' :
  forall (ae : arithmetic_expression)
         (a : list byte_code_instruction),
    make_Eureka_lemma (list byte_code_instruction) nil (@List.app byte_code_instruction) (compile_acc_aux ae) a.
Proof.
  unfold make_Eureka_lemma.
  exact about_compile_acc_aux.
Qed.
      
Lemma about_compile_acc_aux_and_compile_aux :
  forall ae : arithmetic_expression,
    compile_acc_aux ae nil = compile_aux ae.
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - rewrite -> fold_unfold_compile_acc_aux_Literal.
    rewrite -> fold_unfold_compile_aux_Literal.
    reflexivity.
  - rewrite -> fold_unfold_compile_acc_aux_Plus.
    rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> (about_compile_acc_aux' ae2 (ADD :: nil)).
    rewrite -> (about_compile_acc_aux' ae1 (compile_acc_aux ae2 nil ++ ADD :: nil)).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - rewrite -> fold_unfold_compile_acc_aux_Minus.
    rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> (about_compile_acc_aux' ae2 (SUB :: nil)).
    rewrite -> (about_compile_acc_aux' ae1 (compile_acc_aux ae2 nil ++ SUB :: nil)).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

Theorem compile_acc_satisfies_the_specification_of_compile :
  specification_of_compile compile_acc.
Proof.
  unfold specification_of_compile, compile_acc.
  intros compile_aux1 S_compile_aux1 ae.
  rewrite <- (there_is_at_most_one_compile_aux_function compile_aux compile_aux1 compile_aux_satisfies_the_specification_of_compile_aux S_compile_aux1 ae).
  rewrite -> (about_compile_acc_aux_and_compile_aux ae).
  reflexivity.
Qed.

Theorem compile_and_compile_acc_are_equivalent :
  forall sp : source_program,
    compile sp = compile_acc sp.
Proof.
  intros [ae].
  exact (there_is_at_most_one_compile_function compile compile_acc compile_satisfies_the_specification_of_compile compile_acc_satisfies_the_specification_of_compile ae).
Qed.
      
(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
*)

Lemma the_commuting_diagram_aux :
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
    rewrite -> fold_unfold_fetch_decode_execute_cons.
    unfold decode_execute.   
    rewrite -> fold_unfold_fetch_decode_execute_nil.
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
    destruct (about_fetch_decode_execute_loop (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae1_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (about_fetch_decode_execute_loop (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
      case (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      * destruct (IHae2 (n1 :: ds)) as [IHae2_OK IHae2_KO].
        rewrite -> (H_fdel_ae2_OK (n2 :: n1 :: ds) (IHae2_OK n2 (eq_refl (Expressible_nat n2)))).
        rewrite -> fold_unfold_fetch_decode_execute_cons.
        unfold decode_execute.
        rewrite -> fold_unfold_fetch_decode_execute_nil.
        injection H_n' as H_n1_n2.
        rewrite -> H_n1_n2.
        reflexivity.
      * discriminate H_n'.
    + discriminate H_n'.
  - intros s H_s.
    rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> fold_unfold_evaluate_Plus in H_s.
    destruct (about_fetch_decode_execute_loop (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae1_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (about_fetch_decode_execute_loop (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
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
    destruct (about_fetch_decode_execute_loop (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae2_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (about_fetch_decode_execute_loop (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
      case (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      * destruct (IHae2 (n1 :: ds)) as [IHae2_OK IHHae2_KO].
        case (n1 <? n2) eqn: H_n1_lt_n2.
        { discriminate H_n'. }
        rewrite -> (H_fdel_ae2_OK (n2 :: n1 :: ds) (IHae2_OK n2 (eq_refl (Expressible_nat n2)))).
        rewrite -> fold_unfold_fetch_decode_execute_cons.
        unfold decode_execute.
        rewrite -> H_n1_lt_n2.
        rewrite -> fold_unfold_fetch_decode_execute_nil.
        injection H_n' as H_n1_n2.
        rewrite -> H_n1_n2.
        reflexivity. 
      * discriminate H_n'.
    + discriminate H_n'.
  - intros s H_s.
    rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> fold_unfold_evaluate_Minus in H_s.
    destruct (about_fetch_decode_execute_loop (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_fdel_ae1_OK H_fdel_ae1_KO].
    case (evaluate ae1) as [n1 | s1] eqn: H_ae1.
    + destruct (IHae1 ds) as [IHae1_OK IHae1_KO].
      rewrite -> (H_fdel_ae1_OK (n1 :: ds) (IHae1_OK n1 (eq_refl (Expressible_nat n1)))).
      destruct (about_fetch_decode_execute_loop (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_fdel_ae2_OK H_fdel_ae2_KO].
      case (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      * destruct (IHae2 (n1 :: ds)) as [IHae2_OK IHHae2_KO].
        case (n1 <? n2) eqn: H_n1_lt_n2.
        { rewrite -> (H_fdel_ae2_OK (n2 :: n1 :: ds) (IHae2_OK n2 (eq_refl (Expressible_nat n2)))).
        rewrite -> fold_unfold_fetch_decode_execute_cons.
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
  
Theorem the_commuting_diagram :
  forall sp : source_program,
    interpret sp = run (compile sp).
Proof.
  intros [ae].
  unfold interpret, run, compile.
  destruct (the_commuting_diagram_aux ae nil) as [H_fdel_OK H_fdel_KO].
  destruct (evaluate ae) as [n | s] eqn: H_ae.
  - rewrite -> (H_fdel_OK n (eq_refl (Expressible_nat n))).
    reflexivity.
  - rewrite -> (H_fdel_KO s (eq_refl (Expressible_msg s))).
    reflexivity.
Qed.
      
(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

Lemma fold_unfold_verify_aux_nil :
  forall n : nat,
    verify_aux nil n = Some n.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (n : nat),
    verify_aux (bci :: bcis') n =
    match bci with
      | PUSH _ =>
        verify_aux bcis' (S n)
      | _ =>
        match n with
          | S (S n') =>
            verify_aux bcis' (S n')
          | _ =>
            None
        end
    end.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end.

Definition test_verify candidate :=
  (eqb_expressible_value (interpret (Source_program (Literal 10))) (run (candidate (Source_program (Literal 10)))))
  && (eqb_expressible_value (interpret (Source_program (Plus (Literal 1) (Literal 10)))) (run (candidate (Source_program (Plus (Literal 1) (Literal 10))))))
  && (eqb_expressible_value (interpret (Source_program (Plus (Literal 1) (Minus (Literal 9) (Literal 10))))) (run (candidate (Source_program (Plus (Literal 1) (Minus (Literal 9) (Literal 10)))))))
  && (eqb_expressible_value (interpret (Source_program (Plus (Minus (Literal 9) (Literal 10)) (Literal 1)))) (run (candidate (Source_program (Plus (Minus (Literal 9) (Literal 10)) (Literal 1))))))
  && (eqb_expressible_value (interpret (Source_program (Minus (Literal 10) (Literal 1)))) (run (candidate (Source_program (Minus (Literal 10) (Literal 1))))))
  && (eqb_expressible_value (interpret (Source_program (Minus (Literal 1) (Minus (Literal 9) (Literal 10))))) (run (candidate (Source_program (Minus (Literal 1) (Minus (Literal 9) (Literal 10)))))))
  && (eqb_expressible_value (interpret (Source_program (Minus (Minus (Literal 9) (Literal 10)) (Literal 1)))) (run (candidate (Source_program (Minus (Minus (Literal 9) (Literal 10)) (Literal 1)))))).

Compute (test_verify compile = true).
Compute (test_verify compile_acc = true).

(* Task 10 (time permitting):
   Prove that the compiler emits code
   that is accepted by the verifier.
*)

Lemma about_verify_aux :
  forall (bci1s bci2s : list byte_code_instruction)
         (n n' : nat),
        verify_aux bci1s n = Some n' ->
        verify_aux (bci1s ++ bci2s) n = verify_aux bci2s n'.
Proof.
  intro bci1s.
  induction bci1s as [ | bci1 bci1s' IHbci1s']; intros bci2s n n' H_n.
  - rewrite -> fold_unfold_list_append_nil.
    rewrite -> fold_unfold_verify_aux_nil in H_n.
    injection H_n as H_eq_n_n'.
    rewrite -> H_eq_n_n'.
    reflexivity.
  - rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_cons in H_n.
    case bci1 as [n'' | | ].
    + rewrite -> (IHbci1s' bci2s (S n) n' H_n).
      reflexivity.
    + case n as [ | [ | n'']].
      * discriminate H_n.
      * discriminate H_n.
      * rewrite -> (IHbci1s' bci2s (S n'') n' H_n).
        reflexivity.
    + case n as [ | [ | n'']].
      * discriminate H_n.
      * discriminate H_n.
      * rewrite -> (IHbci1s' bci2s (S n'') n' H_n).
        reflexivity.
Qed.

Lemma the_compiler_emits_well_behaved_code_aux :
  forall (ae : arithmetic_expression)
         (s : nat),
    verify_aux (compile_aux ae) s = Some (S s).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro s.
  - rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> (about_verify_aux (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) s (S s) (IHae1 s)).
    rewrite -> (about_verify_aux (compile_aux ae2) (ADD :: nil) (S s) (S (S s)) (IHae2 (S s))).
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> (about_verify_aux (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) s (S s) (IHae1 s)).
    rewrite -> (about_verify_aux (compile_aux ae2) (SUB :: nil) (S s) (S (S s)) (IHae2 (S s))).
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
Qed.

Theorem the_compiler_emits_well_behaved_code :
  forall sp : source_program,
    verify (compile sp) = true.
Proof.
  intros [ae].
  unfold verify, compile.
  rewrite -> the_compiler_emits_well_behaved_code_aux.
  reflexivity.
Qed.
   
(* Subsidiary question: What is the practical consequence of this theorem?

   No underflow occurs during execution of compilation and there is one and one only natural number on top of the stack when the program completes. Hence, running a compiled program never returns the "no result" or "too many results" error.
*)

(* ********** *)

(* Task 11:

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.
      (This will require stripping your source interpreter from its error parts.)
*)

Definition magritte_expressible_value := arithmetic_expression.

Fixpoint eqb_magritte_expressible_value (ae1 ae2 : arithmetic_expression) : bool :=
  match ae1 with
  | Literal n1 =>
      match ae2 with
      | Literal n2 =>
          eqb_nat n1 n2
      | Plus ae3 ae4 =>
          false
      | Minus ae5 ae6 =>
          false
      end
  | Plus ae7 ae8 =>
      match ae2 with
      | Literal n2 =>
          false
      | Plus ae9 ae10 =>
          (eqb_magritte_expressible_value ae7 ae9) && (eqb_magritte_expressible_value ae8 ae10)
      | Minus ae11 ae12 =>
          false
      end
  | Minus ae7 ae8 =>
      match ae2 with
      | Literal n2 =>
          false
      | Plus ae9 ae10 =>
          false
      | Minus ae11 ae12 =>
          (eqb_magritte_expressible_value ae7 ae11) && (eqb_magritte_expressible_value ae8 ae12)
      end
  end.

Fixpoint magritte_evaluate (ae : arithmetic_expression) : magritte_expressible_value :=
  match ae with
  | Literal n =>
      Literal n
  | Plus ae1 ae2 =>
      Plus (magritte_evaluate ae1) (magritte_evaluate ae2)
  | Minus ae1 ae2 =>
      Minus (magritte_evaluate ae1) (magritte_evaluate ae2)
  end.

Definition test_magritte_evaluate candidate :=
  (eqb_magritte_expressible_value (candidate (Literal 10)) (Literal 10))
  && (eqb_magritte_expressible_value (candidate (Plus (Literal 5) (Literal 3))) (Plus (Literal 5) (Literal 3)))
  && (eqb_magritte_expressible_value (candidate (Minus (Literal 8) (Literal 3))) (Minus (Literal 8) (Literal 3))).

Compute (test_magritte_evaluate magritte_evaluate = true).

Lemma fold_unfold_magritte_evaluate_Literal :
  forall n : nat,
    magritte_evaluate (Literal n) = Literal n.
Proof.
  fold_unfold_tactic magritte_evaluate.
Qed.

Lemma fold_unfold_magritte_evaluate_Plus :
  forall ae1 ae2 : arithmetic_expression,
    magritte_evaluate (Plus ae1 ae2) =
      Plus (magritte_evaluate ae1) (magritte_evaluate ae2).
Proof.
  fold_unfold_tactic magritte_evaluate.
Qed.

Lemma fold_unfold_magritte_evaluate_Minus :
  forall ae1 ae2 : arithmetic_expression,
    magritte_evaluate (Minus ae1 ae2) =
      Minus (magritte_evaluate ae1) (magritte_evaluate ae2).
Proof.
  fold_unfold_tactic magritte_evaluate.
Qed.

Theorem about_magritte_evaluate :
  forall ae : arithmetic_expression,
    magritte_evaluate ae = ae.
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 | ae2 IHae2].
  - exact (fold_unfold_magritte_evaluate_Literal n).
  - rewrite -> fold_unfold_magritte_evaluate_Plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - rewrite -> fold_unfold_magritte_evaluate_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.
      
Definition magritte_interpret (sp : source_program) : source_program :=
  match sp with
    Source_program ae =>
      Source_program (magritte_evaluate ae)
  end.

(* this is placed here as it is dependent on eqb_magritte_expressible_value *)
Definition eqb_source_program (sp1 sp2 : source_program) : bool :=
  match sp1 with
  | Source_program ae1 =>
      match sp2 with
      | Source_program ae2 =>
          eqb_magritte_expressible_value ae1 ae2
      end
  end.

Definition test_magritte_interpret candidate :=
  (eqb_source_program (candidate (Source_program (Plus (Literal 1) (Literal 10)))) (Source_program (Plus (Literal 1) (Literal 10))))
  && (eqb_source_program (candidate (Source_program (Minus (Literal 1) (Literal 10)))) (Source_program (Minus (Literal 1) (Literal 10))))
  && (eqb_source_program (candidate (Source_program (Minus (Literal 10) (Literal 1)))) (Source_program (Minus (Literal 10) (Literal 1)))).

Compute (test_magritte_interpret magritte_interpret = true).
  
Theorem about_magritte_interpret :
  forall sp : source_program,
    magritte_interpret sp = sp.
Proof.
  intros [ae].
  unfold magritte_interpret.
  rewrite -> about_magritte_evaluate.
  reflexivity.
Qed.
      
(*
   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.
      (This will require stripping your target interpreter from its error parts.)
*)

Definition magritte_data_stack := list arithmetic_expression.

Definition eqb_magritte_data_stack (mds1 mds2 : list arithmetic_expression) : bool :=
  eqb_list arithmetic_expression eqb_magritte_expressible_value mds1 mds2.

Inductive magritte_result_of_decoding_and_execution : Type :=
  magritte_OK : magritte_data_stack -> magritte_result_of_decoding_and_execution
| magritte_KO : string -> magritte_result_of_decoding_and_execution.

Definition eqb_magritte_result_of_decoding_and_execution (res1 res2 : magritte_result_of_decoding_and_execution) : bool :=
  match res1 with
  | magritte_OK mds1 =>
      match res2 with
      | magritte_OK mds2 =>
          eqb_magritte_data_stack mds1 mds2
      | magritte_KO msg2 =>
          false
      end
  | magritte_KO msg1 =>
      match res2 with
      | magritte_OK mds2 =>
          false
      | magritte_KO msg2 =>
          eqb_string msg1 msg2
      end
  end.

Definition magritte_decode_execute (bci : byte_code_instruction) (ds : magritte_data_stack) : magritte_result_of_decoding_and_execution :=
  match bci with
  | PUSH n =>
      magritte_OK (Literal n :: ds)
  | ADD =>
      match ds with
      | nil =>
          magritte_KO "ADD: stack underflow"
      | ae2 :: ds' =>
          match ds' with
          | nil =>
              magritte_KO "ADD: stack underflow"
          | ae1 :: ds'' =>
              magritte_OK (Plus ae1 ae2 :: ds'')
          end
      end
  | SUB =>
      match ds with
      | nil =>
          magritte_KO "SUB: stack underflow"
      | ae2 :: ds' =>
          match ds' with
          | nil =>
              magritte_KO "SUB: stack underflow"
          | ae1 :: ds'' =>
              magritte_OK (Minus ae1 ae2 :: ds'')
          end
      end
  end.

Definition test_magritte_decode_execute candidate :=
  (eqb_magritte_result_of_decoding_and_execution (candidate (PUSH 4) ((Literal 3) :: (Literal 2) :: (Literal 1) :: nil)) (magritte_OK ((Literal 4) :: (Literal 3) :: (Literal 2) :: (Literal 1) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate ADD nil) (magritte_KO "ADD: stack underflow"))
  && (eqb_magritte_result_of_decoding_and_execution (candidate ADD ((Literal 1) :: nil)) (magritte_KO "ADD: stack underflow"))
  && (eqb_magritte_result_of_decoding_and_execution (candidate ADD ((Literal 2) :: (Literal 1) :: nil)) (magritte_OK (Plus (Literal 1) (Literal 2) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate ADD ((Literal 3) :: (Literal 2) :: (Literal 1) :: nil)) (magritte_OK (Plus (Literal 2) (Literal 3) :: Literal 1 :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate SUB nil) (magritte_KO "SUB: stack underflow"))
  && (eqb_magritte_result_of_decoding_and_execution (candidate SUB ((Literal 1) :: nil)) (magritte_KO "SUB: stack underflow"))
  && (eqb_magritte_result_of_decoding_and_execution (candidate SUB ((Literal 2) :: (Literal 1) :: nil)) (magritte_OK (Minus (Literal 1) (Literal 2) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate SUB ((Literal 1) :: (Literal 2) :: nil)) (magritte_OK (Minus (Literal 2) (Literal 1) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate SUB ((Literal 1) :: (Literal 2) :: (Literal 3) :: (Literal 4) :: nil)) (magritte_OK (Minus (Literal 2) (Literal 1) :: (Literal 3) :: (Literal 4) :: nil))).

Compute (test_magritte_decode_execute magritte_decode_execute = true).

Fixpoint magritte_fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : magritte_data_stack) : magritte_result_of_decoding_and_execution :=
  match bcis with
  | nil =>
      magritte_OK ds
  | bci :: bcis' =>
      match magritte_decode_execute bci ds with
      | magritte_OK ds' =>
          magritte_fetch_decode_execute_loop bcis' ds'
      | magritte_KO s =>
          magritte_KO s
      end
  end.

Definition test_magritte_fetch_decode_execute_loop candidate :=
  (eqb_magritte_result_of_decoding_and_execution (candidate nil ((Literal 3) :: (Literal 2) :: (Literal 1) :: nil)) (magritte_OK ((Literal 3) :: (Literal 2) :: (Literal 1) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate ((PUSH 3) :: (PUSH 4) :: nil) ((Literal 2) :: (Literal 1) :: nil)) (magritte_OK ((Literal 4) :: (Literal 3) :: (Literal 2) :: (Literal 1) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate (ADD :: (PUSH 2) :: nil) nil) (magritte_KO "ADD: stack underflow"))
  && (eqb_magritte_result_of_decoding_and_execution (candidate (ADD :: (PUSH 2) :: nil) ((Literal 1) :: nil)) (magritte_KO "ADD: stack underflow"))
  && (eqb_magritte_result_of_decoding_and_execution (candidate (SUB :: (PUSH 2) :: nil) ((Literal 1) :: nil)) (magritte_KO "SUB: stack underflow"))
  && (eqb_magritte_result_of_decoding_and_execution (candidate (SUB :: (PUSH 3) :: nil) ((Literal 2) :: (Literal 1) :: nil)) (magritte_OK ((Literal 3) :: Minus (Literal 1) (Literal 2) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate (SUB :: (PUSH 10) :: nil) ((Literal 1) :: (Literal 2) :: nil)) (magritte_OK ((Literal 10) :: Minus (Literal 2) (Literal 1) :: nil)))
  && (eqb_magritte_result_of_decoding_and_execution (candidate (SUB :: (PUSH 10) :: nil) ((Literal 1) :: (Literal 2) :: (Literal 100) :: nil)) (magritte_OK ((Literal 10) :: Minus (Literal 2) (Literal 1) :: (Literal 100) :: nil))).

Compute (test_magritte_fetch_decode_execute_loop magritte_fetch_decode_execute_loop = true).

Lemma fold_unfold_magritte_fetch_decode_execute_loop_nil :
  forall (ds : magritte_data_stack),
    magritte_fetch_decode_execute_loop nil ds = magritte_OK ds.
Proof.
  fold_unfold_tactic magritte_fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_magritte_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : magritte_data_stack),
    magritte_fetch_decode_execute_loop (bci :: bcis') ds =
      match magritte_decode_execute bci ds with
      | magritte_OK ds' =>
          magritte_fetch_decode_execute_loop bcis' ds'
      | magritte_KO s =>
          magritte_KO s
      end. 
Proof.
  fold_unfold_tactic magritte_fetch_decode_execute_loop.
Qed.

Theorem about_magritte_fetch_decode_execute_loop :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds : magritte_data_stack),
    (forall ds' : magritte_data_stack,
        magritte_fetch_decode_execute_loop bci1s ds = magritte_OK ds' ->
        magritte_fetch_decode_execute_loop (bci1s ++ bci2s) ds =
          magritte_fetch_decode_execute_loop bci2s ds')
    /\
      (forall s : string,
          magritte_fetch_decode_execute_loop bci1s ds = magritte_KO s ->
          magritte_fetch_decode_execute_loop (bci1s ++ bci2s) ds =
            magritte_KO s).
Proof.
  intros bci1s bci2s.
  induction bci1s as [ | [n | | ] bci1s' IHbci1s']; intro ds; split.
  - intros ds' H_fdel_nil_OK.
    unfold magritte_fetch_decode_execute_loop in H_fdel_nil_OK.
    injection H_fdel_nil_OK as H_eq_ds_ds'.
    rewrite -> H_eq_ds_ds'.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - intros s H_absurd.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_nil in H_absurd.
    discriminate H_absurd.
    
  - intros ds' H_fdel_push_cons_OK.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    destruct (IHbci1s' (Literal n :: ds)) as [IHbci1s'_OK _].
    exact (IHbci1s'_OK ds' H_fdel_push_cons_OK).
  - intros s H_fdel_push_cons_KO.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    destruct (IHbci1s' (Literal n :: ds)) as [_ IHbci1s'_KO].
    exact (IHbci1s'_KO s H_fdel_push_cons_KO).

  - intros ds1 H_fdel_add_cons_OK.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons in H_fdel_add_cons_OK.
    unfold magritte_decode_execute in H_fdel_add_cons_OK.
    case ds as [ | ae2 ds'].
    { discriminate H_fdel_add_cons_OK. }
    case ds' as [ | ae1 ds''].
    { discriminate H_fdel_add_cons_OK. }    
    destruct (IHbci1s' (Plus ae1 ae2 :: ds'')) as [IHbci1s'_OK _].
    exact (IHbci1s'_OK ds1 H_fdel_add_cons_OK).
  - intros s H_fdel_add_cons_KO.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons in H_fdel_add_cons_KO.
    unfold magritte_decode_execute in H_fdel_add_cons_KO.
    case ds as [ | ae2 ds'].
    { exact H_fdel_add_cons_KO. }
    case ds' as [ | ae1 ds''].
    { exact H_fdel_add_cons_KO. }    
    destruct (IHbci1s' (Plus ae1 ae2 :: ds'')) as [_ IHbci1s'_KO].
    exact (IHbci1s'_KO s H_fdel_add_cons_KO).
    
  - intros ds1 H_fdel_sub_cons_OK.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons in H_fdel_sub_cons_OK.
    unfold magritte_decode_execute in H_fdel_sub_cons_OK.
    case ds as [ | ae2 ds'].
    { discriminate H_fdel_sub_cons_OK. }
    case ds' as [ | ae1 ds''].
    { discriminate H_fdel_sub_cons_OK. }    
    destruct (IHbci1s' (Minus ae1 ae2 :: ds'')) as [IHbci1s'_OK _].
    exact (IHbci1s'_OK ds1 H_fdel_sub_cons_OK).
  - intros s H_fdel_sub_cons_KO.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons in H_fdel_sub_cons_KO.
    unfold magritte_decode_execute in H_fdel_sub_cons_KO.
    case ds as [ | ae2 ds'].
    { exact H_fdel_sub_cons_KO. }
    case ds' as [ | ae1 ds''].
    { exact H_fdel_sub_cons_KO. }    
    destruct (IHbci1s' (Minus ae1 ae2 :: ds'')) as [_ IHbci1s'_KO].
    exact (IHbci1s'_KO s H_fdel_sub_cons_KO).
Qed.

Inductive magritte_expressible_value' : Type :=
  magritte_Expressible_nat : source_program -> magritte_expressible_value'
| magritte_Expressible_msg : string -> magritte_expressible_value'.

Definition eqb_magritte_expressible_value' (mev1 mev2 : magritte_expressible_value') : bool :=
  match mev1 with
  | magritte_Expressible_nat sp1 =>
      match mev2 with
      | magritte_Expressible_nat sp2 =>
          eqb_source_program sp1 sp2
      | magritte_Expressible_msg msg2 =>
          false
      end
  | magritte_Expressible_msg msg1 =>
      match mev2 with
      | magritte_Expressible_nat sp2 =>
          false
      | magritte_Expressible_msg msg2 =>
          eqb_string msg1 msg2
      end
  end.

Definition magritte_run' (tp : target_program) : magritte_expressible_value' :=
  match tp with
  | Target_program bcis =>
      match magritte_fetch_decode_execute_loop bcis nil with
      | magritte_OK nil =>
          magritte_Expressible_msg "no result on the data stack"
      | magritte_OK (ae :: nil) =>
          magritte_Expressible_nat (Source_program ae)
      | magritte_OK (ae :: ae' :: ds'') =>
          magritte_Expressible_msg "too many results on the data stack"
      | magritte_KO s =>
          magritte_Expressible_msg s
      end
  end.

Definition test_magritte_run' candidate :=
  (eqb_magritte_expressible_value' (candidate (Target_program nil)) (magritte_Expressible_msg "no result on the data stack"))
  && (eqb_magritte_expressible_value' (candidate (Target_program (PUSH 4 :: nil))) (magritte_Expressible_nat (Source_program (Literal 4))))
  && (eqb_magritte_expressible_value' (candidate (Target_program (PUSH 4 :: PUSH 3 :: PUSH 2 :: nil))) (magritte_Expressible_msg "too many results on the data stack"))
  && (eqb_magritte_expressible_value' (candidate (Target_program (PUSH 3 :: PUSH 2 :: nil))) (magritte_Expressible_msg "too many results on the data stack"))
  && (eqb_magritte_expressible_value' (candidate (Target_program (ADD :: PUSH 4 :: nil))) (magritte_Expressible_msg "ADD: stack underflow"))
  && (eqb_magritte_expressible_value' (candidate (Target_program (SUB :: PUSH 4 :: nil))) (magritte_Expressible_msg "SUB: stack underflow"))
  && (eqb_magritte_expressible_value' (candidate (Target_program (PUSH 4 :: PUSH 5 :: SUB :: nil))) (magritte_Expressible_nat (Source_program (Minus (Literal 4) (Literal 5))))).

Compute (test_magritte_run' magritte_run' = true).

(*
   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.
*)

Lemma the_magritte_commuting_diagram_aux :
  forall (ae : arithmetic_expression)
         (ds : magritte_data_stack),
    magritte_fetch_decode_execute_loop (compile_aux ae) ds =
      magritte_OK (ae :: ds).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds.
  - rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.   
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Plus.
    destruct (about_magritte_fetch_decode_execute_loop (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_fdel_ae1_OK _].
    rewrite -> (H_fdel_ae1_OK (ae1 :: ds) (IHae1 ds)).
    destruct (about_magritte_fetch_decode_execute_loop (compile_aux ae2) (ADD :: nil) (ae1 :: ds)) as [H_fdel_ae2_OK _].
    rewrite -> (H_fdel_ae2_OK (ae2 :: ae1 :: ds) (IHae2 (ae1 :: ds))).
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Minus.
    destruct (about_magritte_fetch_decode_execute_loop (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_fdel_ae1_OK _].
    rewrite -> (H_fdel_ae1_OK (ae1 :: ds) (IHae1 ds)).
    destruct (about_magritte_fetch_decode_execute_loop (compile_aux ae2) (SUB :: nil) (ae1 :: ds)) as [H_fdel_ae2_OK _].
    rewrite -> (H_fdel_ae2_OK (ae2 :: ae1 :: ds) (IHae2 (ae1 :: ds))).
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_cons.
    unfold magritte_decode_execute.
    rewrite -> fold_unfold_magritte_fetch_decode_execute_loop_nil.
    reflexivity.
Qed.  

Theorem the_magritte_commuting_diagram :
  forall sp sp' : source_program,
    magritte_run' (compile sp) = magritte_Expressible_nat sp' ->
    magritte_interpret sp = sp'.
Proof.
  intros [ae] sp' H_sp.
  unfold magritte_run', compile in H_sp.
  rewrite -> the_magritte_commuting_diagram_aux in H_sp.
  injection H_sp as H_sp'.
  rewrite -> H_sp'.
  rewrite -> about_magritte_interpret.
  reflexivity.
Qed.

Definition test_magritte_commutes candidate :=
  (eqb_magritte_expressible_value' (magritte_Expressible_nat (magritte_interpret (Source_program (Literal 10)))) (magritte_run' (candidate (Source_program (Literal 10)))))
  && (eqb_magritte_expressible_value' (magritte_Expressible_nat (magritte_interpret (Source_program (Plus (Literal 1) (Literal 10))))) (magritte_run' (candidate (Source_program (Plus (Literal 1) (Literal 10))))))
  && (eqb_magritte_expressible_value' (magritte_Expressible_nat (magritte_interpret (Source_program (Plus (Literal 1) (Minus (Literal 9) (Literal 10)))))) (magritte_run' (candidate (Source_program (Plus (Literal 1) (Minus (Literal 9) (Literal 10)))))))
  && (eqb_magritte_expressible_value' (magritte_Expressible_nat (magritte_interpret (Source_program (Plus (Minus (Literal 9) (Literal 10)) (Literal 1))))) (magritte_run'(candidate (Source_program (Plus (Minus (Literal 9) (Literal 10)) (Literal 1))))))
  && (eqb_magritte_expressible_value' (magritte_Expressible_nat (magritte_interpret(Source_program (Minus (Literal 10) (Literal 1))))) (magritte_run' (candidate (Source_program (Minus (Literal 10) (Literal 1))))))
  && (eqb_magritte_expressible_value' (magritte_Expressible_nat (magritte_interpret (Source_program (Minus (Literal 1) (Minus (Literal 9) (Literal 10)))))) (magritte_run'(candidate (Source_program (Minus (Literal 1) (Minus (Literal 9) (Literal 10)))))))
  && (eqb_magritte_expressible_value'(magritte_Expressible_nat (magritte_interpret (Source_program (Minus (Minus (Literal 9) (Literal 10)) (Literal 1))))) (magritte_run'(candidate (Source_program (Minus (Minus (Literal 9) (Literal 10)) (Literal 1)))))).

Compute (test_magritte_commutes compile = true).

Compute (test_magritte_commutes compile_acc = true).

Theorem magritte_run'_is_a_decompiler :
  forall sp : source_program,
    magritte_run' (compile sp) = magritte_Expressible_nat sp.
Proof.
  intros [ae].
  unfold magritte_run', compile.
  rewrite -> the_magritte_commuting_diagram_aux.
  reflexivity.
Qed.

Theorem magritte_running_a_compiled_program_never_returns_an_error_message :
  forall sp : source_program,
    exists sp' : source_program,
      magritte_run' (compile sp) = magritte_Expressible_nat sp'.
Proof.
  intro sp.
  exists sp.
  exact (magritte_run'_is_a_decompiler sp).
Qed.

Definition magritte_run (tp : target_program) : option source_program :=
  match tp with
  | Target_program bcis =>
      match magritte_fetch_decode_execute_loop bcis nil with
      | magritte_OK (ae :: nil) =>
          Some (Source_program ae)
      | _ =>
          None
      end
  end.

Definition eqb_option_source_program (osp1 osp2 : option source_program) : bool :=
  eqb_option source_program eqb_source_program osp1 osp2.

Definition test_magritte_run candidate :=
  (eqb_option_source_program (candidate (Target_program nil)) (None))
  && (eqb_option_source_program (candidate (Target_program (PUSH 4 :: nil))) (Some (Source_program (Literal 4))))
  && (eqb_option_source_program (candidate (Target_program (PUSH 4 :: PUSH 3 :: PUSH 2 :: nil))) (None))
  && (eqb_option_source_program (candidate (Target_program (PUSH 3 :: PUSH 2 :: nil))) (None))
  && (eqb_option_source_program (candidate (Target_program (ADD :: PUSH 4 :: nil))) (None))
  && (eqb_option_source_program (candidate (Target_program (SUB :: PUSH 4 :: nil))) (None))
  && (eqb_option_source_program (candidate (Target_program (PUSH 4 :: PUSH 5 :: SUB :: nil))) (Some (Source_program (Minus (Literal 4) (Literal 5))))).

Compute (test_magritte_run magritte_run = true).

(*
   D. How do the Magritte target interpreter and the compiler compare?

  One function implements a compiler and the other a de-compiler.
*)

(* ********** *)

(* end of term-project.v *)
