(* week-13_a-continuation-based-interpreter_the-live-proving-session.v *)
(* Version of 15 Nov 2023 *)
(* was: *)
(* week-13_a-continuation-based-interpreter.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 07 Nov 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List String Ascii.

(* ***** *)

Check (1 =? 2).
Check Nat.eqb.
Check (Nat.eqb 1 2).

Check (1 <=? 2).
Check Nat.leb.
Check (Nat.leb 1 2).

Check (1 <? 2).
Check Nat.ltb.
Check (Nat.ltb 1 2).

(* ***** *)

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

(* ********** *)

(* Beginning of an evaluation function in undelimited continuation-passing style: *)

(*
Fixpoint evaluate_cps (Ans : Type) (ae : arithmetic_expression) (k : expressible_value -> Ans) : Ans :=
  match ae with
    Literal n =>
    k (Expressible_nat n)
  | Plus ae1 ae2 =>
    evaluate_cps Ans ae1 (fun ev1 =>
                            evaluate_cps Ans ae2 (fun ev2 =>
                                                    ...))
  | Minus ae1 ae2 =>
    ...
  end.

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
    Source_program ae =>
    evaluate_cps expressible_value ae (fun ev => ev)
  end.
*)

(* ********** *)

(* An evaluation function in delimited continuation-passing style: *)

Fixpoint evaluate_cb (ae : arithmetic_expression) (k : nat -> expressible_value) : expressible_value :=
  match ae with
    Literal n =>
    k n
  | Plus ae1 ae2 =>
    evaluate_cb ae1 (fun n1 =>
                       evaluate_cb ae2 (fun n2 =>
                                          k (n1 + n2)))
  | Minus ae1 ae2 =>
    evaluate_cb ae1 (fun n1 =>
                       evaluate_cb ae2 (fun n2 =>
                                          if n1 <? n2
                                          then (Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
                                          else k (n1 - n2)))
  end.

Lemma fold_unfold_evaluate_cb_Literal :
  forall (n : nat)
         (k : nat -> expressible_value),
    evaluate_cb (Literal n) k =
    k n.
Proof.
  fold_unfold_tactic evaluate_cb.
Qed.

Lemma fold_unfold_evaluate_cb_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (k : nat -> expressible_value),
    evaluate_cb (Plus ae1 ae2) k =
    evaluate_cb ae1 (fun n1 =>
                       evaluate_cb ae2 (fun n2 =>
                                          k (n1 + n2))).
Proof.
  fold_unfold_tactic evaluate_cb.
Qed.

Lemma fold_unfold_evaluate_cb_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (k : nat -> expressible_value),
    evaluate_cb (Minus ae1 ae2) k =
    evaluate_cb ae1 (fun n1 =>
                       evaluate_cb ae2 (fun n2 =>
                                          if n1 <? n2
                                          then (Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
                                          else k (n1 - n2))).
Proof.
  fold_unfold_tactic evaluate_cb.
Qed.

(* ***** *)

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
    Source_program ae =>
    evaluate_cb ae (fun n => Expressible_nat n)
  end.

Compute (interpret (Source_program (Plus (Literal 1) (Literal 10))) =
         Expressible_nat 11).

Compute (interpret (Source_program (Minus (Literal 1) (Literal 10)))).

Compute (interpret (Source_program (Minus (Literal 10) (Literal 1)))).

(* ***** *)

Lemma about_evaluate_cb :
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      (exists n : nat,
          evaluate ae = Expressible_nat n
          /\
          forall k : nat -> expressible_value,
            evaluate_cb ae k = k n)
      \/
      (exists s : string,
          evaluate ae = Expressible_msg s
          /\
          forall k : nat -> expressible_value,
            evaluate_cb ae k = Expressible_msg s).
Proof.
  intros evaluate S_evaluate.
  intro ae.
  induction ae as [n |
                   ae1 [[n1 [D_n1 K_n1]] | [s1 [D_n1 K_s1]]] ae2 [[n2 [D_n2 K_n2]] | [s2 [D_n2 K_s2]]] |
                   ae1 [[n1 [D_n1 K_n1]] | [s1 [D_n1 K_s1]]] ae2 [[n2 [D_n2 K_n2]] | [s2 [D_n2 K_s2]]]].

  - left.
    exists n.
    split.
    + destruct S_evaluate as [fold_unfold_evaluate_Literal _].
      exact (fold_unfold_evaluate_Literal n).
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Literal.
      reflexivity.
  - destruct S_evaluate as [_ [[_ [_ X]] _]].
    Check (X ae1 ae2 n1 n2 D_n1 D_n2).
    rewrite -> (X ae1 ae2 n1 n2 D_n1 D_n2).
    left.
    exists (n1 + n2).
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Plus.
      rewrite -> (K_n1 (fun n0 : nat => evaluate_cb ae2 (fun n3 : nat => k (n0 + n3)))).
      rewrite -> (K_n2 (fun n3 : nat => k (n1 + n3))).
      reflexivity.

  - destruct S_evaluate as [_ [[_ [X _]] _]].
    Check (X ae1 ae2 n1 s2 D_n1 D_n2).
    rewrite -> (X ae1 ae2 n1 s2 D_n1 D_n2).
    right.
    exists s2.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Plus.
      rewrite -> (K_n1 (fun n0 : nat => evaluate_cb ae2 (fun n2 : nat => k (n0 + n2)))).
      rewrite -> (K_s2 (fun n2 : nat => k (n1 + n2))).
      reflexivity.

  - destruct S_evaluate as [_ [[X _] _]].
    rewrite -> (X ae1 ae2 s1 D_n1).
    right.
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Plus.
      rewrite -> (K_s1 (fun n1 : nat => evaluate_cb ae2 (fun n0 : nat => k (n1 + n0)))).
      reflexivity.

  - destruct S_evaluate as [_ [[X _] _]].
    rewrite -> (X ae1 ae2 s1 D_n1).
    right.
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Plus.
      rewrite -> (K_s1 (fun n1 : nat => evaluate_cb ae2 (fun n0 : nat => k (n1 + n0)))).
      reflexivity.

  - case (n1 <? n2) as [ | ] eqn:H_n1_n2.
    + destruct S_evaluate as [_ [_ [_ [_ [X _]]]]].
      Check (X ae1 ae2 n1 n2 D_n1 D_n2 H_n1_n2).
      rewrite -> (X ae1 ae2 n1 n2 D_n1 D_n2 H_n1_n2).
      right.
      exists (String.append "numerical underflow: -" (string_of_nat (n2 - n1))).
      split.
      * reflexivity.
      * intro k.
        rewrite -> fold_unfold_evaluate_cb_Minus.
        rewrite -> (K_n1 (fun n0 : nat => evaluate_cb ae2 (fun n3 : nat => if n0 <? n3 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n3 - n0)) else k (n0 - n3)))).
        rewrite -> (K_n2 (fun n3 : nat => if n1 <? n3 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n3 - n1)) else k (n1 - n3))).
        rewrite -> H_n1_n2.
        reflexivity.
    + destruct S_evaluate as [_ [_ [_ [_ [_ X]]]]].
      rewrite -> (X ae1 ae2 n1 n2 D_n1 D_n2 H_n1_n2).
      left.
      exists (n1 - n2).
      split.
      * reflexivity.
      * intro k.
        rewrite -> fold_unfold_evaluate_cb_Minus.
        rewrite -> (K_n1 (fun n0 : nat => evaluate_cb ae2 (fun n3 : nat => if n0 <? n3 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n3 - n0)) else k (n0 - n3)))).
        rewrite -> (K_n2 (fun n3 : nat => if n1 <? n3 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n3 - n1)) else k (n1 - n3))).
        rewrite -> H_n1_n2.
        reflexivity.
  - destruct S_evaluate as [_ [_ [_ [X [_ _]]]]].
    rewrite -> (X ae1 ae2 n1 s2 D_n1 D_n2).
    right.
    exists s2.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Minus.
      rewrite -> (K_n1 (fun n0 : nat => evaluate_cb ae2 (fun n2 : nat => if n0 <? n2 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n2 - n0)) else k (n0 - n2)))).
      rewrite -> (K_s2 (fun n2 : nat => if n1 <? n2 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n2 - n1)) else k (n1 - n2))).
      reflexivity.
  - destruct S_evaluate as [_ [_ [X [_ [_ _]]]]].
    rewrite -> (X ae1 ae2 s1 D_n1).
    right.
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Minus.
      rewrite -> (K_s1 (fun n1 : nat => evaluate_cb ae2 (fun n0 : nat => if n1 <? n0 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n0 - n1)) else k (n1 - n0)))).
      reflexivity.
  - destruct S_evaluate as [_ [_ [X [_ [_ _]]]]].
    rewrite -> (X ae1 ae2 s1 D_n1).
    right.
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cb_Minus.
      rewrite -> (K_s1 (fun n1 : nat => evaluate_cb ae2 (fun n0 : nat => if n1 <? n0 then Expressible_msg ("numerical underflow: -" ++ string_of_nat (n0 - n1)) else k (n1 - n0)))).
      reflexivity.
Qed.

(* ***** *)

Theorem interpret_satisfies_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros evaluate S_evaluate ae.
  Check (about_evaluate_cb
           evaluate
           S_evaluate
           ae).
  destruct (about_evaluate_cb
              evaluate
              S_evaluate
              ae) as [[n [H_eval H_eval_cb]] | [s [H_eval H_eval_cb]]].
  - Check (H_eval_cb (fun n0 : nat => Expressible_nat n0)).
    rewrite -> (H_eval_cb (fun n0 : nat => Expressible_nat n0)).
    Check (eq_sym H_eval).
    exact (eq_sym H_eval).
  - Check (H_eval_cb (fun n0 : nat => Expressible_nat n0)).
    rewrite -> (H_eval_cb (fun n0 : nat => Expressible_nat n0)).
    exact (eq_sym H_eval).
Qed.

(* ********** *)

(* end of week-13_a-continuation-based-interpreter_the-live-proving-session.v *)
