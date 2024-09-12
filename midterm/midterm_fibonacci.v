(* midterm_fibonacci.v *)

(* MR 2024 - YSC 2024-2025, Sem1 *)
(* Version of 12 Sep 2024 *)

(* ********** *)

(* student name: Adam Chan
   e-mail address: adam.chan@u.yale-nus.edu.sg
   student ID number: A0242453O)
 *)

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

(* ********** *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 =>
    0
  | S n' =>
    match n' with
    | 0 =>
      1
    | S n'' =>
      fib n'' + fib n'
    end
  end.

Lemma fold_unfold_fib_O :
  fib 0 =
  0.
Proof.
  fold_unfold_tactic fib.
Qed.

Lemma fold_unfold_fib_S :
  forall n' : nat,
    fib (S n') =
    match n' with
    | 0 =>
      1
    | S n'' =>
      fib n'' + fib n'
    end.
Proof.
  fold_unfold_tactic fib.
Qed.

Corollary fold_unfold_fib_1 :
  fib 1 =
  1.
Proof.
  rewrite -> fold_unfold_fib_S.
  reflexivity.
Qed.

Corollary fold_unfold_fib_SS :
  forall n'' : nat,
    fib (S (S n'')) =
    fib n'' + fib (S n'').
Proof.
  intro n''.
  rewrite -> fold_unfold_fib_S.
  reflexivity.
Qed.

(* ********** *)

Theorem evenness_of_fibonacci :
  forall (n : nat),
    exists (q2 : nat),
      fib n = 2 * q2 <->
      exists (q3 : nat),
        n = 3 * q3.
Proof.
Admitted.

Theorem oddness_of_fibonacci :
  forall (n : nat),
    exists (q2 : nat),
      fib n = 2 * q2 + 1 <->
      exists (q3 : nat),
        n = 3 * q3 + 1 \/
          n = 3 * q3 + 2.
Proof.
Admitted.

(* ********** *)

(* end of midterm_fibonacci.v)
