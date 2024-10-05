(* nested-summations.v *)
(* Singapore, Oct 2023 - Aug 2024 *)
(* Olivier Danvy <danvy@acm.org> *)

(* This .v file accompanies "Nested Summations".
   It loads with versions 8.5pl3, 8.8.0, and 8.19.1. *)

(*
   JENSFEST '24, October 22, 2024, Pasadena, CA, USA
   (C) 2024 Copyright is held by the owner/author(s). Publication rights licensed to ACM.
   ACM 979-8-4007-1257-9/24/10
   https://doi.org/10.1145/3694848.3694858
*)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

(* Summation functions: from 0, and then from 1. *)

(* ***** *)

Fixpoint Sigma0 (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O =>
    f 0
  | S n' =>
    Sigma0 n' f + f n
  end.

Lemma fold_unfold_Sigma0_O :
  forall (f : nat -> nat),
    Sigma0 0 f =
    f 0.
Proof.
  fold_unfold_tactic Sigma0.
Qed.

Lemma fold_unfold_Sigma0_S :
  forall (n' : nat)
         (f : nat -> nat),
    Sigma0 (S n') f =
    Sigma0 n' f + f (S n').
Proof.
  fold_unfold_tactic Sigma0.
Qed.

Lemma about_Sigma0_with_two_equivalent_functions :
  forall (x : nat)
         (f g : nat -> nat),
    (forall i : nat,
        f i = g i) ->
    Sigma0 x f = Sigma0 x g.
Proof.
  intros x f g eq_f_g.
  induction x as [ | x' IHx'].
  - rewrite ->2 fold_unfold_Sigma0_O.
    exact (eq_f_g 0).
  - rewrite ->2 fold_unfold_Sigma0_S.
    rewrite -> IHx'.
    rewrite -> (eq_f_g (S x')).
    reflexivity.
Qed.

(* ***** *)

Fixpoint Sigma1 (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O =>
    0
  | S n' =>
    Sigma1 n' f + f n
  end.

Lemma fold_unfold_Sigma1_O :
  forall (f : nat -> nat),
    Sigma1 0 f =
    0.
Proof.
  fold_unfold_tactic Sigma1.
Qed.

Lemma fold_unfold_Sigma1_S :
  forall (n' : nat)
         (f : nat -> nat),
    Sigma1 (S n') f =
    Sigma1 n' f + f (S n').
Proof.
  fold_unfold_tactic Sigma1.
Qed.

Lemma about_Sigma1_with_two_equivalent_functions :
  forall (x : nat)
         (f g : nat -> nat),
    (forall i : nat,
        f i = g i) ->
    Sigma1 x f = Sigma1 x g.
Proof.
  intros x f g eq_f_g.
  induction x as [ | x' IHx'].
  - rewrite ->2 fold_unfold_Sigma1_O.
    reflexivity.
  - rewrite ->2 fold_unfold_Sigma1_S.
    rewrite -> IHx'.
    rewrite -> (eq_f_g (S x')).
    reflexivity.
Qed.

(* ********** *)

(* Second-order, third-order, etc. induction principles. *)

(* ***** *)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (H2 : P n /\ P (S n)).
  { induction n as [ | n' [IHn' IHSn']].
    - Check (conj H_P0 H_P1).
      exact (conj H_P0 H_P1).
    - Check (H_PSS n' IHn' IHSn').
      Check (conj IHSn' (H_PSS n' IHn' IHSn')).
      exact (conj IHSn' (H_PSS n' IHn' IHSn')).
  } 
  destruct H2 as [ly _].
  exact ly.
Qed.

(* ***** *)

Lemma nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n)))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (H3 : P n /\ P (S n) /\ P (S (S n))).
  { induction n as [ | n' [IHn' [IHSn' IHSSn']]].
    - exact (conj H_P0 (conj H_P1 H_P2)).
    - Check (H_PSSS n' IHn' IHSn' IHSSn').
      exact (conj IHSn' (conj IHSSn' (H_PSSS n' IHn' IHSn' IHSSn'))).
  }
  destruct H3 as [ly _].
  exact ly.
Qed.

(* ***** *)

Lemma nat_ind4 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    P 3 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n))) -> P (S (S (S (S n))))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_P2 H_P3 H_PSSSS n.
  assert (H4 : P n /\ P (S n) /\ P (S (S n)) /\ P (S (S (S n)))).
  { induction n as [ | n' [IHn' [IHSn' [IHSSn' IHSSSn']]]].
    - exact (conj H_P0 (conj H_P1 (conj H_P2 H_P3))).
    - Check (H_PSSSS n' IHn' IHSn' IHSSn' IHSSSn').
      exact (conj IHSn' (conj IHSSn' (conj IHSSSn' (H_PSSSS n' IHn' IHSn' IHSSn' IHSSSn')))).
  }
  destruct H4 as [ly _].
  exact ly.
Qed.

(* ***** *)

Lemma nat_ind5 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    P 3 ->
    P 4 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n))) -> P (S (S (S (S n)))) -> P (S (S (S (S (S n)))))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_P2 H_P3 H_P4 H_PSSSSS n.
  assert (H5 : P n /\ P (S n) /\ P (S (S n)) /\ P (S (S (S n))) /\ P (S (S (S (S n))))).
  { induction n as [ | n' [IHn' [IHSn' [IHSSn' [IHSSSn' IHSSSSn']]]]].
    - exact (conj H_P0 (conj H_P1 (conj H_P2 (conj H_P3 H_P4)))).
    - Check (H_PSSSSS n' IHn' IHSn' IHSSn' IHSSSn' IHSSSSn').
      exact (conj IHSn' (conj IHSSn' (conj IHSSSn' (conj IHSSSSn' (H_PSSSSS n' IHn' IHSn' IHSSn' IHSSSn' IHSSSSn'))))).
  }
  destruct H5 as [ly _].
  exact ly.
Qed.

(* ********** *)

(* Definition 2.1: the Fibonacci function *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 =>
    0
  | S n' =>
    match n' with
    | 0 =>
      1
    | S n'' =>
      fib n' + fib n''
    end
  end.

(* ***** *)

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
      fib n' + fib n''
    end.
Proof.
  fold_unfold_tactic fib.
Qed.

Corollary fold_unfold_fib_SO :
  fib 1 =
  1.
Proof.
  rewrite -> fold_unfold_fib_S.
  reflexivity.
Qed.

Corollary fold_unfold_fib_SS :
  forall n'' : nat,
    fib (S (S n'')) =
    fib (S n'') + fib n''.
Proof.
  intro n''.
  rewrite -> fold_unfold_fib_S.
  reflexivity.
Qed.

(* ********** *)

Fixpoint fib_sum_aux (f : nat -> nat) (n i : nat) : nat :=
  match n with
    O =>
    f (1 - i)
  | S n' =>
    Sigma0 (1 - i) (fun j => fib_sum_aux f n' j)
  end.

Definition fib_sum_f (n : nat) : nat :=
  match n with
    O => 
    0
  | S _ =>
    1
  end.

Definition fib_sum (n : nat) : nat :=
  Sigma0 1 (fun i => fib_sum_aux fib_sum_f n i).

(* ***** *)

Lemma fold_unfold_fib_sum_aux_O :
  forall (f : nat -> nat)
         (i : nat),
    fib_sum_aux f O i =
    f (1 - i).
Proof.
  fold_unfold_tactic fib_sum_aux.
Qed.

Lemma fold_unfold_fib_sum_aux_S :
  forall (f : nat -> nat)
         (n' i : nat),
    fib_sum_aux f (S n') i =
    Sigma0 (1 - i) (fun j => fib_sum_aux f n' j).
Proof.
  fold_unfold_tactic fib_sum_aux.
Qed.

(* ********** *)

(* Lemma 1.3 *)

Lemma about_fib_sum_aux_and_fib_0 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall n : nat,
      fib_sum_aux f n 0 = fib (S n).
Proof.
  Compute (let f n := n in
           let n := 5 in
           fib_sum_aux f n 0 = fib (S n)).
  intros f H_f_0 H_f_1 n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite ->2 fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    simpl (1 - 1).
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    exact (eq_sym (fold_unfold_fib_SS (S n'))).
Qed.

(* ***** *)

Lemma about_fib_sum_aux_and_fib_1 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall n : nat,
      fib_sum_aux f n 1 = fib n.
Proof.
  Compute (let f n := n in
           let n := 5 in
           fib_sum_aux f n 1 = fib n).
  intros f H_f_0 H_f_1 [ | n'].
  - rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 1).
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    exact (about_fib_sum_aux_and_fib_0 f H_f_0 H_f_1 n').
Qed.

(* ***** *)

(* Theorem 1.2 *)

Compute ((fib_sum 0 =? fib 2)
         &&
         (fib_sum 1 =? fib 3)
         &&
         (fib_sum 2 =? fib 4)
         &&
         (fib_sum 3 =? fib 5)
         &&
         (fib_sum 4 =? fib 6)
         &&
         (fib_sum 5 =? fib 7)).

Theorem Fibonacci_numbers_as_nested_sums :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall n : nat,
      Sigma0 1 (fun i => fib_sum_aux f n i) = fib (n + 2).
Proof.
  (* Proof using Lemmas about_fib_sum_aux_and_fib_0 and about_fib_sum_aux_and_fib_1: *)
  intros f H_f_0 H_f_1 n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  rewrite -> (about_fib_sum_aux_and_fib_0 f H_f_0 H_f_1 n).
  rewrite -> (about_fib_sum_aux_and_fib_1 f H_f_0 H_f_1 n).
  exact (eq_sym (fold_unfold_fib_SS n)).

  Restart.

  (* Self-contained proof, as in the opening of Section 1: *)
  intros f H_f_0 H_f_1 n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite ->2 fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    simpl (1 - 1).
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->2 fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite ->2 fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    simpl (1 - 1).
    rewrite -> H_f_0.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    symmetry.
    exact (fold_unfold_fib_SS (S (S n'))).
Qed.

(* ***** *)

(* Section 1.2 *)

(* A002449 = 1, 1, 2, 6, 26, 166, 1626, 25510, ... *)

(* Irwin's conjecture: *)

Compute ((Sigma1 2 (fun i1 => 1) =? 2)
         &&
         (Sigma1 2 (fun i1 => Sigma1 (2 * i1) (fun i2 => 1)) =? 6)
         &&
         (Sigma1 2 (fun i1 => Sigma1 (2 * i1) (fun i2 => Sigma1 (2 * i2) (fun i3 => 1))) =? 26)
         &&
         (Sigma1 2 (fun i1 => Sigma1 (2 * i1) (fun i2 => Sigma1 (2 * i2) (fun i3 => Sigma1 (2 * i3) (fun i4 => 1)))) =? 166)
         &&
         (Sigma1 2 (fun i1 => Sigma1 (2 * i1) (fun i2 => Sigma1 (2 * i2) (fun i3 => Sigma1 (2 * i3) (fun i4 => Sigma1 (2 * i4) (fun i5 => 1))))) =? 1626)).

Fixpoint fib_sum_Lahlou (n i : nat) : nat :=
  match n with
    O =>
    3 - i
  | S n' =>
    Sigma1 (3 - i) (fun j => fib_sum_Lahlou n' j)
  end.

Lemma fold_unfold_fib_sum_Lahlou_O :
  forall i : nat,
    fib_sum_Lahlou 0 i =
    3 - i.
Proof.
  fold_unfold_tactic fib_sum_Lahlou.
Qed.

Lemma fold_unfold_fib_sum_Lahlou_S :
  forall n' i : nat,
    fib_sum_Lahlou (S n') i =
    Sigma1 (3 - i) (fun j => fib_sum_Lahlou n' j).
Proof.
  fold_unfold_tactic fib_sum_Lahlou.
Qed.

Definition fib_Lahlou (n : nat) : nat :=
  match n with
    O =>
    1
  | S O =>
    1
  | S (S n'') =>
    Sigma1 1 (fun j => fib_sum_Lahlou n'' j)
  end.

Compute ((fib_Lahlou 0 =? fib 1)
         && 
         (fib_Lahlou 1 =? fib 2)
         &&
         (fib_Lahlou 2 =? fib 3)
         && 
         (fib_Lahlou 3 =? fib 4)
         &&
         (fib_Lahlou 4 =? fib 5)).

(* Theorem 1.4 *)

Theorem Fibonacci_numbers_as_nested_sums_Lahlou :
  forall n : nat,
    fib_Lahlou n = fib (S n).
Proof.
  intros [ | [ | n]]; unfold fib_Lahlou.
  - compute.
    reflexivity.
  - compute.
    reflexivity.
  - rewrite -> fold_unfold_Sigma1_S.
    rewrite -> fold_unfold_Sigma1_O.
    rewrite -> Nat.add_0_l.
    induction n as [ | | n' IHn' IHSn'] using nat_ind2.
    + compute.
      reflexivity.
    + compute.
      reflexivity.
    + rewrite -> fold_unfold_fib_sum_Lahlou_S.
      simpl (3 - 1).
      rewrite ->2 fold_unfold_Sigma1_S.
      rewrite -> fold_unfold_Sigma1_O.
      rewrite -> Nat.add_0_l.
      rewrite -> IHSn'.
      rewrite -> fold_unfold_fib_sum_Lahlou_S.
      simpl (3 - 2).
      rewrite -> fold_unfold_Sigma1_S.
      rewrite -> fold_unfold_Sigma1_O.
      rewrite -> Nat.add_0_l.
      rewrite -> IHn'.
      exact (eq_sym (fold_unfold_fib_SS (S (S (S n'))))).
Qed.

(* ***** *)

Fixpoint binomial_coefficient (n k : nat) : nat :=
  match n with
    O =>
    match k with
      O =>
      1
    | S k' =>
      0
    end
  | S n' =>
    match k with
      O =>
      1
    | S k' =>
      binomial_coefficient n' k' + binomial_coefficient n' (S k')
    end
  end.

Lemma fold_unfold_binomial_coefficient_O :
  forall k : nat,
    binomial_coefficient 0 k =
    match k with
      O =>
      1
    | S k' =>
      0
    end.
Proof.
  fold_unfold_tactic binomial_coefficient.
Qed.

Lemma fold_unfold_binomial_coefficient_S :
  forall n' k : nat,
    binomial_coefficient (S n') k =
    match k with
      O =>
      1
    | S k' =>
      binomial_coefficient n' k' + binomial_coefficient n' (S k')
    end.
Proof.
  fold_unfold_tactic binomial_coefficient.
Qed.

Lemma about_binomial_coefficient_n_more_than_n :
  forall n k : nat,
    n < k <-> binomial_coefficient n k = 0.
Proof.
  intro n.
  induction n as [ | n' IHn']; intro k.
  - split.
    + intro H_k.
      case k as [ | k'].
      * Search (~ (_ < _)).
        Check (Nat.lt_irrefl 0 H_k).
        contradiction (Nat.lt_irrefl 0 H_k).
      * rewrite -> fold_unfold_binomial_coefficient_O.
        reflexivity.
    + intro H_k.
      case k as [ | k'].
      * rewrite -> fold_unfold_binomial_coefficient_O in H_k.
        discriminate H_k.
      * Search (0 < S _).
        exact (Nat.lt_0_succ k').
  - split.
    + intro H_k.
      case k as [ | k'].
      * Search (_ < 0).
        Check (Nat.nlt_0_r (S n') H_k).
        contradiction (Nat.nlt_0_r (S n') H_k).
      * rewrite -> fold_unfold_binomial_coefficient_S.
        destruct (IHn' k') as [lt_implies_O O_implies_lt].
        Search (S _ < S _ -> _ < _).
        assert (lt_S_n : forall n m : nat, S n < S m -> n < m).
        { exact (fun n m : nat => proj2 (Nat.succ_lt_mono n m)). }
        Check (lt_implies_O (lt_S_n n' k' H_k)).
        rewrite -> (lt_implies_O (lt_S_n n' k' H_k)).
        rewrite -> Nat.add_0_l.
        destruct (IHn' (S k')) as [lt_implies_O' O_implies_lt'].
        Search (_ < _ -> _ < _ -> _ < _).
        Check (Nat.lt_trans n' (S n') (S k')).
        Search (_ < S _).
        Check (Nat.lt_succ_diag_r n').
        Check (Nat.lt_trans n' (S n') (S k') (Nat.lt_succ_diag_r n')).
        Check (Nat.lt_trans n' (S n') (S k') (Nat.lt_succ_diag_r n') H_k).
        Check (lt_implies_O' (Nat.lt_trans n' (S n') (S k') (Nat.lt_succ_diag_r n') H_k)).
        exact (lt_implies_O' (Nat.lt_trans n' (S n') (S k') (Nat.lt_succ_diag_r n') H_k)).
    + intro H_k.
      case k as [ | k'].
      * rewrite -> fold_unfold_binomial_coefficient_S in H_k.
        discriminate H_k.
      * rewrite -> fold_unfold_binomial_coefficient_S in H_k.
        Search (_ + _ = 0).
        destruct (Nat.eq_add_0 (binomial_coefficient n' k') (binomial_coefficient n' (S k'))) as [key _].
        destruct (key H_k) as [H_n'_k' H_n'_Sk'].
        destruct (IHn' k') as [lt_implies_O O_implies_lt].
        Check (O_implies_lt H_n'_k').
        Search (_ < _ -> S _ < S _).
        Search (S _ < S _).
        destruct (Nat.succ_lt_mono n' k') as [lt_n_S _].
        Check (lt_n_S (O_implies_lt H_n'_k')).
        exact (lt_n_S (O_implies_lt H_n'_k')).
Qed.

Lemma about_binomial_coefficients_n_0 :
  forall n : nat,
    binomial_coefficient n 0 = 1.
Proof.
  intros [ | n'].
  - rewrite -> fold_unfold_binomial_coefficient_O.
    reflexivity.
  - rewrite -> fold_unfold_binomial_coefficient_S.
    reflexivity.
Qed.

Fixpoint binomial_coefficient_sum1 (n i : nat) : nat :=
  match n with
    O =>
    1
  | S n' =>
    Sigma1 i (fun i => binomial_coefficient_sum1 n' i)
  end.

Lemma fold_unfold_binomial_coefficient_sum1_O :
  forall i : nat,
    binomial_coefficient_sum1 O i =
    1.
Proof.
  fold_unfold_tactic binomial_coefficient_sum1.
Qed.

Lemma fold_unfold_binomial_coefficient_sum1_S :
  forall n' i : nat,
    binomial_coefficient_sum1 (S n') i =
    Sigma1 i (fun i => binomial_coefficient_sum1 n' i).
Proof.
  fold_unfold_tactic binomial_coefficient_sum1.
Qed.

Compute ((let x := 3 in
          let n := 0 in
          (binomial_coefficient_sum1 n x =? binomial_coefficient (x + n - 1) n))
         &&
         (let x := 3 in
          let n := 1 in
          (binomial_coefficient_sum1 n x =? binomial_coefficient (x + n - 1) n))
         &&
         (let x := 3 in
          let n := 2 in
          (binomial_coefficient_sum1 n x =? binomial_coefficient (x + n - 1) n))
         &&
         (let x := 5 in
          let n := 2 in
          (binomial_coefficient_sum1 n x =? binomial_coefficient (x + n - 1) n))
         &&
         (let x := 5 in
          let n := 3 in
          (binomial_coefficient_sum1 n x =? binomial_coefficient (x + n - 1) n))).

Theorem Multiset_coefficients_as_nested_sums_Rosen :
  forall x n : nat,
    binomial_coefficient_sum1 n x = binomial_coefficient (x + n - 1) n.
Proof.
  intros x n.
  revert x.
  induction n as [ | n' IHn']; intro x.
  - rewrite -> fold_unfold_binomial_coefficient_sum1_O.
    rewrite -> about_binomial_coefficients_n_0.
    reflexivity.
  - rewrite -> fold_unfold_binomial_coefficient_sum1_S.
    Check (about_Sigma1_with_two_equivalent_functions x (fun i => binomial_coefficient_sum1 n' i) (fun i => binomial_coefficient (i + n' - 1) n') IHn').
    rewrite -> (about_Sigma1_with_two_equivalent_functions x (fun i => binomial_coefficient_sum1 n' i) (fun i => binomial_coefficient (i + n' - 1) n') IHn').
    clear IHn'.
    rewrite <- plus_n_Sm.
    rewrite -> Nat.sub_succ.
    rewrite -> Nat.sub_0_r.
    induction x as [ | x' IHx'].
    + rewrite -> fold_unfold_Sigma1_O.
      rewrite -> Nat.add_0_l.
      destruct (about_binomial_coefficient_n_more_than_n n' (S n')) as [H_key _].
      exact (eq_sym (H_key (Nat.lt_succ_diag_r n'))).
    + rewrite -> fold_unfold_Sigma1_S.
      rewrite -> IHx'.
      rewrite -> plus_Sn_m.
      rewrite -> Nat.sub_succ.
      rewrite -> Nat.sub_0_r.
      rewrite -> (fold_unfold_binomial_coefficient_S (x' + n') (S n')).
      apply Nat.add_comm.
Qed.

(* ***** *)

(* Catalan numbers (Grimaldi and Rosen) *)

Compute ((1
          =? 1)
         &&
         (Sigma1 1 (fun i1 => 1)
          =? 1)
         &&
         (Sigma1 1 (fun i1 => Sigma1 (i1 + 1) (fun i2 => 1))
          =? 2)
         &&
         (Sigma1 1 (fun i1 => Sigma1 (i1 + 1) (fun i2 => Sigma1 (i2 + 1) (fun i3 => 1)))
          =? 5)
         &&
         (Sigma1 1 (fun i1 => Sigma1 (i1 + 1) (fun i2 => Sigma1 (i2 + 1) (fun i3 => Sigma1 (i3 + 1) (fun i4 => 1))))
          =? 14)
         &&
         (Sigma1 1 (fun i1 => Sigma1 (i1 + 1) (fun i2 => Sigma1 (i2 + 1) (fun i3 => Sigma1 (i3 + 1) (fun i4 => Sigma1 (i4 + 1) (fun i5 => 1)))))
          =? 42)
         &&
         (Sigma1 1 (fun i1 => Sigma1 (i1 + 1) (fun i2 => Sigma1 (i2 + 1) (fun i3 => Sigma1 (i3 + 1) (fun i4 => Sigma1 (i4 + 1) (fun i5 => Sigma1 (i5 + 1) (fun i6 => 1))))))
          =? 132)).

(* Catalan numbers (via Moessner) *)

Compute ((1
          =? 1)
         &&
         (Sigma0 0 (fun i1 => 1)
          =? 1)
         &&
         (Sigma0 0 (fun i1 => Sigma0 (i1 + 1) (fun i2 => 1))
          =? 2)
         &&
         (Sigma0 0 (fun i1 => Sigma0 (i1 + 1) (fun i2 => Sigma0 (i2 + 1) (fun i3 => 1)))
          =? 5)
         &&
         (Sigma0 0 (fun i1 => Sigma0 (i1 + 1) (fun i2 => Sigma0 (i2 + 1) (fun i3 => Sigma0 (i3 + 1) (fun i4 => 1))))
          =? 14)
         &&
         (Sigma0 0 (fun i1 => Sigma0 (i1 + 1) (fun i2 => Sigma0 (i2 + 1) (fun i3 => Sigma0 (i3 + 1) (fun i4 => Sigma0 (i4 + 1) (fun i5 => 1)))))
          =? 42)
         &&
         (Sigma0 0 (fun i1 => Sigma0 (i1 + 1) (fun i2 => Sigma0 (i2 + 1) (fun i3 => Sigma0 (i3 + 1) (fun i4 => Sigma0 (i4 + 1) (fun i5 => Sigma0 (i5 + 1) (fun i7 => 1))))))
          =? 132)).

(* ********** *)

(* Section 2 *)

(* ***** *)

Proposition Proposition_2_dot_1 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall (m : nat)
           (g : nat -> nat),
    (forall j : nat,
        g j = fib_sum_aux f m (1 - j)) ->
    forall n : nat,
      Sigma0 1 (fun i => fib_sum_aux g n i) = fib (n + m + 2).
Proof.
  Compute (let f j := j in
           let m := 5 in
           let g j := fib_sum_aux f m (1 - j) in
           let n := 3 in
           Sigma0 1 (fun i => fib_sum_aux g n i) = fib (n + m + 2)).
  intros f H_f_0 H_f_1 m g H_g n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (Nat.add_comm (n + m) 2); simpl (2 + (n + m)).
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> (H_g 1).
    simpl (1 - 1).
    rewrite -> (about_fib_sum_aux_and_fib_0 f H_f_0 H_f_1 m).
    rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 1).
    rewrite -> (H_g 0).
    simpl (1 - 0).
    rewrite -> (about_fib_sum_aux_and_fib_1 f H_f_0 H_f_1 m).
    rewrite -> Nat.add_0_l.
    exact (eq_sym (fold_unfold_fib_SS m)).
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> (H_g 1).
    simpl (1 - 1).
    rewrite -> (about_fib_sum_aux_and_fib_0 f H_f_0 H_f_1 m).
    rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 1).
    rewrite -> (H_g 0).
    simpl (1 - 0).
    rewrite -> (about_fib_sum_aux_and_fib_1 f H_f_0 H_f_1 m).
    rewrite <- (fold_unfold_fib_SS m).
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> (H_g 1).
    simpl (1 - 1).
    rewrite -> (about_fib_sum_aux_and_fib_0 f H_f_0 H_f_1 m).
    rewrite -> (Nat.add_1_l m).
    exact (eq_sym (fold_unfold_fib_SS (S m))).
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    rewrite -> (plus_Sn_m n' m).
    rewrite -> (plus_Sn_m (S n') m).
    rewrite -> (plus_Sn_m n' m).
    exact (eq_sym (fold_unfold_fib_SS (S (S (n' + m))))).
Qed.

(* ***** *)

Fixpoint A006356 (n : nat) : nat :=
  match n with
    O =>
    1
  | S n' =>
    match n' with
      O =>
      3
    | S n'' =>
      match n'' with
        O =>
        6
      | S n''' =>
        2 * A006356 n' + A006356 n'' - A006356 n'''
      end
    end
  end.

Lemma fold_unfold_A006356_O :
  A006356 0 =
  1.
Proof.
  fold_unfold_tactic A006356.
Qed.

Lemma fold_unfold_A006356_S :
  forall n' : nat,
    A006356 (S n') =
    match n' with
      O =>
      3
    | S n'' =>
      match n'' with
        O =>
        6
      | S n''' =>
        2 * A006356 n' + A006356 n'' - A006356 n'''
      end
    end.
Proof.
  fold_unfold_tactic A006356.
Qed.

Corollary fold_unfold_A006356_SO :
  A006356 1 =
  3.
Proof.
  rewrite -> fold_unfold_A006356_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006356_SS :
  forall n'' : nat,
    A006356 (S (S n'')) =
    match n'' with
      O =>
      6
    | S n''' =>
      2 * A006356 (S n'') + A006356 n'' - A006356 n'''
    end.
Proof.
  intros [ | n'''].
  - rewrite -> fold_unfold_A006356_S.
    reflexivity.
  - rewrite -> fold_unfold_A006356_S.
    reflexivity.
Qed.

Corollary fold_unfold_A006356_SSO :
  A006356 2 =
  6.
Proof.
  rewrite -> fold_unfold_A006356_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006356_SSS :
  forall n''' : nat,
    A006356 (S (S (S n'''))) =
    2 * A006356 (S (S n''')) + A006356 (S n''') - A006356 n'''.
Proof.
  intro n'''.
  rewrite -> fold_unfold_A006356_S.
  reflexivity.
Qed.

(* ***** *)

Fixpoint A006356_sum_aux (f : nat -> nat) (n i : nat) : nat :=
  match n with
    O =>
    f (2 - i)
  | S n' =>
    Sigma0 (2 - i) (fun j => A006356_sum_aux f n' j)
  end.

Definition A006356_sum_f (n : nat) : nat :=
  match n with
    O => 
    0
  | S O =>
    0
  | S (S _) =>
    1
  end.

Definition A006356_sum (n : nat) : nat :=
  Sigma0 2 (fun i => A006356_sum_aux A006356_sum_f n i).

(* ***** *)

Lemma fold_unfold_A006356_sum_aux_O :
  forall (f : nat -> nat)
         (i : nat),
    A006356_sum_aux f O i =
    f (2 - i).
Proof.
  fold_unfold_tactic A006356_sum_aux.
Qed.

Lemma fold_unfold_A006356_sum_aux_S :
  forall (f : nat -> nat)
         (n' i : nat),
    A006356_sum_aux f (S n') i =
    Sigma0 (2 - i) (fun j => A006356_sum_aux f n' j).
Proof.
  fold_unfold_tactic A006356_sum_aux.
Qed.

(* ***** *)

Compute ((A006356_sum 0 =? A006356 0)
         &&
         (A006356_sum 1 =? A006356 1)
         &&
         (A006356_sum 2 =? A006356 2)
         &&
         (A006356_sum 3 =? A006356 3)).

Theorem Theorem_2_dot_3 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 0 ->
    f 2 = 1 ->
    forall n : nat,
      Sigma0 2 (fun i => A006356_sum_aux f n i) = A006356 n.
Proof.
  intros f H_f_0 H_f_1 H_f_2 n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  induction n as [ | | | n' IHn' IHSn' IHSSn'] using nat_ind3.
  - simpl.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_A006356_SSS.
    rewrite <- IHSSn'.
    rewrite <- IHSn'.
    rewrite <- IHn'.
    simpl.
    remember (A006356_sum_aux f n' 0) as x0 eqn:E_x0.
    remember (A006356_sum_aux f n' 1) as x1 eqn:E_x1.
    remember (A006356_sum_aux f n' 2) as x2 eqn:E_x2.
    Search (_ + _ + _).
    assert (tmp :
              x0 + x1 + x2 + (x0 + x1) + x0 = (x0 + x1) + x0 + (x0 + x1 + x2)).
    { ring. }
    rewrite -> tmp.
    rewrite -> (Nat.add_assoc (x0 + x1 + x0 + (x0 + x1 + x2) + (x0 + x1 + x2 + (x0 + x1)) + (x0 + x1 + x2) + (x0 + x1 + x0 + (x0 + x1 + x2) + (x0 + x1 + x2 + (x0 + x1)) + (x0 + x1 + x2) + 0)) (x0 + x1 + x0) (x0 + x1 + x2)).
    rewrite -> (Nat.add_sub (x0 + x1 + x0 + (x0 + x1 + x2) + (x0 + x1 + x2 + (x0 + x1)) + (x0 + x1 + x2) + (x0 + x1 + x0 + (x0 + x1 + x2) + (x0 + x1 + x2 + (x0 + x1)) + (x0 + x1 + x2) + 0) + (x0 + x1 + x0)) (x0 + x1 + x2)).
    ring.
Qed.

(* ********** *)

(* Definition 2.4: the Lucas function *)

Fixpoint luc (n : nat) : nat :=
  match n with
  | 0 =>
    2
  | S n' =>
    match n' with
    | 0 =>
      1
    | S n'' =>
      luc n' + luc n''
    end
  end.

Lemma fold_unfold_luc_O :
  luc 0 =
  2.
Proof.
  fold_unfold_tactic luc.
Qed.

Lemma fold_unfold_luc_S :
  forall n' : nat,
    luc (S n') =
    match n' with
    | 0 =>
      1
    | S n'' =>
      luc n' + luc n''
    end.
Proof.
  fold_unfold_tactic luc.
Qed.

Corollary fold_unfold_luc_SO :
  luc 1 =
  1.
Proof.
  rewrite -> fold_unfold_luc_S.
  reflexivity.
Qed.

Corollary fold_unfold_luc_SS :
  forall n'' : nat,
    luc (S (S n'')) =
    luc (S n'') + luc n''.
Proof.
  intro n''.
  rewrite -> fold_unfold_luc_S.
  reflexivity.
Qed.

(* ***** *)

(* Theorem 2.5 *)

Theorem Lucas_numbers_in_term_of_Fibonacci_numbers :
  forall n : nat,
    luc (S n) = fib (S n) + 2 * fib n.
Proof.
  Compute (let n := 0 in luc (S n) = fib (S n) + 2 * fib n).
  Compute (let n := 1 in luc (S n) = fib (S n) + 2 * fib n).
  Compute (let n := 2 in luc (S n) = fib (S n) + 2 * fib n).
  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - compute.
    reflexivity.
  - compute.
    reflexivity.
  - rewrite -> fold_unfold_luc_SS.
    rewrite -> fold_unfold_fib_SS.
    rewrite -> IHSn'.
    rewrite -> IHn'.
    rewrite -> fold_unfold_fib_SS.
    ring.
Qed.

(* ********** *)

(* Definition 3.1: the Fibonacci function parameterized with its zero case *)

Fixpoint fibz (z n : nat) : nat :=
  match n with
  | 0 =>
    z
  | S n' =>
    match n' with
    | 0 =>
      1
    | S n'' =>
      fibz z n' + fibz z n''
    end
  end.

Lemma fold_unfold_fibz_O :
  forall z : nat,
    fibz z 0 =
    z.
Proof.
  fold_unfold_tactic fibz.
Qed.

Lemma fold_unfold_fibz_S :
  forall z n' : nat,
    fibz z (S n') =
    match n' with
    | 0 =>
      1
    | S n'' =>
      fibz z n' + fibz z n''
    end.
Proof.
  fold_unfold_tactic fibz.
Qed.

Corollary fold_unfold_fibz_SO :
  forall z : nat,
    fibz z 1 =
    1.
Proof.
  intro z.
  rewrite -> fold_unfold_fibz_S.
  reflexivity.
Qed.

Corollary fold_unfold_fibz_SS :
  forall z n'' : nat,
    fibz z (S (S n'')) =
    fibz z (S n'') + fibz z n''.
Proof.
  intros z n''.
  rewrite -> fold_unfold_fibz_S.
  reflexivity.
Qed.

(* ***** *)

Proposition about_fibz_0 :
  forall n : nat,
    fibz 0 n = fib n.
Proof.
  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fibz_O.
    rewrite -> fold_unfold_fib_O.
    reflexivity.
  - rewrite -> fold_unfold_fibz_SO.
    rewrite -> fold_unfold_fib_SO.
    reflexivity.
  - rewrite -> fold_unfold_fibz_SS.
    rewrite -> fold_unfold_fib_SS.
    rewrite -> IHn'.
    rewrite -> IHSn'.
    reflexivity.
Qed.

(* ***** *)

Proposition about_fibz_2 :
  forall n : nat,
    fibz 2 n = luc n.
Proof.
  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fibz_O.
    rewrite -> fold_unfold_luc_O.
    reflexivity.
  - rewrite -> fold_unfold_fibz_SO.
    rewrite -> fold_unfold_luc_SO.
    reflexivity.
  - rewrite -> fold_unfold_fibz_SS.
    rewrite -> fold_unfold_luc_SS.
    rewrite -> IHn'.
    rewrite -> IHSn'.
    reflexivity.
Qed.

(* ***** *)

(* Theorem 3.2: *)

Theorem Members_of_Fibonacci_sequences_parameterized_with_their_zero_case_in_terms_of_Fibonacci_numbers :
  forall z n : nat,
    fibz z (S n) = fib (S n) + z * fib n.
Proof.
  intros z n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fibz_SO.
    rewrite -> fold_unfold_fib_SO.
    rewrite -> fold_unfold_fib_O.
    ring.
  - rewrite -> fold_unfold_fibz_SS.
    rewrite -> fold_unfold_fibz_SO.
    rewrite -> fold_unfold_fibz_O.
    rewrite -> fold_unfold_fib_SS.
    rewrite -> fold_unfold_fib_SO.
    rewrite -> fold_unfold_fib_O.
    ring.
  - rewrite -> fold_unfold_fibz_SS.
    rewrite -> fold_unfold_fib_SS.
    rewrite -> IHn'.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_fib_SS.
    ring.
Qed.    

(* ***** *)

Lemma about_fib_sum_aux_and_fibz_0 :
  forall (z : nat)
         (f : nat -> nat),
    f 0 = z ->
    f 1 = 1 ->
    forall n : nat,
      fib_sum_aux f n 0 = fibz z (S n).
Proof.
  intros z f H_f_0 H_f_1 n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    rewrite -> fold_unfold_fibz_SO.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite ->2 fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    simpl (1 - 1).
    rewrite -> H_f_0.
    rewrite -> fold_unfold_fibz_SS.
    rewrite -> fold_unfold_fibz_SO.
    rewrite -> fold_unfold_fibz_O.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    exact (eq_sym (fold_unfold_fibz_SS z (S n'))).
Qed.

(* ***** *)

Lemma about_fib_sum_aux_and_fibz_1 :
  forall (z : nat)
         (f : nat -> nat),
    f 0 = z ->
    f 1 = 1 ->
    forall n : nat,
      fib_sum_aux f n 1 = fibz z n.
Proof.
  intros z f H_f_0 H_f_1 [ | n'].
  - rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 1).
    rewrite -> H_f_0.
    rewrite -> fold_unfold_fibz_O.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    exact (about_fib_sum_aux_and_fibz_0 z f H_f_0 H_f_1 n').
Qed.

(* ***** *)

(* Theorem 3.3: *)

Theorem Members_of_Fibonacci_sequences_parameterized_with_their_zero_case_as_nested_sums :
  forall (z : nat)
         (f : nat -> nat),
    f 0 = z ->
    f 1 = 1 ->
    forall n : nat,
      Sigma0 1 (fun i => fib_sum_aux f n i) = fibz z (n + 2).
Proof.
  intros z f H_f_0 H_f_1 n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (about_fib_sum_aux_and_fibz_0 z f H_f_0 H_f_1 n).
  rewrite -> (about_fib_sum_aux_and_fibz_1 z f H_f_0 H_f_1 n).
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  exact (eq_sym (fold_unfold_fibz_SS z n)).
Qed.

(* ***** *)

(* Corollary 3.4: *)

Corollary Lucas_numbers_as_nested_sums :
  forall f : nat -> nat,
    f 0 = 2 ->
    f 1 = 1 ->
    forall n : nat,
      Sigma0 1 (fun i => fib_sum_aux f n i) = luc (n + 2).
Proof.
  intros f H_f_0 H_f_1 n.
  rewrite -> (Members_of_Fibonacci_sequences_parameterized_with_their_zero_case_as_nested_sums 2 f H_f_0 H_f_1 n).
  exact (about_fibz_2 (n + 2)).
Qed.

(* ***** *)

(* Definition 3.5: the Fibonacci function parameterized with both its base cases *)

Fixpoint fibf (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 =>
    f 0
  | S n' =>
    match n' with
    | 0 =>
      f 1
    | S n'' =>
      fibf f n' + fibf f n''
    end
  end.

Lemma fold_unfold_fibf_O :
  forall f : nat -> nat,
    fibf f 0 =
    f 0.
Proof.
  fold_unfold_tactic fibf.
Qed.

Lemma fold_unfold_fibf_S :
  forall (f : nat -> nat)
         (n' : nat),
    fibf f (S n') =
    match n' with
    | 0 =>
      f 1
    | S n'' =>
      fibf f n' + fibf f n''
    end.
Proof.
  fold_unfold_tactic fibf.
Qed.

Corollary fold_unfold_fibf_SO :
  forall f : nat -> nat,
    fibf f 1 =
    f 1.
Proof.
  intro f.
  rewrite -> fold_unfold_fibf_S.
  reflexivity.
Qed.

Corollary fold_unfold_fibf_SS :
  forall (f : nat -> nat)
         (n'' : nat),
    fibf f (S (S n'')) =
    fibf f (S n'') + fibf f n''.
Proof.
  intros v n''.
  rewrite -> fold_unfold_fibf_S.
  reflexivity.
Qed.

(* ***** *)

Proposition about_fibf_01 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall n : nat,
      fibf f n = fib n.
Proof.
  intros f H_f_0 H_f_1 n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fibf_O.
    rewrite -> H_f_0.
    rewrite -> fold_unfold_fib_O.
    reflexivity.
  - rewrite -> fold_unfold_fibf_SO.
    rewrite -> H_f_1.
    rewrite -> fold_unfold_fib_SO.
    reflexivity.
  - rewrite -> fold_unfold_fibf_SS.
    rewrite -> fold_unfold_fib_SS.
    rewrite -> IHn'.
    rewrite -> IHSn'.
    reflexivity.
Qed.

(* ***** *)

Proposition about_fibf_21 :
  forall f : nat -> nat,
    f 0 = 2 ->
    f 1 = 1 ->
    forall n : nat,
      fibf f n = luc n.
Proof.
  intros f H_f_0 H_f_1 n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fibf_O.
    rewrite -> H_f_0.
    rewrite -> fold_unfold_luc_O.
    reflexivity.
  - rewrite -> fold_unfold_fibf_SO.
    rewrite -> H_f_1.
    rewrite -> fold_unfold_luc_SO.
    reflexivity.
  - rewrite -> fold_unfold_fibf_SS.
    rewrite -> fold_unfold_luc_SS.
    rewrite -> IHn'.
    rewrite -> IHSn'.
    reflexivity.
Qed.

(* ***** *)

(* Theorem 3.6 *)

Theorem Members_of_Fibonacci_sequences_parameterized_with_their_base_cases_in_terms_of_Fibonacci_numbers :
  forall (f : nat -> nat)
         (n : nat),
    fibf f (S n) = f 1 * fib (S n) + f 0 * fib n.
Proof.
  intros f n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fibf_SO.
    rewrite -> fold_unfold_fib_SO.
    rewrite -> fold_unfold_fib_O.
    ring.
  - rewrite -> fold_unfold_fibf_SS.
    rewrite -> fold_unfold_fibf_SO.
    rewrite -> fold_unfold_fibf_O.
    rewrite -> fold_unfold_fib_SS.
    rewrite -> fold_unfold_fib_SO.
    rewrite -> fold_unfold_fib_O.
    ring.
  - rewrite -> fold_unfold_fibf_SS.
    rewrite -> fold_unfold_fib_SS.
    rewrite -> IHSn'.
    rewrite -> IHn'.
    rewrite -> fold_unfold_fib_SS.
    ring.
Qed.

(* ***** *)

Lemma about_fib_sum_aux_and_fibf_0 :
  forall (f : nat -> nat)
         (n : nat),
    fib_sum_aux f n 0 = fibf f (S n).
Proof.
  intros f n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> fold_unfold_fibf_SO.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite ->2 fold_unfold_fib_sum_aux_O.
    simpl (1 - 0).
    simpl (1 - 1).
    rewrite -> fold_unfold_fibf_SS.
    rewrite -> fold_unfold_fibf_SO.
    rewrite -> fold_unfold_fibf_O.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    exact (eq_sym (fold_unfold_fibf_SS f (S n'))).
Qed.

(* ***** *)

Lemma about_fib_sum_aux_and_fibf_1 :
  forall (f : nat -> nat)
         (n : nat),
    fib_sum_aux f n 1 = fibf f n.
Proof.
  intros f [ | n'].
  - rewrite -> fold_unfold_fib_sum_aux_O.
    simpl (1 - 1).
    rewrite -> fold_unfold_fibf_O.
    reflexivity.
  - rewrite -> fold_unfold_fib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    exact (about_fib_sum_aux_and_fibf_0 f n').
Qed.

(* ***** *)

(* Theorem 3.7: *)

Theorem Members_of_Fibonacci_sequences_parameterized_with_their_base_cases_in_terms_of_Fibonacci_numbers_as_nested_sums :
  forall (f : nat -> nat)
         (n : nat),
      Sigma0 1 (fun i => fib_sum_aux f n i) = fibf f (n + 2).
Proof.
  intros f n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (about_fib_sum_aux_and_fibf_0 f n).
  rewrite -> (about_fib_sum_aux_and_fibf_1 f n).
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  exact (eq_sym (fold_unfold_fibf_SS f n)).
Qed.

(* ********** *)

Fixpoint A006357 (n : nat) : nat :=
  match n with
    O =>
    1
  | S n' =>
    match n' with
      O =>
      4
    | S n'' =>
      match n'' with
        O =>
        10
      | S n''' =>
        match n''' with
          O =>
          30
        | S n'''' =>
          2 * A006357 n' + 3 * A006357 n'' - A006357 n''' - A006357 n''''
        end
      end
    end
  end.

Lemma fold_unfold_A006357_O :
  A006357 0 =
  1.
Proof.
  fold_unfold_tactic A006357.
Qed.

Lemma fold_unfold_A006357_S :
  forall n' : nat,
    A006357 (S n') =
    match n' with
      O =>
      4
    | S n'' =>
      match n'' with
        O =>
        10
      | S n''' =>
        match n''' with
          O =>
          30
        | S n'''' =>
          2 * A006357 n' + 3 * A006357 n'' - A006357 n''' - A006357 n''''
        end
      end
    end.
Proof.
  fold_unfold_tactic A006357.
Qed.

Corollary fold_unfold_A006357_SO :
  A006357 1 =
  4.
Proof.
  rewrite -> fold_unfold_A006357_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006357_SSO :
  A006357 2 =
  10.
Proof.
  rewrite -> fold_unfold_A006357_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006357_SSSO :
  A006357 3 =
  30.
Proof.
  rewrite -> fold_unfold_A006357_S.
  reflexivity.
Qed.

Lemma fold_unfold_A006357_SSSS :
  forall n'''' : nat,
  A006357 (S (S (S (S n'''')))) =
  2 * A006357 (S (S (S n''''))) + 3 * A006357 (S (S n'''')) - A006357 (S n'''') - A006357 n''''.
Proof.
  intro n''''.
  rewrite -> fold_unfold_A006357_S.
  reflexivity.
Qed.

(* ***** *)

Fixpoint A006357_sum_aux (f : nat -> nat) (n i : nat) : nat :=
  match n with
    O =>
    f (3 - i)
  | S n' =>
    Sigma0 (3 - i) (fun j => A006357_sum_aux f n' j)
  end.

Definition A006357_sum_f (n : nat) : nat :=
  match n with
    O => 
    0
  | S O =>
    0
  | S (S O) =>
    0
  | S (S (S _)) =>
    1
  end.

Definition A006357_sum (n : nat) : nat :=
  Sigma0 3 (fun i => A006357_sum_aux A006357_sum_f n i).

(* ***** *)

Lemma fold_unfold_A006357_sum_aux_O :
  forall (f : nat -> nat)
         (i : nat),
    A006357_sum_aux f O i =
    f (3 - i).
Proof.
  fold_unfold_tactic A006357_sum_aux.
Qed.

Lemma fold_unfold_A006357_sum_aux_S :
  forall (f : nat -> nat)
         (n' i : nat),
    A006357_sum_aux f (S n') i =
    Sigma0 (3 - i) (fun j => A006357_sum_aux f n' j).
Proof.
  fold_unfold_tactic A006357_sum_aux.
Qed.

(* ***** *)

Compute ((A006357_sum 0 =? A006357 0)
         &&
         (A006357_sum 1 =? A006357 1)
         &&
         (A006357_sum 2 =? A006357 2)
         &&
         (A006357_sum 3 =? A006357 3)).

(* Theorem 4.1 *)

Theorem Theorem_4_dot_1 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 0 ->
    f 2 = 0 ->
    f 3 = 1 ->
    forall n : nat,
      Sigma0 3 (fun i => A006357_sum_aux f n i) = A006357 n.
Proof.
  intros f H_f_0 H_f_1 H_f_2 H_f_3 n.
  rewrite ->3 fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  induction n as [ | | | | n' IHn' IHSn' IHSSn' IHSSSn'] using nat_ind4.
  - simpl.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_A006357_SSSS.
    rewrite <- IHSSSn'.
    rewrite <- IHSSn'.
    rewrite <- IHSn'.
    rewrite <- IHn'.
    simpl.
    remember (A006357_sum_aux f n' 0) as x0 eqn:E_x0.
    remember (A006357_sum_aux f n' 1) as x1 eqn:E_x1.
    remember (A006357_sum_aux f n' 2) as x2 eqn:E_x2.
    remember (A006357_sum_aux f n' 3) as x3 eqn:E_x3.
    remember (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1) + x0) as y eqn:E_y.
    remember (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1)) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2)) + (x0 + x1 + x2 + x3) + (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1)) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2))) + (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1))) + y + (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1)) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2)) + (x0 + x1 + x2 + x3) + (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1)) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2))) + (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1))) + y + 0)) as a eqn:E_a.
    rewrite -> (Nat.add_assoc a _ _).
    remember (a + (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1)) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2)) + (x0 + x1 + x2 + x3))) as b eqn:E_b.
    rewrite -> (Nat.add_assoc b _ _).
    remember (b + (y + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1)) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2)) + (x0 + x1 + x2 + x3))) as c eqn:E_c.
    rewrite -> Nat.add_0_r.
    rewrite <- (Nat.add_assoc y (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1)) (x0 + x1 + x2 + x3 + (x0 + x1 + x2))).
    rewrite <- (Nat.add_assoc y (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2))) (x0 + x1 + x2 + x3)).
    rewrite -> (Nat.add_comm y (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2)) + (x0 + x1 + x2 + x3))).
    rewrite -> (Nat.add_assoc c _ y).
    rewrite -> (Nat.add_sub (c + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2)) + (x0 + x1 + x2 + x3))) y).
    rewrite -> (Nat.add_assoc c (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2))) (x0 + x1 + x2 + x3)).
    rewrite -> (Nat.add_sub (c + (x0 + x1 + x2 + x3 + (x0 + x1 + x2) + (x0 + x1) + (x0 + x1 + x2 + x3 + (x0 + x1 + x2)))) (x0 + x1 + x2 + x3)).
    rewrite -> E_c.
    rewrite -> E_b.
    rewrite -> E_a.
    ring.
Qed.

(* ********** *)

Fixpoint A006358 (n : nat) : nat :=
  match n with
    O =>
    1
  | S n' =>
    match n' with
      O =>
      5
    | S n'' =>
      match n'' with
        O =>
        15
      | S n''' =>
        match n''' with
          O =>
          55
        | S n'''' =>
          match n'''' with
            O =>
            190
          | S n''''' =>
            4 * A006358 n' + 3 * A006358 n'' - 4 * A006358 n''' - A006358 n'''' + A006358 n'''''
          end
        end
      end
    end
  end.

Lemma fold_unfold_A006358_O :
  A006358 0 =
  1.
Proof.
  fold_unfold_tactic A006358.
Qed.

Lemma fold_unfold_A006358_S :
  forall n' : nat,
    A006358 (S n') =
    match n' with
      O =>
      5
    | S n'' =>
      match n'' with
        O =>
        15
      | S n''' =>
        match n''' with
          O =>
          55
        | S n'''' =>
          match n'''' with
            O =>
            190
          | S n''''' =>
            4 * A006358 n' + 3 * A006358 n'' - 4 * A006358 n''' - A006358 n'''' + A006358 n'''''
          end
        end
      end
    end.
Proof.
  fold_unfold_tactic A006358.
Qed.

Corollary fold_unfold_A006358_SO :
  A006358 1 =
  5.
Proof.
  rewrite -> fold_unfold_A006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006358_SSO :
  A006358 2 =
  15.
Proof.
  rewrite -> fold_unfold_A006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006358_SSSO :
  A006358 3 =
  55.
Proof.
  rewrite -> fold_unfold_A006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006358_SSSSO :
  A006358 4 =
  190.
Proof.
  rewrite -> fold_unfold_A006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_A006358_SSSS :
  forall n'''' : nat,
  A006358 (S (S (S (S (S n''''))))) =
  4 * A006358 (S (S (S (S n'''')))) + 3 * A006358 (S (S (S n''''))) - 4 * A006358 (S (S n'''')) - A006358 (S n'''') + A006358 n''''.
Proof.
  intro n''''.
  rewrite -> fold_unfold_A006358_S.
  reflexivity.
Qed.

(* ***** *)

Fixpoint A006358_sum_aux (f : nat -> nat) (n i : nat) : nat :=
  match n with
    O =>
    f (4 - i)
  | S n' =>
    Sigma0 (4 - i) (fun j => A006358_sum_aux f n' j)
  end.

Definition A006358_sum_f (n : nat) : nat :=
  match n with
    O => 
    0
  | S O =>
    0
  | S (S O) =>
    0
  | S (S (S O)) =>
    0
  | S (S (S (S _))) =>
    1
  end.

Definition A006358_sum (n : nat) : nat :=
  Sigma0 4 (fun i => A006358_sum_aux A006358_sum_f n i).

(* ***** *)

Lemma fold_unfold_A006358_sum_aux_O :
  forall (f : nat -> nat)
         (i : nat),
    A006358_sum_aux f O i =
    f (4 - i).
Proof.
  fold_unfold_tactic A006358_sum_aux.
Qed.

Lemma fold_unfold_A006358_sum_aux_S :
  forall (f : nat -> nat)
         (n' i : nat),
    A006358_sum_aux f (S n') i =
    Sigma0 (4 - i) (fun j => A006358_sum_aux f n' j).
Proof.
  fold_unfold_tactic A006358_sum_aux.
Qed.

(* ***** *)

Compute ((A006358_sum 0 =? A006358 0)
         &&
         (A006358_sum 1 =? A006358 1)
         &&
         (A006358_sum 2 =? A006358 2)
         &&
         (A006358_sum 3 =? A006358 3)).

(* Theorem 4.2 *)

Theorem Theorem_4_dot_2 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 0 ->
    f 2 = 0 ->
    f 3 = 0 ->
    f 4 = 1 ->
    forall n : nat,
      Sigma0 4 (fun i => A006358_sum_aux f n i) = A006358 n.
Proof.
  intros f H_f_0 H_f_1 H_f_2 H_f_3 H_f_4 n.
  rewrite ->4 fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  induction n as [ | | | | | n' IHn' IHSn' IHSSn' IHSSSn' IHSSSSn'] using nat_ind5.
  - simpl.
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
(*
  - simpl.
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - simpl.
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_A006358_SSSS.
    rewrite <- IHSSSSn'.
    rewrite <- IHSSSn'.
    rewrite <- IHSSn'.
    rewrite <- IHSn'.
    rewrite <- IHn'.
*)
Abort.

(* Theorem 4.2 is proved below for a sequence of integers rather than a sequence of natural numbers
   because of the pesky subtractions. *)

(* ********** *)

(* Definition 5.1: the Jacobstahl function *)

Fixpoint jac (n : nat) : nat :=
  match n with
  | 0 =>
    0
  | S n' =>
    match n' with
    | 0 =>
      1
    | S n'' =>
      jac n' + 2 * jac n''
    end
  end.

Lemma fold_unfold_jac_O :
  jac 0 =
  0.
Proof.
  fold_unfold_tactic jac.
Qed.

Lemma fold_unfold_jac_S :
  forall n' : nat,
    jac (S n') =
    match n' with
    | 0 =>
      1
    | S n'' =>
      jac n' + 2 * jac n''
    end.
Proof.
  fold_unfold_tactic jac.
Qed.

Corollary fold_unfold_jac_SO :
  jac 1 =
  1.
Proof.
  rewrite -> fold_unfold_jac_S.
  reflexivity.
Qed.

Corollary fold_unfold_jac_SS :
  forall n'' : nat,
    jac (S (S n'')) =
    jac (S n'') + 2 * jac n''.
Proof.
  intro n''.
  rewrite -> fold_unfold_jac_S.
  reflexivity.
Qed.

(* ********** *)

Fixpoint jac_sum_aux (f : nat -> nat) (n i : nat) : nat :=
  S i * match n with
          O =>
          f (1 - i)
        | S n' =>
          Sigma0 (1 - i) (fun j => jac_sum_aux f n' j)
        end.

Definition jac_sum_f (n : nat) : nat :=
  match n with
    O => 
    0
  | S _ =>
    1
  end.

Definition jac_sum (n : nat) : nat :=
  Sigma0 1 (fun i => jac_sum_aux jac_sum_f n i).

(* ***** *)

Lemma fold_unfold_jac_sum_aux_O :
  forall (f : nat -> nat)
         (i : nat),
    jac_sum_aux f O i =
    S i * f (1 - i).
Proof.
  fold_unfold_tactic jac_sum_aux.
Qed.

Lemma fold_unfold_jac_sum_aux_S :
  forall (f : nat -> nat)
         (n' i : nat),
    jac_sum_aux f (S n') i =
    S i * Sigma0 (1 - i) (fun j => jac_sum_aux f n' j).
Proof.
  fold_unfold_tactic jac_sum_aux.
Qed.

Compute ((jac_sum 0 =? jac 2)
         &&
         (jac_sum 1 =? jac 3)
         &&
         (jac_sum 2 =? jac 4)
         &&
         (jac_sum 3 =? jac 5)
         &&
         (jac_sum 4 =? jac 6)
         &&
         (jac_sum 5 =? jac 7)).

Lemma about_jac_sum_aux_and_jac_0 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall n : nat,
      jac_sum_aux f n 0 = jac (S n).
Proof.
  Compute (let f n := n in
           let n := 5 in
           jac_sum_aux f n 0 = jac (S n)).
  intros f H_f_0 H_f_1 n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_jac_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_jac_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite ->2 fold_unfold_jac_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    simpl (1 - 1).
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_jac_sum_aux_S.
    rewrite -> Nat.mul_1_l.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_jac_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    exact (eq_sym (fold_unfold_jac_SS (S n'))).
Qed.

Lemma about_jac_sum_aux_and_jac_1 :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall n : nat,
      jac_sum_aux f n 1 = 2 * jac n.
Proof.
  Compute (let f n := n in
           let n := 5 in
           jac_sum_aux f n 1 = 2 * jac n).
  intros f H_f_0 H_f_1 [ | n'].
  - rewrite -> fold_unfold_jac_sum_aux_O.
    simpl (1 - 1).
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_jac_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    exact (f_equal (fun z => 2 * z) (about_jac_sum_aux_and_jac_0 f H_f_0 H_f_1 n')).
Qed.

(* Theorem 5.2 *)

Theorem Jacobstahl_numbers_as_nested_sums :
  forall f : nat -> nat,
    f 0 = 0 ->
    f 1 = 1 ->
    forall n : nat,
      Sigma0 1 (fun i => jac_sum_aux f n i) = jac (n + 2).
Proof.
  intros f H_f_0 H_f_1 n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  rewrite -> (about_jac_sum_aux_and_jac_0 f H_f_0 H_f_1 n).
  rewrite -> (about_jac_sum_aux_and_jac_1 f H_f_0 H_f_1 n).
  exact (eq_sym (fold_unfold_jac_SS n)).
Qed.

(* ***** *)

(* Definition 5.3 *)

Fixpoint gjac_z_w_k (z w k n : nat) : nat :=
  match n with
  | 0 =>
    z
  | S n' =>
    match n' with
    | 0 =>
      w
    | S n'' =>
      k * gjac_z_w_k z w k n' + k * S k * gjac_z_w_k z w k n''
    end
  end.

Lemma fold_unfold_gjac_z_w_k_O :
  forall z w k : nat,
    gjac_z_w_k z w k 0 =
    z.
Proof.
  fold_unfold_tactic gjac_z_w_k.
Qed.

Lemma fold_unfold_gjac_z_w_k_S :
  forall z w k n' : nat,
    gjac_z_w_k z w k (S n') =
    match n' with
    | 0 =>
      w
    | S n'' =>
      k * gjac_z_w_k z w k n' + k * S k * gjac_z_w_k z w k n''
    end.
Proof.
  fold_unfold_tactic gjac_z_w_k.
Qed.

Corollary fold_unfold_gjac_z_w_k_SO :
  forall z w k : nat,
    gjac_z_w_k z w k 1 =
    w.
Proof.
  intros o w k.
  rewrite -> fold_unfold_gjac_z_w_k_S.
  reflexivity.
Qed.

Corollary fold_unfold_gjac_z_w_k_SS :
  forall z w k n'' : nat,
    gjac_z_w_k z w k (S (S n'')) =
    k * gjac_z_w_k z w k (S n'') + k * S k * gjac_z_w_k z w k n''.
Proof.
  intros z w k n''.
  rewrite -> fold_unfold_gjac_z_w_k_S.
  reflexivity.
Qed.

(* ***** *)

Proposition about_gjac_0_1_1 :
  forall n : nat,
    gjac_z_w_k 0 1 1 n = jac n.
Proof.
  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_gjac_z_w_k_O.
    rewrite -> fold_unfold_jac_O.
    reflexivity.
  - rewrite -> fold_unfold_gjac_z_w_k_SO.
    rewrite -> fold_unfold_jac_SO.
    reflexivity.
  - rewrite -> fold_unfold_gjac_z_w_k_SS.
    rewrite -> Nat.mul_1_l.
    rewrite -> fold_unfold_jac_SS.
    rewrite -> IHn'.
    rewrite -> IHSn'.
    reflexivity.
Qed.

(* ***** *)

Fixpoint gjac_sum_aux (f : nat -> nat) (k n i : nat) : nat :=
  (i + k) * match n with
              O =>
              f (1 - i)
            | S n' =>
              Sigma0 (1 - i) (fun i => gjac_sum_aux f k n' i)
            end.

Lemma fold_unfold_gjac_sum_aux_O :
  forall (f : nat -> nat)
         (k i : nat),
    gjac_sum_aux f k 0 i =
    (i + k) * f (1 - i).
Proof.
  fold_unfold_tactic gjac_sum_aux.
Qed.

Lemma fold_unfold_gjac_sum_aux_S :
  forall (f : nat -> nat)
         (k n' i : nat),
    gjac_sum_aux f k (S n') i =
    (i + k) * Sigma0 (1 - i) (fun i => gjac_sum_aux f k n' i).
Proof.
  fold_unfold_tactic gjac_sum_aux.
Qed.

(* ***** *)

(* towards Theorem 5.4 *)

Compute (let z := 1 in
         let f x := match x with 0 => z | S _ => S z end in
         let k := 1 in
         ((Sigma0 1 (fun i => gjac_sum_aux f k 0 i), gjac_z_w_k z (S z) k 2)
          ,
          (Sigma0 1 (fun i => gjac_sum_aux f k 1 i), gjac_z_w_k z (S z) k 3)
          ,
          (Sigma0 1 (fun i => gjac_sum_aux f k 2 i), gjac_z_w_k z (S z) k 4))).

Compute (let z := 2 in
         let f x := match x with 0 => z | S _ => S z end in
         let k := 1 in
         ((Sigma0 1 (fun i => gjac_sum_aux f k 0 i), gjac_z_w_k z (S z) k 2)
          ,
          (Sigma0 1 (fun i => gjac_sum_aux f k 1 i), gjac_z_w_k z (S z) k 3)
          ,
          (Sigma0 1 (fun i => gjac_sum_aux f k 2 i), gjac_z_w_k z (S z) k 4))).

Compute (let z := 3 in
         let f x := match x with 0 => z | S _ => S z end in
         let k := 1 in
         ((Sigma0 1 (fun i => gjac_sum_aux f k 0 i), gjac_z_w_k z (S z) k 2)
          ,
          (Sigma0 1 (fun i => gjac_sum_aux f k 1 i), gjac_z_w_k z (S z) k 3)
          ,
          (Sigma0 1 (fun i => gjac_sum_aux f k 2 i), gjac_z_w_k z (S z) k 4))).

Lemma about_gjac_sum_aux_and_gjac_z_w_1_0 :
  forall (f : nat -> nat)
         (n : nat),
    gjac_sum_aux f 1 n 0 = gjac_z_w_k (f 0) (f 1) 1 (S n).
Proof.
  Compute (let f n := n in
           let k := 1 in
           let n := 5 in
           gjac_sum_aux f k n 0 = gjac_z_w_k (f 0) (f 1) k (S n)).
  intros f n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_gjac_sum_aux_O.
    simpl (1 - 0).
    rewrite -> fold_unfold_gjac_z_w_k_SO.
    ring.
  - rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite ->2 fold_unfold_gjac_sum_aux_O.
    simpl (1 - 0).
    simpl (1 - 1).
    rewrite -> fold_unfold_gjac_z_w_k_SS.
    rewrite -> fold_unfold_gjac_z_w_k_SO.
    rewrite -> fold_unfold_gjac_z_w_k_O.
    ring.
  - rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    simpl (0 + 1).
    rewrite -> Nat.mul_1_l.
    simpl (1 + 1).
    Check (fold_unfold_gjac_z_w_k_SS (f 0) (f 1) 1 (S n')).
    rewrite <- (Nat.mul_1_l (gjac_z_w_k (f 0) (f 1) 1 (S (S n')))).
    rewrite <- (Nat.mul_1_l 2).
    exact (eq_sym (fold_unfold_gjac_z_w_k_SS (f 0) (f 1) 1 (S n'))).
Qed.

Lemma about_gjac_sum_aux_and_gjac_z_w_1_1 :
  forall (f : nat -> nat)
         (n : nat),
    gjac_sum_aux f 1 n 1 = 2 * gjac_z_w_k (f 0) (f 1) 1 n.
Proof.
  Compute (let f n := n in
           let k := 1 in
           let n := 5 in
           gjac_sum_aux f 1 n 1 = 2 * gjac_z_w_k (f 0) (f 1) 1 n).
  intros f [ | n'].
  - rewrite -> fold_unfold_gjac_sum_aux_O.
    simpl (1 - 1).
    rewrite -> fold_unfold_gjac_z_w_k_O.
    ring.
  - rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> (about_gjac_sum_aux_and_gjac_z_w_1_0 f n').
    ring.
Qed.

(* Theorem 5.4 *)

Theorem Members_of_the_generalized_Jacobstahl_sequences_that_start_with_a_natural_number_and_then_its_successor_and_that_have_1_as_a_core_multiplicative_factor_as_nested_sums :
  forall (z : nat)
         (f : nat -> nat),
    f 0 = z ->
    f 1 = S z ->
    forall n : nat,
      Sigma0 1 (fun i => gjac_sum_aux f 1 n i) = gjac_z_w_k z (S z) 1 (n + 2).
Proof.
  intros z f H_f_0 H_f_1 n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (about_gjac_sum_aux_and_gjac_z_w_1_0 f n).
  rewrite -> (about_gjac_sum_aux_and_gjac_z_w_1_1 f n).
  rewrite -> H_f_0.
  rewrite -> H_f_1.
  rewrite <- (Nat.mul_1_l (gjac_z_w_k z (S z) 1 (S n))).
  rewrite <- (Nat.mul_1_l 2) at 1.
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  exact (eq_sym (fold_unfold_gjac_z_w_k_SS z (S z) 1 n)).
Qed.

(* ***** *)

(* towards Theorem 5.5 *)

Lemma about_gjac_sum_aux_and_gjac_0_w_k_0 :
  forall f : nat -> nat,
    f 0 = 0 ->
    forall k n : nat,
      gjac_sum_aux f k n 0 = k * gjac_z_w_k 0 (f 1) k (S n).
Proof.
  Compute (let w := 5 in
           let f n := match n with O => 0 | S _ => w end in
           let k := 1 in
           let n := 5 in
           gjac_sum_aux f k n 0 = k * gjac_z_w_k 0 w k (S n)).
  Compute (let w := 3 in
           let f n := match n with O => 0 | S _ => w end in
           let k := 2 in
           let n := 5 in
           gjac_sum_aux f k n 0 = k * gjac_z_w_k 0 w k (S n)).
  Compute (let w := 2 in
           let f n := match n with O => 0 | S _ => w end in
           let k := 4 in
           let n := 1 in
           gjac_sum_aux f k n 0 = k * gjac_z_w_k 0 w k (S n)).
Proof.
  intros f H_f_0 k n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_gjac_sum_aux_O.
    simpl (1 - 0).
    rewrite -> fold_unfold_gjac_z_w_k_SO.
    ring.
  - rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite ->2 fold_unfold_gjac_sum_aux_O.
    simpl (1 - 0).
    simpl (1 - 1).
    rewrite -> H_f_0.
    rewrite -> fold_unfold_gjac_z_w_k_SS.
    rewrite -> fold_unfold_gjac_z_w_k_SO.
    rewrite -> fold_unfold_gjac_z_w_k_O.
    ring.
  - rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_Sigma0_S.
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> IHn'.
    simpl (0 + 1).
    rewrite -> (fold_unfold_gjac_z_w_k_SS 0 (f 1) k (S n')).
    ring.
Qed.

Lemma about_gjac_sum_aux_and_gjac_0_w_k_1 :
  forall f : nat -> nat,
    f 0 = 0 ->
    forall k n : nat,
      gjac_sum_aux f k n 1 = k * S k * gjac_z_w_k 0 (f 1) k n.
Proof.
  Compute (let w := 5 in
           let f n := match n with O => 0 | S _ => w end in
           let k := 1 in
           let n := 5 in
           gjac_sum_aux f k n 1 = k * S k * gjac_z_w_k 0 (f 1) k n).
  Compute (let w := 3 in
           let f n := match n with O => 0 | S _ => w end in
           let k := 2 in
           let n := 2 in
           gjac_sum_aux f k n 1 = k * S k * gjac_z_w_k 0 (f 1) k n).
  Compute (let w := 2 in
           let f n := match n with O => 0 | S _ => w end in
           let k := 3 in
           let n := 4 in
           gjac_sum_aux f k n 1 = k * S k * gjac_z_w_k 0 (f 1) k n).
  intros f H_f_0 k [ | n'].
  - rewrite -> fold_unfold_gjac_sum_aux_O.
    simpl (1 - 1).
    rewrite -> H_f_0.
    rewrite -> fold_unfold_gjac_z_w_k_O.
    ring.
  - rewrite -> fold_unfold_gjac_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_Sigma0_O.
    rewrite -> (about_gjac_sum_aux_and_gjac_0_w_k_0 f H_f_0 k n').
    ring.
Qed.

(* Theorem 5.5 *)

Theorem Members_of_the_generalized_Jacobstahl_sequences_that_start_with_0_as_nested_sums :
  forall (w : nat)
         (f : nat -> nat),
    f 0 = 0 ->
    f 1 = w ->
    forall k n : nat,
      Sigma0 1 (fun i => gjac_sum_aux f k n i) = gjac_z_w_k 0 w k (n + 2).
Proof.
  intros w f H_f_0 H_f_1 k n.
  rewrite -> fold_unfold_Sigma0_S.
  rewrite -> fold_unfold_Sigma0_O.
  rewrite -> (about_gjac_sum_aux_and_gjac_0_w_k_0 f H_f_0 k n).
  rewrite -> (about_gjac_sum_aux_and_gjac_0_w_k_1 f H_f_0 k n).
  rewrite -> H_f_1.
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  exact (eq_sym (fold_unfold_gjac_z_w_k_SS 0 w k n)).
Qed.

(* ********** *)

(* La même chose, with integers: *)

Require Import ZArith.

Fixpoint ZSigma0 (n : nat) (f : nat -> Z) : Z :=
  match n with
  | O =>
    f 0
  | S n' =>
    Z.add (ZSigma0 n' f) (f n)
  end.

Lemma fold_unfold_ZSigma0_O :
  forall (f : nat -> Z),
    ZSigma0 0 f =
    f 0.
Proof.
  fold_unfold_tactic ZSigma0.
Qed.

Lemma fold_unfold_ZSigma0_S :
  forall (n' : nat)
         (f : nat -> Z),
    ZSigma0 (S n') f =
    Z.add (ZSigma0 n' f) (f (S n')).
Proof.
  fold_unfold_tactic ZSigma0.
Qed.

(* ***** *)

Fixpoint zfib (n : nat) : Z :=
  match n with
  | 0 =>
    0%Z
  | S n' =>
    match n' with
    | 0 =>
      1%Z
    | S n'' =>
      Z.add (zfib n') (zfib n'')
    end
  end.

Lemma fold_unfold_zfib_O :
  zfib 0 =
  0%Z.
Proof.
  fold_unfold_tactic zfib.
Qed.

Lemma fold_unfold_zfib_S :
  forall n' : nat,
    zfib (S n') =
    match n' with
    | 0 =>
      1%Z
    | S n'' =>
      Z.add (zfib n') (zfib n'')
    end.
Proof.
  fold_unfold_tactic zfib.
Qed.

Corollary fold_unfold_zfib_SO :
  zfib 1 =
  1%Z.
Proof.
  rewrite -> fold_unfold_zfib_S.
  reflexivity.
Qed.

Corollary fold_unfold_zfib_SS :
  forall n'' : nat,
    zfib (S (S n'')) =
    Z.add (zfib (S n'')) (zfib n'').
Proof.
  intro n''.
  rewrite -> fold_unfold_zfib_S.
  reflexivity.
Qed.

(* ***** *)

Fixpoint zfib_sum_aux (f : nat -> Z) (n i : nat) : Z :=
  match n with
    O =>
    f (1 - i)
  | S n' =>
    ZSigma0 (1 - i) (fun j => zfib_sum_aux f n' j)
  end.

Definition zfib_sum_f (n : nat) : Z :=
  match n with
    O => 
    0%Z
  | S _ =>
    1%Z
  end.

Definition zfib_sum (n : nat) : Z :=
  ZSigma0 1 (fun i => zfib_sum_aux zfib_sum_f n i).

Lemma fold_unfold_zfib_sum_aux_O :
  forall (f : nat -> Z)
         (i : nat),
    zfib_sum_aux f O i =
    f (1 - i).
Proof.
  fold_unfold_tactic zfib_sum_aux.
Qed.

Lemma fold_unfold_zfib_sum_aux_S :
  forall (f : nat -> Z)
         (n' i : nat),
    zfib_sum_aux f (S n') i =
    ZSigma0 (1 - i) (fun j => zfib_sum_aux f n' j).
Proof.
  fold_unfold_tactic zfib_sum_aux.
Qed.

(* ***** *)

(* Corollary 6.2 *)

Theorem Fibonacci_numbers_as_nested_sums_of_integers_extrapolated :
  forall f : nat -> Z,
    f 0 = (-1)%Z ->
    f 1 = 1%Z ->
    forall n : nat,
      ZSigma0 1 (fun i => zfib_sum_aux f n i) = zfib n.
Proof.
  intros f H_f_0 H_f_1 n.
  rewrite -> fold_unfold_ZSigma0_S.
  rewrite -> fold_unfold_ZSigma0_O.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 1)%nat.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_ZSigma0_S.
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 1).
    rewrite -> H_f_0.
    rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_ZSigma0_S.
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_ZSigma0_S.
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> IHn'.
    exact (eq_sym (fold_unfold_zfib_SS n')).
Qed.

(* ***** *)

Fixpoint zluc (n : nat) : Z :=
  match n with
  | 0 =>
    2%Z
  | S n' =>
    match n' with
    | 0 =>
      1%Z
    | S n'' =>
      Z.add (zluc n') (zluc n'')
    end
  end.

Lemma fold_unfold_zluc_O :
  zluc 0 =
  2%Z.
Proof.
  fold_unfold_tactic zluc.
Qed.

Lemma fold_unfold_zluc_S :
  forall n' : nat,
    zluc (S n') =
    match n' with
    | 0 =>
      1%Z
    | S n'' =>
      Z.add (zluc n') (zluc n'')
    end.
Proof.
  fold_unfold_tactic zluc.
Qed.

Corollary fold_unfold_zluc_SO :
  zluc 1 =
  1%Z.
Proof.
  rewrite -> fold_unfold_zluc_S.
  reflexivity.
Qed.

Corollary fold_unfold_zluc_SS :
  forall n'' : nat,
    zluc (S (S n'')) =
    Z.add (zluc (S n'')) (zluc n'').
Proof.
  intro n''.
  rewrite -> fold_unfold_zluc_S.
  reflexivity.
Qed.

(* ***** *)

(* Corollary 6.3 *)

Theorem Lucas_numbers_as_nested_sums_of_integers_extrapolated :
  forall f : nat -> Z,
    f 0 = 3%Z ->
    f 1 = (-1)%Z ->
    forall n : nat,
      ZSigma0 1 (fun i => zfib_sum_aux f n i) = zluc n.
Proof.
  intros f H_f_0 H_f_1 n.
  rewrite -> fold_unfold_ZSigma0_S.
  rewrite -> fold_unfold_ZSigma0_O.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 1)%nat.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_ZSigma0_S.
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 1).
    rewrite -> H_f_0.
    rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> fold_unfold_zfib_sum_aux_O.
    simpl (1 - 0).
    rewrite -> H_f_1.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_ZSigma0_S.
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> IHSn'.
    rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 1).
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> fold_unfold_zfib_sum_aux_S.
    simpl (1 - 0).
    rewrite -> fold_unfold_ZSigma0_S.
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite -> IHn'.
    exact (eq_sym (fold_unfold_zluc_SS n')).
Qed.

(* ********** *)

Fixpoint ZA006357 (n : nat) : Z :=
  match n with
    O =>
    1%Z
  | S n' =>
    match n' with
      O =>
      4%Z
    | S n'' =>
      match n'' with
        O =>
        10%Z
      | S n''' =>
        match n''' with
          O =>
          30%Z
        | S n'''' =>
          Z.add (Z.add (Z.add (Z.mul 2%Z (ZA006357 n'))
                              (Z.mul 3%Z (ZA006357 n'')))
                       (Z.mul (-1)%Z (ZA006357 n''')))
                (Z.mul (-1)%Z (ZA006357 n''''))
        end
      end
    end
  end.

Lemma fold_unfold_ZA006357_O :
  ZA006357 0 =
  1%Z.
Proof.
  fold_unfold_tactic ZA006357.
Qed.

Lemma fold_unfold_ZA006357_S :
  forall n' : nat,
    ZA006357 (S n') =
    match n' with
      O =>
      4%Z
    | S n'' =>
      match n'' with
        O =>
        10%Z
      | S n''' =>
        match n''' with
          O =>
          30%Z
        | S n'''' =>
          Z.add (Z.add (Z.add (Z.mul 2%Z (ZA006357 n'))
                              (Z.mul 3%Z (ZA006357 n'')))
                       (Z.mul (-1)%Z (ZA006357 n''')))
                (Z.mul (-1)%Z (ZA006357 n''''))
        end
      end
    end.
Proof.
  fold_unfold_tactic ZA006357.
Qed.

Corollary fold_unfold_ZA006357_SO :
  ZA006357 1 =
  4%Z.
Proof.
  rewrite -> fold_unfold_ZA006357_S.
  reflexivity.
Qed.

Corollary fold_unfold_ZA006357_SSO :
  ZA006357 2 =
  10%Z.
Proof.
  rewrite -> fold_unfold_ZA006357_S.
  reflexivity.
Qed.

Corollary fold_unfold_ZA006357_SSSO :
  ZA006357 3 =
  30%Z.
Proof.
  rewrite -> fold_unfold_ZA006357_S.
  reflexivity.
Qed.

Lemma fold_unfold_ZA006357_SSSS :
  forall n'''' : nat,
    ZA006357 (S (S (S (S n'''')))) =
    Z.add (Z.add (Z.add (Z.mul 2%Z (ZA006357 (S (S (S n'''')))))
                        (Z.mul 3%Z (ZA006357 (S (S n'''')))))
                 (Z.mul (-1)%Z (ZA006357 (S n''''))))
          (Z.mul (-1)%Z (ZA006357 n'''')).
Proof.
  intro n''''.
  rewrite -> fold_unfold_ZA006357_S.
  reflexivity.
Qed.

(* ***** *)

Fixpoint ZA006357_sum_aux (f : nat -> Z) (n i : nat) : Z :=
  match n with
    O =>
    f (3 - i)
  | S n' =>
    ZSigma0 (3 - i) (fun j => ZA006357_sum_aux f n' j)
  end.

Definition ZA006357_sum_f (n : nat) : Z :=
  match n with
    O => 
    0%Z
  | S O =>
    0%Z
  | S (S O) =>
    0%Z
  | S (S (S _)) =>
    1%Z
  end.

Definition ZA006357_sum (n : nat) : Z :=
  ZSigma0 3 (fun i => ZA006357_sum_aux ZA006357_sum_f n i).

(* ***** *)

Lemma fold_unfold_ZA006357_sum_aux_O :
  forall (f : nat -> Z)
         (i : nat),
    ZA006357_sum_aux f O i =
    f (3 - i).
Proof.
  fold_unfold_tactic ZA006357_sum_aux.
Qed.

Lemma fold_unfold_ZA006357_sum_aux_S :
  forall (f : nat -> Z)
         (n' i : nat),
    ZA006357_sum_aux f (S n') i =
    ZSigma0 (3 - i) (fun j => ZA006357_sum_aux f n' j).
Proof.
  fold_unfold_tactic ZA006357_sum_aux.
Qed.

(* ***** *)

Compute ((Z.eqb (ZA006357_sum 0) (ZA006357 0))
         &&
         (Z.eqb (ZA006357_sum 1) (ZA006357 1))
         &&
         (Z.eqb (ZA006357_sum 2) (ZA006357 2))
         &&
         (Z.eqb (ZA006357_sum 3) (ZA006357 3))).

(* Theorem 4.1 for integers *)

Theorem Theorem_4_dot_1_for_Z :
  forall f : nat -> Z,
    f 0 = 0%Z ->
    f 1 = 0%Z ->
    f 2 = 0%Z ->
    f 3 = 1%Z ->
    forall n : nat,
      ZSigma0 3 (fun i => ZA006357_sum_aux f n i) = ZA006357 n.
Proof.
  intros f H_f_0 H_f_1 H_f_2 H_f_3 n.
  rewrite ->3 fold_unfold_ZSigma0_S.
  rewrite -> fold_unfold_ZSigma0_O.
  induction n as [ | | | | n' IHn' IHSn' IHSSn' IHSSSn'] using nat_ind4.
  - rewrite ->? fold_unfold_ZA006357_sum_aux_O.
    simpl (3 - 0).
    simpl (3 - 1).
    simpl (3 - 2).
    simpl (3 - 3).
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->? fold_unfold_ZA006357_sum_aux_S.
    simpl (3 - 0).
    simpl (3 - 1).
    simpl (3 - 2).
    simpl (3 - 3).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006357_sum_aux_S;
            rewrite ->? fold_unfold_ZA006357_sum_aux_O;
            simpl (3 - 0);
            simpl (3 - 1);
            simpl (3 - 2);
            simpl (3 - 3)).
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->? fold_unfold_ZA006357_sum_aux_S.
    simpl (3 - 0).
    simpl (3 - 1).
    simpl (3 - 2).
    simpl (3 - 3).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006357_sum_aux_S;
            rewrite ->? fold_unfold_ZA006357_sum_aux_O;
            simpl (3 - 0);
            simpl (3 - 1);
            simpl (3 - 2);
            simpl (3 - 3)).
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->? fold_unfold_ZA006357_sum_aux_S.
    simpl (3 - 0).
    simpl (3 - 1).
    simpl (3 - 2).
    simpl (3 - 3).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006357_sum_aux_S;
            rewrite ->? fold_unfold_ZA006357_sum_aux_O;
            simpl (3 - 0);
            simpl (3 - 1);
            simpl (3 - 2);
            simpl (3 - 3)).
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_ZA006357_SSSS.
    rewrite <- IHSSSn'.
    rewrite <- IHSSn'.
    rewrite <- IHSn'.
    rewrite <- IHn'.
    rewrite ->? fold_unfold_ZA006357_sum_aux_S.
    simpl (3 - 0).
    simpl (3 - 1).
    simpl (3 - 2).
    simpl (3 - 3).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006357_sum_aux_S;
            rewrite ->? fold_unfold_ZA006357_sum_aux_O;
            simpl (3 - 0);
            simpl (3 - 1);
            simpl (3 - 2);
            simpl (3 - 3)).
    ring.
Qed.

(* ********** *)

Fixpoint ZA006356 (n : nat) : Z :=
  match n with
    O =>
    1%Z
  | S n' =>
    match n' with
      O =>
      3%Z
    | S n'' =>
      match n'' with
        O =>
        6%Z
      | S n''' =>
        Z.sub (Z.add (Z.mul 2%Z (ZA006356 n')) (ZA006356 n'')) (ZA006356 n''')
      end
    end
  end.

Lemma fold_unfold_ZA006356_O :
  ZA006356 0 =
  1%Z.
Proof.
  fold_unfold_tactic ZA006356.
Qed.

Lemma fold_unfold_ZA006356_S :
  forall n' : nat,
    ZA006356 (S n') =
    match n' with
      O =>
      3%Z
    | S n'' =>
      match n'' with
        O =>
        6%Z
      | S n''' =>
        Z.sub (Z.add (Z.mul 2%Z (ZA006356 n')) (ZA006356 n'')) (ZA006356 n''')
      end
    end.
Proof.
  fold_unfold_tactic ZA006356.
Qed.

Corollary fold_unfold_ZA006356_SO :
  ZA006356 1 =
  3%Z.
Proof.
  rewrite -> fold_unfold_ZA006356_S.
  reflexivity.
Qed.

Corollary fold_unfold_ZA006356_SS :
  forall n'' : nat,
    ZA006356 (S (S n'')) =
    match n'' with
      O =>
      6%Z
    | S n''' =>
      Z.sub (Z.add (Z.mul 2%Z (ZA006356 (S n''))) (ZA006356 n'')) (ZA006356 n''')
    end.
Proof.
  intros [ | n'''].
  - rewrite -> fold_unfold_ZA006356_S.
    reflexivity.
  - rewrite -> fold_unfold_ZA006356_S.
    reflexivity.
Qed.

Corollary fold_unfold_ZA006356_SSO :
  ZA006356 2 =
  6%Z.
Proof.
  fold_unfold_tactic ZA006356.
Qed.

Corollary fold_unfold_ZA006356_SSS :
  forall n''' : nat,
    ZA006356 (S (S (S n'''))) =
    Z.sub (Z.add (Z.mul 2%Z (ZA006356 (S (S n''')))) (ZA006356 (S n''') )) (ZA006356 n''').
Proof.
  intro n'''.
  rewrite -> fold_unfold_ZA006356_S.
  reflexivity.
Qed.

(* ***** *)

Fixpoint ZA006356_sum_aux (f : nat -> Z) (n i : nat) : Z :=
  match n with
    O =>
    f (2 - i)
  | S n' =>
    ZSigma0 (2 - i) (fun j => ZA006356_sum_aux f n' j)
  end.

Definition ZA006356_sum_f (n : nat) : Z :=
  match n with
    O => 
    0%Z
  | S O =>
    0%Z
  | S (S _) =>
    1%Z
  end.

Definition ZA006356_sum (n : nat) : Z :=
  ZSigma0 2 (fun i => ZA006356_sum_aux ZA006356_sum_f n i).

(* ***** *)

Lemma fold_unfold_ZA006356_sum_aux_O :
  forall (f : nat -> Z)
         (i : nat),
    ZA006356_sum_aux f O i =
    f (2 - i).
Proof.
  fold_unfold_tactic ZA006356_sum_aux.
Qed.

Lemma fold_unfold_ZA006356_sum_aux_S :
  forall (f : nat -> Z)
         (n' i : nat),
    ZA006356_sum_aux f (S n') i =
    ZSigma0 (2 - i) (fun j => ZA006356_sum_aux f n' j).
Proof.
  fold_unfold_tactic ZA006356_sum_aux.
Qed.

(* ***** *)

(* Theorem 6.8 for integers *)

Theorem Theorem_6_dot_8_for_Z :
  forall s : nat -> Z,
  forall f : nat -> Z,
    f 0 = Z.add (Z.add (s 0) (Z.mul 2%Z (s 1))) (Z.mul (-1)%Z (s 2)) ->
    f 1 = Z.add (Z.add (Z.mul (-3)%Z (s 0)) (Z.mul (-3)%Z (s 1))) (Z.mul 2%Z (s 2)) ->
    f 2 = Z.add (Z.add (Z.mul 3%Z (s 0)) (s 1)) (Z.mul (-1)%Z (s 2)) ->
    (forall n : nat,
        s n = ZSigma0 2 (fun i => ZA006356_sum_aux f n i)) ->
    forall n : nat,
      s (n + 3) = Z.sub (Z.add (Z.mul 2%Z (s (n + 2))) (s (n + 1))) (s n).
Proof.
  intros s f H_f_0 H_f_1 H_f_2 H_s n.
  rewrite -> (Nat.add_comm n 3); simpl (3 + n).
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  rewrite -> (Nat.add_comm n 1); simpl (1 + n).
  induction n as [ | | | n' IHn' IHSn' IHSSn'] using nat_ind3.
  - rewrite -> (H_s 3).
    rewrite -> (H_s 2).
    rewrite -> (H_s 1).
    rewrite -> (H_s 0).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_O.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    ring.
  - rewrite -> (H_s 4).
    rewrite -> (H_s 3).
    rewrite -> (H_s 2).
    rewrite -> (H_s 1).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_O.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    ring.
  - rewrite -> (H_s 5).
    rewrite -> (H_s 4).
    rewrite -> (H_s 3).
    rewrite -> (H_s 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_O.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    ring.
  - rewrite -> (H_s (S (S (S (S (S (S n'))))))).
    rewrite ->2 fold_unfold_ZSigma0_S.
    rewrite -> fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    remember (ZA006356_sum_aux f n' 0) as f_0 eqn:E_f_0.
    remember (ZA006356_sum_aux f n' 1) as f_1 eqn:E_f_1.
    remember (ZA006356_sum_aux f n' 2) as f_2 eqn:E_f_2.
    rewrite ->? IHSSn'.
    rewrite ->? IHSn'.
    rewrite ->? IHn'.
    rewrite -> (H_s (S (S n'))).
    rewrite -> (H_s (S n')).
    rewrite -> (H_s n').
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite ->? fold_unfold_ZSigma0_S.
    rewrite ->? fold_unfold_ZSigma0_O.
    rewrite ->? fold_unfold_ZA006356_sum_aux_S.
    simpl (2 - 0).
    simpl (2 - 1).
    simpl (2 - 2).
    rewrite <-? E_f_2.
    rewrite <-? E_f_1.
    rewrite <-? E_f_0.
    ring.

  Restart.

  intros s f H_f_0 H_f_1 H_f_2 H_s n.
  rewrite -> (Nat.add_comm n 3); simpl (3 + n).
  rewrite -> (Nat.add_comm n 2); simpl (2 + n).
  rewrite -> (Nat.add_comm n 1); simpl (1 + n).
  induction n as [ | | | n' IHn' IHSn' IHSSn'] using nat_ind3.
  - rewrite -> (H_s 3).
    rewrite -> (H_s 2).
    rewrite -> (H_s 1).
    rewrite -> (H_s 0).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006356_sum_aux_S;
            simpl (2 - 0);
            simpl (2 - 1);
            simpl (2 - 2)).
    ring.
  - rewrite -> (H_s 4).
    rewrite -> (H_s 3).
    rewrite -> (H_s 2).
    rewrite -> (H_s 1).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006356_sum_aux_S;
            simpl (2 - 0);
            simpl (2 - 1);
            simpl (2 - 2)).
    ring.
  - rewrite -> (H_s 5).
    rewrite -> (H_s 4).
    rewrite -> (H_s 3).
    rewrite -> (H_s 2).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006356_sum_aux_S;
            simpl (2 - 0);
            simpl (2 - 1);
            simpl (2 - 2)).
    ring.
  - rewrite -> (H_s (S (S (S (S (S (S n'))))))).
    rewrite ->? IHSSn'.
    rewrite ->? IHSn'.
    rewrite ->? IHn'.
    rewrite -> (H_s (S (S n'))).
    rewrite -> (H_s (S n')).
    rewrite -> (H_s n').
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006356_sum_aux_S;
            simpl (2 - 0);
            simpl (2 - 1);
            simpl (2 - 2)).
    ring.
Qed.

(* ********** *)

(* Section 4.2 *)

Fixpoint ZA006358 (n : nat) : Z :=
  match n with
    O =>
    1%Z
  | S n' =>
    match n' with
      O =>
      5%Z
    | S n'' =>
      match n'' with
        O =>
        15%Z
      | S n''' =>
        match n''' with
          O =>
          55%Z
        | S n'''' =>
          match n'''' with
            O =>
            190%Z
          | S n''''' =>
            Z.add (Z.add (Z.add (Z.add (Z.mul 3%Z (ZA006358 n'))
                                       (Z.mul 3%Z (ZA006358 n'')))
                                (Z.mul (-4)%Z (ZA006358 n''')))
                         (Z.mul (-1)%Z (ZA006358 n'''')))
                  (ZA006358 n''''')
          end
        end
      end
    end
  end.

Lemma fold_unfold_ZA006358_O :
  ZA006358 0 =
  1%Z.
Proof.
  fold_unfold_tactic ZA006358.
Qed.

Lemma fold_unfold_ZA006358_S :
  forall n' : nat,
    ZA006358 (S n') =
    match n' with
      O =>
      5%Z
    | S n'' =>
      match n'' with
        O =>
        15%Z
      | S n''' =>
        match n''' with
          O =>
          55%Z
        | S n'''' =>
          match n'''' with
            O =>
            190%Z
          | S n''''' =>
            Z.add (Z.add (Z.add (Z.add (Z.mul 3%Z (ZA006358 n'))
                                       (Z.mul 3%Z (ZA006358 n'')))
                                (Z.mul (-4)%Z (ZA006358 n''')))
                         (Z.mul (-1)%Z (ZA006358 n'''')))
                  (ZA006358 n''''')
          end
        end
      end
    end.
Proof.
  fold_unfold_tactic ZA006358.
Qed.

Corollary fold_unfold_ZA006358_SO :
  ZA006358 1 =
  5%Z.
Proof.
  rewrite -> fold_unfold_ZA006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_ZA006358_SSO :
  ZA006358 2 =
  15%Z.
Proof.
  rewrite -> fold_unfold_ZA006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_ZA006358_SSSO :
  ZA006358 3 =
  55%Z.
Proof.
  rewrite -> fold_unfold_ZA006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_ZA006358_SSSSO :
  ZA006358 4 =
  190%Z.
Proof.
  rewrite -> fold_unfold_ZA006358_S.
  reflexivity.
Qed.

Corollary fold_unfold_ZA006358_SSSS :
  forall n'''' : nat,
  ZA006358 (S (S (S (S (S n''''))))) =
  Z.add (Z.add (Z.add (Z.add (Z.mul 3%Z (ZA006358 (S (S (S (S n''''))))))
                             (Z.mul 3%Z (ZA006358 (S (S (S n''''))))))
                      (Z.mul (-4)%Z (ZA006358 (S (S n'''')))))
               (Z.mul (-1)%Z (ZA006358 (S n''''))))
        (ZA006358 n'''').
Proof.
  intro n''''.
  rewrite -> fold_unfold_ZA006358_S.
  reflexivity.
Qed.

(* ***** *)

Fixpoint ZA006358_sum_aux (f : nat -> Z) (n i : nat) : Z :=
  match n with
    O =>
    f (4 - i)
  | S n' =>
    ZSigma0 (4 - i) (fun j => ZA006358_sum_aux f n' j)
  end.

Definition ZA006358_sum_f (n : nat) : Z :=
  match n with
    O => 
    0%Z
  | S O =>
    0%Z
  | S (S O) =>
    0%Z
  | S (S (S O)) =>
    0%Z
  | S (S (S (S _))) =>
    1%Z
  end.

Definition ZA006358_sum (n : nat) : Z :=
  ZSigma0 4 (fun i => ZA006358_sum_aux ZA006358_sum_f n i).

(* ***** *)

Lemma fold_unfold_ZA006358_sum_aux_O :
  forall (f : nat -> Z)
         (i : nat),
    ZA006358_sum_aux f O i =
    f (4 - i).
Proof.
  fold_unfold_tactic ZA006358_sum_aux.
Qed.

Lemma fold_unfold_ZA006358_sum_aux_S :
  forall (f : nat -> Z)
         (n' i : nat),
    ZA006358_sum_aux f (S n') i =
    ZSigma0 (4 - i) (fun j => ZA006358_sum_aux f n' j).
Proof.
  fold_unfold_tactic ZA006358_sum_aux.
Qed.

(* ***** *)

(* Theorem 4.2 for integers *)

Compute ((Z.eqb (ZA006358_sum 0) (ZA006358 0))
         &&
         (Z.eqb (ZA006358_sum 1) (ZA006358 1))
         &&
         (Z.eqb (ZA006358_sum 2) (ZA006358 2))
         &&
         (Z.eqb (ZA006358_sum 3) (ZA006358 3))
         &&
         (Z.eqb (ZA006358_sum 4) (ZA006358 4))
         &&
         (Z.eqb (ZA006358_sum 5) (ZA006358 5))
         &&
         (Z.eqb (ZA006358_sum 6) (ZA006358 6))).

Theorem Theorem_4_dot_2_for_Z :
  forall f : nat -> Z,
    f 0 = 0%Z ->
    f 1 = 0%Z ->
    f 2 = 0%Z ->
    f 3 = 0%Z ->
    f 4 = 1%Z ->
    forall n : nat,
      ZSigma0 4 (fun i => ZA006358_sum_aux f n i) = ZA006358 n.
Proof.
  intros f H_f_0 H_f_1 H_f_2 H_f_3 H_f_4 n.
  rewrite ->4 fold_unfold_ZSigma0_S.
  rewrite -> fold_unfold_ZSigma0_O.
  induction n as [ | | | | | n' IHn' IHSn' IHSSn' IHSSSn' IHSSSSn'] using nat_ind5.
  - rewrite ->? fold_unfold_ZA006358_sum_aux_O.
    simpl (4 - 0).
    simpl (4 - 1).
    simpl (4 - 2).
    simpl (4 - 3).
    simpl (4 - 4).
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->? fold_unfold_ZA006358_sum_aux_S.
    simpl (4 - 0).
    simpl (4 - 1).
    simpl (4 - 2).
    simpl (4 - 3).
    simpl (4 - 4).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006358_sum_aux_S;
            rewrite ->? fold_unfold_ZA006358_sum_aux_O;
            simpl (4 - 0);
            simpl (4 - 1);
            simpl (4 - 2);
            simpl (4 - 3);
            simpl (4 - 4)).
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->? fold_unfold_ZA006358_sum_aux_S.
    simpl (4 - 0).
    simpl (4 - 1).
    simpl (4 - 2).
    simpl (4 - 3).
    simpl (4 - 4).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006358_sum_aux_S;
            rewrite ->? fold_unfold_ZA006358_sum_aux_O;
            simpl (4 - 0);
            simpl (4 - 1);
            simpl (4 - 2);
            simpl (4 - 3);
            simpl (4 - 4)).
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->? fold_unfold_ZA006358_sum_aux_S.
    simpl (4 - 0).
    simpl (4 - 1).
    simpl (4 - 2).
    simpl (4 - 3).
    simpl (4 - 4).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006358_sum_aux_S;
            rewrite ->? fold_unfold_ZA006358_sum_aux_O;
            simpl (4 - 0);
            simpl (4 - 1);
            simpl (4 - 2);
            simpl (4 - 3);
            simpl (4 - 4)).
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite ->? fold_unfold_ZA006358_sum_aux_S.
    simpl (4 - 0).
    simpl (4 - 1).
    simpl (4 - 2).
    simpl (4 - 3).
    simpl (4 - 4).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006358_sum_aux_S;
            rewrite ->? fold_unfold_ZA006358_sum_aux_O;
            simpl (4 - 0);
            simpl (4 - 1);
            simpl (4 - 2);
            simpl (4 - 3);
            simpl (4 - 4)).
    rewrite -> H_f_4.
    rewrite -> H_f_3.
    rewrite -> H_f_2.
    rewrite -> H_f_1.
    rewrite -> H_f_0.
    compute.
    reflexivity.
  - rewrite -> fold_unfold_ZA006358_SSSS.
    rewrite <- IHSSSSn'.
    rewrite <- IHSSSn'.
    rewrite <- IHSSn'.
    rewrite <- IHSn'.
    rewrite <- IHn'.
    rewrite ->? fold_unfold_ZA006358_sum_aux_S.
    simpl (4 - 0).
    simpl (4 - 1).
    simpl (4 - 2).
    simpl (4 - 3).
    simpl (4 - 4).
    repeat (rewrite ->? fold_unfold_ZSigma0_S;
            rewrite ->? fold_unfold_ZSigma0_O;
            rewrite ->? fold_unfold_ZA006358_sum_aux_S;
            rewrite ->? fold_unfold_ZA006358_sum_aux_O;
            simpl (4 - 0);
            simpl (4 - 1);
            simpl (4 - 2);
            simpl (4 - 3);
            simpl (4 - 4)).
    ring.
Qed.

(* ********** *)

(* end of nested-summations.v *)
