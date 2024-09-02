(* week-08_uniqueness-of-the-quotient-and-remainder.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 10 Oct 2023 *)

(* ********** *)

Require Import Arith Bool.

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

(* ********** *)

Check plus_reg_l.
(* : forall n m p : nat, p + n = p + m -> n = m *)

(* ***** *)

Lemma plus_reg_r :
  forall n m p : nat,
    n + p = m + p ->
    n = m.
Proof.
  intros n m p P.
  rewrite ->2 (Nat.add_comm _ p) in P.
  Check (plus_reg_l n m p P).
  exact (plus_reg_l n m p P).
Qed.

(* ********** *)

Definition fold_unfold_mul_O := Nat.mul_0_l.
  
Definition fold_unfold_mul_S := Nat.mul_succ_l.

(* ********** *)

(* Needed: the analogue of plus_reg_l for multiplication *)

Lemma times_reg_l :
  forall n m p : nat,
    S p * n = S p * m ->
    n = m.
Proof.
  intros n m p.
  revert m.
  induction n as [ | n' IHn']; intros [ | m'] H_Sp.
  Search (0 * _ = _).
  Search (S _ * _ = _).
Admitted.

(* ********** *)

Print Nat.sub.

Lemma fold_unfold_sub_O :
  forall m : nat,
    0 - m = 0.
Proof.
  fold_unfold_tactic Nat.sub.
Qed.

Lemma fold_unfold_sub_S :
  forall n' m : nat,
    S n' - m =
    match m with
    | 0 => S n'
    | S m' => n' - m'
    end.
Proof.
  fold_unfold_tactic Nat.sub.
Qed.

(* ********** *)

(* Useful: the following resident lemmas *)

(*
  Nat.add_sub_assoc : forall n m p : nat, p <= m -> n + (m - p) = n + m - p
  Nat.add_sub_eq_l : forall n m p : nat, m + p = n -> n - m = p
  Nat.add_sub_eq_r : forall n m p : nat, m + p = n -> n - p = m
  Nat.lt_0_succ : forall n : nat, 0 < S n
  Nat.lt_le_incl : forall n m : nat, n < m -> n <= m
  Nat.lt_trans : forall n m p : nat, n < m -> m < p -> n < p
  Nat.mul_sub_distr_r : forall n m p : nat, (n - m) * p = n * p - m * p
  Nat.sub_0_r : forall n : nat, n - 0 = n
  Nat.sub_add_distr : forall n m p : nat, n - (m + p) = n - m - p
  Nat.sub_gt : forall n m : nat, m < n -> n - m <> 0
  Nat.sub_lt : forall n m : nat, m <= n -> 0 < m -> n - m < n
  mult_S_lt_compat_l : forall n m p : nat, m < p -> S n * m < S n * p
*)

(* ********** *)

Lemma helpful_1 :
  forall x y : nat,
    x * S y < S y ->
    x = 0.
Proof.
  intros [ | x'] y H_lt.
  - reflexivity.
  - Search (S _ * _ = _ * _ + _).
    rewrite -> fold_unfold_mul_S in H_lt.
    rewrite -> Nat.add_comm in H_lt.
    rewrite <- (Nat.add_0_r (S y)) in H_lt at 3.
    Search (_ + _ < _ + _ -> _ < _).
    Check (plus_lt_reg_l (x' * S y) 0 (S y)).
    Check (plus_lt_reg_l (x' * S y) 0 (S y) H_lt).
    (* : x' * S y < 0 *)
    Search (_ < 0).
    Check (Nat.nlt_0_r (x' * S y)).
    Check (Nat.nlt_0_r (x' * S y) (plus_lt_reg_l (x' * S y) 0 (S y) H_lt)).
    contradiction (Nat.nlt_0_r (x' * S y) (plus_lt_reg_l (x' * S y) 0 (S y) H_lt)).
Qed.

(* ********** *)

Lemma helpful_2 :
  forall x y : nat,
    x - y = 0 ->
    x <= y.
Proof.
  intro x.
  induction x as [ | x' IHx']; intros y H_y.
  - Search (0 <= _).
    Check (Nat.le_0_l y).
    exact (Nat.le_0_l y).
  - case y as [ | y'].
    + rewrite -> fold_unfold_sub_S in H_y.
      discriminate H_y.
    + rewrite -> fold_unfold_sub_S in H_y.
      Check (IHx' y' H_y).
      Search (_ <= _ -> S _ <= S _).
      Check (le_n_S x' y').
      Check (le_n_S x' y' (IHx' y' H_y)).
      exact (le_n_S x' y' (IHx' y' H_y)).
Qed.

(* ********** *)

Lemma uniqueness_lt_lt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 < q2 ->
    r1 < r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r1_r2.
  Check Nat.add_sub_eq_r.
  Check (Nat.add_sub_eq_r (q2 * S d + r2) (q1 * S d) r1).
  apply (Nat.add_sub_eq_r (q2 * S d + r2) (q1 * S d) r1) in H_main.
  Check Nat.add_sub_assoc.
  Check (Nat.add_sub_assoc (q2 * S d) r2 r1).
  Search (_ < _ -> _ <= _).
  Check (Nat.lt_le_incl r1 r2).
  Check (Nat.lt_le_incl r1 r2 lt_r1_r2).
  Check (Nat.add_sub_assoc (q2 * S d) r2 r1 (Nat.lt_le_incl r1 r2 lt_r1_r2)).
  rewrite <- (Nat.add_sub_assoc (q2 * S d) r2 r1 (Nat.lt_le_incl r1 r2 lt_r1_r2)) in H_main.
  Check Nat.add_sub_eq_l.
  rewrite <- (Nat.add_0_r (q1 * S d)) in H_main.
  Check Nat.add_sub_eq_l.
  symmetry in H_main.
  Check Nat.add_sub_eq_l.
  Check (Nat.add_sub_eq_l (q2 * S d + (r2 - r1)) (q1 * S d) 0).
  apply (Nat.add_sub_eq_l (q2 * S d + (r2 - r1)) (q1 * S d) 0) in H_main.
  rewrite -> Nat.add_comm in H_main.
  Check Nat.add_sub_assoc.
  Check (Nat.add_sub_assoc (r2 - r1) (q2 * S d) (q1 * S d)).
  assert (wanted :
            q1 * S d <= q2 * S d).
  { Search (_ < _ -> S _ * _ < S _ * _).
      Check (mult_S_lt_compat_l d q1 q2 lt_q1_q2).
      rewrite ->2 (Nat.mul_comm _ (S d)).
      Check (mult_S_lt_compat_l d q1 q2 lt_q1_q2).
      Search (_ < _ -> _ <= _).
      Check (Nat.lt_le_incl (S d * q1) (S d * q2)).
      Check (Nat.lt_le_incl (S d * q1) (S d * q2) (mult_S_lt_compat_l d q1 q2 lt_q1_q2)).
      exact (Nat.lt_le_incl (S d * q1) (S d * q2) (mult_S_lt_compat_l d q1 q2 lt_q1_q2)). }
  Check (Nat.add_sub_assoc (r2 - r1) (q2 * S d) (q1 * S d) wanted).
  rewrite <- (Nat.add_sub_assoc (r2 - r1) (q2 * S d) (q1 * S d) wanted) in H_main.
  Search (_ + _ = 0 -> _ /\ _).
  Check plus_is_O.
  Check (plus_is_O (r2 - r1) (q2 * S d - q1 * S d)).
  Check (plus_is_O (r2 - r1) (q2 * S d - q1 * S d) H_main).
  destruct (plus_is_O (r2 - r1) (q2 * S d - q1 * S d) H_main) as [H_r2_r1 H_q2_q1].
  Check (helpful_2 r2 r1 H_r2_r1).
  Search (_ < _ -> ~ (_ <= _)).
  Check lt_not_le.
  Check (lt_not_le r1 r2 lt_r1_r2).
  Check (lt_not_le r1 r2 lt_r1_r2 (helpful_2 r2 r1 H_r2_r1)).
  contradiction (lt_not_le r1 r2 lt_r1_r2 (helpful_2 r2 r1 H_r2_r1)).
Qed.

Lemma uniqueness_lt_eq :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 < q2 ->
    r1 = r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 eq_r1_r2.
  (* easy: use plus_reg_l and times_reg_l *)
Admitted.

Lemma uniqueness_lt_gt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 < q2 ->
    r2 < r1 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r2_r1.
  (* subtract r2 and q1 * S d, and deduce a contradiction *)
Admitted.

Lemma uniqueness_eq_lt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 = q2 ->
    r1 < r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r1_r2.
  (* easy: use plus_reg_l *)
Admitted.

Lemma uniqueness_eq_eq :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 = q2 ->
    r1 = r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 eq_r1_r2.
  exact (conj eq_q1_q2 eq_r1_r2).
Qed.

Lemma uniqueness_eq_gt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 = q2 ->
    r2 < r1 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r2_r1.
  symmetry in H_main.
  (* use uniqueness_eq_lt *)
(*
  destruct (uniqueness_eq_lt n d ...) as [eq_q2_q1 eq_r2_r1].
  exact (conj eq_q1_q2 (eq_sym eq_r2_r1)).
*)
Admitted.

Lemma uniqueness_gt_lt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q2 < q1 ->
    r1 < r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 lt_r1_r2.
  symmetry in H_main.
  (* use uniqueness_lt_gt *)
(*
  destruct (uniqueness_lt_gt n d ...) as [eq_q2_q1 eq_r2_r1].
  exact (conj (eq_sym eq_q2_q1) (eq_sym eq_r2_r1)).
*)
Admitted.

Lemma uniqueness_gt_eq :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q2 < q1 ->
    r1 = r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main gt_q1_q2 eq_r1_r2.
  symmetry in H_main.
  (* use uniqueness_lt_eq *)
(*
  destruct (uniqueness_lt_eq n d ...) as [lt_q2_q1 eq_r2_r1].
  exact (conj (eq_sym lt_q2_q1) eq_r1_r2).
*)
Admitted.

Lemma uniqueness_gt_gt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q2 < q1 ->
    r2 < r1 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main gt_q1_q2 gt_r1_r2.
  symmetry in H_main.
  (* use uniqueness_lt_lt *)
(*
  destruct (uniqueness_lt_lt n d ...) as [lt_q2_q1 lt_r2_r1].
  exact (conj (eq_sym lt_q2_q1) (eq_sym lt_r2_r1)).
*)
Admitted.

Lemma uniqueness :
  forall n d : nat,
  forall q1 r1 : nat,
    r1 < S d ->
    n = q1 * S d + r1 ->
    forall q2 r2 : nat,
      r2 < S d ->
      n = q2 * S d + r2 ->
      q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 lt_r1_Sd H_n1 q2 r2 lt_r2_Sd H_n2.
  assert (H_main := H_n2).
  rewrite -> H_n1 in H_main.
  Search (_ < _ \/ _ = _ \/ _ < _).
  Check (Nat.lt_trichotomy r1 r2).
  destruct (Nat.lt_trichotomy q1 q2) as [lt_q1_q2 | [eq_q1_q2 | lt_q2_q1]];
    destruct (Nat.lt_trichotomy r1 r2) as [lt_r1_r2 | [eq_r1_r2 | lt_r2_r1]].

  - exact (uniqueness_lt_lt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r1_r2).

  - exact (uniqueness_lt_eq n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 eq_r1_r2).

  - exact (uniqueness_lt_gt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r2_r1).

  - exact (uniqueness_eq_lt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r1_r2).

  - exact (uniqueness_eq_eq n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 eq_r1_r2).

  - exact (uniqueness_eq_gt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r2_r1).

  - exact (uniqueness_gt_lt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 lt_r1_r2).

  - exact (uniqueness_gt_eq n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 eq_r1_r2).

  - exact (uniqueness_gt_gt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 lt_r2_r1).
Qed.

(* ********** *)

(* end of week-08_uniqueness-of-the-quotient-and-remainder.v *)
