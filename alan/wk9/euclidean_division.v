Require Import Bool Arith.

Proposition euclids_division :
  forall d : nat,
    0 < d ->
    forall n : nat,
    exists q r : nat,
      r < d /\ n = q * d + r.
Proof.
  intros d lt_0_d n.
  induction n as [ | n' [q [r [lt_r_Sd' H_n]]]].
  - exists 0, 0.
    split.
    + exact lt_0_d.
    + rewrite -> Nat.add_0_r.
      rewrite -> Nat.mul_0_l.
      reflexivity.
  - case d as [ | d'].
    -- Check (Nat.nlt_0_r 0 lt_0_d).
       contradiction (Nat.nlt_0_r 0 lt_0_d).
    -- Check (le_lt_or_eq).
       Check (lt_le_S r (S d') lt_r_Sd').
       Check (le_S_n r d').
       case (le_lt_or_eq r d' (le_S_n r d' (lt_le_S r (S d') lt_r_Sd'))) as [lt_r_d' | eq_r_d'].
       + exists q, (S r).
         split.
         ++ Search (S _ < S _).
            destruct (Nat.succ_lt_mono r d') as [lt_Sr_Sd' _].
            exact (lt_Sr_Sd' lt_r_d').
         ++ rewrite -> H_n.
            Search (S (_ + _)).
            rewrite -> plus_n_Sm.
            reflexivity.
       + exists (S q), 0.
         split.
         ++ exact lt_0_d.
         ++ rewrite -> H_n.
            rewrite -> plus_n_Sm.
            rewrite -> eq_r_d'.
            rewrite <- Nat.mul_succ_l.
            rewrite -> Nat.add_0_r.
            reflexivity.
Qed.

Proposition euclids_division_alt :
  forall d n : nat,
  exists q r : nat,
    r < S d /\ n = q * (S d) + r.
Proof.
  intros d n.
  induction n as [ | n' [q [r [lt_r_Sd H_n]]]].
  - exists 0, 0.
    split.
    + Search (0 < S _).
      exact (Nat.lt_0_succ d).
    + rewrite -> (Nat.add_0_r (0 * S d)).
      rewrite -> (Nat.mul_0_l (S d)).
      reflexivity.
  - case (le_lt_or_eq r d (le_S_n r d (lt_le_S r (S d) lt_r_Sd))) as [lt_r_d | eq_r_d].
    -- exists q, (S r).
       split.
       + destruct (Nat.succ_lt_mono r d) as [lt_Sr_Sd _].
         exact (lt_Sr_Sd lt_r_d).
       + rewrite -> H_n.
         rewrite -> plus_n_Sm.
         reflexivity.
    -- exists (S q), 0.
       split.
       + exact (Nat.lt_0_succ d).
       + rewrite -> H_n.
         rewrite -> plus_n_Sm.
         rewrite -> eq_r_d.
         rewrite <- Nat.mul_succ_l.
         rewrite -> Nat.add_0_r.
         reflexivity.
Qed.

Corollary euclids_division_alt_using_euclids_division :
  forall d n : nat,
  exists q r : nat,
    r < S d /\ n = q * (S d) + r.
Proof.
  intro d.
  exact (euclids_division (S d) (Nat.lt_0_succ d)).
Qed.

Corollary euclids_division_using_euclids_division_alt :
  forall d : nat,
    0 < d ->
    forall n : nat,
    exists q r : nat,
      r < d /\ n = q * d + r.
Proof.
  intros d lt_0_d n.
  case d as [ | d'].
  - contradiction (Nat.nlt_0_r 0 lt_0_d).
  - exact (euclids_division_alt d' n).
Qed.
