(* week-10_mutual-induction-and-recursion.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 24 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =b= B" :=
  (Bool.eqb A B) (at level 70, right associativity).

(* ********** *)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (H_both : P n /\ P (S n)).
  { induction n as [ | n' [IHn' IHSn']].

    - Check (conj H_P0 H_P1).
      exact (conj H_P0 H_P1).

    - Check (H_PSS n' IHn' IHSn').
      Check (conj IHSn' (H_PSS n' IHn' IHSn')).
      exact (conj IHSn' (H_PSS n' IHn' IHSn')).
  } 
  destruct H_both as [ly _].
  exact ly.
Qed.

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

(* ********** *)

Definition test_evenp (candidate : nat -> bool) : bool :=
  (candidate 0 =b= true) &&
  (candidate 1 =b= false) &&
  (candidate 2 =b= true) &&
  (candidate 3 =b= false) &&
  (candidate 4 =b= true) &&
  (candidate 5 =b= false) &&
  (candidate 6 =b= true) &&
  (candidate 7 =b= false) &&
  (candidate 8 =b= true).

Definition test_oddp (candidate : nat -> bool) : bool :=
  (candidate 0 =b= false) &&
  (candidate 1 =b= true) &&
  (candidate 2 =b= false) &&
  (candidate 3 =b= true) &&
  (candidate 4 =b= false) &&
  (candidate 5 =b= true) &&
  (candidate 6 =b= false) &&
  (candidate 7 =b= true) &&
  (candidate 8 =b= false).

Fixpoint evenp (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    oddp n'
  end
with oddp (n : nat) : bool :=
       match n with
       | 0 =>
         false
       | S n' =>
         evenp n'
       end.

Compute (test_evenp evenp && test_oddp oddp).

Lemma fold_unfold_evenp_O :
  evenp 0 =
  true.
Proof.
  fold_unfold_tactic evenp.
Qed.

Lemma fold_unfold_evenp_S :
  forall n' : nat,
    evenp (S n') =
    oddp n'.
Proof.
  fold_unfold_tactic evenp.
Qed.

Lemma fold_unfold_oddp_O :
  oddp 0 =
  false.
Proof.
  fold_unfold_tactic oddp.
Qed.

Lemma fold_unfold_oddp_S :
  forall n' : nat,
    oddp (S n') =
    evenp n'.
Proof.
  fold_unfold_tactic oddp.
Qed.


Corollary fold_unfold_evenp_1 :
  evenp 1 =
  false.
Proof.
  rewrite -> fold_unfold_evenp_S.
  reflexivity.
Qed.

Corollary fold_unfold_evenp_SS :
  forall n'' : nat,
    evenp (S (S n'')) =
    evenp n''.
Proof.
  intro n''.
  rewrite -> fold_unfold_evenp_S.
  reflexivity.
Qed.

(* ***** *)

Lemma twice_S :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
Proof.
  Compute (let n := 10 in
           S (S (2 * n)) = 2 * S n).
Admitted.

Lemma twice :
  forall n : nat,
    n + n = 2 * n.
Proof.
  intro n.
Admitted.

Theorem soundness_and_completeness_of_evenp :
  forall n : nat,
    evenp n = true <-> exists m : nat, n = 2 * m.
Proof.
  intro n.
  induction n as [ | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete]] using nat_ind2.
  - split.
    + intro H_true.
      exists 0.
      Search (_ * 0 = 0).
      rewrite -> (Nat.mul_0_r 2).
      reflexivity.
    + intro H_true.
      rewrite -> (fold_unfold_evenp_O).
      reflexivity.
  - split.
    + intro H_absurd.
      discriminate H_absurd.
    + rewrite -> (fold_unfold_evenp_S 0).
      rewrite -> (fold_unfold_oddp_O).
      intro H_absurd.
      destruct H_absurd as [m H_m].
      case m as [ | m'].
      ++ rewrite -> (Nat.mul_0_r 2) in H_m.
         discriminate H_m.
      ++ Search (_ * S _).
         Check (Nat.mul_succ_r 2 m').
         rewrite -> (Nat.mul_succ_r 2 m') in H_m.
         Search (_ + S _ = S _).
         rewrite ->2 Nat.add_succ_r in H_m.
         discriminate H_m.
  - split.
    + rewrite -> (fold_unfold_evenp_S (S n')).
      rewrite -> (fold_unfold_oddp_S n').
      intro H_true.
      Check (IHn'_sound H_true).
      destruct (IHn'_sound H_true) as [m H_m].
      rewrite -> H_m.
      Check (twice_S m).
      rewrite -> (twice_S m).
      exists (S m).
      reflexivity.   
    + rewrite -> (fold_unfold_evenp_S (S n')).
      rewrite -> (fold_unfold_oddp_S n').
      intros [m H_m].
      apply IHn'_complete.
      case m as [ | m'].
      ++ rewrite -> (Nat.mul_0_r 2) in H_m.
         discriminate H_m.
      ++ rewrite <- (twice_S m') in H_m.
         (*remember (2 * m') as m'' eqn:H_m''.
         injection H_m as H_n'.
         rewrite -> H_m'' in H_n'.
         clear H_m''.*)
         rewrite -> Nat.mul_comm in H_m.
         injection H_m as H_n'.
         rewrite -> Nat.mul_comm in H_n'.
         rewrite -> H_n'.
         exists m'.
         reflexivity.
Qed.
       
Theorem soundness_and_completeness_of_evenp_messy :
  forall n : nat,
    evenp n = true <-> exists m : nat, n = 2 * m.
Proof.
  intro n.
  induction n as [ | n' [IHn'_sound IHn'_complete]].
  - split.
    + intro H_true.
      exists 0.
      Search (_ * 0 = 0).
      rewrite -> (Nat.mul_0_r 2).
      reflexivity.
    + intro H_true.
      rewrite -> (fold_unfold_evenp_O).
      reflexivity.
  - split.
    + rewrite -> (fold_unfold_evenp_S n').
      intro H_n'.
      case n' as [ | n''].
      * rewrite -> fold_unfold_oddp_O in H_n'.
        discriminate H_n'.
      * rewrite -> fold_unfold_oddp_S in H_n'.
        rewrite -> fold_unfold_evenp_S in IHn'_sound.
        rewrite -> fold_unfold_evenp_S in IHn'_complete.
Abort.

(* ***** *)

Theorem soundness_and_completeness_of_oddp :
  forall n : nat,
    oddp n = true <-> exists m : nat, n = S (2 * m).
Proof.
  intro n.
  induction n as [ | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete]] using nat_ind2.
  - split.
    + intro H_absurd.
      exists 0.
      Search (_ * 0 = 0).
      rewrite -> (Nat.mul_0_r 2).
      discriminate H_absurd.
    + intro H_absurd.
      rewrite -> (fold_unfold_oddp_O).
      destruct H_absurd as [m H_m].
      case m as [ | m'].
      ++ discriminate H_m.
      ++ discriminate H_m.
  - split.
    + intro H_true.
      exists 0.
      Search (_ * 0 = _).
      rewrite -> (Nat.mul_0_r 2).
      reflexivity.
    + intro H_true.
      destruct H_true as [m H_m].
      case m as [ | m'].
      ++ exact (fold_unfold_oddp_S 0).
      ++ exact (fold_unfold_oddp_S 0).
  - split.
    + rewrite -> (fold_unfold_oddp_S (S n')).
      rewrite -> (fold_unfold_evenp_S n').
      intro H_true.
      Check (IHn'_sound H_true).
      destruct (IHn'_sound H_true) as [m H_m].
      rewrite -> H_m.
      Check (twice_S m).
      rewrite -> (twice_S m).
      exists (S m).
      reflexivity.
    + rewrite -> (fold_unfold_oddp_S (S n')).
      rewrite -> (fold_unfold_evenp_S n').
      intros [m H_m].
      apply IHn'_complete.
      case m as [ | m'].
      ++ rewrite -> (Nat.mul_0_r 2) in H_m.
         discriminate H_m.
      ++ rewrite <- (twice_S m') in H_m.
         rewrite -> Nat.mul_comm in H_m.
         injection H_m as H_n'.
         rewrite -> Nat.mul_comm in H_n'.
         rewrite -> H_n'.
         exists m'.
         reflexivity.
Qed.

Theorem soundness_and_completeness_of_oddp_messy :
  forall n : nat,
    oddp n = true <-> exists m : nat, n = S (2 * m).
Proof.
  intro n.
  induction n as [ | n' [IHn'_sound IHn'_complete]].
Abort.

(* ***** *)

Theorem soundness_and_completeness_of_evenp_and_of_oddp :
  forall n : nat,
    (evenp n = true <-> exists m : nat, n = 2 * m)
    /\
      (oddp n = true <-> exists m : nat, n = S (2 * m)).
Proof.
  intro n.
  induction n as [ | n' [[IHn'_esound IHn'_ecomplete] [IHn'_osound IHn'_ocomplete]]].
  - split.
    +  split.
       ++ intro H_true.
          exists 0.
          rewrite -> (Nat.mul_0_r 2).
          reflexivity.
       ++ intro H_true.
          rewrite -> (fold_unfold_evenp_O).
          reflexivity.
    + split.
      ++ intro H_absurd.
         discriminate H_absurd.
      ++ intro H_absurd.
         rewrite -> (fold_unfold_oddp_O).
         destruct H_absurd as [m H_m].
         case m as [ | m'].
         +++ discriminate H_m.
         +++ discriminate H_m.
  - split.
    + split.
      ++ intro H_true.
         rewrite -> (fold_unfold_evenp_S n') in H_true.
         apply IHn'_osound in H_true.
         destruct H_true as [m H_m].
         rewrite -> H_m.
         rewrite -> (twice_S m).
         exists (S m).
         reflexivity.
      ++ rewrite -> (fold_unfold_evenp_S n').
         intros [m H_m].
         apply IHn'_ocomplete.
         case m as [ | m'].
         +++ rewrite -> (Nat.mul_0_r 2) in H_m.
             discriminate H_m.
         +++ rewrite <- (twice_S m') in H_m.
             rewrite -> Nat.mul_comm in H_m.
             injection H_m as H_n'.
             rewrite -> Nat.mul_comm in H_n'.
             rewrite -> H_n'.
             exists m'.
             reflexivity.
    + split.
      ++ intro H_true.
         rewrite -> (fold_unfold_oddp_S n') in H_true.
         apply IHn'_esound in H_true.
         destruct H_true as [m H_m].
         rewrite -> H_m.
         exists m.
         reflexivity.
      ++ rewrite -> (fold_unfold_oddp_S n').
         intros [m H_m].
         apply IHn'_ecomplete.
         case m as [ | m'].
         +++ exists 0.
             injection H_m.
             intro H_n.
             Search (_ * 0 = 0).
             rewrite -> (Nat.mul_0_r 2).
             exact H_n.
         +++ exists (S m').
             injection H_m.
             intro H_n.
             rewrite -> (Nat.add_0_r m') in H_n.
             Search (S (_ + _)).
             rewrite <- (plus_Sn_m m' (S m')) in H_n.
             rewrite -> H_n.
             exact (twice (S m')).
Qed.

(* ********** *)

Definition test_ternaryp (candidate : nat -> bool) : bool :=
  (candidate 0 =b= true) &&
  (candidate 1 =b= false) &&
  (candidate 2 =b= false) &&
  (candidate 3 =b= true) &&
  (candidate 4 =b= false) &&
  (candidate 5 =b= false) &&
  (candidate 6 =b= true) &&
  (candidate 7 =b= false) &&
  (candidate 8 =b= false).

Definition test_pre_ternaryp (candidate : nat -> bool) : bool :=
  (candidate 0 =b= false) &&
  (candidate 1 =b= false) &&
  (candidate 2 =b= true) &&
  (candidate 3 =b= false) &&
  (candidate 4 =b= false) &&
  (candidate 5 =b= true) &&
  (candidate 6 =b= false) &&
  (candidate 7 =b= false) &&
  (candidate 8 =b= true).

Definition test_post_ternaryp (candidate : nat -> bool) : bool :=
  (candidate 0 =b= false) &&
  (candidate 1 =b= true) &&
  (candidate 2 =b= false) &&
  (candidate 3 =b= false) &&
  (candidate 4 =b= true) &&
  (candidate 5 =b= false) &&
  (candidate 6 =b= false) &&
  (candidate 7 =b= true) &&
  (candidate 8 =b= false).

Fixpoint independent_pre_ternaryp (n : nat) : bool :=
  match n with
  | 0 =>
    false
  | 1 =>
    false
  | 2 =>
    true
  | S (S (S n')) =>
    independent_pre_ternaryp n'
  end.

Compute (test_pre_ternaryp independent_pre_ternaryp).

Fixpoint independent_ternaryp (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | 1 =>
    false
  | 2 =>
    false
  | S (S (S n')) =>
    independent_ternaryp n'
  end.

Compute (test_ternaryp independent_ternaryp).

Lemma fold_unfold_independent_ternaryp_O :
  independent_ternaryp 0 =
  true.
Proof.
  fold_unfold_tactic independent_ternaryp.
Qed.

Lemma fold_unfold_independent_ternaryp_1 :
  independent_ternaryp 1 =
  false.
Proof.
  fold_unfold_tactic independent_ternaryp.
Qed.

Lemma fold_unfold_independent_ternaryp_2 :
  independent_ternaryp 2 =
  false.
Proof.
  fold_unfold_tactic independent_ternaryp.
Qed.

Lemma fold_unfold_independent_ternaryp_SSS :
  forall n' : nat,
    independent_ternaryp (S (S (S n'))) =
    independent_ternaryp n'.
Proof.
  fold_unfold_tactic independent_ternaryp.
Qed.

Theorem soundness_and_completeness_of_independent_ternaryp :
  forall n : nat,
    independent_ternaryp n = true <-> exists m : nat, n = 3 * m.
Proof.
  intro n.
  induction n as [ | | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete] [IHSSn'_sound IHSSn'_complete]] using nat_ind3.
Abort.

Theorem soundness_and_completeness_of_independent_ternaryp_messy :
  forall n : nat,
    independent_ternaryp n = true <-> exists m : nat, n = 3 * m.
Proof.
  intro n.
  induction n as [ | n' [IHn'_sound IHn'_complete]].
Abort.

Theorem soundness_and_completeness_of_independent_ternaryp_messy2 :
  forall n : nat,
    independent_ternaryp n = true <-> exists m : nat, n = 3 * m.
Proof.
  intro n.
  induction n as [ | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete]] using nat_ind2.
Abort.

Fixpoint independent_post_ternaryp (n : nat) : bool :=
  match n with
  | 0 =>
    false
  | 1 =>
    true
  | 2 =>
    false
  | S (S (S n')) =>
    independent_post_ternaryp n'
  end.

Compute (test_post_ternaryp independent_post_ternaryp).

(* ***** *)

Fixpoint pre_ternaryp (n : nat) : bool :=
  match n with
  | 0 =>
    false
  | S n' =>
    post_ternaryp n'
  end
with ternaryp (n : nat) : bool :=
       match n with
       | 0 =>
         true
       | S n' =>
         pre_ternaryp n'
       end
with post_ternaryp (n : nat) : bool :=
       match n with
       | 0 =>
         false
       | S n' =>
         ternaryp n'
       end.

Compute (test_pre_ternaryp pre_ternaryp && test_ternaryp ternaryp && test_post_ternaryp post_ternaryp).

Lemma fold_unfold_pre_ternaryp_O :
  pre_ternaryp 0 =
  false.
Proof.
  fold_unfold_tactic pre_ternaryp.
Qed.

Lemma fold_unfold_pre_ternaryp_S :
  forall n' : nat,
    pre_ternaryp (S n') =
    post_ternaryp n'.
Proof.
  fold_unfold_tactic pre_ternaryp.
Qed.

Lemma fold_unfold_ternaryp_O :
  ternaryp 0 =
  true.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_ternaryp_S :
  forall n' : nat,
    ternaryp (S n') =
    pre_ternaryp n'.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_post_ternaryp_O :
  post_ternaryp 0 =
  false.
Proof.
  fold_unfold_tactic post_ternaryp.
Qed.

Lemma fold_unfold_post_ternaryp_S :
  forall n' : nat,
    post_ternaryp (S n') =
    ternaryp n'.
Proof.
  fold_unfold_tactic post_ternaryp.
Qed.

(* ***** *)

Theorem soundness_and_completeness_of_ternaryp :
  forall n : nat,
    ternaryp n = true <-> exists m : nat, n = 3 * m.
Proof.
  intro n.
  induction n as [ | | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete] [IHSSn'_sound IHSSn'_complete]] using nat_ind3.
Abort.

Theorem soundness_and_completeness_of_post_ternaryp :
  forall n : nat,
    post_ternaryp n = true <-> exists m : nat, n = S (3 * m).
Proof.
  intro n.
  induction n as [ | | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete] [IHSSn'_sound IHSSn'_complete]] using nat_ind3.
Abort.

Theorem soundness_and_completeness_of_pre_ternaryp :
  forall n : nat,
    pre_ternaryp n = true <-> exists m : nat, n = S (S (3 * m)).
Proof.
  intro n.
  induction n as [ | | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete] [IHSSn'_sound IHSSn'_complete]] using nat_ind3.
Abort.

(* ***** *)

Theorem soundness_and_completeness_of_ternaryp_and_friends :
  forall n : nat,
    (pre_ternaryp n = true <-> exists m : nat, n = S (S (3 * m)))
    /\
    (ternaryp n = true <-> exists m : nat, n = 3 * m)
    /\
    (post_ternaryp n = true <-> exists m : nat, n = S (3 * m)).
Proof.
  intro n.
  induction n as [ | n' [[IHn'_presound IHn'_precomplete] [[IHn'_tsound IHn'_tcomplete] [IHn'_postsound IHn'_postcomplete]]]].
Abort.

(* ********** *)

(* week-10_mutual-induction-and-recursion.v *)
