(* week-10_induction-principles.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 24 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

(* One goal of this lecture is to revisit the proof that
   at most one function satisfies the following specification.
*)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

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

Proposition fib_satisfies_the_specification_of_fib :
  specification_of_the_fibonacci_function fib.
Proof.
  unfold specification_of_the_fibonacci_function.
  Check (conj fold_unfold_fib_O (conj fold_unfold_fib_1 fold_unfold_fib_SS)).
  exact (conj fold_unfold_fib_O (conj fold_unfold_fib_1 fold_unfold_fib_SS)).
Qed.

(* ********** *)

(* The mathematical induction principle already exists,
   it is the structural induction principle associated to Peano numbers:
*)

Check nat_ind.

(* But we can still express it ourselves.
   We can also prove it using the resident mathematical induction principle,
   either implicitly or explicitly:
*)

Lemma nat_ind1 :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.
Proof.
  intros P P_0 P_S n.
  induction n as [ | n' IHn'].
  - exact P_0.
  - Check (P_S n').
    exact (P_S n' IHn').
Qed.

(* ********** *)

(* We can also use nat_ind as an ordinary lemma
   instead of using the induction tactic:
*)

Fixpoint add_v0 (i j : nat) : nat :=
  match i with
  | O =>
    j
  | S i' =>
    S (add_v0 i' j)
  end.

Lemma fold_unfold_add_v0_O :
  forall j : nat,
    add_v0 0 j =
    j.
Proof.
  fold_unfold_tactic add_v0.
Qed.

Lemma fold_unfold_add_v0_S :
  forall i' j : nat,
    add_v0 (S i') j =
    S (add_v0 i' j).
Proof.
  fold_unfold_tactic add_v0.
Qed.

Proposition add_v0_0_r :
  forall i : nat,
    add_v0 i 0 = i.
Proof.
  (* First, a routine induction: *)
  intro i.
  induction i as [ | i' IHi'].
  - exact (fold_unfold_add_v0_O 0).
  - rewrite -> fold_unfold_add_v0_S.
    Check f_equal.
    Check (f_equal S). (* : forall x y : nat, x = y -> S x = S y *)
    Check (f_equal S IHi').
    exact (f_equal S IHi').

  Restart.

  (* And now for using nat_ind: *)
  Check nat_ind.
  Check (nat_ind (fun i => add_v0 i 0 = i)).
  Check (nat_ind (fun i => add_v0 i 0 = i) (fold_unfold_add_v0_O 0)).
  apply (nat_ind (fun i => add_v0 i 0 = i) (fold_unfold_add_v0_O 0)).
  intros n IHn.
  rewrite -> fold_unfold_add_v0_S.
  Check (f_equal S IHn).
  exact (f_equal S IHn).
Qed.

(* ********** *)

Fixpoint fibfib (n : nat) : nat * nat :=
  match n with
  | O =>
    (0, 1)
  | S n' =>
    let (fib_n', fib_succ_n') := fibfib n'
    in (fib_succ_n', fib_n' + fib_succ_n')
  end.

Definition fib_lin (n : nat) : nat :=
  let (fib_n, _) := fibfib n
  in fib_n.

Lemma fold_unfold_fibfib_O :
  fibfib 0 =
  (0, 1).
Proof.
  fold_unfold_tactic fibfib.
Qed.

Lemma fold_unfold_fibfib_S :
  forall n' : nat,
    fibfib (S n') =
    let (fib_n', fib_succ_n') := fibfib n'
    in (fib_succ_n', fib_n' + fib_succ_n').
Proof.
  fold_unfold_tactic fibfib.
Qed.

Lemma about_fibfib :
  forall fib : nat -> nat,
    specification_of_the_fibonacci_function fib ->
    forall n : nat,
      fibfib n = (fib n, fib (S n)).
Proof.
  unfold specification_of_the_fibonacci_function.
  intros fib [S_fib_O [S_fib_1 S_fib_SS]] n.
  induction n as [ | [ | n''] IH].
  - rewrite -> fold_unfold_fibfib_O.
    rewrite -> S_fib_O.
    rewrite -> S_fib_1.
    reflexivity.
  - rewrite -> fold_unfold_fibfib_S.
    rewrite -> fold_unfold_fibfib_O.
    rewrite -> S_fib_1.
    rewrite -> S_fib_SS.
    rewrite -> S_fib_O.
    rewrite -> S_fib_1.
    reflexivity.
  - rewrite -> fold_unfold_fibfib_S.
    rewrite -> IH.
    rewrite <- (S_fib_SS (S n'')).
    reflexivity.
Qed.

Proposition fib_lin_satisfies_the_specification_of_fib :
  specification_of_the_fibonacci_function fib_lin.
Proof.
  unfold specification_of_the_fibonacci_function, fib_lin.
  split.
  - rewrite -> fold_unfold_fibfib_O.
    reflexivity.
  - split.
    + rewrite -> fold_unfold_fibfib_S.
      rewrite -> fold_unfold_fibfib_O.
      reflexivity.
    + intro i.
      Check (about_fibfib fib fib_satisfies_the_specification_of_fib (S (S i))).
      rewrite -> (about_fibfib fib fib_satisfies_the_specification_of_fib (S (S i))).
      rewrite -> (about_fibfib fib fib_satisfies_the_specification_of_fib i).
      rewrite -> (about_fibfib fib fib_satisfies_the_specification_of_fib (S i)).
      exact (fold_unfold_fib_SS i).
Qed.

(* ********** *)

(* We can also express a mathematical induction principle
   with two base cases and two induction hypotheses
   that befits the structure of the Fibonacci function:
*)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  induction n as [ | [ | n''] IHn'].
  - exact H_P0.
  - exact H_P1.
  -

  Restart.

  intros P H_P0 H_P1 H_PSS n.
  assert (both :
           forall m : nat,
             P m /\ P (S m)).
  { intro m.
    induction m as [ | m' [IHm' IHSm']].
    - exact (conj H_P0 H_P1).
    - split.
      + exact IHSm'.
      + exact (H_PSS m' IHm' IHSm'). }
  destruct (both n) as [ly _].
  exact ly.
Qed.

(* Thus equipped, the following theorem is proved pretty directly: *)

Theorem there_is_at_most_one_fibonacci_function :
  forall fib1 fib2 : nat -> nat,
    specification_of_the_fibonacci_function fib1 ->
    specification_of_the_fibonacci_function fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_the_fibonacci_function.
  intros [H_fib1_0 [H_fib1_1 H_fib1_SS]]
         [H_fib2_0 [H_fib2_1 H_fib2_SS]]
         n.
  induction n as [ | | n'' IHn'' IHSn''] using nat_ind2.
  - rewrite -> H_fib2_0.
    exact H_fib1_0.
  - rewrite -> H_fib2_1.
    exact H_fib1_1.
  - rewrite -> H_fib1_SS.
    rewrite -> H_fib2_SS.
    rewrite -> IHn''.
    rewrite -> IHSn''.
    reflexivity.
Qed.

(* ***** *)

Fixpoint evenp1 (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    negb (evenp1 n')
  end.

Lemma fold_unfold_evenp1_O :
  evenp1 0 =
  true.
Proof.
  fold_unfold_tactic evenp1.
Qed.

Lemma fold_unfold_evenp1_S :
  forall n' : nat,
    evenp1 (S n') =
    negb (evenp1 n').
Proof.
  fold_unfold_tactic evenp1.
Qed.

(* ***** *)

(* The evenness predicate is often programmed tail-recursively
   and with no accumulator, by peeling two layers of S at a time.
   Its equivalence with evenp1 is messy to prove by mathematical induction
   but effortless using nat_ind2:
*)

Fixpoint evenp2 (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    match n' with
    | 0 =>
      false
    | S n'' =>
      evenp2 n''
    end
  end.

Lemma fold_unfold_evenp2_O :
  evenp2 0 =
  true.
Proof.
  fold_unfold_tactic evenp2.
Qed.

Lemma fold_unfold_evenp2_S :
  forall n' : nat,
    evenp2 (S n') =
    match n' with
    | 0 =>
      false
    | S n'' =>
      evenp2 n''
    end.
Proof.
  fold_unfold_tactic evenp2.
Qed.

Corollary fold_unfold_evenp2_1 :
  evenp2 1 =
  false.
Proof.
  rewrite -> fold_unfold_evenp2_S.
  reflexivity.
Qed.

Corollary fold_unfold_evenp2_SS :
  forall n'' : nat,
    evenp2 (S (S n'')) =
    evenp2 n''.
Proof.
  intro n''.
  rewrite -> fold_unfold_evenp2_S.
  reflexivity.
Qed.

Theorem evenp1_and_evenp2_are_functionally_equal :
  forall n : nat,
    evenp1 n = evenp2 n.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  - rewrite -> fold_unfold_evenp1_O.
    rewrite -> fold_unfold_evenp2_O.
    reflexivity.
  - rewrite -> fold_unfold_evenp1_S.
    rewrite -> fold_unfold_evenp2_S.
    case n' as [ | n''].
    + rewrite -> fold_unfold_evenp1_O.
      compute.
      reflexivity.
    + rewrite -> fold_unfold_evenp1_S.
      rewrite -> fold_unfold_evenp1_S in IHn'.
      rewrite -> negb_involutive.
      
  Restart.

  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  - rewrite -> fold_unfold_evenp1_O.
    rewrite -> fold_unfold_evenp2_O.
    reflexivity.
  - rewrite -> fold_unfold_evenp1_S.
    rewrite -> fold_unfold_evenp1_O.
    rewrite -> fold_unfold_evenp2_S.
    compute.
    reflexivity.
  - rewrite ->2 fold_unfold_evenp1_S.
    rewrite -> negb_involutive.
    rewrite -> fold_unfold_evenp2_SS.
    exact IHn'.
Qed.

(* ***** *)

Lemma twice_succ :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
Proof.
  intro n.
  rewrite -> (plus_n_O (2 * n)).
  rewrite ->2 plus_n_Sm.
  rewrite -> (plus_n_O n) at 2.
  rewrite -> plus_n_Sm.
  rewrite -> Nat.mul_add_distr_l.
  simpl (2 * 1).
  reflexivity.
Qed.

Theorem soundness_and_completeness_of_evenp_using_nat_ind2 :
  forall n : nat,
    evenp2 n = true <-> exists m : nat, n = 2 * m.
Proof.
  intro n.
  induction n as [ | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete]] using nat_ind2.
  - split; intro H.
    + exists 0.
      compute.
      reflexivity.
    + exact fold_unfold_evenp2_O.
  - split; intro H.
    + rewrite -> fold_unfold_evenp2_1 in H.
      discriminate H.
    + destruct H as [m H_m].
      case m as [ | m'].
      * compute in H_m.
        discriminate H_m.
      * rewrite -> Nat.mul_succ_r in H_m.
        rewrite ->2 Nat.add_succ_r in H_m.
        discriminate H_m.   
  - split; intro H.
    + rewrite -> fold_unfold_evenp2_SS in H.
      destruct (IHn'_sound H) as [m H_n'].
      exists (S m).
      rewrite -> H_n'.
      ring.
    + destruct H as [m H_SSn'].
      rewrite -> fold_unfold_evenp2_SS.
      apply IHn'_complete.
      case m as [ | m'].
      * rewrite -> Nat.mul_0_r in H_SSn'.
        discriminate H_SSn'.
      * rewrite <- twice_succ in H_SSn'.
        rewrite -> Nat.mul_comm in H_SSn'.
        injection H_SSn' as H_n'.
        rewrite -> Nat.mul_comm in H_n'.
        exists m'.
        exact H_n'.
Qed.

(* ***** *)

(* For another example, we can prove the mathematical induction principle using nat_ind2: *)

Lemma nat_ind1' :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_PS n.
  induction n as [ | | n' IHn'] using nat_ind2.
  - exact H_P0.
  - Check (H_PS 0 H_P0).
    exact (H_PS 0 H_P0).
  - Check (H_PS (S n') IHn).
    exact (H_PS (S n') IHn).
Qed.

(* We can also generalize nat_ind2 to an induction principle
   with three base cases and three induction hypotheses: *)

Lemma nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n)))) ->
    forall n : nat, P n.
Proof.
  intros P P_0 P_1 P_2 P_SSS.
  assert (all :
           forall m : nat,
             P m /\ P (S m) /\ P (S (S m))).
  { intro m.
    induction m as [ | m' [IHm' [IHSm' IHSSm']]].
    - exact (conj P_0 (conj P_1 P_2)).
    - exact (conj IHSm' (conj IHSSm' (P_SSS m' IHm' IHSm' IHSSm'))). }
  intro n.
  destruct (all n) as [ly _].
  exact ly.

  Restart.

  intros P P_0 P_1 P_2 P_SSS.
  assert (all :
           forall m : nat,
             P m /\ P (S m)).
  { intro m.
    induction m as [ | | m' [IHm' IHSm'] [ISSm' IHSSm']] using nat_ind2.
    - exact (conj P_0 P_1).
    - exact (conj P_1 P_2).
    - exact (conj IHSSm' (P_SSS m' IHm' IHSm' IHSSm')). }
  intro n.
  destruct (all n) as [ly _].
  exact ly.
Qed.

(* ***** *)

Fixpoint ternaryp (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | 1 =>
    false
  | 2 =>
    false
  | S (S (S n')) =>
    ternaryp n'
  end.

Lemma fold_unfold_ternaryp_O :
  ternaryp 0 =
  true.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_ternaryp_1 :
  ternaryp 1 =
  false.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_ternaryp_2 :
  ternaryp 2 =
  false.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma fold_unfold_ternaryp_SSS :
  forall n' : nat,
    ternaryp (S (S (S n'))) =
    ternaryp n'.
Proof.
  fold_unfold_tactic ternaryp.
Qed.

Lemma three_times_succ :
  forall n : nat,
    S (S (S (3 * n))) = 3 * S n.
Proof.
  intro n.
  rewrite -> (plus_n_O (3 * n)).
  rewrite ->3 plus_n_Sm.
  rewrite -> (plus_n_O n) at 2.
  rewrite -> plus_n_Sm.
  rewrite -> Nat.mul_add_distr_l.
  simpl (3 * 1).
  reflexivity.
Qed.
     
Theorem soundness_and_completeness_of_ternaryp_using_nat_ind3 :
  forall n : nat,
    ternaryp n = true <-> exists m : nat, n = 3 * m.
Proof.
  intro n.
  induction n as [ | | | n' [IHn'_sound IHn'_complete] [IHSn'_sound IHSn'_complete] [IHSSn'_sound IHSSn'_complete]] using nat_ind3.
  - split; intro H.
    + exists 0.
      compute; reflexivity.
    + exact fold_unfold_ternaryp_O.
  - split; intro H.
    + rewrite -> fold_unfold_ternaryp_1 in H.
      discriminate H.
    + destruct H as [m H_m].
      case m as [ | [ | m']].
      * compute in H_m.
        discriminate H_m.
      * compute in H_m.
        discriminate H_m.
      * rewrite -> Nat.mul_succ_r in H_m.
        rewrite ->3 Nat.add_succ_r in H_m.
        discriminate H_m.
  - split; intro H.
    + rewrite -> fold_unfold_ternaryp_2 in H.
      discriminate H.
    + destruct H as [m H_m].
      case m as [ | m'].
      * compute in H_m.
        discriminate H_m.
      * rewrite -> Nat.mul_succ_r in H_m.
        rewrite ->3 Nat.add_succ_r in H_m.
        discriminate H_m.
  - split; intro H.
    + rewrite -> fold_unfold_ternaryp_SSS in H.
      destruct (IHn'_sound H) as [m H_n'].
      exists (S m).
      rewrite -> H_n'.
      ring.
    + destruct H as [m H_SSSn'].
      rewrite -> fold_unfold_ternaryp_SSS.
      apply IHn'_complete.
      case m as [ | m'].
      * rewrite -> Nat.mul_0_r in H_SSSn'.
        discriminate H_SSSn'.
      * rewrite <- three_times_succ in H_SSSn'.
        rewrite -> Nat.mul_comm in H_SSSn'.
        injection H_SSSn' as H_n'.
        rewrite -> Nat.mul_comm in H_n'.
        exists m'.
        exact H_n'.
Qed.

(* ********** *)

Property threes_and_fives :
  forall n : nat,
  exists a b : nat,
    8 + n = 3 * a + 5 * b.
Proof.
  intro n.
  induction n as [ | | | n' [a [b IHn']] _ _] using nat_ind3.
  - exists 1, 1.
    compute; reflexivity.
  - exists 3, 0.
    compute; reflexivity.
  - exists 0, 2.
    compute; reflexivity.
  - exists (S a), b.
    rewrite <- three_times_succ.
    rewrite -> (plus_n_O n').
    rewrite ->3 plus_n_Sm.
    rewrite -> (plus_n_O (3 * a)).
    rewrite ->3 plus_n_Sm.
    rewrite -> Nat.add_assoc.
    rewrite <- (Nat.add_assoc (3 * a) 3 (5 * b)).
    rewrite -> (Nat.add_comm 3 (5 * b)).
    rewrite -> Nat.add_assoc.
    destruct (Nat.add_cancel_r (8 + n') (3 * a + 5 * b) 3) as [_ H_tmp].
    exact (H_tmp IHn').
Qed.

(* ********** *)

Lemma nat_ind4 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    P 3 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n))) -> P (S (S (S (S n))))) ->
    forall n : nat, P n.
Proof.
  intros P P_0 P_1 P_2 P_3 P_SSSS.
  assert (all :
           forall m : nat,
             P m /\ P (S m) /\ P (S (S m)) /\ P (S (S (S m)))).
  { intro m.
    induction m as [ | m' [IHm' [IHSm' [IHSSm' IHSSSm']]]].
    - exact (conj P_0 (conj P_1 (conj P_2 P_3))).
    - exact (conj IHSm' (conj IHSSm' (conj IHSSSm' (P_SSSS m' IHm' IHSm' IHSSm' IHSSSm')))). }
  intro n.
  destruct (all n) as [ly _].
  exact ly.

  Restart.

  intros P P_0 P_1 P_2 P_3 P_SSSS.
  assert (all :
           forall m : nat,
             P m /\ P (S m) /\ P (S (S m))).
  { intro m.
    induction m as [ | | m' [IHm' [IHSm' IHSSm']] [_ [_ IHSSSm']]] using nat_ind2.
    - exact (conj P_0 (conj P_1 P_2)).
    - exact (conj P_1 (conj P_2 P_3)).
    - exact (conj IHSSm' (conj IHSSSm' (P_SSSS m' IHm' IHSm' IHSSm' IHSSSm'))). }
  intro n.
  destruct (all n) as [ly _].
  exact ly.

  Restart.

  intros P P_0 P_1 P_2 P_3 P_SSSS.
  assert (all :
           forall m : nat,
             P m /\ P (S m)).
  { intro m.
    induction m as [ | | | m' [IHm' IHSm'] [_ IHSSm'] [_ IHSSSm']] using nat_ind3.
    - exact (conj P_0 P_1).
    - exact (conj P_1 P_2).
    - exact (conj P_2 P_3).
    - exact (conj IHSSSm' (P_SSSS m' IHm' IHSm' IHSSm' IHSSSm')). }
  intro n.
  destruct (all n) as [ly _].
  exact ly.
Qed.
  
Lemma four_times_succ :
  forall n : nat,
    S (S (S (S (4 * n)))) = 4 * S n.
Proof.
  intro n.
  rewrite -> (plus_n_O (4 * n)).
  rewrite ->4 plus_n_Sm.
  rewrite -> (plus_n_O n) at 2.
  rewrite -> plus_n_Sm.
  rewrite -> Nat.mul_add_distr_l.
  simpl (4 * 1).
  reflexivity.
Qed.

Lemma five_times_succ :
  forall n : nat,
    S (S (S (S (S (5 * n))))) = 5 * S n.
Proof.
  intro n.
  rewrite -> (plus_n_O (5 * n)).
  rewrite ->5 plus_n_Sm.
  rewrite -> (plus_n_O n) at 2.
  rewrite -> plus_n_Sm.
  rewrite -> Nat.mul_add_distr_l.
  simpl (5 * 1).
  reflexivity.
Qed.

Property fours_and_fives :
  forall n : nat,
  exists a b : nat,
    12 + n = 4 * a + 5 * b.
Proof.
  intro n.
  induction n as [ | | | | n' [a [b IHn']] _ _ _] using nat_ind4.
  - exists 3, 0.
    compute; reflexivity.
  - exists 2, 1.
    compute; reflexivity.
  - exists 1, 2.
    compute; reflexivity.
  - exists 0, 3.
    compute; reflexivity.
  - exists (S a), b.
    rewrite <- four_times_succ.
    rewrite -> (plus_n_O n').
    rewrite ->4 plus_n_Sm.
    rewrite -> (plus_n_O (4 * a)).
    rewrite ->4 plus_n_Sm.
    rewrite -> Nat.add_assoc.
    rewrite <- (Nat.add_assoc (4 * a) 4 (5 * b)).
    rewrite -> (Nat.add_comm 4 (5 * b)).
    rewrite -> Nat.add_assoc.
    destruct (Nat.add_cancel_r (12 + n') (4 * a + 5 * b) 4) as [_ H_tmp].
    exact (H_tmp IHn').
Qed.

Property fours_and_fives_via_mathematical_induction :
  forall n : nat,
  exists a b : nat,
    12 + n = 4 * a + 5 * b.
Proof.
  intro n.
  induction n as [ | n' [a' [b' IHn']]].
  - exists 3, 0.
    compute.
    reflexivity.
  -  case a' as [ | a''].
    * rewrite -> Nat.mul_0_r in IHn'.
      rewrite -> Nat.add_0_l in IHn'.
      case b' as [ | [ | [ | b'']]].
      + rewrite -> Nat.mul_0_r in IHn'.
        Search (_ + _ = 0).
        rewrite Nat.eq_add_0 in IHn'.
        destruct IHn' as [H_absurd _].
        discriminate H_absurd.
      + rewrite -> Nat.mul_1_r in IHn'.
        assert (5 + 7 = 12) as H_tmp.
        {compute. reflexivity.}
        rewrite <- H_tmp in IHn'.
        Check Nat.add_assoc.
        rewrite <- Nat.add_assoc in IHn'.
        Search (_ = _ + 0).
        rewrite -> plus_n_O in IHn'.
        rewrite Nat.add_cancel_l in IHn'.
        rewrite Nat.eq_add_0 in IHn'.
        destruct IHn' as [H_absurd _].
        discriminate H_absurd.
      + assert (5 * 2 = 10) as H_tmp.
        {compute. reflexivity.}
        rewrite -> H_tmp in IHn'.
        clear H_tmp.
        assert (10 + 2 = 12) as H_tmp.
        {compute. reflexivity.}
        rewrite <- H_tmp in IHn'.
        Check Nat.add_assoc.
        rewrite <- Nat.add_assoc in IHn'.
        Search (_ = _ + 0).
        rewrite -> plus_n_O in IHn'.
        rewrite Nat.add_cancel_l in IHn'.
        rewrite Nat.eq_add_0 in IHn'.
        destruct IHn' as [H_absurd _].
        discriminate H_absurd.      
        + rewrite -> Nat.mul_succ_r in IHn'. 
        rewrite -> Nat.mul_succ_r in IHn'.
        assert (5 + 5 = 10) as H_tmp.
        {compute. reflexivity.}
        rewrite <- Nat.add_assoc in IHn'.
        rewrite H_tmp in IHn'.
        clear H_tmp.
        Check plus_reg_l.
        Search (_ + _ = _ + S _).
        rewrite ->2 Nat.add_succ_comm in IHn'.
        Check plus_reg_l.
        Search (_ + _ = _ + _).
        rewrite (Nat.add_comm (5 * S b'') 10) in IHn'.
        Search (_ + _ = _ + _ -> _ = _).
        apply plus_reg_l in IHn'.
        assert (12 + S n' = 11 + S (S n')) as H_tmp.
        {
          rewrite ->3 Nat.add_succ_r.
          rewrite Nat.add_succ_l.
          reflexivity.
        }
        rewrite H_tmp.
        clear H_tmp.
        rewrite -> IHn'.
        rewrite -> Nat.mul_succ_r.
        Search (_ + _ = _ + _).
        rewrite Nat.add_assoc.
        Check (Nat.add_comm 11 (5 * b'')).
        rewrite -> (Nat.add_comm 11 (5 * b'')).
        assert (11 + 5 = 16) as H_tmp.
        {compute. reflexivity.}
        rewrite <- Nat.add_assoc.
        rewrite H_tmp.
        clear H_tmp.
        rewrite Nat.add_comm.
        exists 4, b''.
        assert (4 * 4 = 16) as H_tmp.
        {compute. reflexivity.}
        rewrite H_tmp.
        reflexivity.
   * rewrite -> Nat.add_succ_r.
     rewrite -> IHn'.
     exists a'', (S b').
     Check Nat.add_succ_r.
     rewrite <- Nat.add_succ_r.
     rewrite <- (Nat.add_1_r (5 * b')).
     Search (_ * S _ = _).
     rewrite -> Nat.mul_succ_r.
     Search (_ + _ = _ + _).
     rewrite -> (Nat.add_comm (5 * b') 1).
     rewrite -> Nat.add_assoc.
     assert (4 + 1 = 5) as H_tmp.
     {compute. reflexivity.}
     Check Nat.add_assoc.
     rewrite <- (Nat.add_assoc (4 * a'') 4 1) .
     rewrite -> H_tmp.
     Check Nat.mul_succ_r.
     rewrite -> Nat.mul_succ_r.
     rewrite -> (Nat.add_comm (5 * b') 5).
     rewrite Nat.add_assoc.
     reflexivity.
Qed.

(* ********** *)

(* end of week-10_induction-principles.v *)
