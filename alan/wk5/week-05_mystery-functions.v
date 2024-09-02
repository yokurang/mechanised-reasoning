(* week-05_mystery-functions.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 12 Sep 2023 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Bool Arith.

Check Nat.eqb.
Check (fun i j => Nat.eqb i j).
(* so "X =? Y" is syntactic sugar for "Nat.eqb X Y" *)

Check Bool.eqb.
Check (fun b1 b2 => Bool.eqb b1 b2).
(* so eqb stands for Bool.eqb *)

(* ********** *)

Definition specification_of_mystery_function_00 (mf : nat -> nat) :=
  mf 0 = 1 /\ forall i j : nat, mf (S (i + j)) = mf i + mf j.

(* ***** *)

Proposition there_is_at_most_one_mystery_function_00 :
  forall f g : nat -> nat,
    specification_of_mystery_function_00 f ->
    specification_of_mystery_function_00 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.

(* ***** *)

Definition unit_test_for_mystery_function_00a (mf : nat -> nat) :=
  (mf 0 =? 1) (* etc. *).

Definition unit_test_for_mystery_function_00b (mf : nat -> nat) :=
  (mf 0 =? 1) && (mf 1 =? 2) (* etc. *).

Definition unit_test_for_mystery_function_00c (mf : nat -> nat) :=
  (mf 0 =? 1) && (mf 1 =? 2) && (mf 2 =? 3) (* etc. *).

Definition unit_test_for_mystery_function_00d (mf : nat -> nat) :=
  (mf 0 =? 1) && (mf 1 =? 2) && (mf 2 =? 3) && (mf 3 =? 4)
  (* etc. *).

(* ***** *)

Definition mystery_function_00 := S.

Definition less_succinct_mystery_function_00 (n : nat) : nat :=
  S n.

Compute (unit_test_for_mystery_function_00d mystery_function_00).

Theorem there_is_at_least_one_mystery_function_00 :
  specification_of_mystery_function_00 mystery_function_00.
Proof.
  unfold specification_of_mystery_function_00, mystery_function_00.
  split.
  - reflexivity.
  - intros i j.
    rewrite -> (plus_Sn_m i (S j)).
    rewrite <- (plus_n_Sm i j).
    reflexivity.
Qed.

(* ***** *)

Definition mystery_function_00_alt := fun (n : nat) => n + 1.

Theorem there_is_at_least_one_mystery_function_00_alt :
  specification_of_mystery_function_00 mystery_function_00_alt.
Proof.
Abort.

(* ********** *)

Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.

(* ********** *)

Definition specification_of_mystery_function_04 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  forall n' : nat,
    mf (S n') = mf n' + S (2 * n').

(* ********** *)

Definition specification_of_mystery_function_15 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (S x, y * S x).

(* ********** *)

Definition specification_of_mystery_function_16 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (y, x + y).

(* ********** *)

Definition specification_of_mystery_function_17 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall p q : nat,
    mf (S (p + q)) = mf (S p) * mf (S q) + mf p * mf q.

Definition unit_test_for_mystery_function_17 (mf : nat -> nat) :=
  let b0 := (mf 0 =? 0) in
  let b1 := (mf 1 =? 1) in
  let b2 := (mf 2 =? 1) in
  let b3 := (mf 3 =? 2) in
  let b4 := (mf 4 =? 3) in
  let b5 := (mf 5 =? 5) in
  b0 && b1 && b2 && b3 && b4 && b5.

Theorem there_is_at_most_one_mystery_function_17 :
  forall f g : nat -> nat,
    specification_of_mystery_function_17 f ->
    specification_of_mystery_function_17 g ->
    forall n : nat,
      f n = g n.
Proof.  
  intros f g.
  unfold specification_of_mystery_function_17.
  intros [S_f_O [S_f_1 [S_f_2 S_f_S]]] [S_g_O [S_g_1 [S_g_2 S_g_S]]].
  assert (both :
           forall n : nat,
             f n = g n /\ f (S n) = g (S n)).
  {
    intro n.
    induction n as [ | n' [IHn' IHSn']].    
    - split.
      + rewrite -> S_g_O.
        exact S_f_O.
      + rewrite -> S_g_1.
        exact S_f_1.
    - split.
      + exact IHSn'.
      + Check (Nat.add_1_l).
        rewrite <- (Nat.add_1_l n').
        rewrite -> (S_f_S 1 n').
        rewrite -> (S_g_S 1 n').
        rewrite -> S_f_2.
        rewrite -> S_g_2.
        rewrite -> IHSn'.
        rewrite -> S_f_1.
        rewrite -> S_g_1.
        rewrite -> IHn'.
        reflexivity.        
  }
  intro n.
  Check (both n).
  destruct (both n) as [ly _].
  exact ly.
Qed.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      match n' with
      | 0 => 1
      | S n'' => fib n' + fib n''
      end
  end.

Definition mystery_function_17 := fib.

Compute unit_test_for_mystery_function_17 mystery_function_17.

Lemma fold_unfold_fib_O :
  fib 0 = 0.
Proof.
  fold_unfold_tactic fib.
Qed.

Lemma fold_unfold_fib_S :
  forall n' : nat,
    fib (S n') =
      match n' with
      | 0 => 1
      | S n'' => fib n' + fib n''
      end.
Proof.
  fold_unfold_tactic fib.
Qed.

Corollary fold_unfold_fib_SO :
  fib 1 = 1.
Proof.
  rewrite -> (fold_unfold_fib_S 0).
  reflexivity.
Qed.

Corollary fold_unfold_fib_SS :
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.
Proof.
  intro n''.
  rewrite -> (fold_unfold_fib_S (S n'')).
  reflexivity.
Qed.

Theorem there_is_at_least_one_mystery_function_17 :
  specification_of_mystery_function_17 fib.
Proof.
  unfold specification_of_mystery_function_17.
  split.
  { exact fold_unfold_fib_O. }
  split.
  { exact fold_unfold_fib_SO. }
  split.
  { rewrite -> (fold_unfold_fib_SS 0).
    rewrite -> fold_unfold_fib_SO.
    rewrite -> fold_unfold_fib_O.
    exact (Nat.add_0_r 1). }
  intro p.
  induction p as [ | p' IHp'].
  - intro q.
    rewrite -> (Nat.add_0_l q).
    rewrite -> (fold_unfold_fib_S q).
    case q as [ | q'].
    + rewrite -> (Nat.mul_1_r (fib 1)).
      rewrite -> fold_unfold_fib_SO.
      rewrite -> fold_unfold_fib_O.
      rewrite -> (Nat.mul_0_l 0).
      rewrite -> (Nat.add_0_r 1).
      reflexivity.
    + rewrite -> fold_unfold_fib_SO.
      rewrite -> (Nat.mul_1_l (fib (S q') + fib q')).
      rewrite -> fold_unfold_fib_O.
      rewrite -> (Nat.mul_0_l (fib (S q'))).
      rewrite -> (Nat.add_0_r (fib (S q') + fib q')).
      reflexivity.
  - intro q.
    Search (S _ + _ = _ + S _).
    rewrite -> (Plus.plus_Snm_nSm p' q).
    rewrite -> (IHp' (S q)).
    rewrite -> (fold_unfold_fib_SS q).
    rewrite -> (fold_unfold_fib_SS p').
    Search (_ * (_ + _)).
    rewrite -> (Nat.mul_add_distr_l (fib (S p')) (fib (S q)) (fib q)).
    Check (Nat.mul_add_distr_r).
    rewrite -> (Nat.mul_add_distr_r (fib (S p')) (fib p') (fib (S q))).
    Check (Nat.add_assoc).
    rewrite <- (Nat.add_assoc (fib (S p') * fib (S q)) (fib (S p') * fib q) (fib p' * fib (S q))).
    rewrite -> (Nat.add_comm (fib (S p') * fib q) (fib p' * fib (S q))).
    exact (Nat.add_assoc (fib (S p') * fib (S q)) (fib p' * fib (S q)) (fib (S p') * fib q)).
Qed.
  
(* ********** *)

Definition specification_of_mystery_function_18 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall n''' : nat,
    mf n''' + mf (S (S (S n'''))) = 2 * mf (S (S n''')).

(* ********** *)

Definition specification_of_mystery_function_03 (mf : nat -> nat -> nat) :=
  mf 0 0 = 0
  /\
  (forall i j: nat, mf (S i) j = S (mf i j))
  /\
  (forall i j: nat, S (mf i j) = mf i (S j)).

(* ********** *)

Definition specification_of_mystery_function_42 (mf : nat -> nat) :=
  mf 1 = 42
  /\
  forall i j : nat,
    mf (i + j) = mf i + mf j.

(* ********** *)

Definition specification_of_mystery_function_07 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf 0 j = j)
  /\
  (forall i : nat, mf i 0 = i)
  /\
  (forall i j k : nat, mf (i + k) (j + k) = (mf i j) + k).

(* ********** *)

Definition specification_of_mystery_function_08 (mf : nat -> nat -> bool) :=
  (forall j : nat, mf 0 j = true)
  /\
  (forall i : nat, mf (S i) 0 = false)
  /\
  (forall i j : nat, mf (S i) (S j) = mf i j).

(* ********** *)

Definition specification_of_mystery_function_23 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 0
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_24 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_13 (mf : nat -> nat) :=
  (forall q : nat, mf (2 * q) = q)
  /\
  (forall q : nat, mf (S (2 * q)) = q).

(* ********** *)

Definition specification_of_mystery_function_25 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  (forall q : nat,
      mf (2 * (S q)) = S (mf (S q)))
  /\
  mf 1 = 0
  /\
  (forall q : nat,
      mf (S (2 * (S q))) = S (mf (S q))).

(* ****** *)

Definition specification_of_mystery_function_20 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = S (mf i j)).

(* ****** *)

Definition specification_of_mystery_function_21 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = mf i (S j)).

(* ****** *)

Definition specification_of_mystery_function_22 (mf : nat -> nat -> nat) :=
  forall i j : nat,
    mf O j = j
    /\
    mf (S i) j = mf i (S j).

(* ********** *)

(* Binary trees of natural numbers: *)

Inductive tree : Type :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.

Definition specification_of_mystery_function_19 (mf : tree -> tree) :=
  (forall n : nat,
     mf (Leaf n) = Leaf n)
  /\
  (forall (n : nat) (t : tree),
     mf (Node (Leaf n) t) = Node (Leaf n) (mf t))
  /\
  (forall t11 t12 t2 : tree,
     mf (Node (Node t11 t12) t2) = mf (Node t11 (Node t12 t2))).

(* You might not manage to prove
   that at most one function satisfies this specification (why?),
   but consider whether the following function does.
   Assuming it does, what does this function do?
   And what is the issue here?
*)

Fixpoint mystery_function_19_aux (t a : tree) : tree :=
  match t with
  | Leaf n =>
     Node (Leaf n) a
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19_aux t2 a)
  end.

Fixpoint mystery_function_19 (t : tree) : tree :=
  match t with
  | Leaf n =>
     Leaf n
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19 t2)
  end.

(* ********** *)

Definition specification_of_mystery_function_05 (mf : nat -> nat) :=
  mf 0 = 1
  /\
  forall i j : nat,
    mf (S (i + j)) = 2 * mf i * mf j.

Theorem there_is_at_most_one_mystery_function_05 :
  forall f g : nat -> nat,
    specification_of_mystery_function_05 f ->
    specification_of_mystery_function_05 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_05.
  intros [S_f_O S_f_S] [S_g_O S_g_S].
  intro n.
  induction n as [ | n' IHn'].
  - rewrite -> S_f_O.
    rewrite -> S_g_O.
    reflexivity.
  - Check (Nat.add_0_r).
    Check (Nat.add_0_r n').
    rewrite <- (Nat.add_0_r n').
    Check (S_f_S n' 0).
    rewrite -> (S_f_S n' 0).
    rewrite -> (S_g_S n' 0).
    rewrite -> IHn'.
    rewrite -> S_f_O.
    rewrite -> S_g_O.
    reflexivity.
Qed.


Definition unit_test_for_the_mystery_function_05 (mf : nat -> nat) :=
  let b0 := (mf 0 =? 1) in
  let b1 := (mf 1 =? 2) in
  let b2 := (mf 2 =? 4) in
  let b3 := (mf 3 =? 8) in
  b0 && b1 && b2 && b3.

Fixpoint pow2 (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => 2 * pow2 n'
  end.

Definition mystery_function_05 := pow2.

Compute unit_test_for_the_mystery_function_05 mystery_function_05.

Lemma fold_unfold_pow2_O:
  pow2 0 = 1.
Proof.
  fold_unfold_tactic pow2.
Qed.
  
Lemma fold_unfold_pow2_S:
  forall n' : nat,
    pow2 (S n') = 2 * pow2 n'.
Proof.
  fold_unfold_tactic pow2.
Qed.


Lemma about_pow2 :
  forall i j : nat,
   pow2 (i + j) = pow2 i * pow2 j.
Proof.
  intros i j.
  induction i as [ | i' IHi'].
  - Check (Nat.add_0_l j).
    rewrite -> (Nat.add_0_l j).
    rewrite -> fold_unfold_pow2_O.
    Check (Nat.mul_1_l).
    Check (Nat.mul_1_r).
    rewrite -> (Nat.mul_1_l (pow2 j)).
    reflexivity.
  - Check (plus_Sn_m).
    rewrite -> (plus_Sn_m i' j).
    Check (fold_unfold_pow2_S).
    rewrite -> (fold_unfold_pow2_S (i' + j)).
    Check (fold_unfold_pow2_S).
    rewrite -> (fold_unfold_pow2_S i').
    rewrite -> IHi'.
    Check (Nat.mul_assoc).
    Check (Nat.mul_assoc 2 (pow2 i') (pow2 j)).
    exact (Nat.mul_assoc 2 (pow2 i') (pow2 j)).
Qed.

    
Theorem there_is_at_least_one_mystery_function_05 :
  specification_of_mystery_function_05 pow2.
Proof.
  unfold specification_of_mystery_function_05.
  split.
  - exact fold_unfold_pow2_O.
  - intros i j.
    rewrite -> (fold_unfold_pow2_S (i + j)).
    rewrite -> (about_pow2 i j).
    exact (Nat.mul_assoc 2 (pow2 i) (pow2 j)).
Qed.

    

(* ********** *)

Definition specification_of_mystery_function_06 (mf : nat -> nat) :=
  mf 0 = 2
  /\
  forall i j : nat,
    mf (S (i + j)) = mf i * mf j.

(* ********** *)

Definition specification_of_mystery_function_09 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = xorb (mf i) (mf j).

(* ********** *)

Definition specification_of_mystery_function_10 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = Bool.eqb (mf i) (mf j).


Theorem there_is_at_most_one_mystery_function_10 :
  forall f g : nat -> bool,
    specification_of_mystery_function_10 f ->
    specification_of_mystery_function_10 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_10.
  intros [S_f_O S_f_1] [S_g_O S_g_1].
  destruct S_f_1.
  destruct S_g_1.
  intro n.
  induction n as [ | n' IHn'].
  - rewrite -> S_f_O.
    rewrite -> S_g_O.
    reflexivity.
  - Check (Nat.add_1_r).
    rewrite <- (Nat.add_1_r n').
    Check (H0).
    rewrite -> (H0 n' 1).
    Check (H2).
    rewrite -> (H2 n' 1).
    rewrite -> H.
    rewrite -> H1.
    rewrite -> IHn'.
    reflexivity.
Qed.


Lemma two_is_one_plus_one : 2 = 1 + 1.
Proof.
  reflexivity.
Qed.


Lemma two_is_two_plus_zero : 2 = 2 + 0.
Proof.
  reflexivity.
Qed.

Lemma a_contradictory_aspect_of_the_mystery_function_10 :
  forall mf : nat -> bool,
    specification_of_mystery_function_10 mf ->
    mf 2 = true /\ mf 2 = false.
Proof.
  intro mf.
  unfold specification_of_mystery_function_10.
  intros [H_mf_0 H_mf_1].
  split.
  - destruct H_mf_1.
    rewrite -> (two_is_one_plus_one).
    rewrite -> (H0 1 1).
    rewrite -> H.
    reflexivity.
  - destruct H_mf_1.
    rewrite -> (two_is_two_plus_zero).
    rewrite -> (H0 2 0).
    rewrite -> (H_mf_0).
    rewrite -> (two_is_one_plus_one).
    rewrite -> (H0 1 1).
    rewrite -> H.
    reflexivity.
Qed.
    

Theorem there_are_zero_mystery_functions_10 :
  forall mf : nat -> bool,
    specification_of_mystery_function_10 mf ->
    exists n : nat,
      mf n <> mf n.
Proof.
  intros mf S_mf.
  Check (a_contradictory_aspect_of_the_mystery_function_10 mf S_mf).
  destruct (a_contradictory_aspect_of_the_mystery_function_10 mf S_mf) as [H_mf_true H_mf_false].
  exists 2.
  rewrite -> H_mf_true at 1.
  rewrite -> H_mf_false.
  discriminate.
Qed.
  

(* ********** *)

Definition specification_of_mystery_function_12 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i : nat,
    mf (S (S i)) = (S (S i)) * mf (S i).

(* ********** *)

Definition specification_of_mystery_function_14 (mf : nat -> bool) :=
  (forall q : nat, mf (2 * q) = true)
  /\
  (forall q : nat, mf (S (2 * q)) = false).

(* ********** *)

(* Simple examples of specifications: *)

(* ***** *)

Definition specification_of_the_factorial_function (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat, fac (S n') = S n' * fac n'.

(* ***** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

(* ********** *)

(* end of week-05_mystery-functions.v *)
