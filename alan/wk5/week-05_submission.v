(* week-05_mystery-functions.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 12 Sep 2023 *)

(* ********** *)

(* Name: Alan Matthew
   Student number: A0224197B
   Email address: alan.matthew@u.yale-nus.edu.sg
*)

(* Name: Jingyi Hou
   Student number: A0242429E
   Email address: jingyi.hou@u.yale-nus.edu.sg
*)

(* Name: Sean Lim
   Student number: A0230369E 
   Email address: sean.lim@u.yale-nus.edu.sg
*)

(* Name: Zhu Wentao
   Student number: A0224190N
   Email address: zhu.wentao@u.yale-nus.edu.sg
*)

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
  intros f g H_f H_g.
  unfold specification_of_mystery_function_00 in H_f.
  unfold specification_of_mystery_function_00 in H_g.
  intro n.
  induction n as [ | n' IHn'].

  + destruct H_f as [H_f_O _].
    destruct H_g as [H_g_O _].
    rewrite -> H_f_O.
    rewrite -> H_g_O.
    reflexivity.

  + destruct H_f as [H_f_O H_f_S].
    destruct H_g as [H_g_O H_g_S].
    Check (H_f_S n' 0).
    Check (Nat.add_0_l n').
    rewrite <- (Nat.add_0_r n').
    rewrite -> (H_f_S n' 0).
    rewrite -> (H_g_S n' 0).
    Check IHn'.
    rewrite -> IHn'.
    rewrite -> H_f_O.
    rewrite -> H_g_O.
    reflexivity.
Qed.    
  
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
  + reflexivity.
  + intros i j.
    rewrite -> (plus_Sn_m i (S j)).
    rewrite <- (plus_n_Sm i j).
    reflexivity.
Qed.

(* ***** *)

Definition mystery_function_00_alt := fun (n : nat) => n + 1.

Theorem there_is_at_least_one_mystery_function_00_alt :
  specification_of_mystery_function_00 mystery_function_00_alt.
Proof.
  unfold specification_of_mystery_function_00.
  unfold mystery_function_00_alt.
  split.  
  + Search (0 + _ = _).
    rewrite -> (Nat.add_0_l 1).
    reflexivity.
  + intros i j.
    rewrite -> (Nat.add_1_r j).
    rewrite <- (Nat.add_succ_r i j).
    rewrite -> (Nat.add_shuffle0 i 1(S j)).
    reflexivity.
Qed.       
    
(* ********** *)

Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.

(* Prove at most one function that satisfied *)

Definition test_mystery_function_11 (mf : nat -> nat) :=
  (mf 1 =? 1)
  && (mf 0 =? 0)
  && (mf 2 =? 4)
  && (mf 3 =? 9).

(* ********** *)

Theorem there_is_at_most_one_mystery_function_11:
  forall f g : nat -> nat,
    specification_of_mystery_function_11 f ->
    specification_of_mystery_function_11 g ->
    forall x : nat,
      f x = g x.
Proof.
  unfold specification_of_mystery_function_11.
  intros f g [H_f_1 H_f_ij] [H_g_1 H_g_ij].
  intro x.
  induction x as [ | x' IHx'].
  
  - assert (H_f_1_0 := H_f_ij 1 0).
    rewrite -> (Nat.add_0_r 1) in H_f_1_0.
    rewrite -> (Nat.mul_0_r (2 * 1)) in H_f_1_0.
    rewrite -> (Nat.add_0_r (f 1)) in H_f_1_0.
    rewrite -> H_f_1 in H_f_1_0.
(*
    Search (_ + _ = _ + _ -> _ = _).
    Check (plus_reg_l 0 (f 0) 1).
    Check (plus_reg_l 0 (f 0) 1 H_f_1_0).
*)
    rewrite -> (Nat.add_1_l (f 0)) in H_f_1_0.
    injection H_f_1_0 as f_0_is_0.

    assert (H_g_1_0 := H_g_ij 1 0).
    rewrite -> (Nat.add_0_r 1) in H_g_1_0.
    rewrite -> (Nat.mul_0_r (2 * 1)) in H_g_1_0.
    rewrite -> (Nat.add_0_r (g 1)) in H_g_1_0.
    rewrite -> H_g_1 in H_g_1_0.
(*
    Search (_ + _ = _ + _ -> _ = _).
    Check (plus_reg_l 0 (f 0) 1).
    Check (plus_reg_l 0 (f 0) 1 H_f_1_0).
*)
    rewrite -> (Nat.add_1_l (g 0)) in H_g_1_0.
    injection H_g_1_0 as g_0_is_0.
    rewrite <- f_0_is_0.
    rewrite <- g_0_is_0.
    reflexivity.

  - rewrite <- (Nat.add_1_l x').
    rewrite -> (H_f_ij 1 x').
    rewrite -> (H_g_ij 1 x').
    rewrite -> H_f_1.
    rewrite -> H_g_1.
    rewrite -> IHx'.
    reflexivity.
Qed.

(* ********** *)

Definition mystery_function_11 (x : nat) : nat :=
  x * x.

Compute (test_mystery_function_11 mystery_function_11).

Theorem there_is_at_least_one_mystery_function_11:
  specification_of_mystery_function_11 mystery_function_11.
Proof.
  unfold specification_of_mystery_function_11, mystery_function_11.
  split.
  - rewrite -> (Nat.mul_1_r 1).
    reflexivity.
  - intros i j.
    Search (_ * (_ + _ ) = _ + _).
    rewrite -> (Nat.mul_add_distr_l (i + j) i j).
    rewrite -> (Nat.mul_add_distr_r i j i).
    rewrite -> (Nat.mul_add_distr_r i j j).
    rewrite -> (Nat.add_assoc (i * i + j * i) (i * j) (j * j)).
    rewrite -> (Nat.mul_comm j i).
    rewrite <- (Nat.add_assoc (i * i) (i * j) (i * j)).
    rewrite <- (Nat.mul_1_l (i * j)).
    rewrite <- (Nat.mul_add_distr_r 1 1 (i * j)).
    rewrite -> (Nat.add_1_l 1).
    rewrite -> (Nat.mul_assoc 2 i j).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_04 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  forall n' : nat,
    mf (S n') = mf n' + S (2 * n').

(* Prove at most one function that satisfied *)
Proposition there_is_at_most_one_mystery_function_04 :
  forall f g : nat -> nat,
    specification_of_mystery_function_04 f ->
    specification_of_mystery_function_04 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_04.
  intros S_f S_g.
  intro n.
  induction n as [ | n' IHn'].
  + destruct S_f as [S_f_O _].
    destruct S_g as [S_g_O _].
    rewrite -> S_g_O.
    exact (S_f_O).
  + destruct S_f as [_ S_f_S].
    destruct S_g as [_ S_g_S].
    rewrite -> (S_f_S n').
    rewrite -> (S_g_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Tabulation of the Specification
   mf 0 = 0

   mf 1 = mf (S 0)
        = mf 0 + S (2 * 0)
         = 0 + S (0)
         = 1

   mf 2 = mf (S 1)
        = mf 1 + S (2 * 1)
        = 1 + 3
        = 4

   mf 3 = mf (S 2)
        = mf 2 + S (2 * 2)
        = 4 + 5
        = 9

   mf 4 = mf (S 3)
        = mf 3 + S (2 * 3)
        = 9 + 7
        = 16
 *)

(* unit test for the mystery function *) 
Definition test_mystery_function_04 (mf : nat -> nat) :=
  (mf 0 =? 0)
  && (mf 1 =? 1)
  && (mf 2 =? 4)
  && (mf 3 =? 9)
  && (mf 4 =? 16).

(*
  Assuming that the set of natural numbers includes zero, the mystery function maps the natural number n to the  square of the nth natural number i.e f n => n^2. 
*)

Fixpoint nat_square (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => nat_square n' + S (2 * n')
  end.

Lemma fold_unfold_nat_square_O :
    nat_square 0 = 0.
Proof.
  fold_unfold_tactic nat_square.
Qed.

Lemma fold_unfold_nat_square_S :
  forall n' : nat,
    nat_square (S n') = nat_square n' + S (2 * n').     
Proof.
  fold_unfold_tactic nat_square.
Qed.

Definition mystery_function_04 (n : nat) :=
  nat_square n.

Compute (test_mystery_function_04 mystery_function_04).

Proposition there_is_at_least_one_mystery_function_04 :
  specification_of_mystery_function_04 mystery_function_04.
Proof.
  unfold specification_of_mystery_function_04.
  unfold mystery_function_04.
  split.
  + rewrite -> fold_unfold_nat_square_O.
    reflexivity.
  + intro n'.
    rewrite -> (fold_unfold_nat_square_S n').
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_15 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (S x, y * S x).

(* Prove at most one function that satisfied *)

Proposition there_is_at_most_one_mystery_function_15 :
  forall f g : nat -> nat * nat,
    specification_of_mystery_function_15 f ->
    specification_of_mystery_function_15 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_15.
  intros S_f S_g.
  intro n.
  induction n as [ | n' IHn'].
  + destruct S_f as [S_f_O _].
    destruct S_g as [S_g_O _].
    rewrite -> S_g_O.
    exact (S_f_O).
  + destruct S_f as [_ H_f_S].
    destruct S_g as [_ H_g_S].
    rewrite -> (H_g_S n').
    rewrite -> (H_f_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.

Definition eqb_pair_nat (n : nat * nat) (m : nat * nat) : bool :=
  match n, m with
  | (x1, y1), (x2, y2) =>
    if Nat.eqb x1 x2 then
      Nat.eqb y1 y2
    else
      false
  end.

(* unit test for the mystery function *) 
Definition test_mystery_function_15 (mf : nat -> nat * nat) :=
  eqb_pair_nat (mf 0) (0, 1)
  && eqb_pair_nat (mf 1) (1, 1)
  && eqb_pair_nat (mf 2) (2 , 2)
  && eqb_pair_nat (mf 3) (3 , 6).

Fixpoint fac (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => ((S n') * fac n')
  end.

Definition mystery_function_15 (n : nat) : nat * nat := (n, fac n).

Compute (test_mystery_function_15 mystery_function_15).

Lemma fold_unfold_fac_O :
    fac 0 = 1.
Proof.
  fold_unfold_tactic fac.
Qed. 

Lemma fold_unfold_fac_S :
  forall n : nat,
  fac (S n) = (S n * fac n).
Proof.
  fold_unfold_tactic fac.
Qed.

Theorem there_is_at_least_one_mystery_function_15: 
  specification_of_mystery_function_15 mystery_function_15.
Proof.
  unfold specification_of_mystery_function_15, mystery_function_15.
  split.  

  + rewrite -> fold_unfold_fac_O.
    reflexivity.

  + intro n'.
    assert (H_fac_O := fold_unfold_fac_O).
    assert (H_fac_S := fold_unfold_fac_S).
    rewrite -> (H_fac_S n').    
    Search (_ * _ = _ * _).
    rewrite -> (Nat.mul_comm (S n') (fac n')).
    reflexivity.
    Qed.

(* ********** *)

Definition specification_of_mystery_function_16 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (y, x + y).

Proposition there_is_at_most_one_mystery_function_16 :
  forall f g : nat -> nat * nat,
    specification_of_mystery_function_16 f ->
    specification_of_mystery_function_16 g ->
    forall n : nat,
      f n = g n.
Proof.
  unfold specification_of_mystery_function_16.
  intros f g [Hf_O Hf_S] [Hg_O Hg_S].
  intro n.
  
  induction n as [| n' IH_n ].
  + rewrite -> Hg_O.
    exact Hf_O.

  + rewrite -> (Hf_S n').
    rewrite -> (Hg_S n').
    rewrite -> IH_n.
    reflexivity.
Qed.

Definition test_mystery_function_16 (mf : nat -> nat * nat) :=
  eqb_pair_nat (mf 0) (0,1)
  && eqb_pair_nat (mf 1) (1,1)
  && eqb_pair_nat (mf 2) (1,2)
  && eqb_pair_nat (mf 3) (2,3).

Fixpoint mystery_function_16 (n : nat) : (nat * nat) :=
  match n with
  | 0 => (0, 1)
  | S n' =>
      let (x, y) := mystery_function_16 n' in
      (y, x + y)
  end.

Compute (test_mystery_function_16 mystery_function_16).

Lemma fold_unfold_16_O :
  mystery_function_16 0 = (0, 1).
Proof.
  fold_unfold_tactic mystery_function_16.
Qed.

Lemma fold_unfold_16_S :
  forall n : nat,
    mystery_function_16 (S n) =
      let (x, y) := mystery_function_16 n in
      (y, x + y).
Proof.
  fold_unfold_tactic mystery_function_16.
Qed.

Theorem there_is_at_least_one_mystery_function_16 :
  specification_of_mystery_function_16 mystery_function_16.
Proof.
  unfold specification_of_mystery_function_16.
  split.
  + exact fold_unfold_16_O.
  + exact fold_unfold_16_S.
Qed.

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
    rewrite -> (Nat.add_succ_comm p' q).
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

Theorem there_is_at_most_one_mystery_function_18 :
  forall f g : nat -> nat,
    specification_of_mystery_function_18 f ->
    specification_of_mystery_function_18 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_18.
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
      + assert (H_f := S_f_S n').
        assert (H_g := S_g_S n').

  Restart.
           
  intros f g.
  unfold specification_of_mystery_function_18.
  intros [S_f_O [S_f_1 [S_f_2 S_f_S]]] [S_g_O [S_g_1 [S_g_2 S_g_S]]].
  assert (the_current_n_and_also_Sn_and_also_SSn :
                 forall n : nat,
                   f n = g n /\ f (S n) = g (S n) /\ f (S (S n)) = g (S (S n))).
  { intro n.
    induction n as [ | n' [IHn' [IHn'' IHn''']]].
    - split.
    { rewrite -> S_g_O.
        exact S_f_O. }
    split.
    { rewrite -> S_g_1.
      exact S_f_1. }
    rewrite -> S_g_2.
    exact S_f_2.
    - split.
      { exact IHn''. }
      split.
      { exact IHn'''. }
      assert (H_f := S_f_S n').
      assert (H_g := S_g_S n').
      Search (_ + _ = _ ->  _ - _ = _).
      rewrite <- (Nat.add_sub_eq_l (2 * f (S (S n'))) (f n') (f (S (S (S n')))) H_f).
      rewrite <- (Nat.add_sub_eq_l (2 * g (S (S n'))) (g n') (g (S (S (S n')))) H_g).
      rewrite -> IHn'''.
      rewrite -> IHn'.
      reflexivity.
  }
  intro n.
  destruct (the_current_n_and_also_Sn_and_also_SSn n) as [ly _].
  exact ly.
Qed.

Definition unit_test_for_mystery_function_18 (mf : nat -> nat) :=
  let b0 := (mf 0 =? 0) in
  let b1 := (mf 1 =? 1) in
  let b2 := (mf 2 =? 1) in
  let b3 := (mf 3 =? 2) in
  let b4 := (mf 4 =? 3) in
  let b5 := (mf 5 =? 5) in
  b0 && b1 && b2 && b3 && b4 && b5.

Definition mystery_function_18 := fib.

Compute unit_test_for_mystery_function_18 mystery_function_18.

Lemma twice_a_nat :
    forall x : nat,
      x + x = 2 * x.
Proof.
  intro n.
  Search (S _ * _ = _ + _).
  rewrite -> (Nat.mul_succ_l 1 n).
  rewrite -> (Nat.mul_succ_l 0 n).
  rewrite -> (Nat.mul_0_l n).
  rewrite -> (Nat.add_0_l n).
  reflexivity.
Qed.

Theorem there_is_at_least_one_mystery_function_18 :
  specification_of_mystery_function_18 fib.
Proof.
  unfold specification_of_mystery_function_18.
  split.
  { exact fold_unfold_fib_O. }
  split.
  { exact fold_unfold_fib_SO. }
  split.
  { rewrite -> (fold_unfold_fib_SS 0).
    rewrite -> fold_unfold_fib_SO.
    rewrite -> fold_unfold_fib_O.
    exact (Nat.add_0_r 1). }
  intro n.
  induction n as [ | n' IHn'].
  - rewrite -> fold_unfold_fib_O.
    rewrite -> (fold_unfold_fib_SS 1).
    rewrite -> (fold_unfold_fib_SS 0).
    rewrite -> fold_unfold_fib_SO.
    rewrite -> fold_unfold_fib_O.
    rewrite -> (Nat.add_0_l (1 + 0 + 1)).
    rewrite -> (Nat.add_0_r 1).
    exact (twice_a_nat 1).
  - rewrite -> (fold_unfold_fib_SS (S (S n'))).
    rewrite -> (fold_unfold_fib_SS n').
    rewrite -> (Nat.add_comm (fib (S n')) (fib n')).
    Check Nat.add_assoc.
    rewrite -> (Nat.add_assoc (fib (S (S (S n')))) (fib n') (fib (S n'))).
    rewrite -> (Nat.add_comm (fib (S (S (S n')))) (fib n')).
    rewrite -> IHn'.
    rewrite -> (Nat.add_comm (2 * fib (S (S n'))) (fib (S n'))).
    rewrite -> (Nat.add_assoc (fib (S n')) (fib (S n')) (2 * fib (S (S n')))).
    rewrite -> (twice_a_nat (fib (S n'))).
    rewrite -> (fold_unfold_fib_SS (S n')).
    Check Nat.mul_add_distr_l.
    rewrite -> (Nat.mul_add_distr_l 2 (fib (S (S n'))) (fib (S n'))).
    rewrite -> (Nat.add_comm (2 * fib (S n')) (2 * fib (S (S n')))).
    reflexivity.
Qed.    
         
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
(* *)
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

Proposition there_is_at_most_one_mystery_function_19 :
  forall f g : tree -> tree,
    specification_of_mystery_function_19 f ->
    specification_of_mystery_function_19 g ->
    forall t : tree,
      f t = g t.
Proof.
  unfold specification_of_mystery_function_19.
  intros f g [S_f_Leaf [S_f_Node_Leaf S_f_Node_Node]] [S_g_Leaf [S_g_Node_Leaf S_g_Node_Node]].
  intro t.
  induction t as [ v | t1 IHt1 t2 IHt2].
  + rewrite -> (S_g_Leaf v).
    exact (S_f_Leaf v).
  + Check (S_f_Node_Node t1 t2).
Abort.

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

Lemma fold_unfold_mystery_function_19_aux_leaf :
  forall (n : nat) (a : tree),
    mystery_function_19_aux (Leaf n) a = Node (Leaf n) a.
Proof. 
  fold_unfold_tactic mystery_function_19_aux.
Qed.

Lemma fold_unfold_mystery_function_19_aux_node :
  forall (t1 t2 a : tree),
    mystery_function_19_aux (Node t1 t2) a =  mystery_function_19_aux t1 (mystery_function_19_aux t2 a).
Proof.
  fold_unfold_tactic mystery_function_19_aux.
Qed.

Lemma fold_unfold_mystery_function_19_leaf :
  forall (n : nat),
    mystery_function_19 (Leaf n) = (Leaf n).
Proof.
  fold_unfold_tactic mystery_function_19.
Qed.

Lemma fold_unfold_mystery_function_19_node :
  forall (t1 t2 : tree),
    mystery_function_19 (Node t1 t2) = mystery_function_19_aux t1 (mystery_function_19 t2).
Proof.
  fold_unfold_tactic mystery_function_19.
Qed.

Fixpoint eqb_tree_nat (t1 t2 : tree) : bool :=
  match t1 with
    Leaf n1 =>
    match t2 with
      Leaf n2 =>
      Nat.eqb n1 n2
    | Node _ _ =>
      false
    end
  | Node t11 t12 =>
    match t2 with
      Leaf _ =>
      false
    | Node t21 t22 =>
      (eqb_tree_nat t11 t21) && (eqb_tree_nat t12 t22)
    end
  end.

Definition test_mystery_function_19 (mf : tree -> tree) :=
  (eqb_tree_nat (mf (Leaf 0)) (Leaf 0)) &&
  (eqb_tree_nat (mf (Node (Leaf 1)
                       (Node (Leaf 2)
                          (Leaf 3))))
     (Node (Leaf 1)
        (Node (Leaf 2)
           (Leaf 3)))) &&
  (eqb_tree_nat (mf (Node (Leaf 1)
                       (Node
                          (Node (Leaf 2)
                             (Leaf 3))
                          (Leaf 4))))
     (Node (Leaf 1)
        (Node (Leaf 2)
           (Node (Leaf 3)
              (Leaf 4))))) &&
  (eqb_tree_nat (mf (Node
                       (Node
                          (Node (Leaf 1)
                             (Leaf 2))
                          (Node (Leaf 3)
                             (Leaf 4)))
                       (Node (Leaf 5)
                          (Leaf 6))))
     (Node (Leaf 1)
        (Node (Leaf 2)
           (Node (Leaf 3)
              (Node (Leaf 4)
                 (Node (Leaf 5)
                    (Leaf 6))))))) &&
  (eqb_tree_nat (mf (Node (Node (Node (Node (Node (Leaf 1)
                                               (Leaf 2))
                                         (Leaf 3))
                                   (Leaf 4))
                             (Leaf 5))
                       (Leaf 6)))
     (Node (Leaf 1)
        (Node (Leaf 2)
           (Node (Leaf 3)
              (Node (Leaf 4)
                 (Node (Leaf 5)
                    (Leaf 6))))))) &&
  (eqb_tree_nat (mf (Node (Node
                             (Node (Leaf 1)
                                (Leaf 0))
                             (Node (Leaf 1)
                                (Leaf 0)))
                       (Node
                          (Node (Leaf 1)
                             (Leaf 0))
                          (Node (Leaf 1)
                             (Leaf 0)))))
     (Node (Leaf 1)
        (Node (Leaf 0)
           (Node (Leaf 1)
              (Node (Leaf 0)
                 (Node (Leaf 1)
                    (Node (Leaf 0)
                       (Node (Leaf 1)
                          (Leaf 0))))))))) &&
  (eqb_tree_nat (mf (Leaf 1)) (Leaf 1)) &&
  (eqb_tree_nat (mf (Leaf 1)) (Leaf 1)) && 
  (eqb_tree_nat (mf (Node (Leaf 1) (Leaf 2))) (Node (Leaf 1) (Leaf 2))) &&
  (eqb_tree_nat (mf (Leaf 1)) (Leaf 1)) && 
  (eqb_tree_nat (mf (Node (Leaf 1) (Leaf 2))) (Node (Leaf 1) (Leaf 2))) && 
  (eqb_tree_nat (mf (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4)))) 
   (Node (Leaf 1) (Node (Leaf 2) (Node (Leaf 3) (Leaf 4))))).

Compute (test_mystery_function_19 mystery_function_19).

Theorem there_is_at_least_one_mystery_function_19 :
  specification_of_mystery_function_19 mystery_function_19.
Proof.
  unfold specification_of_mystery_function_19.
  split.
  + exact fold_unfold_mystery_function_19_leaf.
  + split.
    ++ intros n t.
       Check (fold_unfold_mystery_function_19_node (Leaf n) t).
       rewrite -> (fold_unfold_mystery_function_19_node (Leaf n) t).
       Check (fold_unfold_mystery_function_19_aux_leaf n (mystery_function_19 t)).
       exact (fold_unfold_mystery_function_19_aux_leaf n (mystery_function_19 t)).
    ++ intros t11 t12 t2.
       Check (fold_unfold_mystery_function_19_node (Node t11 t12) t2).
       rewrite -> (fold_unfold_mystery_function_19_node (Node t11 t12) t2).
       Check (fold_unfold_mystery_function_19_aux_node t11 t12 (mystery_function_19 t2)).
       rewrite -> (fold_unfold_mystery_function_19_aux_node t11 t12 (mystery_function_19 t2)).
       Check (fold_unfold_mystery_function_19_node t11 (Node t12 t2)).
       rewrite -> (fold_unfold_mystery_function_19_node t11 (Node t12 t2)).
       Check (fold_unfold_mystery_function_19_node t12 t2).
       rewrite -> (fold_unfold_mystery_function_19_node t12 t2).
       reflexivity.
Qed.

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

(* Prove at most one function that satisfied *)

Proposition there_is_at_most_one_mystery_function_06 :
  forall f g : nat -> nat,
    specification_of_mystery_function_06 f ->
    specification_of_mystery_function_06 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_06.
  intros [S_f_O S_f_S] [S_g_O S_g_S].
  intro n.
  induction n as [ | n' IHn'].
  + rewrite -> S_f_O.
    rewrite -> S_g_O.
    reflexivity.
  + Check (Nat.add_0_l).
    
    
    (* The goal is:
         f (S n') = g (S n')
       The assumptions that involve S are
         S_f_S : forall i j : nat, f (S (i + j)) = f i * f j
         S_g_S : forall i j : nat, g (S (i + j)) = g i * g j
       How can we use S_f_S and S_g_S on the goal?
       The mismatch is in the argument of the successor.
       Therefore, we need to create an addition in the goal:
         f (S (? + ?)) = g (S (? + ?))
       The question is which expression (? + ?) is equivalent with n'.
       Eureka step:
         (n' + 0) or (0 + n') does the trick
         because 0 is neutral on the left and on the right of addition.
         A library search such as
           Search (_ + 0).
         yields Nat.add_0_r
         and a library search such as
           Search (0 + _).
         yields Nat.add_0_l.
      After this, the rewrites are obvious and we can proceed by routine. 
   *)
   (* In tCPA and English we explain our procedure step by step. We need to articualte rationally our procedure so that we can reconstruct them. This helps us become more mindful and clear. *)
    rewrite <- (Nat.add_0_l n').
    Check (S_f_S 0 n').
    rewrite -> (S_f_S 0 n').
    rewrite -> S_f_O.
    rewrite -> (S_g_S 0 n').
    rewrite -> S_g_O.
    rewrite -> IHn'.
    reflexivity.
    Show Proof.
Qed.
    

(* Curry vs Uncurry *)

Proposition let_06_implies_06'_and_06'_implies_06 :
  (forall f g : nat -> nat,
    specification_of_mystery_function_06 f ->
    specification_of_mystery_function_06 g ->
    forall n : nat,
      f n = g n) <-> (forall f g : nat -> nat,
    specification_of_mystery_function_06 f /\
    specification_of_mystery_function_06 g ->
    forall n : nat,
      f n = g n).
Proof.
  split.
  + intro H_06.
    intros f g [S_f S_g].
    Check (H_06 f g).
    Check (H_06 f g S_f).
    Check (H_06 f g S_f S_g).
    exact (H_06 f g S_f S_g).
  + intro H_06'.
    intros f g S_f S_g.
    Check (H_06' f g).
    Check (H_06' f g (conj S_f S_g)).
    exact (H_06' f g (conj S_f S_g)).
Show Proof.
Qed.

(* Unit testing mystery_function_06 *)
Definition test_mystery_function_06 (mf : nat -> nat) :=
  (mf 0 =? 2)
  && (mf 1 =? 4)
  && (mf 2 =? 8)
  && (mf 3 =? 16).
(*
  This mystery function maps a natural number n into the (n + 1)th power of 2
  i.e 2^(n+1). Assuming that the power function is already defined,
*)
Fixpoint power (x n : nat) : nat :=
  match n with
  | O => 1
  | S n' => x * power x n'
  end.

Lemma fold_unfold_power_O :
  forall x : nat,
    power x 0 = 1.
Proof.
  fold_unfold_tactic power.
Qed.

Lemma fold_unfold_power_S :
  forall x n' : nat,
    power x (S n') = x * power x n'.
Proof.
  fold_unfold_tactic power.
Qed.

Lemma about_power :
  forall x i j : nat,
    power x (i + j) = power x i * power x j.
Proof.
  intros x i j.
  (* use induction on the argument that the function is recursive on *)
  induction i as [ | i' IHi'].
  + rewrite -> (Nat.add_0_l j).
    rewrite -> (fold_unfold_power_O x).
    rewrite -> (Nat.mul_1_l (power x j)).
    reflexivity.
  + Check (plus_Sn_m).
    rewrite -> (plus_Sn_m i' j).
    rewrite -> (fold_unfold_power_S x (i' + j)).
    rewrite -> (fold_unfold_power_S x i').
    rewrite -> IHi'.
    rewrite -> (Nat.mul_assoc x (power x i') (power x j)).
    reflexivity.
Qed.

Definition mystery_function_06 (n : nat) :=
  power 2 (S n).

Compute (test_mystery_function_06 mystery_function_06).

       (*
         1 = S (? + ?)
           = S (0 + 0)
         mf 1 = mf (S (0 + 0))
              = mf 0 * mf 0
              = 2 * 2
              = 4

        2 = S (? + ?)
          = S (1 + 0) (Also check if  S (0 + 1) produces a different result, if so ambiguous and this is the counter example )
        mf 2 = mf (S (? + ?))
             = mf (S (1 + 0))
             = mf 1 * mf 0
             = 4 * 2
             = 8

        mf 2 = mf (S (? + ?))
             = mf (S (0 + 1))
             = mf 0 * mf 1
             = 2 * 4
             = 8

       mf 3 = mf (S (2 + 0))
            = mf 2 * mf 0
            = 8 * 2
            = 16

      mf 3 = mf (S (0 + 2))
           = mf 0 * mf 2
           = 2 * 8
           = 16

     mf 3 = mf (S (1 + 1))
          = mf 1 * mf 1
          = 4 * 4
          = 16
        *)

Fixpoint mystery_function_06' (n : nat) :=
  match n with
  | O => 2
  | S n' => 2 * mystery_function_06' n'
  end.

Compute (test_mystery_function_06 mystery_function_06').

Lemma fold_unfold_mystery_function_06'_O :
  mystery_function_06' 0 = 2.
Proof.
  fold_unfold_tactic mystery_function_06'.
Qed.

Lemma fold_unfold_mystery_function_06'_S :
  forall n' : nat,
    mystery_function_06' (S n') = 2 * mystery_function_06' n'.
Proof.
  fold_unfold_tactic mystery_function_06'.
Qed.

Proposition mystery_function_06_and_mystery_function_06'_are_equivalent :
  forall n : nat,
    mystery_function_06 n = mystery_function_06' n.
Proof.
  intro n.
  unfold mystery_function_06.
  induction n as [ | n' IHn'].
  + rewrite -> (fold_unfold_power_S 2 0).
    rewrite -> (fold_unfold_power_O 2).
    (* do not unfold on recursive definitions ever; makes proving unpractical *)
    (* Leibniz equality *)
    rewrite -> fold_unfold_mystery_function_06'_O.
    Check (Nat.mul_1_r 2).
    exact (Nat.mul_1_r 2).
  + rewrite -> (fold_unfold_power_S 2 (S n')).
    rewrite -> (fold_unfold_mystery_function_06'_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.

Proposition there_is_at_least_one_mystery_function_06 :
  specification_of_mystery_function_06 mystery_function_06.
Proof.
  unfold specification_of_mystery_function_06.
  unfold mystery_function_06.
  split.
  + rewrite -> (fold_unfold_power_S 2 0).
    rewrite -> (fold_unfold_power_O 2).
    exact (Nat.mul_1_r 2).
  + intro i.
    intro j.
    rewrite -> (fold_unfold_power_S 2 (S (i + j))).
    rewrite -> (fold_unfold_power_S 2 (i + j)).
    rewrite -> (fold_unfold_power_S 2 i).
    rewrite -> (fold_unfold_power_S 2 j).
    Check (Nat.mul_assoc).
    rewrite -> (Nat.mul_assoc 2 2 (power 2 (i + j))).
    rewrite <- (Nat.mul_assoc 2 (power 2 i) (2 * power 2 j)).
    rewrite -> (Nat.mul_assoc (power 2 i) 2 (power 2 j)).
    rewrite -> (Nat.mul_comm (power 2 i) 2).
    rewrite <- (Nat.mul_assoc 2 (power 2 i) (power 2 j)).
    rewrite -> (Nat.mul_assoc 2 2 ((power 2 i) * (power 2 j))).
    rewrite -> (about_power 2 i j).
    reflexivity.
Qed.    

Proposition there_is_at_least_one_mystery_function_06' :
  specification_of_mystery_function_06 mystery_function_06'.
Proof.
  Check (there_is_at_most_one_mystery_function_06 mystery_function_06 mystery_function_06').
  Check (there_is_at_most_one_mystery_function_06 mystery_function_06 mystery_function_06' there_is_at_least_one_mystery_function_06).
  (* You can only rewrite Leibniz equalities *)
  unfold specification_of_mystery_function_06.
  split.
  + rewrite <- (mystery_function_06_and_mystery_function_06'_are_equivalent 0).
    unfold mystery_function_06.
    Compute (power 2 1).
    compute.
    reflexivity.
  + intro i.
    induction i as [ | i' IHi'].
    ++ intro j.
       rewrite -> (Nat.add_0_l j).
       rewrite -> (fold_unfold_mystery_function_06'_S j).
       rewrite -> (fold_unfold_mystery_function_06'_O).
       reflexivity.
    ++ intro j.
       rewrite -> (fold_unfold_mystery_function_06'_S (S i' + j)).
       Search (S _ + _ = S _).
       rewrite -> (plus_Sn_m i' j).
       rewrite -> (fold_unfold_mystery_function_06'_S i').
       rewrite -> (IHi' j).
       rewrite -> (Nat.mul_assoc 2 (mystery_function_06' i') (mystery_function_06' j)).
       reflexivity.
Qed.   

(* At most one, means unambiguous. At least one, means no vacuous. When at most one, and at least one, then exactly one. *) 

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

(* folding-left-and-right-over-peano-numbers *) 

(* Exercise 01 *)

(* ********** *)

Definition specification_of_power (power : nat -> nat -> nat) :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall (x : nat)
          (n' : nat),
      power x (S n') = x * power x n').

(* ***** *)

Proposition there_is_at_most_one_function_satisfying_the_specification_of_power :
  forall power1 power2 : nat -> nat -> nat,
    specification_of_power power1 ->
    specification_of_power power2 ->
    forall x n : nat,
      power1 x n = power2 x n.
Proof.
  intros power1 power2.
  unfold specification_of_power.
  intros [S1_O S1_S] [S2_O S2_S] x n.
  induction n as [ | n' IHn'].
  - rewrite -> (S2_O x).
    exact (S1_O x).
  - rewrite -> (S1_S x n').
    rewrite -> (S2_S x n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ***** *)

Definition test_power (candidate : nat -> nat -> nat) : bool :=
  (candidate 2 0 =? 1) &&
  (candidate 10 2 =? 10 * 10) &&
  (candidate 3 2 =? 3 * 3).

(* ***** *)

Fixpoint power_v0_aux (x n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    x * power_v0_aux x n'
  end.

Definition power_v0 (x n : nat) : nat :=
  power_v0_aux x n.

Compute (test_power power_v0).

Lemma fold_unfold_power_v0_aux_O :
  forall x : nat,
    power_v0_aux x 0 = 1.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Lemma fold_unfold_power_v0_aux_S :
  forall x n' : nat,
    power_v0_aux x (S n') = x * power_v0_aux x n'.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Proposition power_v0_satisfies_the_specification_of_power :
  specification_of_power power_v0.
Proof.
  unfold specification_of_power, power_v0.
  split.
  - exact fold_unfold_power_v0_aux_O.
  - exact fold_unfold_power_v0_aux_S.
Qed.

(* ***** *)

Fixpoint power_v1_aux (x n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    power_v1_aux x n' (x * a)
  end.

Definition power_v1 (x n : nat) : nat :=
  power_v1_aux x n 1.

Compute (test_power power_v1).

Lemma fold_unfold_power_v1_aux_O :
  forall x a : nat,
    power_v1_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

Lemma fold_unfold_power_v1_aux_S :
  forall x n' a : nat,
    power_v1_aux x (S n') a =
    power_v1_aux x n' (x * a).
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

(* ***** *)

(* Eureka lemma: *)

Lemma about_power_v0_aux_and_power_v1_aux :
  forall x n a : nat,
    power_v0_aux x n * a = power_v1_aux x n a.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_O x).
    rewrite -> (fold_unfold_power_v1_aux_O x a).
    exact (Nat.mul_1_l a).
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_S x n').
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    Check (IHn' (x * a)).
    rewrite <- (IHn' (x * a)).
    rewrite -> (Nat.mul_comm x (power_v0_aux x n')).
    Check (Nat.mul_assoc).
    symmetry.
    exact (Nat.mul_assoc (power_v0_aux x n') x a).
Qed.

Theorem power_v0_and_power_v1_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  unfold power_v0, power_v1.
  Check (about_power_v0_aux_and_power_v1_aux x n 1).
  rewrite <- (Nat.mul_1_r (power_v0_aux x n)).
  exact (about_power_v0_aux_and_power_v1_aux x n 1).
Qed.

(* ********** *)

Fixpoint nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s (nat_fold_right V z s n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_right V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_right V z s (S n') =
    s (nat_fold_right V z s n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

(* ***** *)

Fixpoint nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_fold_left V (s z) s n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_left V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_left V z s (S n') =
    nat_fold_left V (s z) s n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ********** *)

Definition power_v0_alt (x n : nat) : nat :=
  nat_fold_right nat 1 (fun ih => x * ih) n.

Compute (test_power power_v0_alt).

Proposition power_v0_alt_satisfies_the_specification_of_power :
  specification_of_power power_v0_alt.
Proof.
  unfold specification_of_power, power_v0_alt.
  split.
  - intro x.
    rewrite -> (fold_unfold_nat_fold_right_O nat 1 (fun ih : nat => x * ih)).
    reflexivity.
  - intros x n'.
    rewrite -> (fold_unfold_nat_fold_right_S nat 1 (fun ih : nat => x * ih) n').
    reflexivity.
Qed.

Corollary power_v0_and_power_v0_alt_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v0_alt x n.
Proof.
  intros x n.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_satisfies_the_specification_of_power
           power_v0_alt_satisfies_the_specification_of_power
           x
           n).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_satisfies_the_specification_of_power
           power_v0_alt_satisfies_the_specification_of_power
           x
           n).
Qed.

(* ***** *)

Definition power_v1_alt (x n : nat) : nat :=
  nat_fold_left nat 1 (fun ih => x * ih) n.

Compute (test_power power_v1_alt).

Lemma power_v1_and_power_v1_alt_are_equivalent_aux :
  forall x n a : nat,
    power_v1_aux x n a = nat_fold_left nat a (fun ih : nat => x * ih) n.
Proof.
  intros x n a.
  induction n as [ | n' IHn'].
  + rewrite -> (fold_unfold_power_v1_aux_O x a).
    rewrite -> fold_unfold_nat_fold_left_O.
    reflexivity.
Admitted.
    
Proposition power_v1_and_power_v1_alt_are_equivalent :
  forall x n : nat,
    power_v1 x n = power_v1_alt x n.
Proof.
  intros x n.
  unfold power_v1, power_v1_alt.
  exact (power_v1_and_power_v1_alt_are_equivalent_aux x n 1).
Qed.

(* ********** *)

(* Eureka lemma: *)

Lemma about_nat_fold_left :
  forall (n : nat) (V : Type) (z : V) (s : V -> V),
    nat_fold_left V (s z) s n = s (nat_fold_left V z s n).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + intros V z s.
    rewrite -> (fold_unfold_nat_fold_left_O V (s z) s).
    rewrite -> (fold_unfold_nat_fold_left_O V z s).
    reflexivity.
  + intros V z s.
    Check (fold_unfold_nat_fold_left_S).
    rewrite -> (fold_unfold_nat_fold_left_S V (s z) s n').
    rewrite -> (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (IHn' V (s z) s).
    reflexivity.
Qed.

Lemma about_nat_fold_right_aux :
  forall (n : nat) (V : Type) (z : V) (s : V -> V),
    nat_fold_right V (s z) s n = s (nat_fold_right V z s n).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + intros V z s.
    rewrite -> (fold_unfold_nat_fold_right_O V (s z) s).
    rewrite -> (fold_unfold_nat_fold_right_O V z s).
    reflexivity.
  + intros V z s.
    rewrite -> (fold_unfold_nat_fold_right_S V (s z) s n').
    rewrite -> (fold_unfold_nat_fold_right_S V z s n').
    rewrite -> (IHn' V z s).
    reflexivity.
Qed.

Lemma about_nat_fold_right :
  forall (n : nat) (V : Type) (z : V) (s : V -> V),
    nat_fold_left V (s z) s n = s (nat_fold_right V z s n).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + intros V z s.
    rewrite -> (fold_unfold_nat_fold_left_O V (s z) s).
    rewrite -> (fold_unfold_nat_fold_right_O V z s).
    reflexivity.
  + intros V z s.
    rewrite -> (fold_unfold_nat_fold_left_S V (s z) s n').
    rewrite -> (fold_unfold_nat_fold_right_S V z s n').
    rewrite -> (IHn' V (s z) s).
    rewrite -> (about_nat_fold_right_aux n' V z s).
    reflexivity.
Qed.

(* Exercise 01 *)

Theorem folding_left_and_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V z s n = nat_fold_right V z s n.
Proof.
  intros V z s n.
  induction n as [ | n' IHn'].
  + rewrite -> (fold_unfold_nat_fold_left_O V z s).
    exact (fold_unfold_nat_fold_right_O V z s).
  + Check (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (fold_unfold_nat_fold_right_S V z s n').
    rewrite <- IHn'.
    exact (about_nat_fold_left n' V z s).

  Restart.
    
  (* solving using about_nat_fold_right *)
  intros V z s n.
  induction n as [ | n' IHn'].
  + rewrite -> (fold_unfold_nat_fold_left_O V z s).
    exact (fold_unfold_nat_fold_right_O V z s).
  + rewrite -> (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (fold_unfold_nat_fold_right_S V z s).
    exact (about_nat_fold_right n' V z s).
Qed.    

(* ********** *)

Corollary power_v0_and_power_v1_are_equivalent_alt :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  rewrite -> (power_v0_and_power_v0_alt_are_equivalent x n).
  rewrite -> (power_v1_and_power_v1_alt_are_equivalent x n).
  unfold power_v0_alt, power_v1_alt.
  symmetry.
  exact (folding_left_and_right nat 1 (fun ih : nat => x * ih) n).
Qed.

(* ********** *)

(* Exercise 06 *) 

(* ********** *)

Fixpoint nat_parafold_right (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s n' (nat_parafold_right V z s n')
  end.

Lemma fold_unfold_nat_parafold_right_O :
  forall (V : Type) (z : V) (s : nat -> V -> V),
    nat_parafold_right V z s 0 =
    z.
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

Lemma fold_unfold_nat_parafold_right_S :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n' : nat),
    nat_parafold_right V z s (S n') =
    s n' (nat_parafold_right V z s n').
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

Fixpoint nat_parafold_left (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_parafold_left V (s n' z) s n'
  end.

Lemma fold_unfold_nat_parafold_left_O :
  forall (V : Type) (z : V) (s : nat -> V -> V),
    nat_parafold_left V z s 0 =
    z.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

Lemma fold_unfold_nat_parafold_left_S :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n' : nat),
    nat_parafold_left V z s (S n') =
    nat_parafold_left V (s n' z) s n'.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

(* ***** *)

Check nat_rect.

Definition nat_parafold_right' (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  nat_rect (fun (_ : nat) => V) z s n.

Lemma fold_unfold_nat_parafold_right'_O :
  forall (V : Type) (z : V) (s : nat -> V -> V),
    nat_parafold_right' V z s 0 =
    z.
Proof.
  fold_unfold_tactic nat_parafold_right'.
Qed.

Lemma fold_unfold_nat_parafold_right'_S :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n' : nat),
    nat_parafold_right' V z s (S n') =
    s n' (nat_parafold_right' V z s n').
Proof.
  fold_unfold_tactic nat_parafold_right'.
Qed.

Proposition equivalence_of_nat_parafold_right_and_nat_parafold_right' :
  forall (V : Type) (z : V) (s : nat -> V -> V) (n : nat),
    nat_parafold_right V z s n = nat_parafold_right' V z s n.
Proof.
  intros V z s n.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_nat_parafold_right_O V z s).
    rewrite -> (fold_unfold_nat_parafold_right'_O V z s).
    reflexivity.
  - rewrite -> (fold_unfold_nat_parafold_right_S V z s n').
    rewrite -> (fold_unfold_nat_parafold_right'_S V z s n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ********** *)

(* Exercise 06 *)

Theorem parafolding_left_and_right :
  exists (V : Type) (z : V) (s : nat -> V -> V) (n : nat),
    nat_parafold_left V z s n <> nat_parafold_right V z s n.
Proof.
  exists nat.
  exists 3.
  exists (fun i' ih => i' - ih).
  exists 2.
  Check (fold_unfold_nat_parafold_left_S).
  rewrite -> (fold_unfold_nat_parafold_left_S nat 3 (fun i' ih : nat => i' - ih) 1).
  rewrite -> (fold_unfold_nat_parafold_left_S nat ((fun i' ih => i' - ih)  1 3) (fun i' ih => i' - ih)  0).
  rewrite -> (fold_unfold_nat_parafold_left_O nat ((fun i' ih => i' - ih)  0 ((fun i' ih => i' - ih)  1 3)) (fun i' ih => i' - ih) ).
  Check (fold_unfold_nat_parafold_right_S).
  rewrite -> (fold_unfold_nat_parafold_right_S nat 3 (fun i' ih => i' - ih)  1).
  rewrite -> (fold_unfold_nat_parafold_right_S nat 3 (fun i' ih => i' - ih)  0).
  rewrite -> (fold_unfold_nat_parafold_right_O nat 3 (fun i' ih => i' - ih) ).
  discriminate.
Qed.

(* ********** *)

(* end of week-05_folding-left-and-right-over-peano-numbers.v *)
