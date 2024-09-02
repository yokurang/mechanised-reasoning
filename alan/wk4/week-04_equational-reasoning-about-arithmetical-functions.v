(* week-04_equational-reasoning-about-arithmetical-functions.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2023 *)

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

Require Import Arith Bool.

(*
Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).
*)

(* ********** *)

(* Two implementations of the addition function *)

(* ***** *)

(* Unit tests *)

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =? 0)
  &&
  (candidate 0 1 =? 1)
  &&
  (candidate 1 0 =? 1)
  &&
  (candidate 1 1 =? 2)
  &&
  (candidate 1 2 =? 3)
  &&
  (candidate 2 1 =? 3)
  &&
  (candidate 2 2 =? 4)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the addition function *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
  | O =>
    j
  | S i' =>
    S (add_v1 i' j)
  end.

Compute (test_add add_v1).

Lemma fold_unfold_add_v1_O :
  forall j : nat,
    add_v1 O j =
    j.
Proof.
  fold_unfold_tactic add_v1.
Qed.

Lemma fold_unfold_add_v1_S :
  forall i' j : nat,
    add_v1 (S i') j =
    S (add_v1 i' j).
Proof.
  fold_unfold_tactic add_v1.
Qed.

(* ***** *)

(* Tail-recursive implementation of the addition function *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Lemma fold_unfold_add_v2_O :
  forall j : nat,
    add_v2 O j =
    j.
Proof.
  fold_unfold_tactic add_v2.
Qed.

Lemma fold_unfold_add_v2_S :
  forall i' j : nat,
    add_v2 (S i') j =
    add_v2 i' (S j).
Proof.
  fold_unfold_tactic add_v2.
Qed.

(* ********** *)

(* Equivalence of add_v1 and add_v2 *)

(* ***** *)

(* The master lemma: *)

Lemma about_add_v2 :
  forall i j : nat,
    add_v2 i (S j) = S (add_v2 i j).
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v2_O (S j)).

  - intro j.
    rewrite -> (fold_unfold_add_v2_S i' (S j)).
    rewrite -> (fold_unfold_add_v2_S i' j).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

(* ***** *)

(* The main theorem: *)

Theorem equivalence_of_add_v1_and_add_v2 :
  forall i j : nat,
    add_v1 i j = add_v2 i j.
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v1_O j).

  - intro j.
    rewrite -> (fold_unfold_add_v1_S i' j).
    rewrite -> (fold_unfold_add_v2_S i' j).
    rewrite -> (IHi' j).
    symmetry.
    exact (about_add_v2 i' j).
Qed.

(* ********** *)

(* Neutral (identity) element for addition *)

(* ***** *)

Property O_is_left_neutral_wrt_add_v1 :
  forall y : nat,
    add_v1 0 y = y.
Proof.
  exact fold_unfold_add_v1_O.
Qed.


(* ***** *)

Property O_is_left_neutral_wrt_add_v2 :
  forall y : nat,
    add_v2 0 y = y.
Proof.
  exact fold_unfold_add_v2_O.
Qed.

(* ***** *)

Property O_is_right_neutral_wrt_add_v1 :
  forall x : nat,
    add_v1 x 0 = x.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - rewrite -> (fold_unfold_add_v1_O 0).
    reflexivity.
  - Check (fold_unfold_add_v1_S x' 0).
    rewrite -> (fold_unfold_add_v1_S x' 0).
    rewrite -> IHx'.
    reflexivity.
Qed.

Property O_is_right_neutral_wrt_add_v2 :
  forall x : nat,
    add_v2 x 0 = x.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - Check (fold_unfold_add_v2_O 0).
    rewrite -> (fold_unfold_add_v2_O 0).
    reflexivity.
  - Check (fold_unfold_add_v2_S x' 0).
    rewrite -> (fold_unfold_add_v2_S x' 0).
    Check about_add_v2.
    Check (about_add_v2 x').
    Check (about_add_v2 x' 0).
    rewrite -> (about_add_v2 x' 0).
    rewrite -> IHx'.
    reflexivity.
Qed.

(* ********** *)

(* Associativity of addition *)

(* ***** *)

Property add_v1_is_associative :
  forall x y z : nat,
    add_v1 x (add_v1 y z) = add_v1 (add_v1 x y) z.
Proof.
  intros x y z.
  induction x as [ | x' IHx'].
  - Check (O_is_left_neutral_wrt_add_v1 y).
    rewrite -> (O_is_left_neutral_wrt_add_v1 y).
    Check (O_is_left_neutral_wrt_add_v1 (add_v1 y z)).
    rewrite -> (O_is_left_neutral_wrt_add_v1 (add_v1 y z)).
    reflexivity.

  Restart.
  intros x y z.
  induction x as [ | x' IHx'].
  - rewrite -> (fold_unfold_add_v1_O (add_v1 y z)).
    rewrite -> (fold_unfold_add_v1_O y).
    reflexivity.
  - rewrite -> (fold_unfold_add_v1_S x' (add_v1 y z)).
    rewrite -> (fold_unfold_add_v1_S x' y).
    rewrite -> (fold_unfold_add_v1_S (add_v1 x' y) z).
    rewrite -> IHx'.
    reflexivity.
Qed.
    
(* ***** *)

Property add_v2_is_associative :
  forall x y z : nat,
    add_v2 x (add_v2 y z) = add_v2 (add_v2 x y) z.
Proof.
  intros x y z.
  induction x as [ | x' IHx'].
  - rewrite -> (fold_unfold_add_v2_O (add_v2 y z)).
    rewrite -> (fold_unfold_add_v2_O y).
    reflexivity.
  - rewrite -> (fold_unfold_add_v2_S x' (add_v2 y z)).
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (about_add_v2 x' (add_v2 y z)).
    rewrite -> (about_add_v2 x' y).
    rewrite -> (fold_unfold_add_v2_S (add_v2 x' y) z).
    rewrite -> (about_add_v2 (add_v2 x' y) z).
    rewrite -> IHx'.
    reflexivity.
Qed.

(* ********** *)

(* Commutativity of addition *)

(* ***** *)

Property add_v1_is_commutative :
  forall x y : nat,
    add_v1 x y = add_v1 y x.
Proof.
  intro x.
  induction x as [ | x' IHx']. 
  - intro y.
    rewrite -> (O_is_left_neutral_wrt_add_v1 y).
    rewrite -> (O_is_right_neutral_wrt_add_v1 y).
    reflexivity.
  - intro y.
    rewrite -> (fold_unfold_add_v1_S x' y).
    rewrite -> (IHx' y).
    rewrite -> (equivalence_of_add_v1_and_add_v2 y x').
    rewrite -> (equivalence_of_add_v1_and_add_v2 y (S x')).
    symmetry.
    exact (about_add_v2 y x').
Qed.

(* ***** *)

Property add_v2_is_commutative :
  forall x y : nat,
    add_v2 x y = add_v2 y x.
Proof.
  intros x y.
  rewrite <- (equivalence_of_add_v1_and_add_v2 x y).
  rewrite <- (equivalence_of_add_v1_and_add_v2 y x).
  exact (add_v1_is_commutative x y).

Restart.

  intro x.
  induction x as [ | x' IHx'].
  - intro y.
    rewrite -> (O_is_left_neutral_wrt_add_v2 y).
    rewrite -> (O_is_right_neutral_wrt_add_v2 y).
    reflexivity.
  - intro y.
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (IHx' (S y)).
    rewrite -> (fold_unfold_add_v2_S y x').
    reflexivity.
Qed.

(* ********** *)

(* Four implementations of the multiplication function *)

(* ***** *)

(* Unit tests *)

Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =? 0)
  &&
  (candidate 0 1 =? 0)
  &&
  (candidate 1 0 =? 0)
  &&
  (candidate 1 1 =? 1)
  &&
  (candidate 1 2 =? 2)
  &&
  (candidate 2 1 =? 2)
  &&
  (candidate 2 2 =? 4)
  &&
  (candidate 2 3 =? 6)
  &&
  (candidate 3 2 =? 6)
  &&
  (candidate 6 4 =? 24)
  &&
  (candidate 4 6 =? 24)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v11 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v1 (mul_v11 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v11_O :
  forall y : nat,
    mul_v11 O y =
    O.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

Lemma fold_unfold_mul_v11_S :
  forall x' y : nat,
    mul_v11 (S x') y =
    add_v1 (mul_v11 x' y) y.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v12 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v2 (mul_v12 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v12_O :
  forall y : nat,
    mul_v12 O y =
    O.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

Lemma fold_unfold_mul_v12_S :
  forall x' y : nat,
    mul_v12 (S x') y =
    add_v2 (mul_v12 x' y) y.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

(* ***** *)

(* Tail-recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v21_aux (x y a : nat) : nat :=
  match x with
  | O =>
    a
  | S x' =>
    mul_v21_aux x' y (add_v1 y a)
  end.

Definition mul_v21 (x y : nat) : nat :=
  mul_v21_aux x y 0.

Compute (test_mul mul_v21).

Lemma fold_unfold_mul_v21_aux_O :
  forall y a : nat,
    mul_v21_aux O y a =
    a.
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

Lemma fold_unfold_mul_v21_aux_S :
  forall x' y a : nat,
    mul_v21_aux (S x') y a =
    mul_v21_aux x' y (add_v1 y a).
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

(* Lemma fold_unfold_mul_v21_O : *)
(*   forall y : nat, *)
(*     mul_v21 O y = *)
(*     O. *)
(* Proof. *)
(*   fold_unfold_tactic mul_v21. *)
(* Qed. *)

(* ***** *)

(* Tail-recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v22_aux (x y a : nat) : nat :=
  match x with
  | O =>
    a
  | S x' =>
    mul_v22_aux x' y (add_v2 y a)
  end.

Definition mul_v22 (x y : nat) : nat :=
  mul_v22_aux x y 0.

Compute (test_mul mul_v22).

Lemma fold_unfold_mul_v22_aux_O :
  forall y a : nat,
    mul_v22_aux O y a =
    a.
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

Lemma fold_unfold_mul_v22_aux_S :
  forall x' y a : nat,
    mul_v22_aux (S x') y a =
    mul_v22_aux x' y (add_v2 y a).
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

(* ********** *)

(* Equivalence of mul_v11, mul_v12, mul_v21, and mul_v22 *)

(* ***** *)

Theorem equivalence_of_mul_v11_and_mul_v12 :
  forall i j : nat,
    mul_v11 i j = mul_v12 i j.
Proof.
  intros i j.
  induction i as [ | i' IHi'].
  - rewrite -> (fold_unfold_mul_v11_O j).
    rewrite -> (fold_unfold_mul_v12_O j).
    reflexivity.
  - rewrite -> (fold_unfold_mul_v11_S i' j).
    rewrite -> (fold_unfold_mul_v12_S i' j).
    rewrite -> IHi'.
    Check (equivalence_of_add_v1_and_add_v2).
    Check (equivalence_of_add_v1_and_add_v2 (mul_v12 i' j) j).
    exact (equivalence_of_add_v1_and_add_v2 (mul_v12 i' j) j).
Qed.

(* ***** *)

(* ... *)

(* ***** *)

(* ... *)

(* ***** *)

Lemma equivalence_of_mul_v21_aux_and_mul_v22_aux:
  forall i j a : nat,
    mul_v21_aux i j a = mul_v22_aux i j a.
Proof.
  intro i.
  induction i as [ | i' IHi'].
  - intros j a.
    rewrite -> (fold_unfold_mul_v21_aux_O j a).
    rewrite -> (fold_unfold_mul_v22_aux_O j a).
    reflexivity.
  - intros j a.
    rewrite -> (fold_unfold_mul_v21_aux_S i' j a).
    rewrite -> (fold_unfold_mul_v22_aux_S i' j a).
    Check (IHi' j (add_v1 j a)).
    rewrite -> (IHi' j (add_v1 j a)).
    Check (equivalence_of_add_v1_and_add_v2 j a).
    rewrite -> (equivalence_of_add_v1_and_add_v2 j a).
    reflexivity.
Qed.
    
Theorem equivalence_of_mul_v21_and_mul_v22 :
  forall i j : nat,
    mul_v21 i j = mul_v22 i j.
Proof.
  intros i j.
  unfold mul_v21.
  unfold mul_v22.
  Check (equivalence_of_mul_v21_aux_and_mul_v22_aux i j 0).
  exact (equivalence_of_mul_v21_aux_and_mul_v22_aux i j 0).
Qed.

(* ********** *)

(* 0 is left absorbing with respect to multiplication *)

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v11 :
  forall y : nat,
    mul_v11 0 y = 0.
Proof.
  exact fold_unfold_mul_v11_O.
Qed.

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v12 :
  forall y : nat,
    mul_v12 0 y = 0.
Proof.
  exact fold_unfold_mul_v12_O.
Qed.

(* ***** *)

Lemma fold_unfold_mul_v21_O :
  forall y : nat,
    mul_v21 O y =
    O.
Proof.
  fold_unfold_tactic mul_v21.
Qed.

Property O_is_left_absorbing_wrt_mul_v21 :
  forall y : nat,
    mul_v21 0 y = 0.
Proof.
  exact fold_unfold_mul_v21_O.
Qed.

(* ***** *)

Lemma fold_unfold_mul_v22_O :
  forall y : nat,
    mul_v22 O y =
    O.
Proof.
  fold_unfold_tactic mul_v22.
Qed.

Check fold_unfold_mul_v21_O.

Property O_is_left_absorbing_wrt_mul_v22 :
  forall y : nat,
    mul_v22 0 y = 0.
Proof.
  exact fold_unfold_mul_v22_O.
Qed.

(* ********** *)

(* 1 is left neutral with respect to multiplication *)

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v11 :
  forall y : nat,
    mul_v11 1 y = y.
Proof.
  intro y.
  rewrite -> (fold_unfold_mul_v11_S 0 y).
  rewrite -> (fold_unfold_mul_v11_O y).
  rewrite -> (fold_unfold_add_v1_O y).
  reflexivity.
Qed.

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v12 :
  forall y : nat,
    mul_v12 1 y = y.
Proof.
  intro y.
  Check (fold_unfold_mul_v12_S 0 y).
  rewrite -> (fold_unfold_mul_v12_S 0 y).
  rewrite -> (fold_unfold_mul_v12_O y).
  rewrite -> (fold_unfold_add_v2_O y).
  reflexivity.
Qed.

(* ***** *)


Property SO_is_left_neutral_wrt_mul_v21 :
  forall y : nat,
    mul_v21 1 y = y.
Proof.
  intro y.
  unfold mul_v21.
  induction y as [ | y' IHy'].
  - Check (fold_unfold_mul_v21_aux_S 0 0 0). 
    rewrite -> (fold_unfold_mul_v21_aux_S 0 0 0).
    rewrite -> (fold_unfold_add_v1_O).
    rewrite -> (fold_unfold_mul_v21_aux_O).
    reflexivity.
  - Check (fold_unfold_mul_v21_aux_S 0 (S y') 0).
    rewrite -> (fold_unfold_mul_v21_aux_S 0 (S y') 0).
    Check (fold_unfold_add_v1_S y' 0).
    rewrite ->(fold_unfold_add_v1_S y' 0).
    rewrite -> (add_v1_is_commutative).
    rewrite -> (fold_unfold_add_v1_O y').
    rewrite -> (fold_unfold_mul_v21_aux_O (S y') (S y')).
    reflexivity.
Qed.

(* ***** *)


Property SO_is_left_neutral_wrt_mul_v22 :
  forall y : nat,
    mul_v22 1 y = y.
Proof.
  intro y.
  unfold mul_v22.
  induction y as [ | y' IHy'].
  - Check (fold_unfold_mul_v22_aux_S 0 0 0). 
    rewrite -> (fold_unfold_mul_v22_aux_S 0 0 0).
    rewrite -> (fold_unfold_add_v2_O).
    rewrite -> (fold_unfold_mul_v22_aux_O).
    reflexivity.
  - Check (fold_unfold_mul_v22_aux_S 0 (S y') 0).
    rewrite -> (fold_unfold_mul_v22_aux_S 0 (S y') 0).
    Check (fold_unfold_add_v2_S y' 0).
    rewrite -> (add_v2_is_commutative).
    rewrite -> (fold_unfold_add_v2_O (S y')).
    rewrite -> (fold_unfold_mul_v22_aux_O (S y') (S y')).
    reflexivity.
Qed.


(* ********** *)

(* 0 is right absorbing with respect to multiplication *)

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 0 = 0.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - rewrite -> (fold_unfold_mul_v11_O 0).
    reflexivity.
  - rewrite -> (fold_unfold_mul_v11_S x' 0).
    rewrite -> IHx'.
    rewrite -> (fold_unfold_add_v1_O 0).
    reflexivity.
Qed.

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 0 = 0.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - rewrite -> (fold_unfold_mul_v12_O 0).
    reflexivity.
  - rewrite -> (fold_unfold_mul_v12_S x' 0).
    rewrite -> IHx'.
    rewrite -> (fold_unfold_add_v2_O 0).
    reflexivity.
Qed.

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 0 = 0.
Proof.
  intro x.
  unfold mul_v21.
  induction x as [ | x' IHx'].
  - rewrite -> (fold_unfold_mul_v21_aux_O 0).
    reflexivity.
  - rewrite -> (fold_unfold_mul_v21_aux_S x' 0 0).
    rewrite -> (fold_unfold_add_v1_O 0).
    exact IHx'.
Qed.

(* ***** *)


Property O_is_right_absorbing_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 0 = 0.
Proof.
  intro x.
  unfold mul_v22.
  induction x as [ | x' IHx'].
  - rewrite -> (fold_unfold_mul_v22_aux_O 0).
    reflexivity.
  - rewrite -> (fold_unfold_mul_v22_aux_S x' 0 0).
    rewrite -> (fold_unfold_add_v2_O 0).
    exact IHx'. 
Qed.

(* ********** *)

(* 1 is right neutral with respect to multiplication *)

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 1 = x.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - rewrite -> fold_unfold_mul_v11_O.
    reflexivity.
  - rewrite -> (fold_unfold_mul_v11_S x' 1).
    rewrite -> IHx'.
    rewrite -> (add_v1_is_commutative).
    rewrite -> (fold_unfold_add_v1_S 0 x').
    rewrite -> (fold_unfold_add_v1_O x').
    reflexivity.
Qed.

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 1 = x.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - rewrite -> fold_unfold_mul_v12_O.
    reflexivity.
  - rewrite -> (fold_unfold_mul_v12_S x' 1).
    rewrite -> IHx'.
    rewrite -> (add_v2_is_commutative).  
    rewrite -> (fold_unfold_add_v2_S 0 x').
    Check (fold_unfold_add_v2_O (S x')).
    rewrite -> (fold_unfold_add_v2_O (S x')).
    reflexivity.
Qed.

(* ***** *)


Lemma SO_is_right_neutral_wrt_mul_v21_aux:
  forall x y a : nat,
    add_v1 (mul_v21_aux x y 0) a = mul_v21_aux x y a.
Proof.
  intro x.
  induction x as [ | x' IHx'].

  + intros y a.
    rewrite -> (fold_unfold_mul_v21_aux_O y 0).
    rewrite -> (fold_unfold_mul_v21_aux_O y a).
    rewrite -> (fold_unfold_add_v1_O a).
    reflexivity.

  + intros y a.
    rewrite -> (fold_unfold_mul_v21_aux_S x' y 0).
    rewrite -> (fold_unfold_mul_v21_aux_S x' y a).
    Check (O_is_right_neutral_wrt_add_v1 y).
    rewrite -> (O_is_right_neutral_wrt_add_v1 y).
    rewrite <- (IHx' y (add_v1 y a)).
    rewrite <- (IHx' y y).
    Check add_v1_is_associative.
    rewrite <- (add_v1_is_associative (mul_v21_aux x' y 0) y a).
    reflexivity.
Qed.

Property SO_is_right_neutral_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 1 = x.
Proof.
unfold mul_v21.
  intro x.
  induction x as [ | x' IHx'].

  + rewrite -> (fold_unfold_mul_v21_aux_O 1 0).
    reflexivity.

  + rewrite -> (fold_unfold_mul_v21_aux_S x' 1 0).
    rewrite -> (fold_unfold_add_v1_S 0 0).
    rewrite -> (fold_unfold_add_v1_O 0).
    Check (SO_is_right_neutral_wrt_mul_v21_aux x' 1 1).
    rewrite <- (SO_is_right_neutral_wrt_mul_v21_aux x' 1 1).
    rewrite -> IHx'.
    rewrite -> (add_v1_is_commutative x' 1).
    rewrite -> (fold_unfold_add_v1_S 0 x').
    rewrite -> (fold_unfold_add_v1_O x').
    reflexivity.
Qed.


(* ***** *)

Lemma SO_is_right_neutral_wrt_mul_v22_aux:
  forall x y a : nat,
    add_v2 (mul_v22_aux x y 0) a = mul_v22_aux x y a.
Proof.
  intro x.
  induction x as [ | x' IHx'].

  + intros y a.
    rewrite -> (fold_unfold_mul_v22_aux_O y 0).
    rewrite -> (fold_unfold_mul_v22_aux_O y a).
    rewrite -> (fold_unfold_add_v2_O a).
    reflexivity.

  + intros y a.
    rewrite -> (fold_unfold_mul_v22_aux_S x' y 0).
    rewrite -> (fold_unfold_mul_v22_aux_S x' y a).
    Check (O_is_right_neutral_wrt_add_v2 y).
    rewrite -> (O_is_right_neutral_wrt_add_v2 y).
    rewrite <- (IHx' y (add_v2 y a)).
    rewrite <- (IHx' y y).
    Check add_v2_is_associative.
    rewrite <- (add_v2_is_associative (mul_v22_aux x' y 0) y a).
    reflexivity.
Qed.

Property SO_is_right_neutral_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 1 = x.
Proof.
  unfold mul_v22.
  intro x.
  induction x as [ | x' IHx'].

  + rewrite -> (fold_unfold_mul_v22_aux_O 1 0).
    reflexivity.

  + rewrite -> (fold_unfold_mul_v22_aux_S x' 1 0).
    rewrite -> (fold_unfold_add_v2_S 0 0).
    rewrite -> (fold_unfold_add_v2_O 1).
    Check (SO_is_right_neutral_wrt_mul_v22_aux x' 1 1).
    rewrite <- (SO_is_right_neutral_wrt_mul_v22_aux x' 1 1).
    rewrite -> IHx'.
    rewrite -> (add_v2_is_commutative x' 1).
    rewrite -> (fold_unfold_add_v2_S 0 x').
    rewrite -> (fold_unfold_add_v2_O (S x')).
    reflexivity.
Qed.

(* ********** *)

(* Multiplication is right-distributive over addition *)

Property mul_v11_is_right_distributive_over_add_v1 :
  forall x y z : nat,
    mul_v11 (add_v1 x y) z = add_v1 (mul_v11 x z) (mul_v11 y z).
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - intros y z.
    rewrite -> (fold_unfold_add_v1_O y).
    rewrite -> (fold_unfold_mul_v11_O z).
    rewrite -> (fold_unfold_add_v1_O (mul_v11 y z)).
    reflexivity.
  - intros y z.
    rewrite -> (fold_unfold_add_v1_S x' y).
    rewrite -> (fold_unfold_mul_v11_S x' z).
    rewrite -> (fold_unfold_mul_v11_S (add_v1 x' y) z).
    Check (IHx' y z).
    rewrite -> (IHx' y z).
    Check (add_v1_is_associative).
    Check (add_v1_is_associative (mul_v11 x' z) (mul_v11 y z) z).
    rewrite <- (add_v1_is_associative (mul_v11 x' z) (mul_v11 y z) z).
    Check (add_v1_is_associative).
    Check (add_v1_is_associative (mul_v11 x' z) z (mul_v11 y z)).
    rewrite <- (add_v1_is_associative (mul_v11 x' z) z (mul_v11 y z)).
    Check (add_v1_is_commutative).
    Check (add_v1_is_commutative (mul_v11 y z) z).
    rewrite -> (add_v1_is_commutative (mul_v11 y z) z).
    reflexivity.
Qed.
    
    
(* ***** *)

Property mul_v12_is_right_distributive_over_add_v2:
  forall x y z : nat,
    mul_v12 (add_v2 x y) z = add_v2 (mul_v12 x z) (mul_v12 y z).
Proof.
  intro x.
  induction x as [ | x' IHx'].

  - intros y z.
    rewrite -> (fold_unfold_add_v2_O y).
    rewrite -> (fold_unfold_mul_v12_O z).
    rewrite -> (fold_unfold_add_v2_O (mul_v12 y z)).
    reflexivity.

  - intros y z.
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (fold_unfold_mul_v12_S x' z).
    rewrite -> (IHx' (S y) z).
    rewrite -> (fold_unfold_mul_v12_S y z).
    Check (add_v2_is_associative (mul_v12 x' z) z (mul_v12 y z)).
    rewrite <- (add_v2_is_associative  (mul_v12 x' z) z (mul_v12 y z)).
    rewrite -> (add_v2_is_commutative z (mul_v12 y z)).
    rewrite -> (add_v2_is_associative (mul_v12 x' z) (mul_v12 y z) z).
    reflexivity.
Qed.

(* ***** *)

Property mul_v21_is_right_distributive_over_add_v1:
  forall x y z : nat,
    mul_v21 (add_v1 x y) z = add_v1 (mul_v21 x z) (mul_v21 y z).
Proof.
  unfold mul_v21.
  intro x.
  induction x as [ | x' IHx'].

  - intros y z.
    rewrite -> (fold_unfold_add_v1_O y).
    rewrite -> (fold_unfold_mul_v21_aux_O z).
    rewrite -> (fold_unfold_add_v1_O (mul_v21_aux y z 0)).
    reflexivity.

  - intros y z.
    rewrite -> (fold_unfold_add_v1_S x' y).
    rewrite -> (fold_unfold_mul_v21_aux_S (add_v1 x' y) z).
    rewrite -> (fold_unfold_mul_v21_aux_S x' z).
    rewrite -> (add_v1_is_commutative z 0).
    rewrite -> (fold_unfold_add_v1_O z).
    Check (SO_is_right_neutral_wrt_mul_v21_aux (add_v1 x' y) z z).
    rewrite <- (SO_is_right_neutral_wrt_mul_v21_aux (add_v1 x' y) z z).
    rewrite <- (SO_is_right_neutral_wrt_mul_v21_aux x' z z).
    rewrite -> (IHx' y z).
    Check (add_v1_is_associative (mul_v21_aux x' z 0) z (mul_v21_aux y z 0)).
    rewrite <- (add_v1_is_associative  (mul_v21_aux x' z 0) z (mul_v21_aux y z 0)).
    rewrite -> (add_v1_is_commutative z (mul_v21_aux y z 0)).
    rewrite -> (add_v1_is_associative (mul_v21_aux x' z 0) (mul_v21_aux y z 0) z).
    reflexivity.
Qed.

(* ***** *)

Property mul_v22_is_right_distributive_over_add_v2:
  forall x y z : nat,
    mul_v22 (add_v2 x y) z = add_v2 (mul_v22 x z) (mul_v22 y z).
Proof.
  unfold mul_v22.
  intro x.
  induction x as [ | x' IHx'].

  - intros y z.
    rewrite -> (fold_unfold_add_v2_O y).
    rewrite -> (fold_unfold_mul_v22_aux_O z).
    rewrite -> (fold_unfold_add_v2_O (mul_v22_aux y z 0)).
    reflexivity.

  - intros y z.
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (fold_unfold_mul_v22_aux_S x' z).
    rewrite -> (add_v2_is_commutative z 0).
    rewrite -> (fold_unfold_add_v2_O z).
    Check (SO_is_right_neutral_wrt_mul_v22_aux x' z z).
    rewrite <- (SO_is_right_neutral_wrt_mul_v22_aux x' z z).
    rewrite -> (IHx' (S y) z).
    rewrite -> (fold_unfold_mul_v22_aux_S y z 0).
    rewrite -> (add_v2_is_commutative z 0).
    rewrite -> (fold_unfold_add_v2_O z).
    Check (SO_is_right_neutral_wrt_mul_v22_aux y z z).
    rewrite <- (SO_is_right_neutral_wrt_mul_v22_aux y z z).
    Check (add_v2_is_associative).
    rewrite -> (add_v2_is_commutative (mul_v22_aux y z 0) z).
    rewrite -> (add_v2_is_associative (mul_v22_aux x' z 0) z (mul_v22_aux y z 0)).
    reflexivity.
Qed.

(*

Lemma mul_v22_aux_is_right_distributive_over_add_v2 :
  forall x y z a : nat,
    add_v2 (mul_v22_aux x z a) (mul_v22_aux y z z) =
      add_v2 (mul_v22_aux x z z) (mul_v22_aux y z a).
Proof.
  intro x.
  induction x as [ | x' IHx'].
  - intros y z a.
    rewrite -> (fold_unfold_mul_v22_aux_O z a).
    rewrite -> (fold_unfold_mul_v22_aux_O z z).
    rewrite -> (SO_is_right_neutral_wrt_mul_v22_aux y z z).
    rewrite -> (SO_is_right_neutral_wrt_mul_v22_aux y z a).
    rewrite -> (add_v2_is_commutative a (add_v2 (mul_v22_aux y z 0) z)).
    rewrite -> (add_v2_is_commutative (mul_v22_aux y z 0) z).
    Check (add_v2_is_associative).
    Check (add_v2_is_associative z (mul_v22_aux y z 0) a).
    Check (eq_sym (add_v2_is_associative z (mul_v22_aux y z 0) a)).
    exact (eq_sym (add_v2_is_associative z (mul_v22_aux y z 0) a)).
  - intros y z a.
    rewrite -> (fold_unfold_mul_v22_aux_S x' z a).
    rewrite -> (fold_unfold_mul_v22_aux_S x' z z).
    Check (IHx' y z (add_v2 z a)).
    rewrite -> (IHx' y z (add_v2 z a)).
    rewrite -> (SO_is_right_neutral_wrt_mul_v22_aux x' z z).
    rewrite -> (SO_is_right_neutral_wrt_mul_v22_aux y z (add_v2 z a)).
    rewrite -> (SO_is_right_neutral_wrt_mul_v22_aux x' z (add_v2 z z)).
    rewrite -> (SO_is_right_neutral_wrt_mul_v22_aux y z a).
    Check (add_v2_is_associative).
    rewrite <- (add_v2_is_associative (mul_v22_aux x' z 0) z (add_v2 (mul_v22_aux y z 0) (add_v2 z a))).
    rewrite <- (add_v2_is_associative (mul_v22_aux x' z 0) (add_v2 z z) (add_v2 (mul_v22_aux y z 0) a)).
    rewrite -> (add_v2_is_commutative z (add_v2 (mul_v22_aux y z 0) (add_v2 z a))). 
    rewrite <- (add_v2_is_associative (mul_v22_aux y z 0) (add_v2 z a) z).
    rewrite -> (add_v2_is_commutative (add_v2 z z) (add_v2 (mul_v22_aux y z 0) a)).
    rewrite <- (add_v2_is_associative (mul_v22_aux y z 0) a (add_v2 z z)).
    rewrite -> (add_v2_is_commutative z a).
    rewrite <- (add_v2_is_associative a z z).
    reflexivity.
Qed.

Property mul_v22_is_right_distributive_over_add_v2 :
  forall x y z : nat,
    mul_v22 (add_v2 x y) z = add_v2 (mul_v22 x z) (mul_v22 y z).
Proof.
  unfold mul_v22.
  intro x.
  induction x as [ | x' IHx'].
  - intros y z.
    rewrite -> (fold_unfold_add_v2_O y).
    rewrite -> (fold_unfold_mul_v22_aux_O z 0).
    rewrite -> (fold_unfold_add_v2_O (mul_v22_aux y z 0)).
    reflexivity.
  - intros y z.
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (fold_unfold_mul_v22_aux_S x' z 0).
    rewrite -> (O_is_right_neutral_wrt_add_v2 z).
    rewrite -> (IHx' (S y) z).
    rewrite -> (fold_unfold_mul_v22_aux_S y z 0).
    rewrite -> (O_is_right_neutral_wrt_add_v2 z).
    exact SO_is_right_neutral_wrt_mul_v21_aux x' y z 0).
Qed.

 *)

(* ********** *)

(* Multiplication is associative *)

(* ***** *)

Property mul_v11_is_associative :
  forall x y z : nat,
    mul_v11 x (mul_v11 y z) = mul_v11 (mul_v11 x y) z.
Proof.
  intros x.
  induction x as [ | x' IHx'].
  - intros y z.
    Check (fold_unfold_mul_v11_O y).
    rewrite -> (fold_unfold_mul_v11_O y).
    rewrite -> (fold_unfold_mul_v11_O z).
    rewrite -> (fold_unfold_mul_v11_O (mul_v11 y z)).
    reflexivity.
  - intros y z.
    rewrite -> (fold_unfold_mul_v11_S x' y).
    rewrite -> (fold_unfold_mul_v11_S x' (mul_v11 y z)).
    Check (mul_v11_is_right_distributive_over_add_v1 (mul_v11 x' y) y z).
    rewrite (mul_v11_is_right_distributive_over_add_v1 (mul_v11 x' y) y z).
    rewrite -> IHx'.
    reflexivity.
Qed.
    
(* ***** *)

Property mul_v12_is_associative :
  forall x y z : nat,
    mul_v12 x (mul_v12 y z) = mul_v12 (mul_v12 x y) z.
Proof.
Abort.

(* ***** *)

(*
Property mul_v21_is_associative :
  forall x y z : nat,
    mul_v21 x (mul_v21 y z) = mul_v21 (mul_v21 x y) z.
Proof.
Abort.
*)

(* ***** *)


Property mul_v22_is_associative :
  forall x y z : nat,
    mul_v22 x (mul_v22 y z) = mul_v22 (mul_v22 x y) z.
Proof.
  unfold mul_v22.
  intros x.
  induction x as [ | x' IHx'].
  - intros y z.
    rewrite -> (fold_unfold_mul_v22_aux_O y).
    rewrite -> (fold_unfold_mul_v22_aux_O z).
    rewrite -> (fold_unfold_mul_v22_aux_O (mul_v22_aux y z 0)).
    reflexivity.
  - intros y z.
    rewrite -> (fold_unfold_mul_v22_aux_S x' y 0).
    rewrite -> (fold_unfold_mul_v22_aux_S x' (mul_v22_aux y z 0) 0).
    rewrite -> (O_is_right_neutral_wrt_add_v2 (mul_v22_aux y z 0)).
    Check (SO_is_right_neutral_wrt_mul_v22_aux).
    rewrite <- (SO_is_right_neutral_wrt_mul_v22_aux x' (mul_v22_aux y z 0) (mul_v22_aux y z 0)).
    rewrite <- (SO_is_right_neutral_wrt_mul_v22_aux x' y (add_v2 y 0)).
    fold (mul_v22 (add_v2 (mul_v22_aux x' y 0) (add_v2 y 0)) z).
    Check (mul_v22_is_right_distributive_over_add_v2).
    rewrite -> (mul_v22_is_right_distributive_over_add_v2 (mul_v22_aux x' y 0) (add_v2 y 0) z).
    unfold mul_v22.
    rewrite -> IHx'.
    Check (O_is_right_neutral_wrt_add_v2 y).
    rewrite -> (O_is_right_neutral_wrt_add_v2 y).
    reflexivity.
Qed.

    
    
(* ********** *)

(* Multiplication is left-distributive over addition *)

(* ***** *)

(* ... *)

(* ********** *)

(* end of week-04_equational-reasoning-about-arithmetical-functions.v *)
