(* week-09_formalizing-summations.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 17 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith.

(* ********** *)

Fixpoint Sigma (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O =>
    f 0
  | S n' =>
    Sigma n' f + f n
  end.

Lemma fold_unfold_Sigma_O :
  forall (f : nat -> nat),
    Sigma 0 f =
    f 0.
Proof.
  fold_unfold_tactic Sigma.
Qed.

Lemma fold_unfold_Sigma_S :
  forall (n' : nat)
         (f : nat -> nat),
    Sigma (S n') f =
    Sigma n' f + f (S n').
Proof.
  fold_unfold_tactic Sigma.
Qed.

(* ***** *)

Lemma about_factoring_a_multiplicative_constant_on_the_right_in_Sigma :
  forall (x c : nat)
         (f : nat -> nat),
    Sigma x (fun i => f i * c) = Sigma x f * c.
Proof.
  intros x c f.
  induction x as [ | x' IHx'].
  - Check fold_unfold_Sigma_O (fun i : nat => f i * c).
    rewrite (fold_unfold_Sigma_O (fun i : nat => f i * c)).
    unfold Sigma.
    reflexivity.
  - Check fold_unfold_Sigma_S.
    rewrite -> (fold_unfold_Sigma_S x' (fun i : nat => f i * c)).
    rewrite -> (fold_unfold_Sigma_S x' f).
    rewrite -> IHx'.
    Check mult_plus_distr_r.
    rewrite -> (mult_plus_distr_r (Sigma x' f) (f (S x')) c).
    reflexivity.
Qed.

(* ***** *)

Lemma about_factoring_a_multiplicative_constant_on_the_left_in_Sigma :
  forall (x c : nat)
         (f : nat -> nat),
    Sigma x (fun i => c * f i) = c * Sigma x f.
Proof.
  intros x c f.
  induction x as [ | x' IHx'].
  - Check fold_unfold_Sigma_O (fun i : nat => f i * c).
    rewrite -> (fold_unfold_Sigma_O (fun i : nat => c * f i)).
    unfold Sigma.
    reflexivity.
  - Check fold_unfold_Sigma_S.
    rewrite -> (fold_unfold_Sigma_S x' (fun i : nat => c * f i)).
    rewrite -> (fold_unfold_Sigma_S x' f).
    rewrite -> IHx'.
    Check mult_plus_distr_l.
    rewrite -> (mult_plus_distr_l c (Sigma x' f) (f (S x'))).
    reflexivity.
Qed.

(* ***** *)
  
Lemma about_swapping_Sigma :
  forall (x y : nat)
         (f : nat -> nat -> nat),
    Sigma x (fun i => Sigma y (fun j => f i j)) = Sigma y (fun j => Sigma x (fun i => f i j)).
Proof.
intros x y f.
  revert y.
  induction x as [ | x' IHx']; intro y.
  - induction y as [ | y' IHy'].
    -- reflexivity. 
    -- rewrite -> fold_unfold_Sigma_O.
       rewrite ->2 fold_unfold_Sigma_S.
       rewrite -> fold_unfold_Sigma_O.
       rewrite -> Nat.add_cancel_r.
       rewrite <- IHy'.
       rewrite -> fold_unfold_Sigma_O.
       reflexivity.
  - rewrite -> fold_unfold_Sigma_S.
    induction y as [ | y' IHy']. 
    -- rewrite -> IHx'.
       rewrite ->3 fold_unfold_Sigma_O.
       rewrite -> fold_unfold_Sigma_S.
       reflexivity.
    -- rewrite ->2 fold_unfold_Sigma_S.
       rewrite -> fold_unfold_Sigma_S.
       rewrite -> (IHx' (S y')).
       rewrite -> fold_unfold_Sigma_S.
       rewrite <- IHy'.
       rewrite -> (IHx' y').
       rewrite <-2 Nat.add_assoc.
       Check (Nat.add_cancel_l
                (Sigma x' (fun i : nat => f i (S y')) +
                   (Sigma y' (fun j : nat => f (S x') j) + f (S x') (S y')))
                (Sigma y' (fun j : nat => f (S x') j) +
   (Sigma x' (fun i : nat => f i (S y')) + f (S x') (S y')))
                (Sigma y' (fun j : nat => Sigma x' (fun i : nat => f i j)))).
       rewrite (Nat.add_cancel_l
                (Sigma x' (fun i : nat => f i (S y')) +
                   (Sigma y' (fun j : nat => f (S x') j) + f (S x') (S y')))
                (Sigma y' (fun j : nat => f (S x') j) +
   (Sigma x' (fun i : nat => f i (S y')) + f (S x') (S y')))
                (Sigma y' (fun j : nat => Sigma x' (fun i : nat => f i j)))).
       rewrite ->2 Nat.add_assoc.
       rewrite Nat.add_cancel_r.
       rewrite Nat.add_comm.
       reflexivity.

Restart.

intros x y f.
  revert y.
  induction x as [ | x' IHx']; intro y.
  - induction y as [ | y' IHy'].
    -- reflexivity. 
    -- rewrite -> fold_unfold_Sigma_O.
       rewrite ->2 fold_unfold_Sigma_S.
       rewrite -> fold_unfold_Sigma_O.
       rewrite <- IHy'.
       rewrite -> fold_unfold_Sigma_O.
       reflexivity.
  - rewrite -> fold_unfold_Sigma_S.
    induction y as [ | y' IHy']. 
    -- rewrite -> IHx'.
       rewrite ->3 fold_unfold_Sigma_O.
       rewrite -> fold_unfold_Sigma_S.
       reflexivity.
    -- rewrite ->2 fold_unfold_Sigma_S.
       rewrite -> fold_unfold_Sigma_S.
       rewrite -> (IHx' (S y')).
       rewrite -> fold_unfold_Sigma_S.
       rewrite <- IHy'.
       rewrite -> (IHx' y').
       rewrite <-2 Nat.add_assoc.
       Check (Nat.add_cancel_l
                (Sigma x' (fun i : nat => f i (S y')) +
                   (Sigma y' (fun j : nat => f (S x') j) + f (S x') (S y')))
                (Sigma y' (fun j : nat => f (S x') j) +
   (Sigma x' (fun i : nat => f i (S y')) + f (S x') (S y')))
                (Sigma y' (fun j : nat => Sigma x' (fun i : nat => f i j)))).
       rewrite (Nat.add_cancel_l
                (Sigma x' (fun i : nat => f i (S y')) +
                   (Sigma y' (fun j : nat => f (S x') j) + f (S x') (S y')))
                (Sigma y' (fun j : nat => f (S x') j) +
   (Sigma x' (fun i : nat => f i (S y')) + f (S x') (S y')))
                (Sigma y' (fun j : nat => Sigma x' (fun i : nat => f i j)))).
       rewrite ->2 Nat.add_assoc.
       Check (Nat.add_comm (Sigma x' (fun i : nat => f i (S y'))) (Sigma y' (fun j : nat => f (S x') j))).
       rewrite -> (Nat.add_comm (Sigma x' (fun i : nat => f i (S y'))) (Sigma y' (fun j : nat => f (S x') j))).
       reflexivity.
Qed.
       
(* ***** *)

Lemma about_Sigma_with_two_equivalent_functions :
  forall (x : nat)
         (f g : nat -> nat),
    (forall i : nat,
        f i = g i) ->
    Sigma x f = Sigma x g.
Proof.
  intros x f g.
  intro i.
  induction x as [ | x' IHx'].
  - rewrite -> fold_unfold_Sigma_O.
    rewrite -> fold_unfold_Sigma_O.
    apply i.
  - rewrite -> (fold_unfold_Sigma_S x' f).
    rewrite -> (fold_unfold_Sigma_S x' g).
    rewrite -> IHx'.
    rewrite -> (i (S x')). 
    reflexivity.
Qed.

(* ***** *)

Lemma about_Sigma_with_two_equivalent_functions_up_to_the_bound :
  forall (x : nat)
         (f g : nat -> nat),
    (forall i : nat,
        i <= x ->
        f i = g i) ->
    Sigma x f = Sigma x g.
Proof.
  intros x f g.
  intro i.
  induction x as [ | x' IHx'].
  - rewrite -> fold_unfold_Sigma_O.
    rewrite -> fold_unfold_Sigma_O.
    apply i.
    Search (_ <= _).
    exact (le_n 0).
  - rewrite -> (fold_unfold_Sigma_S x' f).
    rewrite -> (fold_unfold_Sigma_S x' g).
    rewrite -> IHx'.
    -- rewrite (i (S x')).
       --- reflexivity.
       --- exact (le_n (S x')).
    -- intros i0. 
       intros H_i0_less_than_x'.
       apply (i (i0)).
       rewrite -> H_i0_less_than_x'.
       Search (_ <= S _).
       exact (Nat.le_succ_diag_r x').

Restart.

intros x f g.
intro i.
induction x as [ | x' IHx'].
  - rewrite -> fold_unfold_Sigma_O.
    rewrite -> fold_unfold_Sigma_O.
    apply i.
    Search (_ <= _).
    exact (le_n 0).
  - rewrite -> (fold_unfold_Sigma_S x' f).
    rewrite -> (fold_unfold_Sigma_S x' g).
    rewrite -> IHx'.
    -- rewrite (i (S x')).
       --- reflexivity.
       --- exact (le_n (S x')).
    -- intros i0. 
       intros H_i0_less_than_x'.
       apply (i (i0)).
       apply le_S.
       exact H_i0_less_than_x'.
Qed.

(* ***** *)

Lemma about_Sigma_with_an_additive_function :
  forall (x : nat)
         (f g : nat -> nat),
    Sigma x (fun i => f i + g i) = Sigma x f + Sigma x g.
Proof.
  intros x f g.
  induction x as [ | x' IHx'].
  - rewrite ->3 fold_unfold_Sigma_O. 
    reflexivity.
  - rewrite ->3 fold_unfold_Sigma_S.
    rewrite -> IHx'.
    Search (_ + (_ +_) = _ + _ + _).
    rewrite -> Nat.add_assoc.
    rewrite -> Nat.add_shuffle1.
    rewrite <- Nat.add_assoc.
    reflexivity.
Qed.

(* ***** *)

Lemma about_Sigma_with_a_constant_function :
  forall x y : nat,
    Sigma x (fun _ => y) = y * (S x).
Proof.
  intros x y.
  induction x as [ | x' IHx'].
  - unfold Sigma. 
    Search (_ * 1 = _).
    symmetry.
    exact (Nat.mul_1_r y).
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHx'.
    Search (_ * S _ = _).
    rewrite ->3 Nat.mul_succ_r.
    reflexivity.
Qed.

(* ***** *)

Lemma about_Sigma_with_two_small_a_function :
  forall (x : nat)
         (f : nat -> nat),
    (forall i : nat,
        i <= x ->
        f i = 0) ->
    Sigma x f = 0.
Proof.
  intros x f.
  intro H_f_i.
  induction x as [ | x' IHx'].
  - rewrite -> fold_unfold_Sigma_O.
    apply H_f_i.
    exact (le_n 0).
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHx'.
    -- apply (H_f_i (S x')). 
       exact (le_n (S x')).
    -- intros i H_i_x'.    
       apply H_f_i.
       rewrite -> Nat.le_succ_diag_r.
       Search (S _ <= S  _).
       apply le_n_S.
       exact H_i_x'.

Restart.
       
  intros x f.
  intro H_f_i.
  induction x as [ | x' IHx'].
  - rewrite -> fold_unfold_Sigma_O.
    apply H_f_i.
    exact (le_n 0).
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHx'.
    -- apply (H_f_i (S x')). 
       exact (le_n (S x')).
    -- intros i H_i_x'.    
       apply H_f_i.
       apply le_S in H_i_x'.
       exact (H_i_x').
Qed.

(* ***** *)

Lemma about_Sigma_up_to_a_positive_sum :
  forall (x y : nat)
         (f : nat -> nat),
    Sigma (x + S y) f = Sigma x f + Sigma y (fun i => f (x + S i)).
Proof.
  intros x y f.
  induction y as [ | y' IHy'].
  - Search (_ + 1 = S _).
    rewrite -> Nat.add_1_r. 
    rewrite -> fold_unfold_Sigma_S.
    rewrite -> fold_unfold_Sigma_O.
    rewrite <- Nat.add_1_r.
    reflexivity.
  - rewrite -> Nat.add_succ_r. 
    rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> IHy'.
    Search (_ + _ + _ = _ + (_ + _)).
    rewrite -> plus_assoc_reverse.
    rewrite <- Nat.add_succ_r.
    reflexivity.
Qed.

(* ********** *)

Definition Sigma1 (n : nat) (f : nat -> nat) : nat :=
  match n with
    O =>
    0
  | S n' =>
    Sigma (S n') f
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
    Sigma (S n') f.
Proof.
  fold_unfold_tactic Sigma1.
Qed.

(* ***** *)

Property about_Sigma1 :
  forall f : nat -> nat,
    f 0 = 0 ->
    forall n : nat,
      Sigma1 n f = Sigma n f.
Proof.
  intros f H_f.
  intro n.
  induction n as [ | n' IHn'].
  - rewrite -> fold_unfold_Sigma1_O.
    rewrite -> fold_unfold_Sigma_O.
    symmetry.
    exact H_f.
  - rewrite -> fold_unfold_Sigma_S. 
    Check fold_unfold_Sigma1_S.
    rewrite -> fold_unfold_Sigma1_S.
    rewrite -> fold_unfold_Sigma_S.
    reflexivity.
Qed.

(* ********** *)

(* end of week-09_formalizing-summations.v *)
