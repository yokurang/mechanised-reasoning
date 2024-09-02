(* week-09_formalizing-two-by-two-matrices.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 17 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith.

(* ********** *)

Inductive m22 : Type :=
| M22 : nat -> nat -> nat -> nat -> m22.

Property componential_equality_m22 :
  forall x11 x12 x21 x22 y11 y12 y21 y22 : nat,
    M22 x11 x12
        x21 x22 =
    M22 y11 y12
        y21 y22
    <->
    x11 = y11 /\ x12 = y12 /\ x21 = y21 /\ x22 = y22.
Proof.
  intros x11 x12 x21 x22 y11 y12 y21 y22.
  split.

  - intro H_tmp.
    injection H_tmp as H11 H12 H21 H22.
    rewrite -> H11.
    rewrite -> H12.
    rewrite -> H21.
    rewrite -> H22.
    split; [reflexivity | split; [reflexivity | split; [reflexivity | reflexivity]]].

  - intros [H11 [H12 [H21 H22]]].
    rewrite -> H11.
    rewrite -> H12.
    rewrite -> H21.
    rewrite -> H22.
    reflexivity.
Qed.

(* ***** *)

Definition zero_m22 := M22 0 0
                           0 0.

Definition add_m22 (x y : m22) : m22 :=
  match (x, y) with
  | (M22 x11 x12
         x21 x22,
     M22 y11 y12
         y21 y22) =>
    M22 (x11 + y11) (x12 + y12)
        (x21 + y21) (x22 + y22)
  end.

Lemma add_m22_assoc :
  forall x y z : m22,
    add_m22 x (add_m22 y z) =
    add_m22 (add_m22 x y) z.
Proof.
  intros [x11 x12
          x21 x22]
         [y11 y12
          y21 y22]
         [z11 z12
          z21 z22].
  unfold add_m22.
  rewrite ->4 Nat.add_assoc.
  reflexivity.
Qed.

Lemma add_m22_0_l :
  forall x : m22,
    add_m22 zero_m22 x = 
    x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold add_m22, zero_m22.
  rewrite ->4 Nat.add_0_l.
  reflexivity.
Qed.

Lemma add_m22_0_r :
  forall x : m22,
    add_m22 x zero_m22 =
    x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold add_m22, zero_m22.
  rewrite ->4 Nat.add_0_r.
  reflexivity.
Qed.

(* ********** *)

Inductive mm22 : Type :=
| MM22 : m22 -> m22 -> m22 -> m22 -> mm22.

(* ********** *)


(* Week 9: Exercise 02 *)


(* A) Formalise Definition 9 in Coq *)

Definition mul_m22 (x y : m22) : m22 :=
    match (x, y) with
    | (M22 x11 x12
           x21 x22,
       M22 y11 y12
           y21 y22) =>
        M22 (x11 * y11 + x12 * y21) (x11 * y12 + x12 * y22)
            (x21 * y11 + x22 * y21) (x21 * y12 + x22 * y22)
    end.

(* B) Formalise and Prove Property 10 in Coq *)


Lemma nat_add_shuffle1 :
  forall n m p q : nat,
    n + m + (p + q) = n + p + (m + q).
Proof.
  intros n m p q.
  Check (Nat.add_assoc).
  rewrite -> (Nat.add_assoc (n + m) p q).
  rewrite <- (Nat.add_assoc n m p).
  Check (Nat.add_comm).
  rewrite -> (Nat.add_comm m p).
  rewrite -> (Nat.add_assoc n p m).
  rewrite <- (Nat.add_assoc (n + p) m q).
  reflexivity.
Qed.

Lemma mul_m22_assoc :
  forall x y z : m22,
    mul_m22 x (mul_m22 y z) =
      mul_m22 (mul_m22 x y) z.
Proof.
  intros [x11 x12
          x21 x22]
         [y11 y12
          y21 y22]
         [z11 z12
          z21 z22].
  unfold mul_m22.
  rewrite -> 8 Nat.mul_add_distr_l.
  rewrite -> 16 Nat.mul_assoc.
  rewrite -> 8 Nat.mul_add_distr_r.
  rewrite ->2 (nat_add_shuffle1 _ (x12 * _ * _) _).
  rewrite ->2 (nat_add_shuffle1 _ (x21 * _ * _) _).
  reflexivity.
Qed.

(* C) Formalize and prove Property 12 in Coq *)

Definition identity_m22 := M22 1 0
                               0 1.

Lemma mul_m22_identity_l :
  forall x : m22,
    mul_m22 identity_m22 x =
      x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold mul_m22, identity_m22.
  rewrite -> 4 Nat.mul_1_l.
  rewrite -> 4 Nat.mul_0_l.
  rewrite -> 2 Nat.add_0_r.
  rewrite -> 2 Nat.add_0_l.
  reflexivity.
Qed.

Lemma mul_m22_identity_r :
  forall x : m22,
    mul_m22 x identity_m22 =
      x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold mul_m22, identity_m22.
  rewrite -> 4 Nat.mul_1_r.
  rewrite -> 4 Nat.mul_0_r.
  rewrite -> 2 Nat.add_0_l.
  rewrite -> 2 Nat.add_0_r.
  reflexivity.
Qed.

(* D) Formalize Definition 13 in Coq *)

Fixpoint pow_m22_l (x : m22) (n : nat) : m22 :=
  match n with
  | 0 =>
      identity_m22
  | S n =>
      mul_m22 (pow_m22_l x n) x
  end.

Lemma fold_unfold_pow_m22_l_O :
  forall (x : m22),
    pow_m22_l x 0 =
      identity_m22.
Proof.
  fold_unfold_tactic pow_m22_l.
Qed.

Lemma fold_unfold_pow_m22_l_S :
  forall (x : m22)
         (n : nat),
    pow_m22_l x (S n) =
      mul_m22 (pow_m22_l x n) x.
Proof.
  fold_unfold_tactic pow_m22_l.
Qed.

(* E) Formalize and prove Proposition 14 *)

Proposition about_pow_m22_l :
  forall n : nat,
    pow_m22_l (M22 1 1
                   0 1) n =
      M22 1 n
          0 1.
Proof. 
  intro n.
  induction n as [ | n' IHn'].
  + rewrite -> (fold_unfold_pow_m22_l_O (M22 1 1 0 1)).
    unfold identity_m22.
    reflexivity.
  + rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 0 1) n').
    rewrite -> IHn'.
    unfold mul_m22.
    rewrite -> 2 Nat.mul_1_l.
    rewrite -> (Nat.mul_0_r n').
    rewrite -> (Nat.add_1_l 0).
    rewrite -> (Nat.mul_1_r n').
    Search (1 + _ = S _).
    rewrite -> (Nat.add_1_l n').
    rewrite -> (Nat.mul_0_l 1).
    rewrite -> (Nat.add_0_r 0).
    rewrite -> (Nat.add_1_r 0).
    reflexivity.
Qed.    

(*
F) How does your formalization of Proposition 14 compare with the informal proof of Proposition 14?

 Both proofs use induction. 

 Base Case:
 In the informal proof, the LHS is reduced to the identity matrix by the definition of exponentiating a matrix by zero. In our formal proof, the LHS is also reduced to the indentity matrix by the specification of the power function of matrix. Furthermore, we can instantiate zero on the RHS, and find that the LHS = RHS. In both the formal and informal proof, we solved the goal in the same way

Inductive Case:
In the informal proof, we have the induction hypothesis that F^k = M22 (1 k 0 1). We can show that it holds for k + 1 by simplifying F^(k+1) = F^k * F =>  M22 (1 k 0 1) * M22 (1 1 0 1) => M22 (1 (k + 1) 0 1).

However, in our formal proof, we follow the same procedure of simplifying F^(k+1) = F^k * F =>  M22 (1 k 0 1) * M22 (1 1 0 1) using the fold-unfold lemma for pow_m22_l. Next, we apply the induction hypothesis too. Afterwards, we carry out the matrix multipliction using routine rewrites.

This illustrates that tCPA gives us a domain-specific language for writing proofs. 

*)

(* G) Solve Exercise 25 *)

Definition F := M22 1 1
                    1 0.

Compute (pow_m22_l F 0, pow_m22_l F 1, pow_m22_l F 2, pow_m22_l F 3, pow_m22_l F 4, pow_m22_l F 5, pow_m22_l F 6, pow_m22_l F 7, pow_m22_l F 8).

(* Two accumulators, tail-recursive implementation *) 

Fixpoint fib_aux (n : nat) (a : nat) (b : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fib_aux n' b (a + b)
  end.

Definition fib (n : nat) : nat :=
  fib_aux n 0 1.

Lemma fold_unfold_fib_aux_O :
  forall (a b : nat),
  fib_aux 0 a b = a.
Proof.
  fold_unfold_tactic fib_aux.
Qed.

Lemma fold_unfold_fib_aux_S :
  forall (n : nat)
         (a b : nat),
    fib_aux (S n) a b = fib_aux n b (a + b).
Proof.
  fold_unfold_tactic fib_aux.
Qed.

(* Canonical Definition of Fibonacci Function *) 

Fixpoint fib' (n : nat) : nat :=
  match n with
  | 0 => 0
  |  S n' =>
       match n' with
       | O => 1
       | S n'' =>  fib' n' + fib' n''
       end
  end.

Lemma fold_unfold_fib'_O :
  fib' 0 = 0.
Proof.
  fold_unfold_tactic fib'.
Qed.

Lemma fold_unfold_fib'_S :
  forall (n' : nat),
    fib'(S n') =  match n' with
       | O => 1
       | S n'' =>  fib' n' + fib' n''
       end.
Proof.
  fold_unfold_tactic fib'.
Qed.

Corollary fold_unfold_fib'_1 :
  fib' 1 = 1.
Proof.
  exact (fold_unfold_fib'_S 0).
Qed.

Corollary fold_unfold_fib'_SS :
  forall (n'' : nat),
    fib' (S (S n'')) =
      fib' (S n'') + fib' n''.
Proof.
  intro n''.
  exact (fold_unfold_fib'_S (S n'')).
Qed.

(* FibFib Implementation *)

Fixpoint fibfib (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 1)
  | S n' =>
    let (fib_n', fib_Sn') := fibfib n' in
    (fib_Sn', fib_Sn'+ fib_n')
  end.

Definition fib'' (n : nat) : nat :=
  fst (fibfib n).
       
Lemma fold_unfold_fibfib_O :
  fibfib 0 = (0, 1).
Proof.
  fold_unfold_tactic fibfib.
Qed.

Lemma fold_unfold_fibfib_S :
  forall (n' : nat),
    fibfib (S n') = 
    let (fib_n', fib_Sn') := fibfib n' in 
    (fib_Sn', fib_Sn' + fib_n').
Proof.
  fold_unfold_tactic fibfib.
Qed.

Lemma about_fibfib :
  forall (n : nat),
    fibfib n = (fib' n, fib' (S n)).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + rewrite -> fold_unfold_fibfib_O.
    rewrite -> fold_unfold_fib'_O.
    rewrite -> fold_unfold_fib'_1.
    reflexivity.
  + rewrite -> fold_unfold_fibfib_S.
    rewrite -> IHn'.
    rewrite <- fold_unfold_fib'_SS.
    reflexivity.
Qed.

Lemma about_fib_aux_S :
  forall (n a b a' b': nat),
    fib_aux n a b + fib_aux n a' b' =
      fib_aux n (a + a') (b + b').
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + intros a b a' b'.
    rewrite -> (fold_unfold_fib_aux_O a b).
    rewrite -> (fold_unfold_fib_aux_O a' b').
    rewrite -> (fold_unfold_fib_aux_O (a + a') (b + b')).
    reflexivity.
  + intros a b a' b'.
    rewrite -> (fold_unfold_fib_aux_S n' a b).
    rewrite -> (fold_unfold_fib_aux_S n' a' b').
    rewrite -> (IHn' b (a + b) b' (a' + b')).
    Search (_ + _ + ( _ ) = _ + _ + _ ).
    (*  (a + b + (a' + b')) ->
        (a + a' + (b + b'))*)
    rewrite -> (nat_add_shuffle1 a b a' b').
    rewrite -> (fold_unfold_fib_aux_S n' (a + a') (b + b')).
    reflexivity.
Qed.

(* Prove the same for the tail-recursive version of fib *)
Lemma about_fib_aux :
  forall (n'' a b : nat),
    fib_aux (S (S n'')) a b = fib_aux n'' a b + fib_aux (S n'') a b.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + intros a b.
    rewrite -> fold_unfold_fib_aux_S.
    rewrite -> fold_unfold_fib_aux_S.
    rewrite -> fold_unfold_fib_aux_O.

    rewrite -> fold_unfold_fib_aux_O.
    rewrite -> fold_unfold_fib_aux_S.
    rewrite -> fold_unfold_fib_aux_O.

    reflexivity.
  + intros a b.
    rewrite -> fold_unfold_fib_aux_S.
    rewrite -> (IHn' b (a + b)).
    rewrite -> fold_unfold_fib_aux_S.
    rewrite -> (about_fib_aux_S n' b (a + b) (a + b) (b + (a + b))).

    rewrite -> fold_unfold_fib_aux_S.
    rewrite -> (IHn' a b).
    rewrite -> fold_unfold_fib_aux_S.
    rewrite -> (about_fib_aux_S n' a b b (a + b)).
    rewrite -> (about_fib_aux_S n' b (a + b) (a + b) (b + (a + b))).
    reflexivity.
Qed.
      
(* Unit test for fibonacci function *) 

Definition test_fib (candidate : nat -> nat) : bool :=
  (Nat.eqb (candidate 0) 0) &&
    (Nat.eqb (candidate 1) 1) &&
    (Nat.eqb (candidate 2) 1) &&
    (Nat.eqb (candidate 3) 2) &&
    (Nat.eqb (candidate 4) 3) &&
    (Nat.eqb (candidate 5) 5) &&
    (Nat.eqb (candidate 6) 8) &&
    (Nat.eqb (candidate 7) 13) &&
    (Nat.eqb (candidate 8) 21) &&
    (Nat.eqb (candidate 9) 34) &&
    (Nat.eqb (candidate 10) 55).

Compute (test_fib fib).

Compute (test_fib fib').

Compute (test_fib fib'').

(* Using two accumulators *) 

Lemma fib_aux_sequence :
  (forall n' : nat,
      pow_m22_l (M22 1 1 1 0) (S n') =
        M22 (fib_aux (S (S n')) 0 1) (fib_aux (S n') 0 1)
            (fib_aux (S n') 0 1) (fib_aux n' 0 1)).
Proof.
    intro n'.
    unfold F.
    induction n' as [ | n' IHn''].
    ++ rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) 0).
       rewrite -> (fold_unfold_pow_m22_l_O (M22 1 1 1 0)).
       rewrite -> (mul_m22_identity_l (M22 1 1 1 0)).
       rewrite -> about_fib_aux.
       rewrite -> fold_unfold_fib_aux_O.
       rewrite -> fold_unfold_fib_aux_S.
       rewrite -> Nat.add_0_l.
       rewrite -> Nat.add_1_r.
       rewrite -> fold_unfold_fib_aux_O.
       reflexivity.
    ++ rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) (S n')).
       rewrite -> IHn''.
       unfold mul_m22.
       rewrite -> 3 about_fib_aux.
       rewrite -> fold_unfold_fib_aux_S.
       rewrite -> Nat.add_0_l.
       rewrite -> 3 Nat.mul_1_r.
       rewrite -> 2 Nat.mul_0_r.
       rewrite -> 2 Nat.add_0_r.
       rewrite -> 4 about_fib_aux_S.
       rewrite -> Nat.add_0_l.
       rewrite -> 2 Nat.add_1_r.
       rewrite -> Nat.add_0_r.
       Search (1 + _ = _).
       rewrite -> (Nat.add_1_l 2).
       reflexivity.
Qed.
  
Corollary ex25_fib_aux :
  (pow_m22_l F 0 =
     identity_m22)
  /\
    (forall n' : nat,
        pow_m22_l F (S n') =
          M22 (fib (S (S n'))) (fib (S n'))    
              (fib (S n'))     (fib n')).
Proof.
  split.
  + rewrite -> (fold_unfold_pow_m22_l_O F).
    reflexivity.
  + unfold F, fib.
    exact fib_aux_sequence.
Qed.

(* Using the Cannonical Definition of the Fibonacci Function *) 

Lemma ex25_fib' :
  (pow_m22_l F 0 =
     identity_m22)
  /\
    (forall n' : nat,
        pow_m22_l F (S n') =
          M22 (fib' (S (S n'))) (fib' (S n'))    
              (fib' (S n'))     (fib' n')).
Proof.
  split.
  + rewrite -> (fold_unfold_pow_m22_l_O F).
    reflexivity.
  + intro n'.
    unfold F.
    induction n' as [ | n' IHn''].
    ++ rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) 0).
       rewrite -> (fold_unfold_pow_m22_l_O (M22 1 1 1 0)).
       rewrite -> (mul_m22_identity_l (M22 1 1 1 0)).
       rewrite -> fold_unfold_fib'_SS.
       rewrite -> fold_unfold_fib'_1.
       rewrite -> fold_unfold_fib'_O.
       rewrite -> Nat.add_0_r.
       reflexivity.
    ++ rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) (S n')).
       rewrite -> IHn''.
       unfold mul_m22.
       rewrite -> 3 Nat.mul_1_r.
       rewrite -> 2 Nat.mul_0_r.
       rewrite -> 2 Nat.add_0_r.
       rewrite <- 2 fold_unfold_fib'_SS.
       reflexivity.
Qed.

(* Using the Fibfib Implementation *) 

Lemma about_fibfib_S :
  forall (n : nat),
    fst (fibfib  (S n)) + fst (fibfib n) = fst (fibfib (S (S n))).
Proof.
  intro n.
  rewrite -> 3 about_fibfib.
  unfold fst.
  rewrite <- fold_unfold_fib'_SS.
  reflexivity.
Qed.

Lemma fibfib_sequence :
  forall (n' : nat),
    pow_m22_l F (S n') =
      M22 (fst (fibfib (S (S n')))) (fst (fibfib (S n')))    
          (fst (fibfib (S n'))) (fst (fibfib n')).
Proof.
  intro n'.
  unfold F.
  induction n' as [ | n' IHn'].
  + rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) 0).
    rewrite -> (fold_unfold_pow_m22_l_O (M22 1 1 1 0)).
    rewrite -> (mul_m22_identity_l (M22 1 1 1 0)).
    rewrite -> 2 about_fibfib.
    rewrite -> fold_unfold_fibfib_O.
    unfold fst.
    rewrite -> fold_unfold_fib'_SS.
    rewrite -> fold_unfold_fib'_1.
    rewrite -> fold_unfold_fib'_O.
    rewrite -> Nat.add_0_r.
    reflexivity.
  + rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) (S n')).
    rewrite -> IHn'.
    unfold mul_m22.
    rewrite -> 3 Nat.mul_1_r.
    rewrite -> 2 Nat.mul_0_r.
    rewrite -> 2 Nat.add_0_r.
    rewrite -> 2 about_fibfib_S.
    reflexivity.
Qed.
                                      
Lemma ex25_fibfib :
  (pow_m22_l F 0 =
     identity_m22)
  /\
    (forall n' : nat,
        pow_m22_l F (S n') =
          M22 (fib'' (S (S n'))) (fib'' (S n'))    
              (fib'' (S n'))     (fib'' n')).
Proof.
  split.
  + rewrite -> (fold_unfold_pow_m22_l_O F).
    reflexivity.
  + intro n'.
    unfold fib''.
    exact (fibfib_sequence n').
Qed.

(* H) Formalize Definition 27 *)

Fixpoint pow_m22_r (x : m22) (n : nat) : m22 :=
  match n with
  | 0 =>
      identity_m22
  | S n =>
      mul_m22 x (pow_m22_r x n)
  end.

Lemma fold_unfold_pow_m22_r_O :
  forall (x : m22),
    pow_m22_r x 0 =
      identity_m22.
Proof.
  fold_unfold_tactic pow_m22_r.
Qed.

Lemma fold_unfold_pow_m22_r_S :
  forall (x : m22)
         (n' : nat),
    pow_m22_r x (S n') =
      mul_m22 x (pow_m22_r x n').
Proof.
  fold_unfold_tactic pow_m22_r.
Qed.

(* I) Are Definitions 13 and 27 equivalent? *)

Lemma pow_m22_comm_r :
  forall (x : m22)
         (n : nat),
    mul_m22 x (pow_m22_r x n) =
      mul_m22 (pow_m22_r x n) x.
Proof.
  intros x n.
  revert x.
  induction n as [ | n' IHn'].
  + intro x.
    rewrite -> (fold_unfold_pow_m22_r_O x).
    rewrite -> (mul_m22_identity_r x).
    rewrite -> (mul_m22_identity_l x).
    reflexivity.
  + intro x.
    rewrite -> (fold_unfold_pow_m22_r_S x n').
    rewrite -> (IHn' x).
    rewrite -> (mul_m22_assoc x (pow_m22_r x n') x).
    rewrite <- (IHn' x).
    reflexivity.
Qed.

Proposition pow_m22_l_is_equivalent_wrt_pow_m22_r :
  forall (x : m22)
         (n : nat),
    pow_m22_l x n =
      pow_m22_r x n.
Proof.
  intros x n.
  revert x.
  induction n as [ | n' IHn'].
  + intro x.
    rewrite -> (fold_unfold_pow_m22_l_O x).
    rewrite -> (fold_unfold_pow_m22_r_O x).
    reflexivity.
  + intro x.
    rewrite -> (fold_unfold_pow_m22_l_S x n').
    rewrite -> (fold_unfold_pow_m22_r_S x n').
    rewrite -> (IHn' x).
    rewrite <- (pow_m22_comm_r x n').
    reflexivity.
Qed.

(* J) Formalize Definition 35 *)

Definition transpose_m22 (x : m22) : m22 :=
  match x with
  | (M22 x11 x12
         x21 x22) =>
      M22 x11 x21
          x12 x22
  end.

(* K) Formalize and prove Property 36 *)

Proposition transpose_is_involutory :
  forall (x : m22),
    transpose_m22 (transpose_m22 x) =
      x.
Proof.
  intro x.
  unfold transpose_m22 at 2.
  destruct x as [x11 x21 x12 x22].
  unfold transpose_m22 at 1.
  reflexivity.
Qed.

(* L) Formalize and prove Proposition 38 *)

Lemma transpose_identity_r :
  transpose_m22 identity_m22 =
    identity_m22.
Proof.
  unfold transpose_m22.
  unfold identity_m22.
  reflexivity.
Qed.

Lemma transposition_distributes_over_mul_m22 :
  forall (x y : m22),
    transpose_m22 (mul_m22 x y) =
      mul_m22 (transpose_m22 y) (transpose_m22 x).
Proof.
  intros x y.  
  
  unfold transpose_m22 at 2.
  destruct x as [x11 x12 x21 x22].
  unfold transpose_m22 at 2.
  destruct y as [y11 y12 y21 y22].
  unfold mul_m22 at 2.

  unfold mul_m22.
  unfold transpose_m22.

  rewrite -> (Nat.mul_comm x11 y11). 
  rewrite -> (Nat.mul_comm x12 y21). 
  rewrite -> (Nat.mul_comm x21 y11).
  rewrite -> (Nat.mul_comm x22 y21).
  rewrite -> (Nat.mul_comm x11 y12).
  rewrite -> (Nat.mul_comm x12 y22).
  rewrite -> (Nat.mul_comm x21 y12).
  rewrite -> (Nat.mul_comm x22 y22). 
  reflexivity.
Qed.

Lemma pow_m22_comm_l :
  forall (x : m22)
         (n : nat),
    mul_m22 x (pow_m22_l x n) =
      mul_m22 (pow_m22_l x n) x.
Proof.
  intros x n.
  revert x.
  induction n as [ | n' IHn'].
  + intro x.
    rewrite -> (fold_unfold_pow_m22_l_O x).
    rewrite -> (mul_m22_identity_l x).
    rewrite -> (mul_m22_identity_r x).
    reflexivity.
  + intro x.
    rewrite -> (fold_unfold_pow_m22_l_S x n').
    rewrite <- (IHn' x).
    rewrite <- (mul_m22_assoc x (pow_m22_l x n') x).
    rewrite -> (IHn' x).
    reflexivity.
Qed.

Proposition transposition_commutes_with_exponentiation :
  forall (x : m22)
         (n : nat),
    transpose_m22 (pow_m22_l x n) =
      pow_m22_l (transpose_m22 x) n.
Proof.
  intros x n.
  revert x.
  induction n as [ | n' IHn'].
  + intro x.
    rewrite -> (fold_unfold_pow_m22_l_O x).
    rewrite -> (fold_unfold_pow_m22_l_O (transpose_m22 x)).
    exact (transpose_identity_r).
  + intro x.
    rewrite -> (fold_unfold_pow_m22_l_S x n').
    rewrite -> (fold_unfold_pow_m22_l_S (transpose_m22 x) n').
    rewrite -> (transposition_distributes_over_mul_m22 (pow_m22_l x n') x).
    rewrite -> (IHn' x).
    Check (pow_m22_comm_l (transpose_m22 x) n').
    exact (pow_m22_comm_l (transpose_m22 x) n').
Qed.

(* M) Solve Exercise 40 *)

Proposition ex40 :
  forall (n : nat),
    transpose_m22 (pow_m22_l (M22 1 1
                                  0 1) n) =
      M22 1 0
          n 1.
Proof.
  intro n.
  rewrite -> (about_pow_m22_l n).
  unfold transpose_m22.
  reflexivity.
Qed.
