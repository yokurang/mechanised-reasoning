(* week-09_formalizing-two-by-two-matrices.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 17 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** Week 09 ********** *)

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

(* Prove the same for the tail-recursive version of fib *)

Lemma about_fix_aux_and_fib'' :
  forall (m i : nat),
    fib_aux m (fib' i) (fib' (S i)) = fib' (m + i).
Proof.
  intro m.
  induction m as [ | m' IHm'].
  + intro i.
    rewrite -> fold_unfold_fib_aux_O.
    rewrite -> Nat.add_0_l.
    reflexivity.
  + intro i.
    rewrite -> fold_unfold_fib_aux_S.
    Search (_ + _  = _ + _).
    rewrite -> (Nat.add_comm (fib' i) (fib' (S i))).
    rewrite <- fold_unfold_fib'_SS.
    rewrite -> (IHm' (S i)).
    rewrite <- plus_n_Sm.
    rewrite -> plus_Sn_m.
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

(* ********** Week 10 ********** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

(* ********** *)

Definition make_Eureka_lemma (A : Type) (id_A : A) (combine_A : A -> A -> A) (c : A -> A) (a : A) : Prop :=
  c a = combine_A (c id_A) a.

(* ********** *)

Fixpoint power_alt_aux (x n a : nat) : nat :=
  match n with
    O =>
    a
  | S n' =>
    power_alt_aux x n' (x * a)
  end.

Definition power_alt (x n : nat) : nat :=
  power_alt_aux x n 1.

Lemma fold_unfold_power_alt_aux_O :
  forall x a : nat,
    power_alt_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic power_alt_aux.
Qed.

Lemma fold_unfold_power_alt_aux_S :
  forall x n' a : nat,
    power_alt_aux x (S n') a =
    power_alt_aux x n' (x * a).
Proof.
  fold_unfold_tactic power_alt_aux.
Qed.

Check (make_Eureka_lemma nat).
Check (make_Eureka_lemma nat 1).
Check (make_Eureka_lemma nat 1).
Check (make_Eureka_lemma nat 1 Nat.mul).
Check (forall x n a : nat, make_Eureka_lemma nat 1 Nat.mul (power_alt_aux x n) a).


Lemma about_power_alt_aux :
  forall x n a : nat,
    make_Eureka_lemma nat 1 Nat.mul (power_alt_aux x n) a.
Proof.
  unfold make_Eureka_lemma.
  intros x n.
  induction n as [ | n' IHn'].
  + intro a.
    rewrite -> 2 fold_unfold_power_alt_aux_O.
    rewrite -> Nat.mul_1_l.
    reflexivity.
  + intro a.
    rewrite -> 2 fold_unfold_power_alt_aux_S.
    rewrite -> (IHn' (x * a)).
    rewrite -> (IHn' (x * 1)).
    rewrite -> Nat.mul_1_r.
    rewrite -> Nat.mul_assoc.
    reflexivity.
Qed.    

(* ********** *)

Fixpoint add_alt_aux (n a : nat) : nat :=
  match n with
    O =>
    a
  | S n' =>
    add_alt_aux n' (S a)
  end.

Lemma fold_unfold_add_alt_aux_O :
  forall (a : nat),
    add_alt_aux 0 a = a.
Proof.
  fold_unfold_tactic add_alt_aux.
Qed.
    
Lemma fold_unfold_add_alt_aux_S :
  forall (n' a : nat),
    add_alt_aux (S n') a = add_alt_aux n' (S a).
Proof.
  fold_unfold_tactic add_alt_aux.
Qed.

Definition add_alt (n m : nat) : nat :=
  add_alt_aux n m.

Lemma about_add_alt_aux :
  forall n a : nat,
    make_Eureka_lemma nat 0 Nat.add (add_alt_aux n) a.
Proof.
  unfold make_Eureka_lemma.
  intro n.
  induction n as [ | n' IHn'].
  + intro a.
    rewrite -> 2 fold_unfold_add_alt_aux_O.
    rewrite -> Nat.add_0_l.
    reflexivity.
  + intro a.
    rewrite -> 2 fold_unfold_add_alt_aux_S.
    rewrite -> (IHn' (S a)).
    rewrite -> (IHn' 1).
    Search (1 + _ = S _).
    rewrite <- Nat.add_1_l.
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.

(* ********** *)

(* Exercise 01 *)

Fixpoint length_alt_aux (V : Type) (vs : list V) (a : nat) : nat :=
  match vs with
    nil =>
    a
  | v :: vs' =>
    length_alt_aux V vs' (S a)
  end.

Lemma fold_unfold_length_alt_aux_nil :
  forall (V : Type)
         (a : nat),
      length_alt_aux V nil a = a.
Proof.
  fold_unfold_tactic length_alt_aux.
Qed.

Lemma fold_unfold_length_alt_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (a : nat),
    length_alt_aux V (v :: vs') a = length_alt_aux V vs' (S a).
Proof.
  fold_unfold_tactic length_alt_aux.
Qed.

Definition length_alt (V : Type) (vs : list V) : nat :=
  length_alt_aux V vs 0.


Check (forall (V : Type) (vs : list V) (a : nat), make_Eureka_lemma nat 0 Nat.add (length_alt_aux V vs) a).

Lemma about_length_alt_aux :
  forall (V : Type) (vs : list V) (a : nat),
    make_Eureka_lemma nat 0 Nat.add (length_alt_aux V vs) a.
Proof.
  unfold make_Eureka_lemma.
  intros V vs.
  induction vs as [n | v vs' IHvs'].
  + intro a.
    rewrite -> 2 fold_unfold_length_alt_aux_nil.
    rewrite -> Nat.add_0_l.
    reflexivity.
  + intro a.
    rewrite -> 2 fold_unfold_length_alt_aux_cons.
    rewrite -> (IHvs' (S a)).
    rewrite -> (IHvs' 1).
    rewrite <- Nat.add_1_l.
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.

(* ********** *)

(* Exercise 02 *)

Definition test_list_append (candidate : forall V : Type, list V -> list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil) nil ) (1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil) nil) (true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: nil) (1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: nil) (true :: nil)) (false :: true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (3 :: nil) (2 :: 1 :: nil)) (3 :: 2 :: 1 :: nil)) &&
    (eqb_list bool Bool.eqb (candidate bool (true :: nil) (false :: true :: nil)) (true :: false :: true :: nil)) &&
(eqb_list nat Nat.eqb (candidate nat (4 :: 3 :: nil) (2 :: 1 :: nil)) (candidate nat (4 :: nil) (3 :: 2 :: 1 :: nil))).

Fixpoint list_append (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
    nil =>
    v2s
  | v1 :: v1s' =>
    v1 :: list_append V v1s' v2s
  end.

Compute (test_list_append list_append).

Lemma fold_unfold_list_append_nil :
  forall (V : Type)
         (v2s : list V),
    list_append V nil v2s = v2s.
Proof.
  fold_unfold_tactic list_append.
Qed.

Lemma fold_unfold_list_append_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    list_append V (v1 :: v1s') v2s = v1 :: (list_append V v1s' v2s).
Proof.
  fold_unfold_tactic list_append.
Qed.

Fixpoint reverse_alt_aux (V : Type) (vs a : list V) : list V :=
  match vs with
    nil =>
    a
  | v :: vs' =>
    reverse_alt_aux V vs' (v :: a)
  end.

Lemma fold_unfold_reverse_alt_aux_nil :
  forall (V : Type)
         (a : list V),
    reverse_alt_aux V nil a = a.
Proof.
   fold_unfold_tactic reverse_alt_aux.
Qed.

Lemma fold_unfold_reverse_alt_aux_cons :
  forall (V : Type)
         (v : V)
         (vs a : list V),
    reverse_alt_aux V (v :: vs) a = reverse_alt_aux  V vs (v :: a).
Proof.
  fold_unfold_tactic reverse_alt_aux.
Qed.

Definition reverse_alt (V : Type) (vs : list V) : list V :=
  reverse_alt_aux V vs nil.

Definition test_list_reverse (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
    (eqb_list bool Bool.eqb (candidate bool nil) nil) &&
    (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) (1 :: nil))  &&
    (eqb_list bool Bool.eqb (candidate bool (true :: nil)) (true :: nil)) &&
    (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil)) (1 :: 2 :: nil)) &&
    (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil)) (true :: false :: nil)) &&
    (eqb_list nat Nat.eqb (candidate nat (3 :: 2 :: 1 :: nil)) (1 :: 2 :: 3 :: nil)) &&
    (eqb_list bool Bool.eqb (candidate bool (true :: false :: true :: nil)) (true :: false :: true :: nil)) &&
    (eqb_list nat Nat.eqb (candidate nat (3 :: 2 :: 1 :: nil)) (list_append nat (candidate nat (2 :: 1 :: nil)) (3 :: nil))).

Compute (test_list_reverse reverse_alt).

Check (forall (V : Type) (vs a : list V), make_Eureka_lemma (list V) vs (list_append V) (reverse_alt_aux V vs) a).

Proposition nil_is_right_neutral_wrt_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V vs nil = vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  + rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  + rewrite -> fold_unfold_list_append_cons.
    rewrite -> IHvs'.
  reflexivity.
Qed.

Proposition nil_is_left_neutral_wrt_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V nil vs = vs.
Proof.
  intros V vs.
  rewrite -> (fold_unfold_list_append_nil V vs).
  reflexivity.
Qed.

Lemma about_list_append_cons :
  forall (V : Type)
         (v2 : V)
         (v1s v2s' : list V),
    list_append V v1s (v2 :: v2s') = list_append V (list_append V v1s (v2 :: nil)) v2s'.
Proof.
  intros V v2 v1s v2s'.
  revert v2.
  induction v1s as [ | v1 v1s' IHv1s'].
  + intro v2.
    rewrite -> nil_is_left_neutral_wrt_list_append.
    rewrite -> fold_unfold_list_append_nil.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> nil_is_left_neutral_wrt_list_append.
    reflexivity.
  + intro v2.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> (IHv1s' v2).
    rewrite -> 2 fold_unfold_list_append_cons.
    reflexivity.
Qed.
    
Lemma about_reverse_alt_aux :
  forall (V : Type) (vs a : list V),
    make_Eureka_lemma (list V) nil (list_append V) (reverse_alt_aux V vs) a.
Proof.
  unfold make_Eureka_lemma.
  intros V vs.
  induction vs as [n | v vs' IHvs'].
  + intro a.
    rewrite -> 2 fold_unfold_reverse_alt_aux_nil.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  + intro a.
    rewrite -> 2 fold_unfold_reverse_alt_aux_cons.
    rewrite -> (IHvs' (v :: a)).
    rewrite -> about_list_append_cons.
    rewrite -> (IHvs' (v :: nil)).
    reflexivity.
Qed.  

(* ********** *)

(* Exercise 04 *)

Fixpoint fac_alt_aux (n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    fac_alt_aux n' (S n' * a)
  end.

Definition fac_alt (n : nat) : nat :=
  fac_alt_aux n 1.

Lemma fold_unfold_fac_alt_aux_O :
  forall a : nat,
    fac_alt_aux 0 a =
    a.
Proof.
  fold_unfold_tactic fac_alt_aux.
Qed.

Lemma fold_unfold_fac_alt_aux_S :
  forall n' a : nat,
    fac_alt_aux (S n') a =
    fac_alt_aux n' (S n' * a).
Proof.
  fold_unfold_tactic fac_alt_aux.
Qed.

Check (make_Eureka_lemma nat).
Check (make_Eureka_lemma nat 1 Nat.mul).
Check (forall n a : nat, make_Eureka_lemma nat 1 Nat.mul (fac_alt_aux n) a).


Lemma about_fac_alt_aux :
  forall n a : nat,
    fac_alt_aux n a = fac_alt_aux n 1 * a.
Proof.
  intro n.
  induction n as [ | n' IHn'].
    + intro a.
    rewrite -> 2 fold_unfold_fac_alt_aux_O.
    rewrite -> Nat.mul_1_l.
    reflexivity.
  + intro a.
    rewrite -> 2 fold_unfold_fac_alt_aux_S.
    rewrite -> (IHn' (S n' * a)).
    rewrite -> (IHn' (S n' * 1)).
    rewrite -> Nat.mul_1_r.
    rewrite -> Nat.mul_assoc.
    reflexivity.
Qed.

Lemma about_fac_alt_aux' :
  forall n a : nat,
    make_Eureka_lemma nat 1 Nat.mul (fac_alt_aux n) a.
Proof.
  unfold make_Eureka_lemma.
  intros n a.
  exact (about_fac_alt_aux n a).
Qed.

(* ********** *)

(* Exercise 05 *)

Inductive binary_tree : Type :=
| Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

(* ***** *)

Fixpoint weight (t : binary_tree) : nat :=
  match t with
  | Leaf n =>
    n
  | Node t1 t2 =>
    weight t1 + weight t2
  end.

Lemma fold_unfold_weight_Leaf :
  forall n : nat,
    weight (Leaf n) = n.
Proof.
  fold_unfold_tactic weight.
Qed.

Lemma fold_unfold_weight_Node :
  forall t1 t2 : binary_tree,
    weight (Node t1 t2) = weight t1 + weight t2.
Proof.
  fold_unfold_tactic weight.
Qed.

(* ***** *)

Fixpoint weight_alt_aux (t : binary_tree) (a : nat) : nat :=
  match t with
  | Leaf n =>
    n + a
  | Node t1 t2 =>
    weight_alt_aux t1 (weight_alt_aux t2 a)
  end.

Definition weight_alt (t : binary_tree) : nat :=
  weight_alt_aux t 0.

Lemma fold_unfold_weight_alt_aux_Leaf :
  forall n a : nat,
    weight_alt_aux (Leaf n) a = n + a.
Proof.
  fold_unfold_tactic weight_alt_aux.
Qed.

Lemma fold_unfold_weight_alt_aux_Node :
  forall (t1 t2 : binary_tree)
         (a : nat),
    weight_alt_aux (Node t1 t2) a = weight_alt_aux t1 (weight_alt_aux t2 a).
Proof.
  fold_unfold_tactic weight_alt_aux.
Qed.

(* ***** *)

Check (forall (t : binary_tree) (a : nat), make_Eureka_lemma nat 0 Nat.add (weight_alt_aux t) a).


Lemma about_weight_alt_aux :
  forall (t : binary_tree)
         (a : nat),
    weight_alt_aux t a = weight_alt_aux t 0 + a.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].
  + intro a.
    rewrite -> (fold_unfold_weight_alt_aux_Leaf n a).
    rewrite -> (fold_unfold_weight_alt_aux_Leaf n 0).
    Search (_ + _ + _ = _ + _ + _).
    rewrite -> Nat.add_shuffle0.
    rewrite -> (Nat.add_0_r (n + a)).
    reflexivity.
  + intro a.
    rewrite -> 2 fold_unfold_weight_alt_aux_Node.
    rewrite -> (IHt1 (weight_alt_aux t2 a)).
    rewrite -> (IHt1 (weight_alt_aux t2 0)).
    rewrite -> (IHt2 a).
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.

Lemma about_weight_alt_aux' :
  forall (t : binary_tree)
         (a : nat),
    make_Eureka_lemma nat 0 Nat.add (weight_alt_aux t) a.
Proof.
 intros t a.
 exact (about_weight_alt_aux t a).
Qed.

Lemma about_weight_and_weight_alt_aux : 
  forall (t : binary_tree),
    weight t = weight_alt_aux t 0.
Proof.  
  intro t.
  Check (about_weight_alt_aux t 0).
  induction t as [n | t1 IHt1 t2 IHt2].
  + rewrite -> fold_unfold_weight_Leaf.
    rewrite -> fold_unfold_weight_alt_aux_Leaf.
    rewrite -> Nat.add_0_r.
    reflexivity.
  + rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_weight_alt_aux_Node.
    rewrite -> about_weight_alt_aux.
    rewrite <- IHt1.
    rewrite <- IHt2.
    reflexivity.
Qed.

Theorem weight_and_weight_alt_are_equivalent :
  forall t : binary_tree,
    weight t = weight_alt t.
Proof.
  unfold weight_alt.
  intro t.
  exact (about_weight_and_weight_alt_aux t).
Qed.


(* ********** *)

(* end of week-10_about-resetting-the-accumulator.v *)

(* alan.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 23 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Fixpoint nat_parafold_right (V : Type) (zero_case : V) (succ_case : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    zero_case
  | S n' =>
    succ_case n' (nat_parafold_right V zero_case succ_case n')
  end.

Lemma fold_unfold_nat_parafold_right_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V),
    nat_parafold_right V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

Lemma fold_unfold_nat_parafold_right_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V)
         (n' : nat),
    nat_parafold_right V zero_case succ_case (S n') =
    succ_case n' (nat_parafold_right V zero_case succ_case n').
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

(* ***** *)

Fixpoint nat_parafold_left (V : Type) (zero_case : V) (succ_case : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    zero_case
  | S n' =>
    nat_parafold_left V (succ_case n' zero_case) succ_case n'
  end.

Lemma fold_unfold_nat_parafold_left_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V),
    nat_parafold_left V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

Lemma fold_unfold_nat_parafold_left_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V)
         (n' : nat),
    nat_parafold_left V zero_case succ_case (S n') =
    nat_parafold_left V (succ_case n' zero_case) succ_case n'.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

(* ********** *)

Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (w : W),
    op2 v1 (op2 v2 w) = op2 v2 (op2 v1 w).

Lemma about_nat_para_folding_left_and_right_for_para_left :
  forall (W : Type)
         (zero_case : W)
         (succ_case : nat -> W -> W),
    is_left_permutative nat W succ_case ->
    forall (n x : nat),
      nat_parafold_left W (succ_case x zero_case) succ_case n =
        succ_case x (nat_parafold_left W zero_case succ_case n).
Proof.
  intros W zero_case succ_case lp n.
  revert zero_case.
  induction n as [ | n' IHn'].
  + intros zero_case x.
    rewrite -> 2 fold_unfold_nat_parafold_left_O.
    reflexivity.
  + intros zero_case x.
    rewrite -> 2 fold_unfold_nat_parafold_left_S.
    unfold is_left_permutative in lp.
    rewrite -> lp.
    rewrite -> (IHn' (succ_case n' zero_case)).
    reflexivity.
Qed.

Lemma about_nat_para_folding_left_and_right_for_para_right :
  forall (W : Type)
         (zero_case : W)
         (succ_case : nat -> W -> W),
    is_left_permutative nat W succ_case ->
    forall (n x : nat),
    nat_parafold_right W (succ_case x zero_case) succ_case n =
      succ_case x (nat_parafold_right W zero_case succ_case n).
Proof.
  intros W zero_case succ_case lp n.
  revert zero_case.
  induction n as [ | n' IHn'].
  + intros zero_case x.
    rewrite -> 2 fold_unfold_nat_parafold_right_O.
    reflexivity.
  + intros zero_case x.
    rewrite -> 2 fold_unfold_nat_parafold_right_S.
    unfold is_left_permutative in lp.
    rewrite -> lp.
    rewrite -> (IHn' zero_case x).
    reflexivity.
Qed.
                   
Theorem parafolding_left_and_right_over_nats :
  forall (W : Type)
         (succ_case : nat -> W -> W),
    is_left_permutative nat W succ_case ->
    forall (zero_case : W)
           (n : nat),
      nat_parafold_left  W zero_case succ_case n =
      nat_parafold_right W zero_case succ_case n.
Proof.
    intros W succ_case nat_left_permutes zero_case n.
    unfold is_left_permutative in nat_left_permutes.
    revert zero_case.
    induction n as [ | n' IHn'].
  + intro zero_case.
    rewrite -> (fold_unfold_nat_parafold_left_O W zero_case succ_case).
    rewrite -> (fold_unfold_nat_parafold_right_O W zero_case succ_case).
    reflexivity.
  + intro zero_case.
    rewrite -> (fold_unfold_nat_parafold_left_S W zero_case succ_case n').
    rewrite -> (fold_unfold_nat_parafold_right_S W zero_case succ_case n').
    rewrite -> (IHn' (succ_case n' zero_case)).
    Check (about_nat_para_folding_left_and_right_for_para_right W zero_case succ_case nat_left_permutes n' n').
    exact (about_nat_para_folding_left_and_right_for_para_right W zero_case succ_case nat_left_permutes n' n').
Qed.

Theorem parafolding_left_and_right_over_nats_converse_base :
  forall (W : Type)
         (succ_case : nat -> W -> W),
    (forall (zero_case : W),
        nat_parafold_left  W zero_case succ_case 2 =
        nat_parafold_right W zero_case succ_case 2) ->
    forall w : W,
      succ_case 1 (succ_case 0 w ) = succ_case 0 (succ_case 1 w).
Proof.
  intros W succ_case H_fold w.
  assert (H_key := H_fold w).
  rewrite -> 2 fold_unfold_nat_parafold_left_S in H_key.
  rewrite -> 2 fold_unfold_nat_parafold_right_S in H_key.
  rewrite -> fold_unfold_nat_parafold_left_O in H_key.
  rewrite -> fold_unfold_nat_parafold_right_O in H_key.
  rewrite -> H_key.
  reflexivity.
Qed.

Theorem parafolding_left_and_right_over_nats_converse_base' :
  forall (W : Type)
         (succ_case : nat -> W -> W),
    (forall (zero_case : W),
        nat_parafold_left  W zero_case succ_case 3 =
        nat_parafold_right W zero_case succ_case 3) ->
    forall w : W,
      succ_case 2 (succ_case 1 w ) = succ_case 1 (succ_case 2 w).
Proof.
  intros W succ_case H_fold w.
  assert (H_key := H_fold w).
  rewrite -> 3 fold_unfold_nat_parafold_left_S in H_key.
  rewrite -> 3 fold_unfold_nat_parafold_right_S in H_key.
  rewrite -> fold_unfold_nat_parafold_left_O in H_key.
  rewrite -> fold_unfold_nat_parafold_right_O in H_key.
Admitted.

Theorem parafolding_left_and_right_over_nats_converse_base'' :
  forall (W : Type)
         (succ_case : nat -> W -> W),
    (forall (zero_case : W),
        nat_parafold_left  W zero_case succ_case 4 =
        nat_parafold_right W zero_case succ_case 4) ->
    forall w : W,
      succ_case 3 (succ_case 2 w ) = succ_case 2 (succ_case 3 w).
Proof.
  intros W succ_case H_fold w.
  assert (H_key := H_fold w).
  rewrite -> 4 fold_unfold_nat_parafold_left_S in H_key.
  rewrite -> 4 fold_unfold_nat_parafold_right_S in H_key.
  rewrite -> fold_unfold_nat_parafold_left_O in H_key.
  rewrite -> fold_unfold_nat_parafold_right_O in H_key.
Admitted.

Theorem parafolding_left_and_right_over_nats_converse :
  forall (W : Type)
         (succ_case : nat -> W -> W),
    (forall (zero_case : W)
            (n : nat),
        nat_parafold_left  W zero_case succ_case n =
        nat_parafold_right W zero_case succ_case n) ->
    is_left_permutative nat W succ_case.
Proof.
  unfold is_left_permutative.
  intros W succ_case H_npl_equals_npr.
  intros v1 v2 w.
  Check (H_npl_equals_npr w).
  assert (H_tmp := H_npl_equals_npr w 2).
  rewrite -> 2 fold_unfold_nat_parafold_left_S in H_tmp.
  rewrite -> 2 fold_unfold_nat_parafold_right_S in H_tmp.
  rewrite -> fold_unfold_nat_parafold_left_O in H_tmp.
  rewrite -> fold_unfold_nat_parafold_right_O in H_tmp.
       
(*
  nat_parafold_left W w succ_case (n - 0) =
  nat_parafold_left W (succ_case (n - 1 w) succ_case (n - 1) =
  nat_parafold_left W (succ_case (n - 2) (succ_case (n - 1) w)) succ_case (n - 2)
  nat_parafold_left W (succ_case (n - 3) (succ_case (n - 2) (succ_case (n - 1) w))) succ_case (n - 3)
  nat_parafold_left W (succ_case (n - 4) (succ_case (n - 3) (succ_case (n - 2) (succ_case (n - 1) w)))) succ_case (n - 4)
 *)
  
Admitted.

(* ********** *)

Fixpoint list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right V W nil_case cons_case vs')
  end.

Lemma fold_unfold_list_fold_right_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_right V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_right_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_right V W nil_case cons_case (v :: vs') =
    cons_case v (list_fold_right V W nil_case cons_case vs').
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

(* ***** *)

Fixpoint list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left V W (cons_case v nil_case) cons_case vs'
  end.

Lemma fold_unfold_list_fold_left_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_left V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

Lemma fold_unfold_list_fold_left_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_left V W nil_case cons_case (v :: vs') =
    list_fold_left V W (cons_case v nil_case) cons_case vs'.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

(* ***** *)

Theorem folding_left_and_right_converse :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    (forall (nil_case : W)
            (vs : list V),
        list_fold_left  V W nil_case cons_case vs =
        list_fold_right V W nil_case cons_case vs) ->
    is_left_permutative V W cons_case.
Proof.
  unfold is_left_permutative.
  intros V W cons_case H_lfl_equals_lfr.
  intros v1 v2 w.
  Check (H_lfl_equals_lfr w).
  Check (H_lfl_equals_lfr w (v1 :: v2 :: nil)).
  assert (H_tmp := H_lfl_equals_lfr w (v1 :: v2 :: nil)).
  rewrite -> 2 fold_unfold_list_fold_left_cons in H_tmp.
  rewrite -> 2 fold_unfold_list_fold_right_cons in H_tmp.
  rewrite -> fold_unfold_list_fold_left_nil in H_tmp.
  rewrite -> fold_unfold_list_fold_right_nil in H_tmp.
  rewrite -> H_tmp.
  reflexivity.
Qed.
(* ********** *)

(* end of alan.v *)
