(* week-10_about-resetting-the-accumulator.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 24 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

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
  (* Forall x n a : nat, power_alt_aux x n a = power_alt_aux x n 1 * a *)
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
(* forall n a : nat, add_alt_aux n a = add_alt_aux n 0 + a *)
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
    rewrite -> 2 nil_is_left_neutral_wrt_list_append.
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
  intro n.
  exact (about_fac_alt_aux n).
Qed.

(*
  We have been writing a collection of Eureka lemmas. But now this make_Eureka_lemma definition shows that all of the eureka lemmas we have written are an instance of the same idea .i.e they have the same structure. 

  The Eureka lemma also applies to the factorial function.

  It is expressible using make_Eureka_lemma.


  Here, we also exact (about_fac_alt_aux n) as the fac_alt_aux function requires that we supply the variable n. 

 *)

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
 intros t.
 exact (about_weight_alt_aux t).
Qed.

(* Same as factorial function: The eureka lemma was an instance of the make_Eureka_lemma *)

(* Whereas here, both the LHS and RHS are recursive. So naturally it is reasonable to reason about them using induction. Furthermore, we used the Eureka lemma from part a), so there is a connection with what we did. *)

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

(* Structuring proofs as programs *)

(* Theorem is a collolary of the lemma. It follows the structure of the program *) 

(*
  Conclusion: Exploit the structure of the problem at hand by structuring the proofs as the way the program is structured or vice versa. 
*)

(* ********** *)

(* end of week-10_about-resetting-the-accumulator.v *)

(* ********** *)

(* One goal of this lecture is to revisit the proof that
   at most one function satisfies the following specification.
*)

(* Notes about Exercise 12 *)

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

(* Exercise 14 *)

Property fours_and_fives_via_mathematical_induction :
  forall n : nat,
  exists a b : nat,
    12 + n = 4 * a + 5 * b.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + exists 3.
    exists 0.
    compute. (* the remaining goals are only computational steps *)
    reflexivity.
  + destruct IHn' as [a [b Hn']].
    case a as [ | a'].
    ++ rewrite -> (Nat.mul_0_r 4) in Hn'. 
       rewrite -> (Nat.add_0_l (5 * b)) in Hn'.
       case b as [ | [ | [ | b''']]].
       +++ rewrite -> (Nat.mul_0_r 5) in Hn'.
           Search (_ + _ = 0).
           Check (Plus.plus_is_O_stt 12 n').
           Check (Plus.plus_is_O_stt 12 n' Hn').
           assert (H_absurd := (Plus.plus_is_O_stt 12 n' Hn')).
           destruct H_absurd as [H_twelve_equals_zero H_n'_equals_zero].
           Search (S _ = _).
           discriminate H_twelve_equals_zero.
       +++ rewrite -> (Nat.mul_1_r 5) in Hn'.
           Search (_ + _ =  _).
           rewrite -> 5 plus_Sn_m in Hn'.
           Search (S _ = S _ -> _ = _).
           Check (Nat.succ_inj ((11 + n')) 4 Hn').
           assert (H1 := Nat.succ_inj ((S (S (S (S (7 + n')))))) 4 Hn').
           assert (H2 := Nat.succ_inj ((S (S (S (7 + n'))))) 3 H1).
           assert (H3 := Nat.succ_inj ((S (S (7 + n')))) 2 H2).
           assert (H4 := Nat.succ_inj ((S (7 + n'))) 1 H3).
           assert (H5 := Nat.succ_inj ((7 + n')) 0 H4).
           Check (Plus.plus_is_O_stt 7 n').
           assert (H_absurd := (Plus.plus_is_O_stt 7 n' H5)).
           destruct H_absurd as [H_seven_equals_zero H_n'_equals_zero].
           discriminate  H_seven_equals_zero.
       +++ rewrite -> (Nat.mul_comm 5 2) in Hn'.
           unfold Nat.mul in Hn'.
           rewrite -> 10 plus_Sn_m in Hn'.           
           rewrite -> (Nat.add_0_r 5) in Hn'.
           simpl (5 + 5) in Hn'.
           assert (H1 := Nat.succ_inj (S (S (S (S (S (S (S (S (S (2 + n')))))))))) 9 Hn').
           assert (H2 := Nat.succ_inj (S (S (S (S (S (S (S (S (2 + n'))))))))) 8 H1).
           assert (H3 := Nat.succ_inj (S (S (S (S (S (S (S (2 + n')))))))) 7 H2).
           assert (H4 := Nat.succ_inj (S (S (S (S (S (S (2 + n'))))))) 6 H3).
           assert (H5 := Nat.succ_inj (S (S (S (S (S (2 + n')))))) 5 H4).
           assert (H6 := Nat.succ_inj (S (S (S (S (2 + n'))))) 4 H5).
           assert (H7 := Nat.succ_inj (S (S (S (2 + n')))) 3 H6).
           assert (H8 := Nat.succ_inj (S (S (2 + n'))) 2 H7).
           assert (H9 := Nat.succ_inj (S (2 + n')) 1 H8).
           assert (H10 := Nat.succ_inj (2 + n') 0 H9).
           assert (H_absurd := (Plus.plus_is_O_stt 2 n' H10)).
           destruct H_absurd as [H_two_equals_zero H_n'_equals_zero].
           discriminate H_two_equals_zero.
       +++ exists 4.
           exists b'''.
           rewrite <-  Nat.add_succ_comm.
           rewrite -> plus_Sn_m.
           rewrite -> Hn'.
           Search (S _ + _ = S (_ + _)).
           rewrite <- 3 five_times_succ.
           rewrite <- (Nat.add_1_l (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (5 * b'''))))))))))))))))).
           rewrite <- 15 Nat.add_succ_comm.
           reflexivity.
    ++ exists a'.
       exists (S b).
       Search (S _ = _).
       rewrite <- (Nat.add_1_r n').
       rewrite -> Nat.add_assoc.
       rewrite -> Hn'.
       rewrite <- five_times_succ.
       rewrite <- four_times_succ.
       rewrite <- (Nat.add_assoc (S (S (S (S (4 * a'))))) (5 * b) 1).
       rewrite -> (Nat.add_comm (5 * b) 1).
       rewrite -> (Nat.add_assoc (S (S (S (S (4 * a'))))) 1 (5 * b)).
       rewrite -> (Nat.add_succ_comm (S (S (S (4 * a')))) 1).
       rewrite -> (Nat.add_succ_comm (S (S (4 * a'))) 2).
       rewrite -> (Nat.add_succ_comm (S (4 * a')) 3).
       rewrite -> (Nat.add_succ_comm (4 * a') 4).
       rewrite <- (Nat.add_1_l (S (S (S (S (5 * b)))))).
       rewrite <- (Nat.add_succ_comm 1 (S (S (S (5 * b))))).
       rewrite <- (Nat.add_succ_comm 2 (S (S (5 * b)))).
       rewrite <- (Nat.add_succ_comm 3 (S (5 * b))).
       rewrite <- (Nat.add_succ_comm 4 (5 * b)).
       rewrite -> (Nat.add_assoc (4 * a') 5 (5 * b)).
       reflexivity.
Qed.

(* ********** *)

(* end of week-10_induction-principles.v *)

(* Exercise 25 *) 

Notation "A =b= B" :=
  (Bool.eqb A B) (at level 70, right associativity).

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
  intro n.
  induction n as [ | n' IHn'].
  + rewrite -> (Nat.mul_0_r 2).
    rewrite -> (Nat.mul_1_r 2).
    reflexivity.
  + Search (_ * S _ = _).
    rewrite -> 2 Nat.mul_succ_r.
    rewrite <- IHn'.
    rewrite -> 2 Nat.add_succ_l.
    reflexivity.
Qed.

Lemma twice :
  forall n : nat,
    n + n = 2 * n.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + rewrite -> Nat.mul_0_r.
    reflexivity.
  + Search (_ * S _ = _).
    rewrite -> Nat.mul_succ_r.
    rewrite <- IHn'.
    Search (_ + _ = S ( _ + _)).
    rewrite -> 3 Nat.add_succ_r.
    rewrite -> Nat.add_0_r.
    reflexivity.
Qed.

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

(* week-10_mutual-induction-and-recursion.v *)
