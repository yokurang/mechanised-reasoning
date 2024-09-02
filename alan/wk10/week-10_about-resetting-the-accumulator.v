(* week-10_about-resetting-the-accumulator.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 24 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

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

(* Exercise 03 *)

Fixpoint list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
    nil =>
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

Check(make_Eureka_lemma nat 0 Nat.add (add_alt_aux 0) 0).

Lemma about_list_fold_left :
  forall (V W : Type)
         (cons_case : V -> W -> W)
         (vs : list V)
         (h : W -> W),
    make_Eureka_lemma (W -> W) (fun a : W => a) (fun f g x => g (f x))
      (fun h =>  list_fold_left V (W -> W) h
                   (fun (v0 : V) (ih : W -> W) (a : W) => ih (cons_case v0 a)) vs) h.
Proof.
  unfold make_Eureka_lemma.
  intros V W cons_case vs.
  induction vs as [ | v vs' IHvs'].
  + intro h.
    rewrite -> 2 fold_unfold_list_fold_left_nil.
    reflexivity.
  + intro h.
    rewrite -> 2 fold_unfold_list_fold_left_cons.
    rewrite -> (IHvs' (fun a : W => h (cons_case v a))).
    rewrite -> (IHvs' (fun a : W => cons_case v a)).
    reflexivity.
Qed.

(*
Lemma about_list_fold_left :
*)

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

(*
  We have been writing a collection of Eureka lemmas. But now this make_Eureka_lemma definition shows that all of the eureka lemmas we have written are an instance of the same idea .i.e they have the same structure. 

  The Eureka lemma also applies to the factorial function.

  It is expressible using make_Eureka_lemma.
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
 intros t a.
 exact (about_weight_alt_aux t a).
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
