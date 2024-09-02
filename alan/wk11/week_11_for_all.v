(* week-11_for-all-there-exists.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 30 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Check nat_ind.
Check nat_rect.
Print nat_rect.

(* ********** *)

Definition test_fac (candidate : nat -> nat) : bool :=
  (candidate 0 =? 1) && (candidate 1 =? 1) && (candidate 2 =? 2) && (candidate 3 =? 6) && (candidate 4 =? 24) && (candidate 5 =? 120).

Definition fac_rect (n : nat) : nat :=
  nat_rect
    (fun _ : nat => nat)
    1
    (fun i' ih =>
       S i' * ih)
    n.

Compute (test_fac fac_rect).

Definition fac_acc_rect (n : nat) : nat :=
  nat_rect
    (fun _ : nat => nat -> nat)
    (fun a => a)
    (fun i' ih a =>
       ih (S i' * a))
    n
    1.

Compute (test_fac fac_acc_rect).

(* ********** *)

Definition nat_parafold_right (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  let fix visit n :=
    match n with
    | O    => z
    | S n' => s n' (visit n')
    end
  in visit n.

Definition nat_parafold_right_rect (V : Type) (z : V) (s : nat -> V -> V) (n : nat) : V :=
  nat_rect (fun (_ : nat) => V) z s n.

(* ***** *)

Definition nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  let fix visit n :=
    match n with
    | O    => z
    | S n' => s (visit n')
    end
  in visit n.

Definition nat_fold_right_rect (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  nat_rect (fun (_ : nat) => V) z (fun _ ih => s ih) n.

(* ***** *)

Definition nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  let fix visit n a :=
    match n with
    | O    => a
    | S n' => visit n' (s a)
    end
  in visit n z.

(* ********** *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
 match ov1 with
 | Some v1 =>
   match ov2 with
     | Some v2 =>
       eqb_V v1 v2
     | None =>
       false
   end
 | None =>
   match ov2 with
     | Some v2 =>
       false
     | None =>
       true
   end
 end.

Definition eqb_pair (V : Type) (eqb_V : V -> V -> bool) (W : Type) (eqb_W : W -> W -> bool) (p1 p2 : V * W) : bool :=
 match p1 with
 | (v1, w1)  =>
   match p2 with
     | (v2, w2) =>
       eqb_V v1 v2 && eqb_W w1 w2
   end
 end.

Definition eqb_nat := Nat.eqb.

(* ********** *)

Definition test_quorem (candidate : nat -> nat -> option (nat * nat)) :=
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 10 0) None) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 0 3) (Some (0, 0))) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 1 3) (Some (0, 1))) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 2 3) (Some (0, 2))) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 3 3) (Some (1, 0))) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 4 3) (Some (1, 1))) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 5 3) (Some (1, 2))) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate 6 3) (Some (2, 0))) &&
  (eqb_option (nat * nat) (eqb_pair nat Nat.eqb nat Nat.eqb) (candidate (5 * 4 + 3) 4) (Some (5, 3))).

(* ***** *)

Definition quorem_Sd'_rect (d' n : nat) : nat * nat :=
  nat_rect
    (fun (_ : nat) => (nat * nat)%type)
    (0, 0)
    (fun _ ih =>
       let (q, r) := ih
       in if r <? d'
          then (q, S r)
          else (S q, 0))
    n.

Definition quorem_rect (n d : nat) : option (nat * nat) :=
  match d with
  | 0 =>
    None
  | S d' =>
    Some (quorem_Sd'_rect d' n)
  end.

Compute (test_quorem quorem_rect).

(* ***** *)

Definition quorem_Sd'_right (d' n : nat) : nat * nat :=
  nat_fold_right
    (nat * nat)
    (0, 0)
    (fun ih =>
       let (q, r) := ih
       in if r <? d'
          then (q, S r)
          else (S q, 0))
    n.

Definition quorem_right (n d : nat) : option (nat * nat) :=
  match d with
  | O =>
    None
  | S d' =>
    Some (quorem_Sd'_right d' n)
  end.

Compute (test_quorem quorem_right).

(* ***** *)

Definition quorem_Sd'_left (d' n : nat) : nat * nat :=
  nat_fold_left
    (nat * nat)
    (0, 0)
    (fun ih =>
       let (q, r) := ih
       in if r <? d'
          then (q, S r)
          else (S q, 0))
    n.

Definition quorem_left (n d : nat) : option (nat * nat) :=
  match d with
  | O =>
    None
  | S d' =>
    Some (quorem_Sd'_left d' n)
  end.

Compute (test_quorem quorem_left).

(* ***** *)

Definition quorem_iterative (n d : nat) : option (nat * nat) :=
  match d with
  | O =>
    None
  | S d' =>
    Some (let fix visit n q r :=
            match n with
            | O =>
              (q, r)
            | S n' =>
              if r <? d'
              then visit n' q (S r)
              else visit n' (S q) 0
            end
          in visit n 0 0)
  end.

Compute (test_quorem quorem_iterative).

(* ********** *)

Definition specification_of_Fibonacci_function (fib : nat -> nat) :=
  (fib 0 = 0)
  /\
  (fib 1 = 1)
  /\
  (forall n : nat,
      fib (S (S n)) = fib n + fib (S n)).

Lemma about_fib_fib :
  forall fib : nat -> nat,
    specification_of_Fibonacci_function fib ->
    forall n : nat,
      exists fib_n fib_Sn : nat,
        fib_n = fib n /\ fib_Sn = fib (S n).
Proof.
  intros fib [F0 [F1 FSS]] n.
  induction n as [ | n' IHn'].
  - exists 0, 1.
    exact (conj (eq_sym F0) (eq_sym F1)).
  - destruct IHn' as [fib_n' [fib_Sn' [Fn' FSn']]].
    exists fib_Sn', (fib_n' + fib_Sn').
    rewrite -> Fn'.
    rewrite -> FSn' at 2.
    exact (conj FSn' (eq_sym (FSS n'))).
Qed.

(*
Definition fibfib_rect (n : nat) : nat * nat :=
  nat_rect
    ...
*)

(* ********** *)

Definition test_subtract (candidate : nat -> nat -> nat) :=
  ((candidate 10 3) =? 7).

Lemma about_subtracting :
  forall i j : nat,
    j <= i ->
    exists k : nat,
      i = j + k.
Proof.
  intros i j.
  intro le_j_i.
  induction i as [| i' IHi'].
  - exists 0.
    Check (_ <= 0).
    rewrite Nat.add_0_r.
    symmetry.
    Check (_ < _).
    Check Nat.le_0_r.
    rewrite Nat.le_0_r in le_j_i.
    exact le_j_i.
  -   

Restart.

  intros i.
  induction i as [| i' IHi']; intros j lt_j.
  - exists 0.
    Check (_ <= 0).
    rewrite Nat.add_0_r.
    symmetry.
    Check (_ < _).
    Check Nat.le_0_r.
    rewrite Nat.le_0_r in lt_j.
    exact lt_j.
  - Check (le_lt_or_eq j (S i') lt_j). 
    destruct (le_lt_or_eq j (S i') lt_j) as [lt_j_S_i' | eq_j_S_i'].
    -- Search ( _ <= _ -> _ < _ ).  
       assert (lt_eq_j := lt_n_Sm_le j i' lt_j_S_i').
       destruct (IHi' j lt_eq_j).
       
Abort.


Definition subtract_rect (i j : nat) : nat :=
  nat_rect
    (fun (_ : nat) => nat)
    0
    (fun i' k =>
         if j <? (S i')
         then S k
         else 0)
    i. 

Compute (test_subtract subtract_rect).

(*
Compute (subtract 3 10).
yields 3 but the input does not abide by the assumption.
*)

(* ********** *)

Lemma twice_S :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
Admitted.

Lemma even_or_odd :
  forall n : nat,
    exists q : nat,
      n = 2 * q \/ n = S (2 * q).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  - exists 0.
    rewrite -> Nat.mul_0_r.
    left.
    reflexivity.
  - destruct IHn' as [q [H_q | H_q]].
    + rewrite -> H_q.
      exists q.
      right.
      reflexivity.
    + rewrite -> H_q.
      rewrite -> twice_S.
      exists (S q).
      left.
      reflexivity.
  Show Proof.
Qed.

Definition test_half_once (candidate : nat -> nat) (n : nat) : bool :=
  let q := candidate n
  in (2 * q =? n) || (S (2 * q) =? n).
  
Definition test_half (candidate : nat -> nat) :=
  (test_half_once candidate 0) && (test_half_once candidate 1) && (test_half_once candidate 2) && (test_half_once candidate 3) && (test_half_once candidate 10) && (test_half_once candidate 13).

Inductive left_or_right : Type :=
  | Left  : nat -> left_or_right
  | Right : nat -> left_or_right.


(* Definition half_rect (n : nat) : nat := *)
(*   match nat_rect *)
(*           (fun _ : nat => left_or_right) *)
(*           ... *)
(*           ... *)
(*           n with *)
(*   | Left q => *)
(*     q *)
(*   | Right q => *)
(*     q *)
(*   end. *)

Definition half_rect (n : nat) : nat :=
  match nat_rect
          (fun _ : nat => left_or_right)  
          (Left 0)                        
          (fun _ ih =>                   
             match ih with
             | Left q =>
                 Right q          
             | Right q =>
                 Left (S q)      
             end)
          n
  with
  | Left q =>
      q
  | Right q =>
      q
  end.

Compute (test_half half_rect).

Definition half_fold_right (n : nat) : nat :=
  match nat_fold_right
          left_or_right
          (Left 0)
          (fun ih =>                   
             match ih with
             | Left q =>
                 Right q          
             | Right q =>
                 Left (S q)
             end)
          n
  with
  | Left q =>
      q
  | Right q =>
      q
  end.

Compute (test_half half_fold_right).

Definition half_fold_left (n : nat) : nat :=
  match nat_fold_left
          left_or_right
          (Left 0)
          (fun ih =>                   
             match ih with
             | Left q =>
                 Right q          
             | Right q =>
                 Left (S q)
             end)
          n
  with
  | Left q =>
      q
  | Right q =>
      q
  end.

Compute (test_half half_fold_left). 

Definition half_iterative (n : nat) : nat :=
  let fix visit n acc :=
    match n, acc with
    | 0, _ =>
        acc
    | S n', Left q =>
        visit n' (Right q)
    | S n', Right q =>
        visit n' (Left (S q))
    end
  in match visit n (Left 0) with
     | Left q =>
         q
     | Right q =>
         q
     end.

Compute (test_half half_iterative).

(* ********** *)

Definition test_square_root_and_remainder (candidate : nat -> nat * nat) :=
  (match candidate 16 with
   | (4, 0) =>
     true
   | _ =>
     false
   end)
    && 
  (match candidate 15 with
   | (3, 6) =>
     true
   | _ =>
     false
   end)
    && 
  (match candidate 14 with
   | (3, 5) =>
     true
   | _ =>
     false
   end)
    && 
  (match candidate 13 with
   | (3, 4) =>
     true
   | _ =>
     false
   end)
    && 
  (match candidate 12 with
   | (3, 3) =>
     true
   | _ =>
     false
   end)
    && 
  (match candidate 11 with
   | (3, 2) =>
     true
   | _ =>
     false
   end)
    && 
  (match candidate 10 with
   | (3, 1) =>
     true
   | _ =>
     false
   end)
    && 
  (match candidate 9 with
   | (3, 0) => true
   | _ => false
   end).

Lemma square_of_successor :
  forall x : nat,
    S x * S x = x * x + S (2 * x).
Proof.
  intro x.
  ring.
Qed.

Lemma square_root :
  forall n : nat,
    exists x r : nat,
      n = x * x + r /\ r < S (2 * x).
Proof.
Abort.

(*
Definition square_root_and_remainder_rect (n : nat) : nat * nat :=
  nat_rect
    (fun _ : nat => (nat * nat)%type)
    ...
    ..
    n.

Compute (test_square_root_and_remainder square_root_and_remainder_rect).
*)

(* ********** *)

(* end of week-11_for-all-there-exists.v *)