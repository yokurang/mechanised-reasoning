(* week-11_reasoning-about-streams.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 01 Nov 2023 *)
(* was: *)
(* Version of 30 Oct 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

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

Lemma binomial_expansion :
  forall x y : nat,
    (x + y) * (x + y) =
    x * x + 2 * x * y + y * y.
Proof.
  intros x y.
  ring.
Qed.

Definition binomial_expansion_Sn :
  forall n : nat,
    (S n) * (S n) =
    S (2 * n) + n * n.
Proof.
  intro n.
  ring.
Qed.

(* ********** *)

CoInductive stream (V : Type) : Type :=
| Cons : V -> stream V -> stream V.

CoInductive bisimilar : forall V : Type, (V -> V -> Prop) -> stream V -> stream V -> Prop :=
| Bisimilar :
    forall (V : Type)
           (eq_V : V -> V -> Prop)
           (v1 v2 : V)
           (v1s v2s : stream V),
    eq_V v1 v2 ->
    bisimilar V eq_V v1s v2s ->
    bisimilar V eq_V (Cons V v1 v1s) (Cons V v2 v2s).

(* ********** *)

Lemma Bisimilar_12_3 :
  forall (V : Type)
         (eq_V : V -> V -> Prop)
         (v1 v2 : V)
         (v1s v2s : stream V),
    eq_V v1 v2 ->
    bisimilar V eq_V v1s v2s ->
    bisimilar V eq_V (Cons V v1 v1s) (Cons V v2 v2s).
Proof.
  exact Bisimilar.
Qed.

Lemma Bisimilar_3_12 :
  forall (V : Type)
         (eq_V : V -> V -> Prop)
         (v1 v2 : V)
         (v1s' v2s' : stream V),
    bisimilar V eq_V (Cons V v1 v1s') (Cons V v2 v2s') ->
    eq_V v1 v2 /\ bisimilar V eq_V v1s' v2s'.
Proof.
  intros V eq_V v1 v2 v1s' v2s' bs_v1s'_v2s'.
  remember (Cons V v1 v1s') as v1s eqn:H_v1s.
  remember (Cons V v2 v2s') as v2s eqn:H_v2s.
  case bs_v1s'_v2s' as [V' eq_V' v1' v2' v1s'' v2s'' eq_v1'_v2' bs_v1s''_v2s''].
  injection H_v1s as eq_v1'_v1 eq_v1s''_v1s'.
  injection H_v2s as eq_v2'_v2 eq_v2s''_v2s'.
  rewrite <- eq_v1'_v1.
  rewrite <- eq_v2'_v2.
  rewrite <- eq_v1s''_v1s'.
  rewrite <- eq_v2s''_v2s'.
  exact (conj eq_v1'_v2' bs_v1s''_v2s'').
Qed.

Lemma Bisimilar_13_2 :
  forall (V : Type)
         (eq_V : V -> V -> Prop)
         (v1 v2 : V)
         (v1s v2s : stream V),
    eq_V v1 v2 ->
    bisimilar V eq_V (Cons V v1 v1s) (Cons V v2 v2s) ->
    bisimilar V eq_V v1s v2s.
Proof.
  intros V eq_V v1 v2 v1s v2s eq_v1_v2 bs_v1_v1s_v2_v2s.
  remember (Cons V v1 v1s) as v1s' eqn:H_v1s'.
  remember (Cons V v2 v2s) as v2s' eqn:H_v2s'.
  case bs_v1_v1s_v2_v2s as [V' eq_V' v1' v2' v1s'' v2s'' eq_v1'_v2' bs_v1s''_v2s''].
  injection H_v1s' as eq_v1'_v1 eq_v1s''_v1s.
  injection H_v2s' as eq_v2'_v2 eq_v2s''_v2s.
  rewrite <- eq_v1s''_v1s.
  rewrite <- eq_v2s''_v2s.
  exact bs_v1s''_v2s''.
Qed.

Lemma Bisimilar_23_1 :
  forall (V : Type)
         (eq_V : V -> V -> Prop)
         (v1 v2 : V)
         (v1s v2s : stream V),
    bisimilar V eq_V v1s v2s ->
    bisimilar V eq_V (Cons V v1 v1s) (Cons V v2 v2s) ->
    eq_V v1 v2.
Proof.
  intros V eq_V v1 v2 v1s v2s eq_v1_v2 bs_v1_v1s_v2_v2s.
  remember (Cons V v1 v1s) as v1s' eqn:H_v1s'.
  remember (Cons V v2 v2s) as v2s' eqn:H_v2s'.
  case bs_v1_v1s_v2_v2s as [V' eq_V' v1' v2' v1s'' v2s'' eq_v1'_v2' bs_v1s''_v2s''].
  injection H_v1s' as eq_v1'_v1 eq_v1s''_v1s.
  injection H_v2s' as eq_v2'_v2 eq_v2s''_v2s.
  rewrite <- eq_v1'_v1.
  rewrite <- eq_v2'_v2.
  exact eq_v1'_v2'.
Qed.

(* ********** *)

Proposition bisimilar_refl :
  forall (V : Type)
         (eq_V : V -> V -> Prop),
    (forall v : V,
        eq_V v v) ->
    forall vs : stream V,
      bisimilar V eq_V vs vs.
Proof.
  intros V eq_V eq_V_refl.
  cofix coIH.
  intros [v vs'].
  Check (Bisimilar V eq_V v v vs' vs' (eq_V_refl v) (coIH vs')).
  exact (Bisimilar V eq_V v v vs' vs' (eq_V_refl v) (coIH vs')).
Qed.

Proposition bisimilar_sym :
  forall (V : Type)
         (eq_V : V -> V -> Prop),
    (forall v1 v2 : V,
        eq_V v1 v2 ->
        eq_V v2 v1) ->
    forall v1s v2s : stream V,
      bisimilar V eq_V v1s v2s ->
      bisimilar V eq_V v2s v1s.
Proof.
  intros V eq_V eq_V_sym.
  cofix coIH.
  intros [v1 v1s'] [v2 v2s'] bs_v1s_v2s.
  Check (Bisimilar_3_12 V eq_V v1 v2 v1s' v2s' bs_v1s_v2s).
  destruct (Bisimilar_3_12 V eq_V v1 v2 v1s' v2s' bs_v1s_v2s) as [eq_v1_v2 bs_v1s'_v2s'].
  Check (Bisimilar V eq_V v2 v1 v2s' v1s').
  Check (Bisimilar V eq_V v2 v1 v2s' v1s' (eq_V_sym v1 v2 eq_v1_v2)).
  Check (Bisimilar V eq_V v2 v1 v2s' v1s' (eq_V_sym v1 v2 eq_v1_v2) (coIH v1s' v2s' bs_v1s'_v2s')).
  exact (Bisimilar V eq_V v2 v1 v2s' v1s' (eq_V_sym v1 v2 eq_v1_v2) (coIH v1s' v2s' bs_v1s'_v2s')).
Qed.

Proposition bisimilar_trans :
  forall (V : Type)
         (eq_V : V -> V -> Prop),
    (forall v1 v2 v3: V,
        eq_V v1 v2 ->
        eq_V v2 v3 ->
        eq_V v1 v3) ->
    forall v1s v2s v3s: stream V,
      bisimilar V eq_V v1s v2s ->
      bisimilar V eq_V v2s v3s ->
      bisimilar V eq_V v1s v3s.
Proof.
  intros V eq_V eq_V_trans.
  cofix coIH.
  intros [v1 v1s'] [v2 v2s'] [v3 v3s'] bs_v1s_v2s bs_v2s_v3s.
  Check (Bisimilar_3_12 V eq_V v2 v3 v2s' v3s' bs_v2s_v3s).
  destruct (Bisimilar_3_12 V eq_V v1 v2 v1s' v2s' bs_v1s_v2s) as [eq_v1_v2 bs_v1s'_v2s'].
  destruct (Bisimilar_3_12 V eq_V v2 v3 v2s' v3s' bs_v2s_v3s) as [eq_v2_v3 bs_v2s'_v3s'].
  Check (Bisimilar V eq_V v2 v3 v2s' v3s').
  Check (Bisimilar V eq_V v1 v3 v1s' v3s' (eq_V_trans v1 v2 v3 eq_v1_v2 eq_v2_v3)).
  Check (Bisimilar V eq_V v1 v3 v1s' v3s' (eq_V_trans v1 v2 v3 eq_v1_v2 eq_v2_v3)
           (coIH v1s' v2s' v3s' bs_v1s'_v2s' bs_v2s'_v3s')).
  exact (Bisimilar V eq_V v1 v3 v1s' v3s' (eq_V_trans v1 v2 v3 eq_v1_v2 eq_v2_v3)
           (coIH v1s' v2s' v3s' bs_v1s'_v2s' bs_v2s'_v3s')).
Qed.

(* ********** *)

(* 

  ********** Exercise 1 and 3 **********

*)

Check nat_ind.
Check nat_rect.
Print nat_rect.

(* ********** *)


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

(* ********** *)

Lemma twice_S :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
  intro n.
  induction n as [ | n' IHn'].
  Search ( S (_) = _).
  + rewrite -> Nat.mul_0_r.
    rewrite -> Nat.mul_1_r.
    reflexivity.
  + Search (_ * S _ = _).
    rewrite -> Nat.mul_succ_r.
    Search (S (_ + _) = _).
    rewrite -> Nat.add_comm.
    rewrite -> 2 plus_n_Sm.
    rewrite -> IHn'.
    Search (_ * S _ = _).
    rewrite <- Nat.add_comm.
    rewrite <- Nat.mul_succ_r.
    reflexivity.
Qed.

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
  intro n.
  induction n as [ | n' [x [r [H_n H_r]]]].
  - exists 0, 0.
    split.
    + compute; reflexivity.
    + rewrite -> Nat.mul_0_r.
      exact Nat.lt_0_1.
  - case (le_lt_or_eq r (2 * x) (Arith_prebase.lt_n_Sm_le r (2 * x) H_r)) as [lt_2x_r | eq_2x_r].
    + exists x, (S r).
      split.
      * rewrite -> H_n.
        ring.
      * Search (_ < _ -> S _ < S _).
        exact (Arith_prebase.lt_n_S_stt r (2 * x) lt_2x_r).
    + exists (S x), 0.
      split.
      * rewrite -> H_n.
        rewrite -> eq_2x_r.
        ring.
      * exact (Nat.lt_0_succ (2 * S x)).
Qed.

Definition square_root_and_remainder_rect (n : nat) : nat * nat :=
  nat_rect
    (fun _ : nat => (nat * nat)%type)
    (0, 0)
    (fun _ ih =>
       let (x, r) := ih
       in if r <? (2 * x)
          then (x, S r)
          else (S x, 0))
    n.

Compute (test_square_root_and_remainder square_root_and_remainder_rect).

Definition square_root_and_remainder_right (n : nat) : nat * nat :=
  nat_parafold_right
    (nat * nat)
    (0, 0)
    (fun _ ih =>
       let (x, r) := ih
       in if r <? (2 * x)
          then (x, S r)
          else (S x, 0))
    n.

Compute (test_square_root_and_remainder square_root_and_remainder_right).

Definition square_root_and_remainder_right' (n : nat) : nat * nat :=
  nat_fold_right
    (nat * nat)
    (0, 0)
    (fun ih =>
       let (x, r) := ih
       in if r <? (2 * x)
          then (x, S r)
          else (S x, 0))
    n.

Compute (test_square_root_and_remainder square_root_and_remainder_right').

Definition square_root_and_remainder_left (n : nat) : nat * nat :=
  nat_fold_left
    (nat * nat)
    (0, 0)
    (fun ih =>
       let (x, r) := ih
       in if r <? (2 * x)
          then (x, S r)
          else (S x, 0))
    n.

Compute (test_square_root_and_remainder square_root_and_remainder_left).

Definition square_root_and_remainder_iterative (n : nat) : (nat * nat) :=
  let fix visit n x r :=
    match n with
    | O =>
        (x, r)
    | S n' =>
        if r <? (2 * x)
        then visit n' x (S r)
        else visit n' (S x) 0
    end
  in visit n 0 0.

Compute (test_square_root_and_remainder square_root_and_remainder_iterative).

(* ********** *)

(* end of week-11_for-all-there-exists.v *)

(* week-11_a-family-of-programming-puzzles-about-lists.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 01 Nov 2023 *)

(* ********** *)

Fixpoint list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right V W nil_case cons_case vs')
  end.

Fixpoint list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left V W (cons_case v nil_case) cons_case vs'
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

Fixpoint list_append (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
  | nil =>
      v2s
  | v1 :: v1s' =>
      v1 :: list_append V v1s' v2s
  end.

Lemma fold_unfold_list_append_nil :
  forall (V : Type)
         (v2s : list V),
    list_append V nil v2s =
      v2s.
Proof.
  fold_unfold_tactic list_append.
Qed.

Lemma fold_unfold_list_append_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    list_append V (v1 :: v1s') v2s =
      v1 :: list_append V v1s' v2s.
Proof.
  fold_unfold_tactic list_append.
Qed.

Fixpoint list_reverse (V : Type) (vs : list V) : list V :=
  match vs with
  | nil =>
      nil
  | v :: vs' =>
      list_append V (list_reverse V vs') (v :: nil)
  end.

Lemma fold_unfold_list_reverse_nil :
  forall V : Type,
    list_reverse V nil =
      nil.

Proof.
  fold_unfold_tactic list_reverse.
Qed.

Lemma fold_unfold_list_reverse_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_reverse V (v :: vs') =
      list_append V (list_reverse V vs') (v :: nil).

Proof.
  fold_unfold_tactic list_reverse.
Qed.

(* ********** *)

Definition eqb_bool := Bool.eqb.

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

Definition test_convolve_nat (candidate : list nat -> list nat -> option (list (nat * nat))) :=
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: nil) nil)
              None)
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate nil (10 :: nil))
              None)
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate nil nil)
              (Some nil))
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: nil) (10 :: nil))
              (Some ((1, 10) :: nil)))
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: 2 :: nil) (10 :: 20 :: nil))
              (Some ((1, 20) :: (2, 10) :: nil)))
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: 2 :: 3 :: nil) (10 :: 20 :: 30 :: nil))
              (Some ((1, 30) :: (2, 20) :: (3, 10) :: nil))).

Fixpoint list_zip (V W : Type) (vs : list V) (ws : list W) : option (list (V * W)) :=
  match vs with
    nil =>
    match ws with
      nil =>
      Some nil
    | _ :: _ =>
      None
    end
  | v :: vs' =>
    match ws with
      nil =>
      None
    | w :: ws' =>
      match list_zip V W vs' ws' with
        Some ps =>
        Some ((v, w) :: ps)
      | None =>
        None
      end
    end
  end.

Compute (test_convolve_nat (fun n1s n2s => list_zip nat nat n1s (List.rev n2s))).

(* ********** *)

Definition test_self_convolve_nat (candidate : list nat -> option (list (nat * nat))) :=
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate nil)
              (Some nil))
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: nil))
              (Some ((1, 1) :: nil)))
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: 2 :: nil))
              (Some ((1, 2) :: (2, 1) :: nil)))
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: 2 :: 3 :: nil))
              (Some ((1, 3) :: (2, 2) :: (3, 1) :: nil)))
  &&
  (eqb_option (list (nat * nat))
              (eqb_list (nat * nat) (eqb_pair nat eqb_nat nat eqb_nat))
              (candidate (1 :: 2 :: 3 :: 4 :: nil))
              (Some ((1, 4) :: (2, 3) :: (3, 2) :: (4, 1) :: nil))).

Compute (test_self_convolve_nat (fun ns => list_zip nat nat ns (List.rev ns))).

(* ********** *)

Definition test_list_reversep_nat (candidate : list nat -> list nat -> bool) :=
  (eqb_bool (candidate nil nil) true)
  &&
  (eqb_bool (candidate (1 :: nil) nil) false)
  &&
  (eqb_bool (candidate nil (1 :: nil)) false)
  &&
  (eqb_bool (candidate (1 :: nil) (1 :: nil)) true)
  &&
  (eqb_bool (candidate (2 :: 1 :: nil) (1 :: 2 :: nil)) true)
  &&
  (eqb_bool (candidate (0 :: 1 :: nil) (1 :: 2 :: nil)) false)
  &&
  (eqb_bool (candidate (2 :: 0 :: nil) (1 :: 2 :: nil)) false)
  &&
  (eqb_bool (candidate (2 :: 1 :: 0 :: nil) (1 :: 2 :: nil)) false)
  &&
  (eqb_bool (candidate (2 :: 1 :: nil) (0 :: 1 :: 2 :: nil)) false)
  &&
  (eqb_bool (candidate (3 :: 2 :: 1 :: nil) (1 :: 2 :: 3 :: nil)) true)
  &&
  (eqb_bool (candidate (0 :: 2 :: 1 :: nil) (1 :: 2 :: 3 :: nil)) false)
  &&
  (eqb_bool (candidate (3 :: 0 :: 1 :: nil) (1 :: 2 :: 3 :: nil)) false)
  &&
  (eqb_bool (candidate (3 :: 2 :: 0 :: nil) (1 :: 2 :: 3 :: nil)) false)
  &&
  (eqb_bool (candidate (3 :: 2 :: 1 :: 0 :: nil) (1 :: 2 :: 3 :: nil)) false)
  &&
  (eqb_bool (candidate (3 :: 2 :: 1 :: nil) (0 :: 1 :: 2 :: 3 :: nil)) false).

Compute (test_list_reversep_nat (fun n1s n2s => eqb_list nat eqb_nat n1s (List.rev n2s))).

(* ********** *)

Definition test_list_reverse_nat (candidate : list nat -> list nat) :=
  (eqb_list nat eqb_nat (candidate nil) nil)
  &&
  (eqb_list nat eqb_nat (candidate (1 :: nil)) (1 :: nil))
  &&
  (eqb_list nat eqb_nat (candidate (2 :: 1 :: nil)) (1 :: 2 :: nil))
  &&
  (eqb_list nat eqb_nat (candidate (3 :: 2 :: 1 :: nil)) (1 :: 2 :: 3 :: nil)).

Compute (test_list_reverse_nat (fun ns : list nat => List.rev ns)).

(* ********** *)

Definition test_list_index_rtl_nat (candidate : list nat -> nat -> option nat) :=
  (eqb_option nat
              eqb_nat
              (candidate nil 0)
              None)
  &&
  (eqb_option nat
              eqb_nat
              (candidate nil 1)
              None)
  &&
  (eqb_option nat
              eqb_nat
              (candidate (0 :: nil) 0)
              (Some 0))
  &&
  (eqb_option nat
              eqb_nat
              (candidate (0 :: nil) 1)
              None)
  &&
  (eqb_option nat
              eqb_nat
              (candidate (1 :: 0 :: nil) 0)
              (Some 0))
  &&
  (eqb_option nat
              eqb_nat
              (candidate (1 :: 0 :: nil) 1)
              (Some 1))
  &&
  (eqb_option nat
              eqb_nat
              (candidate (1 :: 0 :: nil) 2)
              None)
  &&
  (eqb_option nat
              eqb_nat
              (candidate (2 :: 1 :: 0 :: nil) 0)
              (Some 0))
  &&
  (eqb_option nat
              eqb_nat
              (candidate (2 :: 1 :: 0 :: nil) 1)
              (Some 1))
  &&
  (eqb_option nat
              eqb_nat
              (candidate (2 :: 1 :: 0 :: nil) 2)
              (Some 2))
  &&
  (eqb_option nat
              eqb_nat
              (candidate (2 :: 1 :: 0 :: nil) 3)
              None).

Fixpoint list_index_ltr (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
  | nil =>
    None
  | v :: vs' =>
    match n with
    | O =>
      Some v
    | S n' =>
      list_index_ltr V vs' n'
    end
  end.

Lemma fold_unfold_list_index_ltr_nil :
  forall (V : Type)
         (n : nat),
    list_index_ltr V nil n =
      None.
Proof.
  fold_unfold_tactic list_index_ltr.
Qed.

Lemma fold_unfold_list_index_ltr_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (n : nat),
    list_index_ltr V (v :: vs') n =
      match n with
      | O =>
          Some v
      | S n' =>
          list_index_ltr V vs' n'
      end.
Proof.
  fold_unfold_tactic list_index_ltr.
Qed.

Compute (test_list_index_rtl_nat (fun ns n => list_index_ltr nat (list_reverse nat ns) n)).

Definition list_index_rtl_left (V : Type) (vs : list V) (n : nat) : option V :=
  list_fold_left V (nat -> option V) (fun _ => None)
    (fun a ih v =>
       match v with
       | O => Some a
       | S n' => ih n'
       end
    ) vs n.

Compute (test_list_index_rtl_nat (fun ns n => list_index_rtl_left nat ns n)).

(*Theorem about_the_correctness_of_list_index_rtl_left :
  forall (V : Type)
         (v' : V)
         (vs' : list V)
         (n : nat),
    list_index_rtl_left V vs' n =
      list_index_ltr V (list_reverse V vs') n ->
    list_index_rtl_left V (v' :: vs') n =
      list_index_ltr V (list_reverse V (v' :: vs')) n.
Proof.
  intros V v' vs'.
  induction vs' as [ | v vs IHvs].
  - intros [ | n'].
    + intro H_true.
      rewrite -> (fold_unfold_list_reverse_cons V v' nil).
      rewrite -> (fold_unfold_list_reverse_nil V).
      rewrite -> (fold_unfold_list_append_nil V (v' :: nil)).
      rewrite -> (fold_unfold_list_index_ltr_cons_nil V v' nil).
      unfold list_index_rtl_left.
      rewrite -> (fold_unfold_list_fold_left_cons V
                    (nat -> option V)
                    (fun _ : nat => None)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v : nat) => match v with
                                      | 0 => Some a
                                      | S n' => ih n'
                                      end) v' nil).
      rewrite -> (fold_unfold_list_fold_left_nil V
                    (nat -> option V)
                    (fun v : nat => match v with
                                    | 0 => Some v'
                                    | S _ => None
                                    end)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v : nat) => match v with
                                      | 0 => Some a
                                      | S n' => ih n'
                                      end)).
      reflexivity.
    + intro H_true.
      rewrite -> (fold_unfold_list_reverse_cons V v' nil).
      rewrite -> (fold_unfold_list_reverse_nil V).
      rewrite -> (fold_unfold_list_append_nil V (v' :: nil)).
      rewrite -> (fold_unfold_list_index_ltr_cons_cons V v' nil n').
      rewrite -> (fold_unfold_list_index_ltr_nil V n').
      unfold list_index_rtl_left.
      rewrite -> (fold_unfold_list_fold_left_cons V
                    (nat -> option V)
                    (fun _ : nat => None)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v : nat) => match v with
                                      | 0 => Some a
                                      | S n'0 => ih n'0
                                      end) v' nil).
      rewrite -> (fold_unfold_list_fold_left_nil V
                    (nat -> option V)
                    (fun v : nat => match v with
                                    | 0 => Some v'
                                    | S _ => None
                                    end)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v : nat) => match v with
                                      | 0 => Some a
                                      | S n'0 => ih n'0
                                      end)).
      reflexivity.
  - intros [ | n'].
    induction vs as [ | vs' vs'' IHvs''].  
    * intro H_true.
      rewrite -> (fold_unfold_list_reverse_cons V v' (v :: nil)).
      rewrite -> (fold_unfold_list_reverse_cons V v nil).
      rewrite -> (fold_unfold_list_reverse_nil V).
      rewrite -> (fold_unfold_list_append_nil V (v :: nil)).
      rewrite -> (fold_unfold_list_append_cons V v nil (v' :: nil)).
      rewrite -> (fold_unfold_list_append_nil V (v' :: nil)).
      rewrite -> (fold_unfold_list_index_ltr_cons_nil V v (v' :: nil)).
      unfold list_index_rtl_left.
      rewrite -> (fold_unfold_list_fold_left_cons V
                    (nat -> option V)
                    (fun _ : nat => None)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v0 : nat) => match v0 with
                                       | 0 => Some a
                                         | S n' => ih n'
                                       end) v' (v :: nil)).
      rewrite -> (fold_unfold_list_fold_left_cons V
                    (nat -> option V)               
                    (fun v0 : nat => match v0 with
                                     | 0 => Some v'
                                     | S _ => None
                                     end)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v0 : nat) => match v0 with
                                         | 0 => Some a
                                       | S n' => ih n'
                                       end) v nil).
      rewrite -> (fold_unfold_list_fold_left_nil V
                    (nat -> option V)
                    (fun v0 : nat => match v0 with
                                     | 0 => Some v
                                     | 1 => Some v'
                                     | S (S _) => None
                                     end)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v0 : nat) => match v0 with
                                       | 0 => Some a
                                       | S n' => ih n'
                                       end)).
      reflexivity.
    * induction vs'' as [ | vs''' vs'''' IHvs''''].
      ** intro H_true.
         rewrite -> (fold_unfold_list_reverse_cons V v' (v :: vs' :: nil)).
         rewrite -> (fold_unfold_list_reverse_cons V v (vs' :: nil)).
         rewrite -> (fold_unfold_list_reverse_cons V vs' nil).
         rewrite -> (fold_unfold_list_reverse_nil V).
         rewrite -> (fold_unfold_list_append_nil V (vs' :: nil)).
         rewrite -> (fold_unfold_list_append_cons V vs' nil (v :: nil)).
         rewrite -> (fold_unfold_list_append_nil V (v :: nil)).
         rewrite -> (fold_unfold_list_append_cons V vs' (v :: nil)).
         rewrite -> (fold_unfold_list_append_cons V v nil).
         rewrite -> (fold_unfold_list_append_nil V (v' :: nil)).
         rewrite -> (fold_unfold_list_index_ltr_cons_nil V vs' (v :: v' :: nil)).
         unfold list_index_rtl_left.
         rewrite -> (fold_unfold_list_fold_left_cons V
                       (nat -> option V)
                       (fun _ : nat => None)
                       (fun (a : V)
                            (ih : nat -> option V)
                            (v0 : nat) => match v0 with
                                          | 0 => Some a
                                          | S n' => ih n'
                                          end) v' (v :: vs' :: nil)).
         rewrite -> (fold_unfold_list_fold_left_cons V
                       (nat -> option V)
                       (fun v0 : nat => match v0 with
                                        | 0 => Some v'
                                        | S _ => None
                                        end)
                       (fun (a : V)
                            (ih : nat -> option V)
                            (v0 : nat) => match v0 with
                                          | 0 => Some a
                                          | S n' => ih n'
                                          end) v (vs' :: nil)).
         rewrite -> (fold_unfold_list_fold_left_cons V
                       (nat -> option V)
                       (fun v0 : nat => match v0 with
                                        | 0 => Some v
                                        | 1 => Some v'
                                        | S (S _) => None
                                        end)
                       (fun (a : V)
                            (ih : nat -> option V)
                              (v0 : nat) =>
                          match v0 with
                          | 0 => Some a
                          | S n' => ih n'
                          end) vs' nil).
         rewrite -> (fold_unfold_list_fold_left_nil V
                       (nat -> option V)
                       (fun v0 : nat =>
                          match v0 with
                          | 0 => Some vs'
                          | 1 => Some v
                          | 2 => Some v'
                          | S (S (S _)) => None
                          end)
                       (fun (a : V)
                            (ih : nat -> option V)
                            (v0 : nat) => match v0 with
                                          | 0 => Some a
                                          | S n' => ih n'
                                          end)).
         reflexivity.
Abort.*)

Theorem relating_list_fold_left_and_list_fold_right_using_list_reverse :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (vs : list V),
    list_fold_left  V W nil_case cons_case vs =
      list_fold_right V W nil_case cons_case (list_reverse V vs).
Admitted.
           
Theorem correctness_of_list_index_rtl_left :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    list_index_rtl_left V vs n = list_index_ltr V (list_reverse V vs) n.
Proof.
  Compute (let V := nat in
           let vs := 3 :: 2 :: 1 :: 0 :: nil in
           let n := 1 in
           list_index_rtl_left V vs n = list_index_ltr V (List.rev vs) n).  
  intros V vs.
  unfold list_index_rtl_left.
  rewrite -> (relating_list_fold_left_and_list_fold_right_using_list_reverse V
                (nat -> option V)
                (fun _ : nat => None)
                (fun (a : V)
                     (ih : nat -> option V)
                     (v : nat) =>
                   match v with
                   | 0 => Some a
                   | S n' => ih n'
                   end) vs).
  induction vs as [ | v vs' IHvs'].
  - intros [ | n'].
    + rewrite -> (fold_unfold_list_reverse_nil V).
      rewrite -> (fold_unfold_list_index_ltr_nil V).
      rewrite -> (fold_unfold_list_fold_right_nil V
                    (nat -> option V)
                    (fun _ : nat => None)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v : nat) => match v with
                                      | 0 => Some a
                                      | S n' => ih n'
                                      end)).
      reflexivity.
    + rewrite -> (fold_unfold_list_reverse_nil V).
      rewrite -> (fold_unfold_list_index_ltr_nil V).
      rewrite -> (fold_unfold_list_fold_right_nil V
                    (nat -> option V)
                    (fun _ : nat => None)
                    (fun (a : V)
                         (ih : nat -> option V)
                         (v : nat) => match v with
                                      | 0 => Some a
                                      | S n'0 => ih n'0
                                      end)).
      reflexivity.
  - intros [ | n'].
    + induction vs' as [ | v' vs'' IHvs''].
      * rewrite -> (fold_unfold_list_reverse_cons V v nil).
        rewrite -> (fold_unfold_list_reverse_nil V).
        rewrite -> (fold_unfold_list_append_nil V (v :: nil)).
        rewrite -> (fold_unfold_list_index_ltr_cons V v nil 0).
        rewrite -> (fold_unfold_list_fold_right_cons V
                      (nat -> option V)
                      (fun _ : nat => None)
                      (fun (a : V)
                           (ih : nat -> option V)
                           (v0 : nat) => match v0 with
                                         | 0 => Some a
                                         | S n' => ih n'
                                         end) v nil).
        reflexivity.
      * rewrite -> (fold_unfold_list_reverse_cons V v (v' :: vs'')).
        rewrite -> (fold_unfold_list_reverse_cons V v' vs'').
Abort.
           
Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 0.

Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 1.

Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 2.

Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 3.

(* ********** *)

(* end of week-11_a-family-of-programming-puzzles-about-lists.v *)
