(* week-11_exercises.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 5 Nov 2023 *)

(* *********** *)

(*
Name: Tan Zhi Yi [Zach]
Email address: tan.zhi.yi@u.yale-nus.edu.sg
Student ID number: A0223972B

Name: Li Xingqi
Email address: xingqi.li@u.yale-nus.edu.sg
Student ID number: A0242437H

Name: Chan Adam Christopher Yamson
Email address: adam.chan@u.yale-nus.edu.sg
Student ID number: A0242453L

Name: Liau Yee Seng
Email address: edward.liau@u.yale-nus.edu.sg
Student ID number: A0242356H
 *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

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

Definition half_rect (n : nat) : nat :=
  match nat_rect
          (fun _ : nat => left_or_right)
          (Left 0)
          (fun _ ih =>
             match ih with
             | Left q' =>
                 Right q'
             | Right q' => 
                 Left (S q')
          end)               
          n with
          | Left q =>
              q
          | Right q =>
              q
          end.

Compute (test_half half_rect).

(* Exercise 03 *)

Lemma square_root :
  forall n : nat,
    exists x r : nat,
      n = x * x + r /\ r < S (2 * x).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  - exists 0.
    exists 0.
    simpl.
    split.

    -- reflexivity.

    -- Search (0 < S _ ).
       exact Nat.lt_0_1.

  - destruct IHn' as [x [r [H_n' r_lt_S2x]]].
    Search (_ < S _ -> _ <= _).
    Check (lt_n_Sm_le r (2 * x) r_lt_S2x).
    Search (_ <= _ -> _ \/ _).
    Check (le_lt_or_eq r (2 * x) (lt_n_Sm_le r (2 * x) r_lt_S2x)).
    assert (H_r := (le_lt_or_eq r (2 * x) (lt_n_Sm_le r (2 * x) r_lt_S2x))).
    case H_r as [r_lt_2x | r_eq_2x].

    -- exists x.
       exists (S r).
       split.

       + rewrite <- (plus_n_Sm (x * x) r).
         rewrite -> H_n'.
         reflexivity.

       + Search (_ < _ -> S _ < S _).
         apply (lt_n_S r (2 * x)).
         exact r_lt_2x.

    -- exists (S x).
       exists 0.
       split.

       + rewrite -> H_n'.
         rewrite -> r_eq_2x.
         ring.
         
       + Search (0 < S _).
         Check (Nat.lt_0_succ (2 * S x)).
         exact (Nat.lt_0_succ (2 * S x)).
Qed.

  
Definition test_root (candidate : nat -> nat) :=
  (candidate 0 =? 0) && (candidate 1 =? 1) && (candidate 5 =? 2) && (candidate 10000 =? 100).

Definition root_aux (n : nat) :=
  nat_rect
    (fun _ : nat => (nat * nat)%type)
    (0 , 0)
    (fun n' ih =>
       match ih with
       |(x, r) =>
          if r <? (2 * x)
          then (x , S r)
          else (S x, 0)
       end)
    n.

Definition root (n : nat) :=
  match root_aux n with
  |(x, r) =>
     x
  end.

Compute (test_root root).

(* Exercise 4 *)

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
  Check (Bisimilar_3_12 V eq_V v1 v2 v1s' v2s' bs_v1s_v2s).
  destruct (Bisimilar_3_12 V eq_V v1 v2 v1s' v2s' bs_v1s_v2s) as [eq_v1_v2 bs_v1s'_v2s'].
  Check (Bisimilar_3_12 V eq_V v2 v3 v2s' v3s' bs_v2s_v3s).
  destruct (Bisimilar_3_12 V eq_V v2 v3 v2s' v3s' bs_v2s_v3s) as [eq_v2_v3 bs_v2s'_v3s'].
  Check (eq_V_trans v1 v2 v3 eq_v1_v2 eq_v2_v3).
  Check (coIH v1s' v2s' v3s' bs_v1s'_v2s' bs_v2s'_v3s').
  Check (Bisimilar V eq_V v1 v3 v1s' v3s'
           (eq_V_trans v1 v2 v3 eq_v1_v2 eq_v2_v3)
           (coIH v1s' v2s' v3s' bs_v1s'_v2s' bs_v2s'_v3s')).
  exact (Bisimilar V eq_V v1 v3 v1s' v3s'
           (eq_V_trans v1 v2 v3 eq_v1_v2 eq_v2_v3)
           (coIH v1s' v2s' v3s' bs_v1s'_v2s' bs_v2s'_v3s')).
Qed.
(* End of week-11_exercises.v *)

(* ***** *)
