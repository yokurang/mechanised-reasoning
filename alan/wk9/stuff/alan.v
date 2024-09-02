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
