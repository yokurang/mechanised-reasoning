(* week-07_soundness-and-completeness-of-equality-predicates-revisited.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 10 Sep 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)


Definition is_a_sound_and_complete_equality_predicate (V : Type) (eqb_V : V -> V -> bool) :=
  forall v1 v2 : V,
    eqb_V v1 v2 = true <-> v1 = v2.

(* ********** *)

Check Bool.eqb.
(* eqb : bool -> bool -> bool *)

Definition eqb_bool (b1 b2 : bool) : bool :=
  match b1 with
  | true =>
    match b2 with
    | true =>
      true
    | false =>
      false
    end
  | false =>
    match b2 with
    | true =>
      false
    | false =>
      true
    end
  end.

Lemma eqb_bool_is_reflexive :
  forall b : bool,
    eqb_bool b b = true.
Proof.
  intros [ | ]; unfold eqb_bool; reflexivity.
Qed.


Search (eqb _ _ = _ -> _ = _).
(* eqb_prop: forall a b : bool, eqb a b = true -> a = b *)

Lemma fold_unfold_eqb_bool_true :
  forall b2 : bool,
    eqb_bool true b2 =
    match b2 with
    | true =>
      true
    | false  =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_bool.
Qed.


Lemma fold_unfold_eqb_bool_false :
  forall b2 : bool,
    eqb_bool false b2 =
    match b2 with
    | true =>
      false
    | false  =>
      true
    end.
Proof.
  fold_unfold_tactic eqb_bool.
Qed.

Proposition soundness_and_completeness_of_eqb_bool :
  is_a_sound_and_complete_equality_predicate bool eqb_bool.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  intros v1 v2.
  split.
  - Search (eqb _ _ = _ -> _ = _).
    Check (eqb_prop v1 v2).
    exact (eqb_prop v1 v2).
  - intro H_true.
    rewrite <- (eqb_bool_is_reflexive v1).
    rewrite <- H_true.
    reflexivity.
Qed.

(* ***** *)

Check Nat.eqb.
(* Nat.eqb : nat -> nat -> bool *)

Fixpoint eqb_nat (n1 n2 : nat) : bool :=
  match n1 with
  | O =>
    match n2 with
    | O =>
      true
    | S n2' =>
      false
    end
  | S n1' =>
    match n2 with
    | O =>
      false
    | S n2' =>
      eqb_nat n1' n2'
    end
  end.

Lemma fold_unfold_eqb_nat_O :
  forall n2 : nat,
    eqb_nat 0 n2 =
    match n2 with
    | O =>
      true
    | S _ =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_nat.
Qed.

Lemma fold_unfold_eqb_nat_S :
  forall n1' n2 : nat,
    eqb_nat (S n1') n2 =
    match n2 with
    | O =>
      false
    | S n2' =>
      eqb_nat n1' n2'
    end.
Proof.
  fold_unfold_tactic eqb_nat.
Qed.

Search (Nat.eqb _ _ = true -> _ = _).
(* beq_nat_true: forall n m : nat, (n =? m) = true -> n = m *)

Proposition soundness_and_completeness_of_eqb_nat :
  is_a_sound_and_complete_equality_predicate nat eqb_nat.
Proof.
Abort.

(* ***** *)

Lemma fold_unfold_eqb_Nat_O :
  forall n2 : nat,
    0 =? n2 =
    match n2 with
    | O =>
      true
    | S _ =>
      false
    end.
Proof.
  fold_unfold_tactic Nat.eqb.
Qed.

Lemma fold_unfold_eqb_Nat_S :
  forall n1' n2 : nat,
    S n1' =? n2 =
    match n2 with
    | O =>
      false
    | S n2' =>
      n1' =? n2'
    end.
Proof.
  fold_unfold_tactic Nat.eqb.
Qed.

Proposition soundness_and_completeness_of_eqb_nat :
  is_a_sound_and_complete_equality_predicate nat Nat.eqb.
Proof.
Abort.

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

Proposition soundness_and_completeness_of_eqb_option :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    is_a_sound_and_complete_equality_predicate V eqb_V ->
    is_a_sound_and_complete_equality_predicate (option V) (eqb_option V eqb_V).
Proof.
  intros V eqb_V.
  unfold is_a_sound_and_complete_equality_predicate.
  intros H_both [v1 | ] [v2 | ]; unfold eqb_option.

  - destruct (H_both v1 v2) as [H_sound H_complete].
    split; intro H_v1_v2.

    -- rewrite -> (H_sound H_v1_v2).
       reflexivity.

    -- injection H_v1_v2 as H_v1_v2.
       exact (H_complete H_v1_v2).

  - split; intro H_absurd; discriminate H_absurd.

  - split; intro H_absurd; discriminate H_absurd.

  - split; reflexivity.
Qed.

(* ***** *)

Definition eqb_option_option (V : Type) (eqb_V : V -> V -> bool) (oov1 oov2 : option (option V)) : bool :=
  match oov1 with
  | Some ov1 =>
    match oov2 with
    | Some ov2 =>
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
      end
    | None =>
      false
    end
  | None =>
    match oov2 with
    | Some ov2 =>
      false
    | None =>
      true
    end
  end.

Definition eqb_option_option'' (V : Type) (eqb_V : V -> V -> bool) : option (option V) -> option (option V) -> bool :=
  eqb_option (option V) (eqb_option V eqb_V).


Proposition soundness_and_completeness_of_eqb_option_option :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    is_a_sound_and_complete_equality_predicate V eqb_V ->
    is_a_sound_and_complete_equality_predicate (option (option V)) (eqb_option_option V eqb_V).
Proof.
  intros V eqb_V.
  unfold is_a_sound_and_complete_equality_predicate.
  intros H_both [[v1 | ] | ] [[v2 | ] | ]; unfold eqb_option_option.
  split; intro H_v1_v2.

  - destruct (H_both v1 v2) as [H_sound H_complete].
    rewrite -> (H_sound H_v1_v2).
    reflexivity.
  - injection H_v1_v2 as H_v1_v2.
    rewrite -> (H_both v1 v2).
    exact (H_v1_v2).
  - split; intro H_absurd; discriminate H_absurd.
  - split; intro H_absurd; discriminate H_absurd.
  - split; intro H_absurd; discriminate H_absurd.
  - split; intro H_absurd; reflexivity.
  - split; intro H_absurd; discriminate H_absurd.
  - split; intro H_absurd; discriminate H_absurd.
  - split; intro H_absurd; discriminate H_absurd.
  - split; intro H_absurd; reflexivity.
Qed.


Proposition equivalence_of_eqb_option_option_and_eqb_option_option'' :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (oov1 oov2 : option (option V)),
    eqb_option_option V eqb_V oov1 oov2 = eqb_option_option'' V eqb_V oov1 oov2.
Proof.
  intros V eqb_V oov1 oov2.
  reflexivity.
Qed.

Proposition soundness_and_completeness_of_eqb_option_option'' :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    is_a_sound_and_complete_equality_predicate V eqb_V ->
    is_a_sound_and_complete_equality_predicate (option (option V)) (eqb_option_option'' V eqb_V).
Proof.
  intros V eqb_V H_V.
  Check (soundness_and_completeness_of_eqb_option V eqb_V H_V).
  Check (soundness_and_completeness_of_eqb_option (option V) (eqb_option V eqb_V)).
  Check (soundness_and_completeness_of_eqb_option (option V) (eqb_option V eqb_V) (soundness_and_completeness_of_eqb_option V eqb_V H_V)).
  unfold eqb_option_option''.
  exact (soundness_and_completeness_of_eqb_option (option V) (eqb_option V eqb_V) (soundness_and_completeness_of_eqb_option V eqb_V H_V)).
Qed.


(* ********** *)

Definition eqb_pair (V : Type) (eqb_V : V -> V -> bool) (W : Type) (eqb_W : W -> W -> bool) (p1 p2 : V * W) : bool :=
  match p1 with
  | (v1, w1) =>
    match p2 with
    | (v2, w2) =>
      eqb_V v1 v2 && eqb_W w1 w2
    end
  end.

Check (eqb_pair).

Proposition soundness_and_completeness_of_eqb_pair :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (W : Type)
         (eqb_W : W -> W -> bool),
    is_a_sound_and_complete_equality_predicate V eqb_V ->
    is_a_sound_and_complete_equality_predicate W eqb_W ->
    is_a_sound_and_complete_equality_predicate (V * W) (eqb_pair V eqb_V W eqb_W).
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  intros V eqb_V W eqb_W.
  intros SC_eqb_V SC_eqb_W.
  intros [v1 w1] [v2 w2].
  Check (SC_eqb_V v1 v2).
  destruct (SC_eqb_V v1 v2) as [S_eqb_V C_eqb_V].
  destruct (SC_eqb_W w1 w2) as [S_eqb_W C_eqb_W].
  split.
  - unfold eqb_pair.
    intro eqb_VW.
    Search (_ && _ = true -> _).
    Check (andb_prop (eqb_V v1 v2) (eqb_W w1 w2)).
    Check (andb_prop (eqb_V v1 v2) (eqb_W w1 w2) eqb_VW).
    destruct (andb_prop (eqb_V v1 v2) (eqb_W w1 w2) eqb_VW) as [eqb_v1_v2 eqb_w1_w2].
    Check (S_eqb_V eqb_v1_v2).
    rewrite -> (S_eqb_V eqb_v1_v2).
    Check (S_eqb_W eqb_w1_w2).
    rewrite -> (S_eqb_W eqb_w1_w2).
    reflexivity.
  - unfold eqb_pair.
    intro eqb_VW.
    injection eqb_VW as eq_v1_v2 eq_w1_w2.
    Check (C_eqb_V eq_v1_v2).
    rewrite -> (C_eqb_V eq_v1_v2).
    Check (C_eqb_W eq_w1_w2).
    rewrite -> (C_eqb_W eq_w1_w2).
    Search (_ && _ = _).
    Check (andb_true_r true).
    exact (andb_true_r true).
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

Lemma fold_unfold_eqb_list_nil :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v2s : list V),
    eqb_list V eqb_V nil v2s =
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Lemma fold_unfold_eqb_list_cons :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    eqb_list V eqb_V (v1 :: v1s') v2s =
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Proposition soundness_and_completeness_of_eqb_list :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    is_a_sound_and_complete_equality_predicate V eqb_V ->
    is_a_sound_and_complete_equality_predicate (list V) (eqb_list V eqb_V).
Proof.
Admitted.

Definition eqb_option_bool (ov1 ov2 : option bool) : bool :=
  eqb_option bool eqb_bool ov1 ov2.


Proposition soundness_and_completeness_of_eqb_option_bool :
  is_a_sound_and_complete_equality_predicate (option bool) eqb_option_bool.
Proof.
  exact (soundness_and_completeness_of_eqb_option bool eqb_bool (soundness_and_completeness_of_eqb_bool)).
Qed.

Definition eqb_unit (u1 u2 : unit) : bool :=
    true.

Proposition soundness_and_completeness_of_eqb_unit :
  is_a_sound_and_complete_equality_predicate unit eqb_unit.
Proof.
Admitted.

Definition eqb_list_unit (lu1 lu2 : list unit) : bool :=
  eqb_list unit eqb_unit lu1 lu2.

Proposition soundness_and_completeness_of_eqb_list_unit :
  is_a_sound_and_complete_equality_predicate (list unit) eqb_list_unit.
Proof.
  exact (soundness_and_completeness_of_eqb_list unit eqb_unit (soundness_and_completeness_of_eqb_unit)).
Qed.

Definition eqb_option_bool_list_unit (p1 p2 : option bool * list unit) : bool :=
  eqb_pair (option bool) eqb_option_bool (list unit) eqb_list_unit p1 p2.

Check (eqb_option_bool_list_unit).

Proposition about_soundness_and_completeness_of_eqb_option_bool_list_unit :
    is_a_sound_and_complete_equality_predicate (option bool) eqb_option_bool ->
    is_a_sound_and_complete_equality_predicate (list unit) eqb_list_unit ->
    is_a_sound_and_complete_equality_predicate (option bool * list unit) (eqb_pair (option bool) eqb_option_bool (list unit) eqb_list_unit).
Proof.
  exact (soundness_and_completeness_of_eqb_pair (option bool) eqb_option_bool (list unit) eqb_list_unit).
Qed.

Proposition soundness_and_completeness_of_eqb_option_bool_list_unit :
  is_a_sound_and_complete_equality_predicate (option bool * list unit) (eqb_pair (option bool) eqb_option_bool (list unit) eqb_list_unit).
Proof.
  exact (about_soundness_and_completeness_of_eqb_option_bool_list_unit soundness_and_completeness_of_eqb_option_bool soundness_and_completeness_of_eqb_list_unit).
Qed.
    
(* ********** *)

(* end of week-07_soundness-and-completeness-of-equality-predicates-revisited.v *)
