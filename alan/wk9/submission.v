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

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

(* week-07_soundness-and-completeness-of-equality-predicates-revisited.v *)

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
Abort.

Search (eqb _ _ = _ -> _ = _).
(* eqb_prop: forall a b : bool, eqb a b = true -> a = b *)

(*
Proposition soundness_and_completeness_of_eqb_bool :
  is_a_sound_and_complete_equality_predicate bool eqb_bool.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
Proof.
Abort.
*)
(* ***** *)

Proposition soundness_and_completeness_of_eqb_bool :
  is_a_sound_and_complete_equality_predicate bool eqb.
Proof.
Admitted.

(* ********** *)

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
  match u1 with
  | tt =>
      match u2 with
      | tt =>
          true
      end
  end.

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

(* week-08_uniqueness-of-the-quotient-and-remainder.v *)

Check plus_reg_l.
(* : forall n m p : nat, p + n = p + m -> n = m *)

(* ***** *)

Lemma plus_reg_r :
  forall n m p : nat,
    n + p = m + p ->
    n = m.
Proof.
  intros n m p P.
  rewrite ->2 (Nat.add_comm _ p) in P.
  Check (plus_reg_l n m p P).
  exact (plus_reg_l n m p P).
Qed.

(* ********** *)

Definition fold_unfold_mul_O := Nat.mul_0_l.
  
Definition fold_unfold_mul_S := Nat.mul_succ_l.

(* ********** *)

(* Needed: the analogue of plus_reg_l for multiplication *)

Lemma times_reg_l :
  forall n m p : nat,
    S p * n = S p * m ->
    n = m.
Proof.
  intros n m p.
  revert m.
  induction n as [ | n' IHn']; intros [ | m'] H_Sp.
  Search (0 * _ = _).
  Search (S _ * _ = _).
Admitted.

(* ********** *)

Print Nat.sub.

Lemma fold_unfold_sub_O :
  forall m : nat,
    0 - m = 0.
Proof.
  fold_unfold_tactic Nat.sub.
Qed.

Lemma fold_unfold_sub_S :
  forall n' m : nat,
    S n' - m =
    match m with
    | 0 => S n'
    | S m' => n' - m'
    end.
Proof.
  fold_unfold_tactic Nat.sub.
Qed.

(* ********** *)

(* Useful: the following resident lemmas *)

(*
  Nat.add_sub_assoc : forall n m p : nat, p <= m -> n + (m - p) = n + m - p
  Nat.add_sub_eq_l : forall n m p : nat, m + p = n -> n - m = p
  Nat.add_sub_eq_r : forall n m p : nat, m + p = n -> n - p = m
  Nat.lt_0_succ : forall n : nat, 0 < S n
  Nat.lt_le_incl : forall n m : nat, n < m -> n <= m
  Nat.lt_trans : forall n m p : nat, n < m -> m < p -> n < p
  Nat.mul_sub_distr_r : forall n m p : nat, (n - m) * p = n * p - m * p
  Nat.sub_0_r : forall n : nat, n - 0 = n
  Nat.sub_add_distr : forall n m p : nat, n - (m + p) = n - m - p
  Nat.sub_gt : forall n m : nat, m < n -> n - m <> 0
  Nat.sub_lt : forall n m : nat, m <= n -> 0 < m -> n - m < n
  mult_S_lt_compat_l : forall n m p : nat, m < p -> S n * m < S n * p
*)

(* ********** *)

Lemma helpful_1 :
  forall x y : nat,
    x * S y < S y ->
    x = 0.
Proof.
  intros [ | x'] y H_lt.
  - reflexivity.
  - Search (S _ * _ = _ * _ + _).
    rewrite -> fold_unfold_mul_S in H_lt.
    rewrite -> Nat.add_comm in H_lt.
    rewrite <- (Nat.add_0_r (S y)) in H_lt at 3.
    Search (_ + _ < _ + _ -> _ < _).
    Check (plus_lt_reg_l (x' * S y) 0 (S y)).
    Check (plus_lt_reg_l (x' * S y) 0 (S y) H_lt).
    (* : x' * S y < 0 *)
    Search (_ < 0).
    Check (Nat.nlt_0_r (x' * S y)).
    Check (Nat.nlt_0_r (x' * S y) (plus_lt_reg_l (x' * S y) 0 (S y) H_lt)).
    contradiction (Nat.nlt_0_r (x' * S y) (plus_lt_reg_l (x' * S y) 0 (S y) H_lt)).
Qed.

(* ********** *)

Lemma helpful_2 :
  forall x y : nat,
    x - y = 0 ->
    x <= y.
Proof.
  intro x.
  induction x as [ | x' IHx']; intros y H_y.
  - Search (0 <= _).
    Check (Nat.le_0_l y).
    exact (Nat.le_0_l y).
  - case y as [ | y'].
    + rewrite -> fold_unfold_sub_S in H_y.
      discriminate H_y.
    + rewrite -> fold_unfold_sub_S in H_y.
      Check (IHx' y' H_y).
      Search (_ <= _ -> S _ <= S _).
      Check (le_n_S x' y').
      Check (le_n_S x' y' (IHx' y' H_y)).
      exact (le_n_S x' y' (IHx' y' H_y)).
Qed.

(* ********** *)

Lemma uniqueness_lt_lt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 < q2 ->
    r1 < r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r1_r2.
  Check Nat.add_sub_eq_r.
  Check (Nat.add_sub_eq_r (q2 * S d + r2) (q1 * S d) r1).
  apply (Nat.add_sub_eq_r (q2 * S d + r2) (q1 * S d) r1) in H_main.
  Check Nat.add_sub_assoc.
  Check (Nat.add_sub_assoc (q2 * S d) r2 r1).
  Search (_ < _ -> _ <= _).
  Check (Nat.lt_le_incl r1 r2).
  Check (Nat.lt_le_incl r1 r2 lt_r1_r2).
  Check (Nat.add_sub_assoc (q2 * S d) r2 r1 (Nat.lt_le_incl r1 r2 lt_r1_r2)).
  rewrite <- (Nat.add_sub_assoc (q2 * S d) r2 r1 (Nat.lt_le_incl r1 r2 lt_r1_r2)) in H_main.
  Check Nat.add_sub_eq_l.
  rewrite <- (Nat.add_0_r (q1 * S d)) in H_main.
  Check Nat.add_sub_eq_l.
  symmetry in H_main.
  Check Nat.add_sub_eq_l.
  Check (Nat.add_sub_eq_l (q2 * S d + (r2 - r1)) (q1 * S d) 0).
  apply (Nat.add_sub_eq_l (q2 * S d + (r2 - r1)) (q1 * S d) 0) in H_main.
  rewrite -> Nat.add_comm in H_main.
  Check Nat.add_sub_assoc.
  Check (Nat.add_sub_assoc (r2 - r1) (q2 * S d) (q1 * S d)).
  assert (wanted :
            q1 * S d <= q2 * S d).
  { Search (_ < _ -> S _ * _ < S _ * _).
      Check (mult_S_lt_compat_l d q1 q2 lt_q1_q2).
      rewrite ->2 (Nat.mul_comm _ (S d)).
      Check (mult_S_lt_compat_l d q1 q2 lt_q1_q2).
      Search (_ < _ -> _ <= _).
      Check (Nat.lt_le_incl (S d * q1) (S d * q2)).
      Check (Nat.lt_le_incl (S d * q1) (S d * q2) (mult_S_lt_compat_l d q1 q2 lt_q1_q2)).
      exact (Nat.lt_le_incl (S d * q1) (S d * q2) (mult_S_lt_compat_l d q1 q2 lt_q1_q2)). }
  Check (Nat.add_sub_assoc (r2 - r1) (q2 * S d) (q1 * S d) wanted).
  rewrite <- (Nat.add_sub_assoc (r2 - r1) (q2 * S d) (q1 * S d) wanted) in H_main.
  Search (_ + _ = 0 -> _ /\ _).
  Check plus_is_O.
  Check (plus_is_O (r2 - r1) (q2 * S d - q1 * S d)).
  Check (plus_is_O (r2 - r1) (q2 * S d - q1 * S d) H_main).
  destruct (plus_is_O (r2 - r1) (q2 * S d - q1 * S d) H_main) as [H_r2_r1 H_q2_q1].
  Check (helpful_2 r2 r1 H_r2_r1).
  Search (_ < _ -> ~ (_ <= _)).
  Check lt_not_le.
  Check (lt_not_le r1 r2 lt_r1_r2).
  Check (lt_not_le r1 r2 lt_r1_r2 (helpful_2 r2 r1 H_r2_r1)).
  contradiction (lt_not_le r1 r2 lt_r1_r2 (helpful_2 r2 r1 H_r2_r1)).
Qed.

Lemma uniqueness_lt_eq :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 < q2 ->
    r1 = r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 eq_r1_r2.
  (* easy: use plus_reg_l and times_reg_l *)
Admitted.

Lemma uniqueness_lt_gt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 < q2 ->
    r2 < r1 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r2_r1.
  (* subtract r2 and q1 * S d, and deduce a contradiction *)
Admitted.

Lemma uniqueness_eq_lt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 = q2 ->
    r1 < r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r1_r2.
  (* easy: use plus_reg_l *)
Admitted.

Lemma uniqueness_eq_eq :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 = q2 ->
    r1 = r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 eq_r1_r2.
  exact (conj eq_q1_q2 eq_r1_r2).
Qed.

Lemma uniqueness_eq_gt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q1 = q2 ->
    r2 < r1 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r2_r1.
  symmetry in H_main.
  (* use uniqueness_eq_lt *)
(*
  destruct (uniqueness_eq_lt n d ...) as [eq_q2_q1 eq_r2_r1].
  exact (conj eq_q1_q2 (eq_sym eq_r2_r1)).
*)
Admitted.

Lemma uniqueness_gt_lt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q2 < q1 ->
    r1 < r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 lt_r1_r2.
  symmetry in H_main.
  (* use uniqueness_lt_gt *)
(*
  destruct (uniqueness_lt_gt n d ...) as [eq_q2_q1 eq_r2_r1].
  exact (conj (eq_sym eq_q2_q1) (eq_sym eq_r2_r1)).
*)
Admitted.

Lemma uniqueness_gt_eq :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q2 < q1 ->
    r1 = r2 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main gt_q1_q2 eq_r1_r2.
  symmetry in H_main.
  (* use uniqueness_lt_eq *)
(*
  destruct (uniqueness_lt_eq n d ...) as [lt_q2_q1 eq_r2_r1].
  exact (conj (eq_sym lt_q2_q1) eq_r1_r2).
*)
Admitted.

Lemma uniqueness_gt_gt :
  forall n d q1 r1 q2 r2 : nat,
    r1 < S d ->
    r2 < S d ->
    q1 * S d + r1 = q2 * S d + r2 ->
    q2 < q1 ->
    r2 < r1 ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main gt_q1_q2 gt_r1_r2.
  symmetry in H_main.
  (* use uniqueness_lt_lt *)
(*
  destruct (uniqueness_lt_lt n d ...) as [lt_q2_q1 lt_r2_r1].
  exact (conj (eq_sym lt_q2_q1) (eq_sym lt_r2_r1)).
*)
Admitted.

Lemma uniqueness :
  forall n d : nat,
  forall q1 r1 : nat,
    r1 < S d ->
    n = q1 * S d + r1 ->
    forall q2 r2 : nat,
      r2 < S d ->
      n = q2 * S d + r2 ->
      q1 = q2 /\ r1 = r2.
Proof.
  intros n d q1 r1 lt_r1_Sd H_n1 q2 r2 lt_r2_Sd H_n2.
  assert (H_main := H_n2).
  rewrite -> H_n1 in H_main.
  Search (_ < _ \/ _ = _ \/ _ < _).
  Check (Nat.lt_trichotomy r1 r2).
  destruct (Nat.lt_trichotomy q1 q2) as [lt_q1_q2 | [eq_q1_q2 | lt_q2_q1]];
    destruct (Nat.lt_trichotomy r1 r2) as [lt_r1_r2 | [eq_r1_r2 | lt_r2_r1]].

  - exact (uniqueness_lt_lt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r1_r2).

  - exact (uniqueness_lt_eq n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 eq_r1_r2).

  - exact (uniqueness_lt_gt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q1_q2 lt_r2_r1).

  - exact (uniqueness_eq_lt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r1_r2).

  - exact (uniqueness_eq_eq n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 eq_r1_r2).

  - exact (uniqueness_eq_gt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main eq_q1_q2 lt_r2_r1).

  - exact (uniqueness_gt_lt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 lt_r1_r2).

  - exact (uniqueness_gt_eq n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 eq_r1_r2).

  - exact (uniqueness_gt_gt n d q1 r1 q2 r2 lt_r1_Sd lt_r2_Sd H_main lt_q2_q1 lt_r2_r1).
Qed.

(* ********** *)

(* end of week-08_uniqueness-of-the-quotient-and-remainder.v *)

(* week-09_formalizing-summations.v *)

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
       Check Nat.add_cancel_l.
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
    Check (H_f_i (S x')).
    Search (_ <= _).
    Check (Nat.le_refl (S x')).
    Check (H_f_i (S x') (Nat.le_refl (S x'))).
    rewrite -> (H_f_i (S x') (Nat.le_refl (S x'))).
    rewrite -> Nat.add_0_r.
    apply IHx'.
    intros i le_i_x'.
    Check (Nat.le_trans i x' (S x')).
    Check (Nat.le_succ_diag_r x').
    Check (Nat.le_trans i x' (S x') le_i_x' (Nat.le_succ_diag_r x')).
    Check (H_f_i i (Nat.le_trans i x' (S x') le_i_x' (Nat.le_succ_diag_r x'))).
    exact (H_f_i i (Nat.le_trans i x' (S x') le_i_x' (Nat.le_succ_diag_r x'))).
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

(* euclidean_division.v *)

Proposition euclids_division :
  forall d : nat,
    0 < d ->
    forall n : nat,
    exists q r : nat,
      r < d /\ n = q * d + r.
Proof.
  intros d lt_0_d n.
  induction n as [ | n' [q [r [lt_r_Sd' H_n]]]].
  - exists 0, 0.
    split.
    + exact lt_0_d.
    + rewrite -> Nat.add_0_r.
      rewrite -> Nat.mul_0_l.
      reflexivity.
  - case d as [ | d'].
    -- Check (Nat.nlt_0_r 0 lt_0_d).
       contradiction (Nat.nlt_0_r 0 lt_0_d).
    -- Check (le_lt_or_eq).
       Check (lt_le_S r (S d') lt_r_Sd').
       Check (le_S_n r d').
       case (le_lt_or_eq r d' (le_S_n r d' (lt_le_S r (S d') lt_r_Sd'))) as [lt_r_d' | eq_r_d'].
       + exists q, (S r).
         split.
         ++ Search (S _ < S _).
            destruct (Nat.succ_lt_mono r d') as [lt_Sr_Sd' _].
            exact (lt_Sr_Sd' lt_r_d').
         ++ rewrite -> H_n.
            Search (S (_ + _)).
            rewrite -> plus_n_Sm.
            reflexivity.
       + exists (S q), 0.
         split.
         ++ exact lt_0_d.
         ++ rewrite -> H_n.
            rewrite -> plus_n_Sm.
            rewrite -> eq_r_d'.
            rewrite <- Nat.mul_succ_l.
            rewrite -> Nat.add_0_r.
            reflexivity.
Qed.

Proposition euclids_division_alt :
  forall d n : nat,
  exists q r : nat,
    r < S d /\ n = q * (S d) + r.
Proof.
  intros d n.
  induction n as [ | n' [q [r [lt_r_Sd H_n]]]].
  - exists 0, 0.
    split.
    + Search (0 < S _).
      exact (Nat.lt_0_succ d).
    + rewrite -> (Nat.add_0_r (0 * S d)).
      rewrite -> (Nat.mul_0_l (S d)).
      reflexivity.
  - case (le_lt_or_eq r d (le_S_n r d (lt_le_S r (S d) lt_r_Sd))) as [lt_r_d | eq_r_d].
    -- exists q, (S r).
       split.
       + destruct (Nat.succ_lt_mono r d) as [lt_Sr_Sd _].
         exact (lt_Sr_Sd lt_r_d).
       + rewrite -> H_n.
         rewrite -> plus_n_Sm.
         reflexivity.
    -- exists (S q), 0.
       split.
       + exact (Nat.lt_0_succ d).
       + rewrite -> H_n.
         rewrite -> plus_n_Sm.
         rewrite -> eq_r_d.
         rewrite <- Nat.mul_succ_l.
         rewrite -> Nat.add_0_r.
         reflexivity.
Qed.

Corollary euclids_division_alt_using_euclids_division :
  forall d n : nat,
  exists q r : nat,
    r < S d /\ n = q * (S d) + r.
Proof.
  intro d.
  exact (euclids_division (S d) (Nat.lt_0_succ d)).
Qed.

Corollary euclids_division_using_euclids_division_alt :
  forall d : nat,
    0 < d ->
    forall n : nat,
    exists q r : nat,
      r < d /\ n = q * d + r.
Proof.
  intros d lt_0_d n.
  case d as [ | d'].
  - contradiction (Nat.nlt_0_r 0 lt_0_d).
  - exact (euclids_division_alt d' n).
Qed.

(* end of euclidean_division.v *)

(* week-09_formalizing-two-by-two-matrices.v *)


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
  rewrite -> (nat_add_shuffle1 (x11 * y11 * z11) (x11 * y12 * z21) (x12 * y21 * z11) (x12 * y22 * z21)).
  rewrite -> (nat_add_shuffle1 (x11 * y11 * z12) (x11 * y12 * z22) (x12 * y21 * z12) (x12 * y22 * z22)).
  rewrite -> (nat_add_shuffle1 (x21 * y11 * z11) (x21 * y12 * z21) (x22 * y21 * z11) (x22 * y22 * z21)).
  rewrite -> (nat_add_shuffle1 (x21 * y11 * z12) (x21 * y12 * z22) (x22 * y21 * z12) (x22 * y22 * z22)).
  reflexivity.

  Restart. 

(*
  A simpler solution showed by Prof Danvy in which instead of supplying every particular argument to nat_add_shuffle1,
  we provide the more general structure / shape we want the rewrite to apply to. 
 *)  

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

(* Two accumulators implementation *) 

Fixpoint aux_fib (n : nat) (a : nat) (b : nat) : nat :=
  match n with
  | 0 => a
  | S n' => aux_fib n' b (a + b)
  end.

Definition fib (n : nat) : nat :=
  aux_fib n 0 1.

Lemma fold_unfold_aux_fib_O :
  forall (a b : nat),
  aux_fib 0 a b = a.
Proof.
  fold_unfold_tactic aux_fib.
Qed.

Lemma fold_unfold_aux_fib_S :
  forall (n : nat)
         (a b : nat),
    aux_fib (S n) a b = aux_fib n b (a + b).
Proof.
  fold_unfold_tactic aux_fib.
Qed.

(* Canonical definition of the fibonacci function *) 

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
    fib' (S (S n')) = fib' (S n') + fib' n'.
Proof.
  fold_unfold_tactic fib'.
Qed.

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

(* Using two accumulators *) 

Lemma about_aux_fib_S :
  forall (n a b a' b': nat),
    aux_fib n a b + aux_fib n a' b' =
      aux_fib n (a + a') (b + b').
Proof.
  intro n.
  induction n as [ | n' IHn'].
  + intros a b a' b'.
    rewrite -> (fold_unfold_aux_fib_O a b).
    rewrite -> (fold_unfold_aux_fib_O a' b').
    rewrite -> (fold_unfold_aux_fib_O (a + a') (b + b')).
    reflexivity.
  + intros a b a' b'.
    rewrite -> (fold_unfold_aux_fib_S n' a b).
    rewrite -> (fold_unfold_aux_fib_S n' a' b').
    rewrite -> (IHn' b (a + b) b' (a' + b')).
    Search (_ + _ + ( _ ) = _ + _ + _ ).
    (*  (a + b + (a' + b')) ->
        (a + a' + (b + b'))*)
    rewrite -> (nat_add_shuffle1 a b a' b').
    rewrite -> (fold_unfold_aux_fib_S n' (a + a') (b + b')).
    reflexivity.
Qed.

Lemma function_abstraction_and_instantiation :
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
  + intro n'.

    induction n' as [ | n' IHn''].
    ++ unfold F, fib.
       rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) 0).
       rewrite -> (fold_unfold_pow_m22_l_O (M22 1 1 1 0)).
       rewrite -> (mul_m22_identity_l (M22 1 1 1 0)).

       rewrite -> (fold_unfold_aux_fib_S 1 0 1).
       rewrite -> (Nat.add_0_l 1).
       rewrite -> (fold_unfold_aux_fib_S 0 1 1).
       rewrite -> (Nat.add_1_l 1).
       rewrite -> (fold_unfold_aux_fib_O 1 2).

       rewrite -> (fold_unfold_aux_fib_S 0 0 1).
       rewrite -> (Nat.add_0_l 1).
       rewrite -> (fold_unfold_aux_fib_O 1 1).

       rewrite -> (fold_unfold_aux_fib_O 0 1).
       reflexivity.
    ++ unfold F, fib.
       unfold F, fib in IHn''.
       rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) (S n')).
       rewrite -> IHn''.
       rewrite -> (fold_unfold_aux_fib_S (S n') 0 1).
       rewrite -> (Nat.add_0_l 1).
       rewrite -> (fold_unfold_aux_fib_S n' 1 1).
       rewrite -> (Nat.add_1_l 1).

       rewrite -> (fold_unfold_aux_fib_S n' 0 1).
       rewrite -> (Nat.add_0_l 1).

       unfold mul_m22.

       rewrite -> 3 Nat.mul_1_r.
       rewrite -> 2 Nat.mul_0_r.
       rewrite -> 2 Nat.add_0_r.
       
       rewrite -> (fold_unfold_aux_fib_S (S (S n')) 0 1).
       rewrite -> (Nat.add_0_l 1).
       rewrite -> (fold_unfold_aux_fib_S (S n') 1 1).
       rewrite -> (Nat.add_1_l 1).
       rewrite -> (fold_unfold_aux_fib_S n' 1 2).
       rewrite -> (Nat.add_1_l 2).
       
       rewrite -> (about_aux_fib_S n' 1 2 1 1).
       rewrite -> (Nat.add_1_r 1).
       rewrite -> (Nat.add_1_r 2).

       rewrite -> (about_aux_fib_S n' 1 1 0 1).
       rewrite -> (Nat.add_1_l 0).
       rewrite -> (Nat.add_1_l 1).
       reflexivity.
Qed.

(* Using canonical definition of the fibonacci function *) 

Lemma function_abstraction_and_instantiation' :
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
    
    induction n' as [ | n' IHn''].
    ++ unfold F, fib'.
       rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) 0).
       rewrite -> (fold_unfold_pow_m22_l_O (M22 1 1 1 0)).
       rewrite -> (mul_m22_identity_l (M22 1 1 1 0)).
       rewrite -> Nat.add_0_r.
       reflexivity.
    ++ unfold F.
       unfold F in IHn''.
       rewrite -> (fold_unfold_pow_m22_l_S (M22 1 1 1 0) (S n')).
       rewrite -> IHn''.
       unfold mul_m22.
       rewrite -> 3 Nat.mul_1_r.
       rewrite -> 2 Nat.mul_0_r.
       rewrite -> 2 Nat.add_0_r.
       rewrite <- 2 fold_unfold_fib'_S.
       reflexivity.
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

(* end of week-09_formalizing-two-by-two-matrices.v *)
