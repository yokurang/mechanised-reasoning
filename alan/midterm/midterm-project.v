(* midterm-project.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 28 Sep 2023 with no occurrence of "direct style" *)
(* was: *)
(* Version of 19 Sep 2023 *)

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

(* A study of polymorphic lists. *)

(* members of the group:
   date: 

   please upload one .v file and one .pdf file containing a project report

   desiderata:
   - the file should be readable, i.e., properly indented and using items or {...} for subgoals
   - each use of a tactic should achieve one proof step
   - all lemmas should be applied to all their arguments
   - there should be no occurrences of admit, Admitted, and Abort
*)

(* ********** *)

(*
  1. Unit test properties or inductive step (Intro to CS Stuff) 
*)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

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

(* ***** *)

(* Task 1: *)

Theorem soundness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall v1s v2s : list V,
      eqb_list V eqb_V v1s v2s = true ->
      v1s = v2s.
Proof.
  intros V eqb_V H_v1_v2 v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  + intros v2s H_v1s_v2s.
    case v2s as [ | v2 v2s'].
    ++
      reflexivity.
    ++ rewrite -> (fold_unfold_eqb_list_nil V eqb_V (v2 :: v2s')) in H_v1s_v2s.
       discriminate H_v1s_v2s.
  + intros v2s H_v1s_v2s.
    case v2s as [ | v2 v2s'].
    ++ rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' nil) in H_v1s_v2s.
       discriminate H_v1s_v2s.
    ++ rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v2 :: v2s')) in H_v1s_v2s.
       Search (_ && _ = true).
       destruct (andb_prop (eqb_V v1 v2) (eqb_list V eqb_V v1s' v2s') (H_v1s_v2s)) as [v1_equals_v2 v1s'_equals_v2s'].
       rewrite -> (H_v1_v2 v1 v2 v1_equals_v2).
       rewrite -> (IHv1s' v2s' v1s'_equals_v2s').
       reflexivity.
Qed.
(* Abort. *)

Theorem completeness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall v1s v2s : list V,
      v1s = v2s ->
      eqb_list V eqb_V v1s v2s = true.
Proof.
  intros V eqb_V H_v1_v2 v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  + intros v2s H_v1s_v2s.
     case v2s as [ | v2 v2s'].
     ++ rewrite -> (fold_unfold_eqb_list_nil V eqb_V nil).
         reflexivity.
     ++ discriminate H_v1s_v2s.
  + intros v2s H_v1s_v2s.
    case v2s as [ | v2 v2s'].
    ++ discriminate H_v1s_v2s.
    ++ rewrite <- H_v1s_v2s.
       rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v1 :: v1s')).
       Search (_ && _ = true).
       destruct (andb_true_iff (eqb_V v1 v1) (eqb_list V eqb_V v1s' v1s')) as [_ H_tmp].
       apply H_tmp.
       split.
       +++
         apply (H_v1_v2 v1 v1).
         reflexivity.
       +++
         apply (IHv1s' v1s').
         reflexivity.
Qed.       
(* Abort. *)

(* ********** *)

(* A study of the polymorphic length function: *)

Definition specification_of_list_length (length : forall V : Type, list V -> nat) :=
  (forall V : Type,
      length V nil = 0)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     length V (v :: vs') = S (length V vs')).

(* Unit-test function: *)

Definition test_list_length (candidate : forall V : Type, list V -> nat) :=
  (candidate nat nil =? 0) &&
    (candidate bool nil =? 0) &&
    (candidate nat (1 :: nil) =? 1) &&
    (candidate bool (true :: nil) =? 1) &&
    (candidate nat (2 :: 1 :: nil) =? 2) &&
    (candidate bool (false :: true :: nil) =? 2) &&
    (candidate nat (3 :: 2 :: 1 :: nil) =? 3) &&
    (candidate bool (false :: false :: true :: nil) =? 3) &&
    (candidate nat (5 :: 4 :: 3 :: 2 :: 1 :: nil) =? 5) &&
    (candidate bool (true :: true :: false :: false :: true :: nil) =? 5).

(* The specification specifies at most one length function: *)

Theorem there_is_at_most_one_list_length_function :
  forall (V : Type)
         (list_length_1 list_length_2 : forall V : Type, list V -> nat),
    specification_of_list_length list_length_1 ->
    specification_of_list_length list_length_2 ->
    forall vs : list V,
      list_length_1 V vs = list_length_2 V vs.
Proof.
  intros V list_length_1 list_length_2.
  unfold specification_of_list_length.
  intros [S_list_length_1_nil S_list_length_1_cons]
         [S_list_length_2_nil S_list_length_2_cons]
         vs.
  induction vs as [ | v vs' IHvs'].

  - Check (S_list_length_2_nil V).
    rewrite -> (S_list_length_2_nil V).
    Check (S_list_length_1_nil V).
    exact (S_list_length_1_nil V).

  - Check (S_list_length_1_cons V v vs').
    rewrite -> (S_list_length_1_cons V v vs').
    rewrite -> (S_list_length_2_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* Recursive implementation of the length function: *)

Fixpoint list_length (V : Type) (vs : list V) : nat :=
  match vs with
    | nil =>
      0
    | v :: vs' =>
      S (list_length V vs')
  end.

Compute (test_list_length list_length).

(* Associated fold-unfold lemmas: *)

Lemma fold_unfold_list_length_nil :
  forall V : Type,
    list_length V nil =
    0.
Proof.
  fold_unfold_tactic list_length.
Qed.

Lemma fold_unfold_list_length_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_length V (v :: vs') =
    S (list_length V vs').
Proof.
  fold_unfold_tactic list_length.
Qed.

(* The specification specifies at least one length function: *)

Theorem list_length_satisfies_the_specification_of_list_length :
  specification_of_list_length list_length.
Proof.
  unfold specification_of_list_length.
  exact (conj fold_unfold_list_length_nil fold_unfold_list_length_cons).
Qed.

(* ***** *)

(* Task 2: *)

(* Implement the length function using an accumulator. *)


Fixpoint list_length_acc (V : Type) (ls : list V) (a : nat) : nat :=
  match ls with
  | nil =>
      a
  | v :: vs' =>
      list_length_acc V vs' (S a)
  end.


Definition list_length_alt (V : Type) (vs : list V) : nat :=
  list_length_acc V vs 0.

Compute (test_list_length list_length_alt).

Lemma fold_unfold_list_length_acc_nil :
  forall (V : Type)
         (acc : nat),
    list_length_acc V nil acc =
      acc.
Proof.
  fold_unfold_tactic list_length_acc.
Qed.

Lemma fold_unfold_list_length_acc_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (acc : nat),
    list_length_acc V (v :: vs') acc =
      list_length_acc V vs' (S acc).
Proof.
  fold_unfold_tactic list_length_acc.
Qed.

Lemma list_length_S_acc_equals_S_list_length : 
  forall (V: Type)
         (v : V)
         (vs' : list V)
         (a : nat),
    list_length_acc V vs' (S a) = S (list_length_acc V vs' a).
Proof.
  intros V v vs'.
  revert v.
  induction vs' as [ | v' vs'' IHvs''].
  + intros v a.
    rewrite -> (fold_unfold_list_length_acc_nil V (S a)).
    rewrite -> (fold_unfold_list_length_acc_nil V a).
    reflexivity.
  + intros v a.
    rewrite -> (fold_unfold_list_length_acc_cons V v' vs'' (S a)).
    rewrite -> (fold_unfold_list_length_acc_cons V v' vs'' a).
    Check (IHvs'' v (S a)).
    exact (IHvs'' v (S a)).
Qed.

Theorem list_length_alt_satisfies_the_specification_of_list_length :
  specification_of_list_length list_length_alt.
Proof.
  unfold specification_of_list_length, list_length_alt.
  split.
  + intro V.
    rewrite -> (fold_unfold_list_length_acc_nil V 0).
    reflexivity.
  + intros V v vs'.
    rewrite -> (fold_unfold_list_length_acc_cons V v vs' 0).
    rewrite -> (list_length_S_acc_equals_S_list_length V v vs' 0).
    reflexivity.
Qed.

(* ********** *)

(* A study of the polymorphic copy function: *)


Definition specification_of_list_copy (copy : forall V : Type, list V -> list V) :=
  (forall V : Type,
      copy V nil = nil)
  /\
    (forall (V : Type)
            (v : V)
            (vs' : list V),
        copy V (v :: vs') = v :: (copy V vs')).

Proposition there_is_at_most_one_function_that_satisfies_the_specification_of_list_copy :
  forall list_copy_v1 list_copy_v2 : forall V : Type, list V -> list V,
    specification_of_list_copy list_copy_v1 /\ specification_of_list_copy list_copy_v2 ->
    forall (V : Type)
           (vs : list V),     
      list_copy_v1 V vs = list_copy_v2 V vs.
Proof.
  intros list_copy_v1 list_copy_v2.
  unfold specification_of_list_copy.
  intros [[S_list_copy_v1_nil S_list_copy_v1_cons] [S_list_copy_v2_nil S_list_copy_v2_cons]].
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (S_list_copy_v2_nil V).
    exact (S_list_copy_v1_nil V).
  - rewrite -> (S_list_copy_v2_cons V v vs').
    rewrite -> (S_list_copy_v1_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

Proposition there_is_at_most_one_function_that_satisfies_the_specification_of_list_copy' :
  forall list_copy_v1 list_copy_v2 : forall V : Type, list V -> list V,
    specification_of_list_copy list_copy_v1 ->
    specification_of_list_copy list_copy_v2 ->
    forall (V : Type)
           (vs : list V),     
      list_copy_v1 V vs = list_copy_v2 V vs. (* standard: the curried way *)
Proof.
  intros list_copy_v1 list_copy_v2.
  intros S_list_copy_v1 S_list_copy_v2.
  Check (there_is_at_most_one_function_that_satisfies_the_specification_of_list_copy list_copy_v1 list_copy_v2).
  Check (there_is_at_most_one_function_that_satisfies_the_specification_of_list_copy list_copy_v1 list_copy_v2 (conj S_list_copy_v1 S_list_copy_v2)).
  exact (there_is_at_most_one_function_that_satisfies_the_specification_of_list_copy list_copy_v1 list_copy_v2 (conj S_list_copy_v1 S_list_copy_v2)).
  Show Proof.
Qed.
   
Definition test_list_copy (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
    (eqb_list bool Bool.eqb (candidate bool nil) nil) &&
    (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) (1 :: nil)) &&
    (eqb_list bool Bool.eqb (candidate bool (true :: nil)) (true :: nil)) &&
    (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil)) (2 :: 1 :: nil)) &&
    (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil)) (false :: true :: nil)).

(* ***** *)

(* Task 3: *)

(*
   a. Expand the unit-test function for copy with a few more tests.
*)

Definition test_list_copy_expanded (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil)) (false :: true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (4 :: 3 :: 2 :: 1 :: nil)) (4 :: 3 :: 2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: false :: false :: true :: nil)) (true :: false :: false :: true :: nil)).
      
(*
   b. Implement the copy function recursively.
*)

Fixpoint list_copy (V : Type) (vs : list V) : list V :=
  match vs with
  | nil =>
      nil
  | v :: vs' =>
      v :: list_copy V vs'
  end.

Compute (test_list_copy_expanded list_copy).

(*
   c. State its associated fold-unfold lemmas.
*)

Lemma fold_unfold_list_copy_nil :
  forall V : Type,
    list_copy V nil =
      nil.
Proof.
  fold_unfold_tactic list_copy.
Qed.

Lemma fold_unfold_list_copy_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_copy V (v :: vs') =
      v :: list_copy V vs'.
Proof.
  fold_unfold_tactic list_copy.
Qed.
      
(*
   d. Prove whether your implementation satisfies the specification.
*)

Theorem list_copy_satisfies_the_specification_of_list_copy :
  specification_of_list_copy list_copy.
Proof.
  unfold specification_of_list_copy.
  exact (conj fold_unfold_list_copy_nil fold_unfold_list_copy_cons).
Qed.
      
(*
   e. Prove whether copy is idempotent.
*)

Proposition list_copy_is_idempotent :
  forall (V : Type)
         (vs : list V),
    list_copy V (list_copy V vs) = list_copy V vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_list_copy_nil V).
    rewrite -> (fold_unfold_list_copy_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_list_copy_cons V v vs').
    rewrite -> (fold_unfold_list_copy_cons V v (list_copy V vs')).
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   f. Prove whether copying a list preserves its length.
*)

Proposition list_copy_preserves_list_length :
  forall (V : Type)
         (vs : list V),
    list_length V (list_copy V vs) = list_length V vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_list_copy_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_list_copy_cons V v vs').
    rewrite -> (fold_unfold_list_length_cons V v (list_copy V vs')).
    rewrite -> (fold_unfold_list_length_cons V v vs').    
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   g. Subsidiary question: can you think of a strikingly simple implementation of the copy function?
      if so, pray show that it satisfies the specification of copy;
      is it equivalent to your recursive implementation?
*)

Definition list_copy_v2 (V : Type) (vs : list V) : list V := vs.

Compute (test_list_copy list_copy_v2).

Proposition list_copy_v2_satisfies_the_specification_of_list_copy :
  specification_of_list_copy list_copy_v2.
Proof.
  unfold specification_of_list_copy, list_copy_v2.
  split.
  - intro V.
    reflexivity.
  - intros V v vs'.
    reflexivity.
Qed.

Proposition list_copy_and_list_copy_v2_are_equivalent :
  forall (V : Type)
         (vs : list V),
    list_copy V vs = list_copy_v2 V vs.
Proof.
  Check (there_is_at_most_one_function_that_satisfies_the_specification_of_list_copy' list_copy list_copy_v2 list_copy_satisfies_the_specification_of_list_copy list_copy_v2_satisfies_the_specification_of_list_copy).
  exact (there_is_at_most_one_function_that_satisfies_the_specification_of_list_copy' list_copy list_copy_v2 list_copy_satisfies_the_specification_of_list_copy list_copy_v2_satisfies_the_specification_of_list_copy).
Qed.
      
Proposition list_copy_v2_preserves_list_length :
  forall (V : Type)
         (vs : list V),
    list_length V (list_copy_v2 V vs) = list_length V vs.
Proof.
  intros V vs.
  unfold list_copy_v2.
  reflexivity.
Qed.
      
(* ********** *)

(* A study of the polymorphic append function: *)

Definition specification_of_list_append (append : forall V : Type, list V -> list V -> list V) :=
  (forall (V : Type)
          (v2s : list V),
      append V nil v2s = v2s)
  /\
  (forall (V : Type)
          (v1 : V)
          (v1s' v2s : list V),
      append V (v1 :: v1s') v2s = v1 :: append V v1s' v2s).

(* ***** *)

(* Task 4: *)

(*
   a. Define a unit-test function for append.
*)


Definition test_list_append (candidate : forall V : Type, list V -> list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: nil) (1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: nil) (true :: nil)) (false :: true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (4 :: 3 :: nil) (2 :: 1 :: nil)) (4 :: 3 :: 2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil) (false :: true :: nil)) (false :: true :: false :: true :: nil)).

(*
   b. Implement the append function recursively.
*)

Fixpoint list_append (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
  | nil =>
      v2s
  | v1 :: v1s' =>
      v1 :: list_append V v1s' v2s
  end.

Compute test_list_append list_append.
      
(*
   c. State its associated fold-unfold lemmas.
*)

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
      
(*
   d. Prove that your implementation satisfies the specification.
*)

Theorem list_append_satisfies_the_specification_of_list_append :
  specification_of_list_append list_append.
Proof.
  unfold specification_of_list_append.
  exact (conj fold_unfold_list_append_nil fold_unfold_list_append_cons).
Qed.

(*
   e. Prove whether nil is neutral on the left of append.
*)

Proposition nil_is_neutral_on_the_left_of_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V nil vs = vs.
Proof.
  intros V vs.
  exact (fold_unfold_list_append_nil V vs).
Qed.
      
(*
   f. Prove whether nil is neutral on the right of append.
*)

Proposition nil_is_neutral_on_the_right_of_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V vs nil = vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - exact (fold_unfold_list_append_nil V nil).
  - rewrite -> (fold_unfold_list_append_cons V v vs' nil).
    rewrite -> IHvs'.
    reflexivity.
Qed.
      
(*
   g. Prove whether append is commutative.
*)

Proposition list_append_is_not_commutative :
  exists (V : Type)
         (v1s v2s : list V),
    list_append V v1s v2s <> list_append V v2s v1s.
Proof.
  exists nat, (1 :: nil), (2 :: nil).
  unfold not.
  unfold list_append.
  intro H_absurd.
  discriminate H_absurd.
Qed.
      
(*
   h. Prove whether append is associative.
*)

Proposition list_append_is_associative :
  forall (V : Type)
         (v1s v2s v3s : list V),
    list_append V v1s (list_append V v2s v3s) = list_append V (list_append V v1s v2s) v3s.
Proof.
  intros V v1s v2s v3s.
  induction v1s as [ | v v1s' IHv1s'].
  - rewrite -> (fold_unfold_list_append_nil V (list_append V v2s v3s)).
    rewrite -> (fold_unfold_list_append_nil V v2s).
    reflexivity.
  - rewrite -> (fold_unfold_list_append_cons V v v1s' (list_append V v2s v3s)).
    rewrite -> (fold_unfold_list_append_cons V v v1s' v2s).
    rewrite -> (fold_unfold_list_append_cons V v (list_append V v1s' v2s) v3s).
     rewrite -> IHv1s'.
    reflexivity.
Qed.
      
(*
   i. Prove whether appending two lists preserves their length.
*)

Proposition append_and_length_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_length V (list_append V v1s v2s) = list_length V v1s + list_length V v2s.
Proof.
  intros V v1s v2s.
  induction v1s as [ | v v1s' IHv1s'].
  - rewrite -> (fold_unfold_list_append_nil V v2s).
    rewrite -> (fold_unfold_list_length_nil V).
    rewrite -> (Nat.add_0_l (list_length V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_list_append_cons V v v1s' v2s).
    rewrite -> (fold_unfold_list_length_cons V v (list_append V v1s' v2s)).
    rewrite -> (fold_unfold_list_length_cons V v v1s').
    rewrite -> IHv1s'.
    Search (S _ + _ = S (_ + _)).
    rewrite <- (Nat.add_succ_l (list_length V v1s') (list_length V v2s)).
    reflexivity.
Qed.

(*
   j. Prove whether append and copy commute with each other.
*)

Proposition append_and_copy_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_copy V (list_append V v1s v2s) = list_append V (list_copy V v1s) (list_copy V v2s).
Proof.
  intros V v1s v2s.
  induction v1s as [ | v v1s' IHv1s'].
  - rewrite -> (fold_unfold_list_append_nil V v2s).
    rewrite -> (fold_unfold_list_copy_nil V).
    rewrite -> (fold_unfold_list_append_nil V (list_copy V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_list_append_cons V v v1s' v2s).
    rewrite -> (fold_unfold_list_copy_cons V v (list_append V v1s' v2s)).
    rewrite -> (fold_unfold_list_copy_cons V v v1s').
    rewrite -> (fold_unfold_list_append_cons V v (list_copy V v1s') (list_copy V v2s)).
    rewrite -> IHv1s'.
    reflexivity.

    Restart.

    (* simpler proof using the "more equal" version of list_copy *)
    
    intros V v1s v2s.
    rewrite -> (list_copy_and_list_copy_v2_are_equivalent V (list_append V v1s v2s)).
    rewrite -> (list_copy_and_list_copy_v2_are_equivalent V v1s).
    rewrite -> (list_copy_and_list_copy_v2_are_equivalent V v2s).
    unfold list_copy_v2.
    reflexivity.
Qed.


(* ********** *)

(* A study of the polymorphic reverse function: *)

Definition specification_of_list_reverse (reverse : forall V : Type, list V -> list V) :=
  forall append : forall W : Type, list W -> list W -> list W,
    specification_of_list_append append ->
    (forall V : Type,
        reverse V nil = nil)
    /\
    (forall (V : Type)
            (v : V)
            (vs' : list V),
        reverse V (v :: vs') = append V (reverse V vs') (v :: nil)).

(* ***** *)

(* Task 5: *)

(*
   a. Define a unit-test function for an implementation of the reverse function.
*)

Definition test_list_reverse (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil)) (1 :: 2 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil)) (true :: false :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (3 :: 2 :: 1 :: nil)) (1 :: 2 :: 3 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: false :: true :: nil)) (true :: false :: false :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (5 :: 4 :: 3 :: 2 :: 1 :: nil)) (1 :: 2 :: 3 :: 4 :: 5 :: nil)).

(*
   b. Implement the reverse function recursively, using list_append.
*)

Fixpoint list_reverse (V : Type) (vs : list V) : list V :=
  match vs with
  | nil =>
      nil
  | v :: vs' =>
      list_append V (list_reverse V vs') (v :: nil)
  end.

Compute test_list_reverse list_reverse.

(*
   c. State the associated fold-unfold lemmas.
*)

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

(*
   d. Prove whether your implementation satisfies the specification.
 *)

Proposition there_is_at_most_one_list_append_function :
  forall (append1 append2 : forall V : Type, list V -> list V -> list V)
         (V : Type)
         (v1s v2s: list V),
    specification_of_list_append append1 -> specification_of_list_append append2 ->
    append1 V v1s v2s = append2 V v1s v2s.
Proof.
  intros append1 append2 V v1s v2s.
  unfold specification_of_list_append.
  intros [fold_unfold_append1_nil fold_unfold_append1_cons] [fold_unfold_append2_nil fold_unfold_append2_cons].
  induction v1s as [ | v1 v1s' IHv1s'].
  
  - rewrite -> (fold_unfold_append1_nil V v2s).
    rewrite -> (fold_unfold_append2_nil V v2s).
    reflexivity.
    
  - rewrite -> (fold_unfold_append1_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_append2_cons V v1 v1s' v2s).
    rewrite -> IHv1s'.
    reflexivity.
Qed. 
  

Proposition list_reverse_satisfies_the_specification_of_list_reverse :
  specification_of_list_reverse list_reverse.
Proof.
  unfold specification_of_list_reverse.
  Check (conj fold_unfold_list_reverse_nil fold_unfold_list_reverse_cons).
  intros append H_append.
  split.
  - Check fold_unfold_list_reverse_nil.
    exact fold_unfold_list_reverse_nil.
  - intros V v vs'.
    rewrite -> (fold_unfold_list_reverse_cons V v vs').
    Check (there_is_at_most_one_list_append_function list_append append V
             (list_reverse V vs') (v :: nil)
             list_append_satisfies_the_specification_of_list_append H_append).    
    exact (there_is_at_most_one_list_append_function list_append append V
             (list_reverse V vs') (v :: nil)
             list_append_satisfies_the_specification_of_list_append H_append).
Qed.
    
(*
   e. Prove whether list_reverse is involutory.
 *)

Proposition about_reversing_a_singleton_list_with_list_reverse :
  forall (V : Type)
         (v : V),
    list_reverse V (v :: nil) = (v :: nil).
Proof.
  intros V v.
  rewrite -> (fold_unfold_list_reverse_cons V v nil).
  rewrite -> (fold_unfold_list_reverse_nil V).
  Check fold_unfold_list_append_nil.
  rewrite -> (fold_unfold_list_append_nil V (v :: nil)).
  reflexivity.
Qed.

Lemma append_reverse_cons_element :
    forall (V : Type) (vs : list V) (v : V),
      list_append V (list_reverse V vs) (list_append V (list_reverse V nil) (v :: nil)) = list_reverse V (v :: vs).
Proof.
  intros V vs v.
  rewrite -> (fold_unfold_list_reverse_nil V).
  rewrite -> (fold_unfold_list_append_nil V (v :: nil)).
  Check (fold_unfold_list_reverse_cons). 
  rewrite -> (fold_unfold_list_reverse_cons V v vs).
  reflexivity.
Qed.

Proposition list_reverse_distributes_over_list_append :
  forall (V : Type)
         (v1s v2s : list V),
    list_reverse V (list_append V v1s v2s) = list_append V (list_reverse V v2s) (list_reverse V v1s).
Proof.
  Compute (let V := nat in
           let v1s := 1 :: 2 :: nil in
           let v2s := 3 :: 4 :: nil in
           list_reverse V (list_append V v1s v2s) = list_append V (list_reverse V v2s) (list_reverse V v1s)).
Proof.
  intros V v1s v2s.
  induction v1s as [ | v v1s' IHv1s'].
  - rewrite -> (fold_unfold_list_append_nil V v2s).  
    rewrite -> (fold_unfold_list_reverse_nil V).
    rewrite -> (nil_is_neutral_on_the_right_of_list_append V (list_reverse V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_list_append_cons V v v1s' v2s).
    rewrite -> (fold_unfold_list_reverse_cons V v (list_append V v1s' v2s)).
    rewrite -> IHv1s'.
    rewrite -> (fold_unfold_list_reverse_cons V v v1s').
    Check (list_append_is_associative V (list_reverse V v2s)(list_reverse V v1s') (v :: nil)). 
    rewrite -> (list_append_is_associative V (list_reverse V v2s)(list_reverse V v1s') (v :: nil)).
    reflexivity.
Qed.                

Proposition list_reverse_is_involutory :
  forall (V : Type)
         (vs : list V),
    list_reverse V (list_reverse V vs) = vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> fold_unfold_list_reverse_nil.
    reflexivity.
  - rewrite -> fold_unfold_list_reverse_cons.
    Check (list_reverse_distributes_over_list_append V (list_reverse V vs') (v :: nil)).
    rewrite -> (list_reverse_distributes_over_list_append V (list_reverse V vs') (v :: nil)).
    rewrite -> IHvs'.
    Check about_reversing_a_singleton_list_with_list_reverse.
    rewrite -> (about_reversing_a_singleton_list_with_list_reverse V v).
    Check fold_unfold_list_append_cons.
    rewrite -> (fold_unfold_list_append_cons V v nil vs').
    rewrite -> (fold_unfold_list_append_nil V vs'). 
    reflexivity.
Qed.

Lemma length_of_singleton_list : 
  forall (V : Type)
         (v : V),
    list_length V (v :: nil) = 1.
Proof.
  intros V v.
  rewrite -> (fold_unfold_list_length_cons V v nil).
  rewrite -> (fold_unfold_list_length_nil V).
  reflexivity.
Qed.

Lemma length_of_append_singleton : 
  forall (V : Type)
         (vs : list V)
         (v : V),
      list_length V (list_append V vs (v :: nil)) = S (list_length V vs).
Proof.
  intros V vs v.
  induction vs as [ | v' vs' IHvs'].
  - rewrite -> (fold_unfold_list_append_nil V). 
    rewrite -> (fold_unfold_list_length_nil V).
    rewrite -> (fold_unfold_list_length_cons V v nil).
    rewrite -> (fold_unfold_list_length_nil V).
    reflexivity.
  - Check fold_unfold_list_append_cons.
    rewrite -> (fold_unfold_list_append_cons V v' vs' (v :: nil)).
    Check (fold_unfold_list_length_cons).
    rewrite -> (fold_unfold_list_length_cons V v' (list_append V vs' (v :: nil))). 
    rewrite -> IHvs'.
    rewrite -> (fold_unfold_list_length_cons V v' vs').
    reflexivity.

    Restart.

    intros V vs v.
    Check (append_and_length_commute_with_each_other V vs (v :: nil)).
    rewrite -> (append_and_length_commute_with_each_other V vs (v :: nil)).
    Check (fold_unfold_list_length_cons).
    assert (list_length V (v :: nil) = 1) as helpful. {
      admit.
    }
    rewrite -> helpful.
    Search  (_ + 1  =S  _).
    exact (Nat.add_1_r (list_length V vs)).

    Restart.

    intros V vs v.
    Check (append_and_length_commute_with_each_other V vs (v :: nil)).
    rewrite -> (append_and_length_commute_with_each_other V vs (v :: nil)).
    Check (fold_unfold_list_length_cons).
    rewrite -> (length_of_singleton_list V v).
    exact (Nat.add_1_r (list_length V vs)).
Qed.

(*
   f. Prove whether reversing a list preserves its length.
*)

Proposition list_reverse_preserves_length :
  forall (V : Type)
         (vs : list V),
    list_length V vs = list_length V (list_reverse V vs).
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> fold_unfold_list_reverse_nil.
    reflexivity.
  - rewrite -> fold_unfold_list_reverse_cons.
    rewrite -> fold_unfold_list_length_cons.
    rewrite -> IHvs'.
    rewrite -> (length_of_append_singleton V (list_reverse V vs') (v)).
    reflexivity.

  Restart.

  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> fold_unfold_list_reverse_nil.
    reflexivity.
  - rewrite -> fold_unfold_list_reverse_cons.
    rewrite -> fold_unfold_list_length_cons.
    rewrite -> IHvs'.    
    Check (append_and_length_commute_with_each_other).
    rewrite (append_and_length_commute_with_each_other V (list_reverse V vs') (v :: nil)).
    rewrite -> (length_of_singleton_list V v).
    symmetry.
    exact (Nat.add_1_r (list_length V (list_reverse V vs'))).
Qed.

(*
   g. Do list_append and list_reverse commute with each other (hint: yes they do) and if so how?
 *)


Proposition list_append_and_list_reverse_commute_with_each_other :
  forall (V : Type)
         (v1s : list V)
         (v2s : list V),
    list_reverse V (list_append V v1s v2s) = list_append V (list_reverse V v2s) (list_reverse V v1s).
Proof.
  intros V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].

  - intro v2s.
    rewrite -> (fold_unfold_list_append_nil V v2s).
    rewrite -> (fold_unfold_list_reverse_nil V).
    rewrite -> (nil_is_neutral_on_the_right_of_list_append V (list_reverse V v2s)).
    reflexivity.

  - intro v2s.
    rewrite -> (fold_unfold_list_append_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_list_reverse_cons V v1 (list_append V v1s' v2s)).
    rewrite -> (IHv1s' v2s).
    rewrite -> (fold_unfold_list_reverse_cons V v1 v1s').
    Check (list_append_is_associative V (list_reverse V v2s) (list_reverse V v1s') (v1 :: nil) ).
    rewrite <- (list_append_is_associative V (list_reverse V v2s) (list_reverse V v1s') (v1 :: nil)).
    reflexivity.
Qed.


(* See list_reverse_distributes_over_list_append. *)

(*
   h. Implement the reverse function using an accumulator instead of using list_append.
 *)

Fixpoint list_reverse_alt_aux (V : Type) (vs acc : list V) : list V :=
  match vs with
  | nil => acc
  | v :: vs' => list_reverse_alt_aux V vs' (v :: acc)
  end.

Definition list_reverse_alt (V : Type) (vs : list V) : list V :=
  list_reverse_alt_aux V vs nil.

Compute test_list_reverse list_reverse_alt.

Lemma fold_unfold_list_reverse_alt_aux_nil :
  forall (V : Type)
         (acc : list V),
    list_reverse_alt_aux V nil acc =
      acc.
Proof.
  fold_unfold_tactic list_reverse_alt_aux.
Qed.

Lemma fold_unfold_list_reverse_alt_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' acc : list V),
    list_reverse_alt_aux V (v :: vs') acc =
      list_reverse_alt_aux V vs' (v :: acc).
Proof.
  fold_unfold_tactic list_reverse_alt_aux.
Qed.

Lemma fold_unfold_list_reverse_alt_nil :
  forall V : Type,
    list_reverse_alt V nil =
      nil.
Proof.
  fold_unfold_tactic list_reverse_alt.
Qed.

Lemma fold_unfold_list_reverse_alt_cons :
  forall (V : Type)
         (v : V)
         (vs' acc : list V),
    list_reverse_alt_aux V (v :: vs') acc =
      list_reverse_alt_aux V vs' (v :: acc).
Proof.
  fold_unfold_tactic list_reverse_alt_aux.
Qed.

(*
   i. Revisit the propositions above (involution, preservation of length, commutation with append)
      and prove whether reverse_v1 satisfies them.
      Two proof strategies are possible:
      (1) direct, stand-alone proofs with Eureka lemmas, and
      (2) proofs that hinge on the equivalence of list_reverse_alt and list_reverse.
      This subtask is very instructive, but optional.
*)

(* ********** *)

Lemma about_list_reverse_alt_aux :
  forall (V : Type)
         (vs a : list V),
    list_reverse_alt_aux V vs a = list_append V (list_reverse_alt_aux V vs nil) a.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].

  - intro a.
    rewrite -> (fold_unfold_list_reverse_alt_aux_nil V a).
    rewrite -> (fold_unfold_list_reverse_alt_aux_nil V nil).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.

  - intro a.
    rewrite -> (fold_unfold_list_reverse_alt_aux_cons V v vs' a).
    rewrite -> (fold_unfold_list_reverse_alt_aux_cons V v vs' nil).
    Check (IHvs' (v :: a)).
    rewrite -> (IHvs' (v :: a)).
    rewrite -> (IHvs' (v :: nil)).
    rewrite <- (list_append_is_associative V (list_reverse_alt_aux V vs' nil) (v :: nil) a).
    rewrite -> (fold_unfold_list_append_cons V v nil a).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.
Qed.

Proposition list_append_and_list_reverse_alt_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_reverse_alt V (list_append V v1s v2s) =
      list_append V (list_reverse_alt V v2s) (list_reverse_alt V v1s).
Proof.
  intros V v1s.
  unfold list_reverse_alt.
  induction v1s as [ | v1 v1s' IHv1s'].

  - intro v2s.
    rewrite -> (fold_unfold_list_append_nil V v2s).
    rewrite -> (fold_unfold_list_reverse_alt_aux_nil V nil).
    rewrite -> (nil_is_neutral_on_the_right_of_list_append V (list_reverse_alt_aux V v2s nil)).
    reflexivity.

  - intro v2s.
    rewrite -> (fold_unfold_list_append_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_list_reverse_alt_aux_cons V v1 (list_append V v1s' v2s) nil).
    rewrite -> (about_list_reverse_alt_aux V (list_append V v1s' v2s) (v1 :: nil)).
    rewrite -> (IHv1s' v2s).
    rewrite -> (fold_unfold_list_reverse_alt_aux_cons V v1 v1s' nil).
    rewrite -> (about_list_reverse_alt_aux V v1s' (v1 :: nil)).
    rewrite -> (list_append_is_associative V (list_reverse_alt_aux V v2s nil)
                  (list_reverse_alt_aux V v1s' nil)
                  (v1 :: nil)).
    reflexivity.
Qed.

Proposition list_reverse_alt_is_involutory :
  forall (V : Type)
         (vs : list V),
    list_reverse_alt V (list_reverse_alt V vs) = vs.
Proof.
  intros V vs.
  unfold list_reverse_alt.
  induction vs as [ | v vs' IHvs'].

  - rewrite -> (fold_unfold_list_reverse_alt_aux_nil V nil).
    rewrite -> (fold_unfold_list_reverse_alt_aux_nil V nil).
    reflexivity.

  - rewrite -> (fold_unfold_list_reverse_alt_aux_cons V v vs' nil).
    rewrite -> (about_list_reverse_alt_aux V vs' (v :: nil)).
    assert (eureka := list_append_and_list_reverse_alt_commute_with_each_other).
    unfold list_reverse_alt in eureka.
    Check (eureka V (list_reverse_alt_aux V vs' nil) (v :: nil)).
    rewrite -> (eureka V (list_reverse_alt_aux V vs' nil) (v :: nil)).
    rewrite -> (fold_unfold_list_reverse_alt_aux_cons V v nil nil).
    rewrite -> (about_list_reverse_alt_aux V nil (v :: nil)).
    rewrite -> (fold_unfold_list_reverse_alt_aux_nil V nil).
    rewrite -> IHvs'.
    rewrite -> (fold_unfold_list_append_nil V (v :: nil)).
    rewrite -> (fold_unfold_list_append_cons V v nil).
    rewrite -> (fold_unfold_list_append_nil V vs').
    reflexivity.
Qed.

Proposition list_reverse_alt_preserves_length :
  forall (V : Type)
         (vs : list V),
    list_length V vs = list_length V (list_reverse_alt V vs).
Proof.
  intros V vs.
  unfold list_reverse_alt.
  induction vs as [ | v vs' IHvs'].

  - rewrite -> (fold_unfold_list_length_nil V).
    rewrite -> (fold_unfold_list_reverse_alt_aux_nil V nil).
    rewrite -> (fold_unfold_list_length_nil V).
    reflexivity.

  - rewrite -> (fold_unfold_list_length_cons V v vs').
    rewrite -> (fold_unfold_list_reverse_alt_aux_cons V v vs' nil).
    rewrite -> (about_list_reverse_alt_aux V vs' (v :: nil)).
    rewrite -> ( append_and_length_commute_with_each_other V
                  (list_reverse_alt_aux V vs' nil) (v :: nil)).
    rewrite -> (fold_unfold_list_length_cons V v nil).
    rewrite -> IHvs'.
    rewrite -> (fold_unfold_list_length_nil V).
    rewrite -> (Nat.add_1_r (list_length V (list_reverse_alt_aux V vs' nil))).
    reflexivity.
Qed.

(* A study of the polymorphic map function: *)

Definition specification_of_list_map (map : forall V W : Type, (V -> W) -> list V -> list W) :=
  (forall (V W : Type)
          (f : V -> W),
      map V W f nil = nil)
  /\
  (forall (V W : Type)
          (f : V -> W)
          (v : V)
          (vs' : list V),
      map V W f (v :: vs') = f v :: map V W f vs').

(* ***** *)

(* Task 6:

   a. Prove whether the specification specifies at most one map function.
*)

Proposition there_is_at_most_one_list_map_function :
  forall list_map1 list_map2 : forall V W : Type, (V -> W) -> list V -> list W,
      specification_of_list_map list_map1 ->
      specification_of_list_map list_map2 ->
      forall (V W : Type)
             (f : V -> W)
             (vs : list V),
        list_map1 V W f vs = list_map2 V W f vs.
Proof.
  intros list_map1 list_map2 S_list_map1 S_list_map2 V W f vs.
  induction vs as [ | v vs' IHvs'].
  - unfold specification_of_list_map in S_list_map1.
    destruct S_list_map1 as [fold_unfold_list_map1_nil _].
    destruct S_list_map2 as [fold_unfold_list_map2_nil _].
    rewrite -> (fold_unfold_list_map2_nil V W f).
    exact (fold_unfold_list_map1_nil V W f).
  - unfold specification_of_list_map in S_list_map1.
    destruct S_list_map1 as [_ fold_unfold_list_map1_cons].
    destruct S_list_map2 as [_ fold_unfold_list_map2_cons].
    rewrite -> (fold_unfold_list_map1_cons V W f v vs').
    rewrite -> (fold_unfold_list_map2_cons V W f v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   b. Implement the map function recursively.
*)

Fixpoint list_map (V W : Type) (f : V -> W) (vs : list V) : list W :=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    f v :: list_map V W f vs'
  end.

(*
   c. State the associated fold-unfold lemmas.
*)

Lemma fold_unfold_list_map_nil :
  forall (V W : Type)
         (f : V -> W),
    list_map V W f nil =
    nil.
Proof.
  fold_unfold_tactic list_map.
Qed.

Lemma fold_unfold_list_map_cons :
  forall (V W : Type)
         (f : V -> W)
         (v : V)
         (vs' : list V),
    list_map V W f (v :: vs') =
    f v :: list_map V W f vs'.
Proof.
  fold_unfold_tactic list_map.
Qed.


(*
   d. Prove whether your implementation satisfies the specification.
*)

Proposition list_map_satisfies_the_specification_of_list_map :
  specification_of_list_map list_map.
Proof.
  unfold specification_of_list_map.
  exact (conj fold_unfold_list_map_nil fold_unfold_list_map_cons).
Qed.
     
(*
   e. Implement the copy function using list_map.
*)


Definition list_copy_using_list_map (V : Type) (vs : list V) : list V :=
  list_map V V (fun x => x) vs. 

Compute test_list_copy_expanded list_copy_using_list_map.

(*
Hint: Does list_copy_using_list_map satisfy the specification of list_copy?
 *)

Theorem list_copy_using_list_map_satisfies_the_specification_of_list_copy :
  specification_of_list_copy list_copy_using_list_map.
Proof.
  unfold specification_of_list_copy.
  split.
  - intro V. 
    unfold list_copy_using_list_map.
    Check (fold_unfold_list_map_nil V V (fun x : V => x)).
    exact (fold_unfold_list_map_nil V V (fun x : V => x)).
  - intros V v vs'.
    unfold list_copy_using_list_map. 
    Check (fold_unfold_list_map_cons V V (fun x : V => x) v vs').
    exact (fold_unfold_list_map_cons V V (fun x : V => x) v vs').
Qed.

(*
   f. Prove whether mapping a function over a list preserves the length of this list.
*)

Theorem mapping_a_function_over_a_list_preserves_its_length :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V),
    list_length V vs = list_length W (list_map V W f vs).
Proof.
  intros V W f vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_list_map_nil V).
    rewrite -> (fold_unfold_list_length_nil V).
    rewrite -> (fold_unfold_list_length_nil W).
    reflexivity.
  - Check fold_unfold_list_map_cons. 
    rewrite -> (fold_unfold_list_map_cons V W f v vs').
    Check (fold_unfold_list_length_cons W (f v) (list_map V W f vs')).
    rewrite -> (fold_unfold_list_length_cons W (f v) (list_map V W f vs')).
    Check (fold_unfold_list_length_cons W (f v) (list_map V W f vs')).
    Check (fold_unfold_list_length_cons V v vs'). 
    rewrite -> (fold_unfold_list_length_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   g. Do list_map and list_append commute with each other and if so how?
*)

Theorem list_map_distributes_over_list_append :
  forall (V W : Type)
         (f : V -> W)
         (v1s v2s : list V),
  list_map V W f (list_append V v1s v2s) = list_append W (list_map V W f v1s) (list_map V W f v2s).
Proof.
  Compute (let V := nat in
           let W := nat in
           let f := (fun x => x) in
           let v1s := 1 :: 2 :: nil in
           let v2s := 3 :: 4 :: nil in
           list_map V W f (list_append V v1s v2s) = list_append W (list_map V W f v1s) (list_map V W f v2s)).
  intros V W f v1s v2s.
  induction v1s as [ | v v1s' IHv1s'].
  - rewrite -> (fold_unfold_list_append_nil V). 
    rewrite -> (fold_unfold_list_map_nil V W f).
    Check (nil_is_neutral_on_the_left_of_list_append W (list_map V W f v2s)).
    rewrite -> (nil_is_neutral_on_the_left_of_list_append W (list_map V W f v2s)).
    reflexivity.
  - rewrite ->  (fold_unfold_list_append_cons V v v1s' v2s).
    Check (fold_unfold_list_map_cons V W f v v1s'). 
    rewrite -> (fold_unfold_list_map_cons V W f v v1s').
    Check (fold_unfold_list_append_cons W (f v) (list_map V W f v1s') (list_map V W f v2s)).
    rewrite -> (fold_unfold_list_append_cons W (f v) (list_map V W f v1s') (list_map V W f v2s)).
    Check (fold_unfold_list_map_cons V W f v (list_append V v1s' v2s)).
    rewrite -> (fold_unfold_list_map_cons V W f v (list_append V v1s' v2s)).
    rewrite -> IHv1s'.
    reflexivity.
Qed.

(*
   h. Do list_map and list_reverse commute with each other and if so how?
*)

Theorem list_map_and_list_reverse_commute :
   forall (V W : Type)
         (f : V -> W)
         (vs : list V),
   list_map V W f (list_reverse V vs) = list_reverse W (list_map V W f vs).
Proof.
  Compute (let V := nat in
           let W := nat in
           let f := (fun x => x) in
           let vs := 1 :: 2 :: nil in
           list_map V W f (list_reverse V vs) = list_reverse W (list_map V W f vs)).
  intros V W f vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_list_reverse_nil V).
    rewrite -> (fold_unfold_list_map_nil V W f).
    rewrite -> (fold_unfold_list_reverse_nil W).
    reflexivity.
  - rewrite -> (fold_unfold_list_reverse_cons V v vs').
    Check (fold_unfold_list_append_nil).
    (* rewrite -> fold_unfold_list_map_nil. *)
    rewrite -> (fold_unfold_list_map_cons V W f v vs'). 
    Check (fold_unfold_list_reverse_cons).
    rewrite -> (fold_unfold_list_reverse_cons W (f v) (list_map V W f vs')).
    rewrite <- IHvs'.
    Check (list_map_distributes_over_list_append V W f (list_reverse V vs') (v :: nil)).
    rewrite -> (list_map_distributes_over_list_append V W f (list_reverse V vs') (v :: nil)).
    Check (fold_unfold_list_map_cons V W f v nil).
    rewrite -> (fold_unfold_list_map_cons V W f v nil).
    rewrite -> (fold_unfold_list_map_nil V W f).
    reflexivity.
Qed.
(*
   I. Do list_map and list_reverse_alt commute with each other and if so how?
*)

Lemma list_reverse_and_list_reverse_alt_are_equivalent_aux :
  forall (V : Type)
         (vs a : list V),
    list_append V (list_reverse V vs) a = list_reverse_alt_aux V vs a.
Proof.
  Compute (let V := nat in
           let vs := 1 :: 2 :: nil in
           let a := nil in
           list_append V (list_reverse V vs) a = list_reverse_alt_aux V vs a).
  intros V vs.
  induction vs as [ | vs' IHvs'].
  - intro a. 
    rewrite -> (fold_unfold_list_reverse_nil V).
    rewrite -> (fold_unfold_list_append_nil V a).
    rewrite -> (fold_unfold_list_reverse_alt_aux_nil V a).
    reflexivity.
  - intro a.
    simpl.
    Check (IHIHvs' (vs' :: a)).
    rewrite <- (IHIHvs' (vs' :: a)).
    Check (list_append_is_associative).
    rewrite <- (list_append_is_associative V (list_reverse V IHvs') (vs' :: nil) a).
    Check (fold_unfold_list_append_cons V vs' nil a).
    rewrite -> (fold_unfold_list_append_cons V vs' nil a).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.
Qed.

Theorem list_reverse_and_list_reverse_alt_are_equivalent :
  forall (V : Type)
         (vs : list V),
  list_reverse V vs = list_reverse_alt V vs.
Proof.
  intros V vs.
  unfold list_reverse_alt.
  rewrite <- (list_reverse_and_list_reverse_alt_are_equivalent_aux V vs nil).
  Check fold_unfold_list_append_nil.
  rewrite -> (nil_is_neutral_on_the_right_of_list_append V (list_reverse V vs)).
  reflexivity.
Qed.

Theorem list_map_and_list_reverse_alt_commute :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V),
   list_map V W f (list_reverse_alt V vs) = list_reverse_alt W (list_map V W f vs).
Proof.
  Compute (let V := nat in
           let W := nat in
           let f := (fun x => x) in
           let vs := 1 :: 2 :: nil in
           list_map V W f (list_reverse V vs) = list_reverse W (list_map V W f vs)).
  intros V W f vs.
  Check (list_reverse_and_list_reverse_alt_are_equivalent V vs).
  rewrite <- (list_reverse_and_list_reverse_alt_are_equivalent V vs).
  rewrite <- (list_reverse_and_list_reverse_alt_are_equivalent W (list_map V W f vs)).
  Check (list_map_and_list_reverse_commute).
  exact (list_map_and_list_reverse_commute V W f vs).
Qed.

(*
   j. Define a unit-test function for the map function
      and verify that your implementation satisfies it.
 *)

Definition test_list_map (map : forall V W : Type, (V -> W) -> list V -> list W) : bool :=
  (eqb_list nat Nat.eqb (map nat nat (fun x => x + 1) nil) nil) &&
  (eqb_list nat Nat.eqb (map nat nat (fun x => x + 1) (1 :: 2 :: 3 :: nil)) (2 :: 3 :: 4 :: nil)) &&
  (eqb_list bool Bool.eqb (map nat bool (fun x => x <? 3) (1 :: 2 :: 3 :: nil)) (true :: true :: false :: nil)).

Compute (test_list_map list_map).

Definition test_list_map_list_reverse_commutation (map : forall V W : Type, (V -> W) -> list V -> list W)
                                        (reverse : forall V : Type, list V -> list V) : bool :=
  (eqb_list nat Nat.eqb (map nat nat (fun x => x + 1) (reverse nat (1 :: 2 :: 3 :: nil))) 
                        (reverse nat (map nat nat (fun x => x + 1) (1 :: 2 :: 3 :: nil))))
  &&
  (eqb_list bool Bool.eqb (map bool bool (fun x => negb x) (reverse bool (true :: false :: true :: nil))) 
                          (reverse bool (map bool bool (fun x => negb x) (true :: false :: true :: nil)))).

Compute (test_list_map_list_reverse_commutation list_map list_reverse).


(* ********** *)

(* A study of the polymorphic fold-right and fold-left functions: *)

Definition specification_of_list_fold_right (list_fold_right : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_right V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_right V W nil_case cons_case (v :: vs') =
     cons_case v (list_fold_right V W nil_case cons_case vs')).

Definition specification_of_list_fold_left (list_fold_left : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_left V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_left V W nil_case cons_case (v :: vs') =
     list_fold_left V W (cons_case v nil_case) cons_case vs').

(* ***** *)

(* Task 7:

   a. Implement the fold-right function recursively.
*)

Fixpoint list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right V W nil_case cons_case vs')
  end.


(*
   b. Implement the fold-left function recursively.
*)

Fixpoint list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left V W (cons_case v nil_case) cons_case vs'
  end.

(*
   c. state the fold-unfold lemmas associated to list_fold_right and to list_fold_left
*)

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

(*
   d. Prove that each of your implementations satisfies the corresponding specification.
*)


Theorem the_recursive_implementation_of_list_fold_left_satisfies_its_recursive_specification:
  specification_of_list_fold_left list_fold_left.
Proof.
  unfold specification_of_list_fold_left.
  split.
  - exact fold_unfold_list_fold_left_nil.
  - exact fold_unfold_list_fold_left_cons.
Qed.

Theorem the_recursive_implementation_of_list_fold_right_satisfies_its_recursive_specification:
  specification_of_list_fold_right list_fold_right.
Proof.
  unfold specification_of_list_fold_right.
  split.
  - exact fold_unfold_list_fold_right_nil.
  - exact fold_unfold_list_fold_right_cons.
Qed.


(*
   e. Which function do foo and bar (defined just below) compute?
*)


Definition foo (V : Type) (vs : list V) :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.

Compute (foo nat (1 :: 2 :: nil)).
Compute (foo nat (1 :: 2 :: 3 :: nil)).

Theorem foo_satisfies_the_specification_of_list_copy :
  specification_of_list_copy foo.
Proof.
  unfold specification_of_list_copy, foo.
  split.
  - intro V.
    Check (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
    exact (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs'.
    Check (fold_unfold_list_fold_right_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
    exact (fold_unfold_list_fold_right_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
Qed.
    
        
Definition bar (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.

Compute (bar nat (1 :: 2 :: nil)).
Compute (bar nat (1 :: 2 :: 3 :: nil) = 3 :: 2 :: 1 :: nil).
Compute (eqb_list nat Nat.eqb (bar nat (1 :: 2 :: 3 :: nil)) (3 :: 2 :: 1 :: nil)).



Lemma about_bar :
  forall (V : Type)
         (vs a : list V),
  list_fold_left V (list V) a (fun (v0 : V) (vs : list V) => v0 :: vs) vs =
    list_append V (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs) a.
Proof.
  intros V vs.
  induction vs as [ | v' vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_list_fold_left_nil V (list V) a (fun (v0 : V) (vs : list V) => v0 :: vs)).
    rewrite -> (fold_unfold_list_fold_left_nil V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs)).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) a (fun (v0 : V) (vs : list V) => v0 :: vs) v' vs').
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v' vs').
    Check (IHvs' (v' :: a)).
    rewrite -> (IHvs' (v' :: a)).
    Check (IHvs' (v' :: nil)).
    rewrite -> (IHvs' (v' :: nil)).
    Check (list_append_is_associative V (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs') (v' :: nil) a).
    rewrite <- (list_append_is_associative V (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs') (v' :: nil) a).
    rewrite -> (fold_unfold_list_append_cons V v' nil a).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.
Qed.

Proposition there_is_at_most_one_function_that_satisfies_the_specification_of_list_append :
  forall list_append_v1 list_append_v2 : forall V : Type, list V -> list V -> list V,
    specification_of_list_append list_append_v1 ->
    specification_of_list_append list_append_v2 ->
    forall (V : Type)
           (v1s v2s : list V),
      list_append_v1 V v1s v2s = list_append_v2 V v1s v2s.
Proof.
Admitted.
   
 
Theorem bar_satisfies_the_specification_of_list_reverse :
  specification_of_list_reverse bar.
Proof.
  unfold specification_of_list_reverse, bar.
  intro append.
  intro S_append.
  split.
  - intro V.
    Check (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
    exact (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs'.
    Check (fold_unfold_list_fold_left_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
    Check (there_is_at_most_one_function_that_satisfies_the_specification_of_list_append append list_append).
    Check (there_is_at_most_one_function_that_satisfies_the_specification_of_list_append append list_append S_append list_append_satisfies_the_specification_of_list_append V (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs') (v :: nil)).
    rewrite -> (there_is_at_most_one_function_that_satisfies_the_specification_of_list_append append list_append S_append list_append_satisfies_the_specification_of_list_append V (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs') (v :: nil)).
    Check (about_bar V vs' (v :: nil)).
    exact (about_bar V vs' (v :: nil)).
Qed.

(*
   f. Implement the length function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition list_length_right (V : Type) (vs : list V) : nat :=
  list_fold_right V nat 0 (fun _ n => S n) vs.

Compute (test_list_length list_length_right).


Theorem list_length_right_satisfies_the_specification_of_list_length :
  specification_of_list_length list_length_right.
Proof.
  unfold specification_of_list_length, list_length_right.
  split.
  - intro V.
    rewrite -> (fold_unfold_list_fold_right_nil V nat 0 (fun (_ : V) (n : nat) => S n)).
    reflexivity.
  - intros V v vs'.
    rewrite -> (fold_unfold_list_fold_right_cons V nat 0 (fun (_ : V) (n : nat) => S n) v vs').
    reflexivity.
Qed.

             
Definition list_length_left (V : Type) (vs : list V) : nat :=
  list_fold_left V nat 0 (fun _ n => S n) vs.

Compute (test_list_length list_length_left).

Lemma list_length_left_satisfies_the_specification_of_list_length_aux :
  forall (V : Type)
         (vs : list V)
         (a : nat),
    list_fold_left V nat (S a) (fun (_ : V) (n : nat) => S n) vs =
      S (list_fold_left V nat a (fun (_ : V) (n : nat) => S n) vs).
Proof.
  intros V vs.
  induction vs as [ | v' vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_list_fold_left_nil V nat (S a) (fun (_ : V) (n : nat) => S n)).
    rewrite -> (fold_unfold_list_fold_left_nil V nat a (fun (_ : V) (n : nat) => S n)).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_list_fold_left_cons V nat (S a) (fun (_ : V) (n : nat) => S n) v' vs').
    rewrite -> (fold_unfold_list_fold_left_cons V nat a (fun (_ : V) (n : nat) => S n) v' vs').
    Check (IHvs' (S a)).
    exact (IHvs' (S a)).
Qed.

Theorem list_length_left_satisfies_the_specification_of_list_length :
  specification_of_list_length list_length_left.
Proof.
  unfold specification_of_list_length, list_length_left.
  split.
  - intro V.
    rewrite -> (fold_unfold_list_fold_left_nil V nat 0 (fun (_ : V) (n : nat) => S n)).
    reflexivity.
  - intros V v vs'.
    rewrite -> (fold_unfold_list_fold_left_cons V nat 0 (fun (_ : V) (n : nat) => S n) v vs').
    Check (list_length_left_satisfies_the_specification_of_list_length_aux V vs' 0).
    exact (list_length_left_satisfies_the_specification_of_list_length_aux V vs' 0).
Qed.
    

(*
   g. Implement the copy function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition list_copy_right (V : Type) (vs : list V) : list V :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.

Compute (list_copy_right nat (1 :: 2 :: 3 :: nil) = (1 :: 2 :: 3 :: nil)).
Compute (eqb_list nat Nat.eqb (list_copy_right nat (1 :: 2 :: 3 :: nil)) (1 :: 2 :: 3 :: nil)).

Theorem list_copy_right_satisfies_the_specification_of_list_copy :
  specification_of_list_copy list_copy_right.
Proof.
  exact (foo_satisfies_the_specification_of_list_copy).
Qed.

(*
   h. Implement the append function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition list_append_right (V : Type) (vs1 vs2 : list V) : list V :=
  list_fold_right V (list V) vs2 (fun v acc => v :: acc) vs1.

Compute (eqb_list nat Nat.eqb (list_append_right nat (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)) (list_append nat (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil))).

Theorem list_append_right_satisfies_the_specification_of_list_append :
  specification_of_list_append list_append_right.
Proof.
  unfold specification_of_list_append, list_append_right.
  split.
  - intros V v2s.
    rewrite -> (fold_unfold_list_fold_right_nil V (list V) v2s (fun (v : V) (acc : list V) => v :: acc)).
    reflexivity.
  - intros V v1 v1s' v2s.
    rewrite -> (fold_unfold_list_fold_right_cons V (list V) v2s (fun (v : V) (acc : list V) => v :: acc) v1 v1s').
    reflexivity.
Qed.

(*
   i. Implement the reverse function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition list_reverse_left (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.

Compute (list_reverse_left nat (1 :: 2 :: nil)).
Compute (eqb_list nat Nat.eqb (list_reverse_left nat (1 :: 2 :: 3 :: nil)) (3 :: 2 :: 1 :: nil)).

Theorem list_reverse_left_satisfies_the_specification_of_list_reverse :
  specification_of_list_reverse list_reverse_left.
Proof.
  exact (bar_satisfies_the_specification_of_list_reverse).
Qed.

(*
   j. Implement the map function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition list_map_right (V W : Type) (f : V -> W) (vs : list V) : list W :=
  list_fold_right V (list W) nil (fun v acc => f v :: acc) vs.


Compute (eqb_list nat Nat.eqb (list_map_right nat nat (fun x => x * 2) (1 :: 2 :: 3 :: nil)) (2 :: 4 :: 6 :: nil)).

Theorem list_map_right_satisfies_the_specification_of_list_map :
  specification_of_list_map list_map_right.
Proof.
  unfold specification_of_list_map, list_map_right.
  split.
  - intros V W f.
    rewrite -> (fold_unfold_list_fold_right_nil V (list W) nil (fun (v : V) (acc : list W) => f v :: acc)).
    reflexivity.
  - intros V W f v vs'.
    rewrite -> (fold_unfold_list_fold_right_cons V (list W) nil (fun (v0 : V) (acc : list W) => f v0 :: acc) v vs').
    reflexivity.
Qed.

(*
   k. Relate list_fold_right and list_fold_left using the reverse function.
 *)

Definition list_fold_right' (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  let fix visit vs :=
    match vs with
    | nil =>
        nil_case
    | v :: vs' =>
        cons_case v (visit vs')
    end
  in visit vs.


Definition list_reverse_v0 (V : Type) (vs : list V) : list V :=
  let fix visit vs a :=
        match vs with
        | nil =>
            a
        | v :: vs' =>
            visit vs' (v :: a)
        end
  in visit vs nil.

Compute (list_reverse_v0 nat (1 :: 2 :: nil)).

Definition list_reverse_v1 (V : Type) (vs : list V) : list V :=
  let fix visit vs :=
        match vs with
        | nil =>
           (fun a =>  a)
        | v :: vs' =>
            (fun a => visit vs' (v :: a))
        end
  in visit vs nil.

Compute (list_reverse_v1 nat (1 :: 2 :: nil)).

Definition list_reverse_right (V : Type) (vs : list V) : list V :=
  list_fold_right V (list V -> list V)
    (fun a => a)
    (fun v ih => fun a => ih (v :: a))
    vs
    nil.

Compute (list_reverse_right nat (1 :: 2 :: nil)).


Lemma list_reverse_right_satisfies_the_specification_of_list_reverse_aux:
  forall (V : Type)
         (vs a: list V),
    list_fold_right V (list V -> list V) (fun a : list V => a) (fun (v0 : V) (ih : list V -> list V) (a : list V) => ih (v0 :: a)) vs a =
      list_append V (list_fold_right V (list V -> list V) (fun a : list V => a) (fun (v0 : V) (ih : list V -> list V) (a : list V) => ih (v0 :: a)) vs nil) a.
Proof.
  intros V vs.
  induction vs as [ | v' vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_list_fold_right_nil V (list V -> list V) (fun a1 : list V => a1) (fun (v0 : V) (ih : list V -> list V) (a1 : list V) => ih (v0 :: a1))).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_list_fold_right_cons V (list V -> list V) (fun a1 : list V => a1) (fun (v0 : V) (ih : list V -> list V) (a1 : list V) => ih (v0 :: a1)) v' vs').
    rewrite -> (IHvs' (v' :: a)).
    rewrite -> (IHvs' (v' :: nil)).
    rewrite <- (list_append_is_associative V (list_fold_right V (list V -> list V) (fun a0 : list V => a0) (fun (v0 : V) (ih : list V -> list V) (a0 : list V) => ih (v0 :: a0)) vs' nil) (v' :: nil) a).
    Check (fold_unfold_list_append_nil).
    rewrite -> (fold_unfold_list_append_cons V v' nil a).
    rewrite -> (fold_unfold_list_append_nil V a).
    reflexivity.
Qed.
    
             
Theorem list_reverse_right_satisfies_the_specification_of_list_reverse :
  specification_of_list_reverse list_reverse_right.
Proof.
  unfold specification_of_list_reverse, list_reverse_right.
  intros append.
  intro S_append.
  split.
  - intro V.
    rewrite -> (fold_unfold_list_fold_right_nil  V (list V -> list V) (fun a : list V => a) (fun (v : V) (ih : list V -> list V) (a : list V) => ih (v :: a))).
    reflexivity.
  - intros V v vs'.
    rewrite -> (fold_unfold_list_fold_right_cons V (list V -> list V) (fun a : list V => a) (fun (v0 : V) (ih : list V -> list V) (a : list V) => ih (v0 :: a)) v vs').
    Check (there_is_at_most_one_function_that_satisfies_the_specification_of_list_append append list_append).
    Check (there_is_at_most_one_function_that_satisfies_the_specification_of_list_append append list_append S_append list_append_satisfies_the_specification_of_list_append V (list_fold_right V (list V -> list V) (fun a : list V => a) (fun (v0 : V) (ih : list V -> list V) (a : list V) => ih (v0 :: a)) vs' nil) (v :: nil)).
    rewrite -> (there_is_at_most_one_function_that_satisfies_the_specification_of_list_append append list_append S_append list_append_satisfies_the_specification_of_list_append V (list_fold_right V (list V -> list V) (fun a : list V => a) (fun (v0 : V) (ih : list V -> list V) (a : list V) => ih (v0 :: a)) vs' nil) (v :: nil)).
    exact (list_reverse_right_satisfies_the_specification_of_list_reverse_aux V vs' (v :: nil)).
Qed.
                                 
(*
   l. Implement list_fold_right using list_fold_left, without using the reverse function.
*)


Definition list_fold_right_using_list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_left V
    W
    nil_case
    (fun v ih => cons_case v ih)
    (list_reverse V vs).


Definition list_copy_right' (V : Type) (vs : list V) : list V :=
  list_fold_right_using_list_fold_left V (list V) nil (fun v vs => v :: vs) vs.

Compute (list_copy_right' nat (1 :: 2 :: 3 :: nil) = (1 :: 2 :: 3 :: nil)).
Compute (eqb_list nat Nat.eqb (list_copy_right' nat (1 :: 2 :: 3 :: nil)) (1 :: 2 :: 3 :: nil)).


Lemma list_fold_right_using_list_fold_left_satisfies_the_specification_of_list_fold_right_aux:
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs : list V),
    list_fold_left V W nil_case (fun (v0 : V) (ih : W) => cons_case v0 ih) (list_reverse V (v :: vs)) =
      cons_case v (list_fold_left V W nil_case (fun (v0 : V) (ih : W) => cons_case v0 ih) (list_reverse V vs)).
Proof.
  intros V W nil_case cons_case v vs.
  induction vs as [ | v' vs' IHvs'].
  - rewrite -> (fold_unfold_list_reverse_nil).
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case (fun (v0 : V) (ih : W) => cons_case v0 ih)).
    Check (fold_unfold_list_reverse_cons).
    rewrite -> (fold_unfold_list_reverse_cons V v nil).
    rewrite -> (fold_unfold_list_reverse_nil).
    Check (fold_unfold_list_append_nil).
    rewrite -> (fold_unfold_list_append_nil V (v :: nil)).
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case (fun (v0 : V) (ih : W) => cons_case v0 ih) v nil).
    rewrite -> (fold_unfold_list_fold_left_nil V W (cons_case v nil_case) (fun (v0 : V) (ih : W) => cons_case v0 ih)).
    reflexivity.
  - rewrite -> (fold_unfold_list_reverse_cons V v (v' :: vs')).
    rewrite -> (fold_unfold_list_reverse_cons V v' vs').
    Check (list_append_is_associative).
    rewrite <- (list_append_is_associative V (list_reverse V vs') (v' :: nil) (v :: nil)).
    rewrite <- (about_reversing_a_singleton_list_with_list_reverse).
    rewrite <- (list_append_and_list_reverse_commute_with_each_other V (v' :: nil) vs').
Admitted.


    
Theorem list_fold_right_using_list_fold_left_satisfies_the_specification_of_list_fold_right :
  specification_of_list_fold_right list_fold_right_using_list_fold_left.
Proof.
  unfold specification_of_list_fold_right, list_fold_right_using_list_fold_left.
  split.
  - intros V W nil_case cons_case.
    rewrite -> (fold_unfold_list_reverse_nil V).
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case (fun (v : V) (ih : W) => cons_case v ih)).
    reflexivity.
  - intros V W nil_case cons_case v vs'.
    exact (list_fold_right_using_list_fold_left_satisfies_the_specification_of_list_fold_right_aux V W nil_case cons_case v vs').
Qed.

(*
   m. Implement list_fold_left using list_fold_right, without using the reverse function.
*)


Definition list_length_right' (V : Type) (vs : list V) : nat :=
  list_fold_right V
    nat
    0
    (fun _ acc => S acc)
    vs.

Theorem list_length_right'_satisfies_the_specification_of_list_length :
  specification_of_list_length list_length_right.
Proof.
  unfold specification_of_list_length, list_length_right.
  split.
  - intro V.
    rewrite -> (fold_unfold_list_fold_right_nil V nat 0 (fun (_ : V) (acc : nat) => S acc)).
    reflexivity.
  - intros V v vs'.
    rewrite -> (fold_unfold_list_fold_right_cons V nat 0 (fun (_ : V) (n : nat) => S n) v vs').
    reflexivity.
Qed.

Compute (list_length_right' nat (1 :: 2 :: nil)).

Definition list_length_alt' (V : Type) (vs : list V) : nat :=
  let fix visit vs a :=
    match vs with
    | nil =>
        a
    | v :: vs' =>
        visit vs' (S a)
    end
  in visit vs 0.

Compute (list_length_alt' nat (1 :: 2 :: nil) = 2).


Definition list_length_alt'' (V : Type) (vs : list V) : nat :=
  let fix visit vs := fun a => 
    match vs with
    | nil =>
        a
    | v :: vs' =>
        visit vs' (S a)
    end
  in visit vs 0.

Compute (list_length_alt'' nat (1 :: 2 :: nil) = 2).


Definition list_length_alt''' (V : Type) (vs : list V) : nat := 
  let fix visit vs := (* visit : list V  -> nat -> nat *)
    match vs with
    | nil =>
        (fun a => a)
    | v :: vs' =>
        (fun a => visit vs' (S a))
    end
  in visit vs 0.

Compute (list_length_alt''' nat (1 :: 2 :: nil) = 2).

Definition list_length_alt_right (V : Type) (vs : list V) : nat :=
  list_fold_right V
    (nat -> nat)
    (fun a => a)
    (fun v ih => fun a => ih (S a))
    vs
    0.

Compute (list_length_alt_right nat (1 :: 2 :: nil) = 2).


Definition list_fold_left' (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  let fix visit vs a :=
    match vs with
    | nil =>
        a
    | v :: vs' =>
        visit vs' (cons_case v a)
    end
  in visit vs nil_case.


Definition list_fold_left'' (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  let fix visit vs := fun a =>
    match vs with
    | nil =>
        a
    | v :: vs' =>
        visit vs' (cons_case v a)
    end
  in visit vs nil_case.


Definition list_fold_left''' (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  let fix visit vs := (* visit : list V -> W -> W *)
    match vs with
    | nil =>
        (fun a => a)
    | v :: vs' =>
        (fun a => visit vs' (cons_case v a))
    end
  in visit vs nil_case.

Definition list_fold_left_using_list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_right V
    (W -> W)
    (fun a => a)
    (fun v ih => fun a => ih (cons_case v a))
    vs
    nil_case.


Definition list_reverse_left' (V : Type) (vs : list V) :=
  list_fold_left_using_list_fold_right V (list V) nil (fun v vs => v :: vs) vs.

Compute (list_reverse_left' nat (1 :: 2 :: nil)).

Theorem list_fold_left_using_list_fold_right_satisfies_the_specification_of_list_fold_left :
  specification_of_list_fold_left list_fold_left_using_list_fold_right.
Proof.
  unfold specification_of_list_fold_left, list_fold_left_using_list_fold_right.
  split.
  - intros V W nil_case cons_case.
    rewrite -> (fold_unfold_list_fold_right_nil V (W -> W) (fun a : W => a) (fun (v : V) (ih : W -> W) (a : W) => ih (cons_case v a))).
    reflexivity.
  - intros V W nil_case cons_case v vs'.
    rewrite -> (fold_unfold_list_fold_right_cons V (W -> W) (fun a : W => a) (fun (v0 : V) (ih : W -> W) (a : W) => ih (cons_case v0 a)) v vs').
    reflexivity.
Qed.

(*
   n. Show that
      if the cons case is a function that is left permutative (defined just below),
      applying list_fold_left and applying list_fold_right
      to a nil case, this cons case, and a list
      give the same result
*)
  
Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (w : W),
    op2 v1 (op2 v2 w) = op2 v2 (op2 v1 w).

Lemma about_list_fold_right :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    is_left_permutative V W cons_case ->
    list_fold_right V W (cons_case v nil_case) cons_case vs' =
      cons_case v (list_fold_right V W nil_case cons_case vs').
Proof.
  intros V W nil_case cons_case v vs' H_cons.
  induction vs' as [ | v' vs'' IHvs''].
  - rewrite -> (fold_unfold_list_fold_right_nil V W (cons_case v nil_case) cons_case).
    rewrite -> (fold_unfold_list_fold_right_nil V W nil_case cons_case).
    reflexivity.
  - rewrite -> (fold_unfold_list_fold_right_cons V W (cons_case v nil_case) cons_case v' vs'').
    rewrite -> (fold_unfold_list_fold_right_cons V W nil_case cons_case v' vs'').
    rewrite -> IHvs''.
    unfold is_left_permutative in H_cons.
    Check (H_cons v' v (list_fold_right V W nil_case cons_case vs'')).
    exact (H_cons v' v (list_fold_right V W nil_case cons_case vs'')).
Qed.


Lemma about_list_fold_left :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    is_left_permutative V W cons_case ->
    list_fold_left V W (cons_case v nil_case) cons_case vs' =
      cons_case v (list_fold_left V W nil_case cons_case vs').
Proof.
  intros V W nil_case cons_case v vs' H_cons.
  revert v nil_case.
  induction vs' as [ | v' vs'' IHvs''].
  - intros v nil_case.
    rewrite -> (fold_unfold_list_fold_left_nil V W (cons_case v nil_case) cons_case).
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    reflexivity.
  - intros v nil_case.
    rewrite -> (fold_unfold_list_fold_left_cons V W (cons_case v nil_case) cons_case v' vs'').
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v' vs'').
    rewrite -> (IHvs'' v' (cons_case v nil_case)).
    rewrite -> (IHvs'' v nil_case).
    rewrite -> (IHvs'' v' nil_case).
    unfold is_left_permutative in H_cons.
    exact (H_cons v' v (list_fold_left V W nil_case cons_case vs'')).
Qed.

Theorem folding_left_and_right :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (vs : list V),
      list_fold_left V W nil_case cons_case vs =
        list_fold_right V W nil_case cons_case vs.
Proof.
  intros V W cons_case H_cons nil_case vs.
  revert nil_case.
  induction vs as [ | v vs' IHvs'].
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    rewrite -> (fold_unfold_list_fold_right_nil V W nil_case cons_case).
    reflexivity.
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v vs').
    rewrite -> (fold_unfold_list_fold_right_cons V W nil_case cons_case v vs').
    rewrite -> (IHvs' (cons_case v nil_case)).
    exact (about_list_fold_right V W nil_case cons_case v vs' H_cons).

  Restart.

  intros V W cons_case H_cons nil_case vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    rewrite -> (fold_unfold_list_fold_right_nil V W nil_case cons_case).
    reflexivity.
  - rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v vs').
    rewrite -> (fold_unfold_list_fold_right_cons V W nil_case cons_case v vs').
    rewrite <- IHvs'.
    exact (about_list_fold_left V W nil_case cons_case v vs' H_cons).
Qed.
 
(*
   o. Can you think of corollaries of this property?
*)

Lemma plus_is_left_permutative :
  is_left_permutative nat nat plus.
Proof.
  unfold is_left_permutative.
  intros v1 v2 w.
  Search (_ + (_ + _) = (_ + _) + _).
  rewrite -> (Nat.add_assoc v1 v2 w).
  rewrite -> (Nat.add_assoc v2 v1 w).
  Check (Nat.add_comm).
  rewrite -> (Nat.add_comm v1 v2).
  reflexivity.
Qed.


Corollary example_for_plus :
  forall ns : list nat,
    list_fold_left nat nat 0 plus ns = list_fold_right nat nat 0 plus ns.
Proof.
  Check (folding_left_and_right nat nat plus plus_is_left_permutative 0).
  exact (folding_left_and_right nat nat plus plus_is_left_permutative 0).
Qed.


(* What do you make of this corollary?
   Can you think of more such corollaries?
 *)

(*
  It looks like all that the collolary for something to be left-permutative is that it is commutative and associative.
*) 

Lemma mul_is_left_permutative :
  is_left_permutative nat nat Nat.mul.
Proof.
  unfold is_left_permutative.
  intros v1 v2 w.
  rewrite -> (Nat.mul_assoc v1 v2 w).
  rewrite -> (Nat.mul_comm v1 v2).
  rewrite -> (Nat.mul_assoc v2 v1 w).
  reflexivity.
Qed.

Corollary mul_as_cons_is_the_same_folded_left_and_right :
  forall (n : nat)
         (ns : list nat),
    list_fold_left nat nat n Nat.mul ns = list_fold_right nat nat n Nat.mul ns.
Proof.
  intros n ns.
  Check (folding_left_and_right nat nat Nat.mul mul_is_left_permutative n ns).
  exact (folding_left_and_right nat nat Nat.mul mul_is_left_permutative n ns).
Qed.

Lemma add_is_left_permutative :
  is_left_permutative nat nat Nat.add.
Proof.
  unfold is_left_permutative.
  intros v1 v2 w.
  rewrite -> (Nat.add_assoc v1 v2 w).
  rewrite -> (Nat.add_comm v1 v2).
  rewrite -> (Nat.add_assoc v2 v1 w).
  reflexivity.
Qed.

Corollary add_as_cons_is_the_same_folded_left_and_right :
  forall (n : nat)
         (ns : list nat),
    list_fold_left nat nat n Nat.add ns = list_fold_right nat nat n Nat.add ns.
Proof.
  intros n ns.
  Check (folding_left_and_right nat nat Nat.add add_is_left_permutative n ns).
  exact (folding_left_and_right nat nat Nat.add add_is_left_permutative n ns).
Qed.

(*
   p. Subsidiary question: does the converse of Theorem folding_left_and_right hold?
*)

(*
Theorem folding_left_and_right_converse :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    (forall (nil_case : W)
            (vs : list V),
        list_fold_left  V W nil_case cons_case vs =
        list_fold_right V W nil_case cons_case vs) ->
    is_left_permutative V W cons_case.
Proof.
  intros V W cons_case H_fold_eqb.
  unfold is_left_permutative.
  intros v1 v2 w.
Abort.
*)

(* This does not hold, as the successor function in list_length is a counter example (see more in the report) *)
      
(* ********** *)

(* Task 8: *)

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

(* ***** *)

(* A simple example: *)

Definition specification_of_fac (fac : nat -> nat) :=
  (fac 0 = 1)
  /\
  (forall n' : nat,
    fac (S n') = S n' * fac n').

Definition test_fac (candidate : nat -> nat) : bool :=
  (candidate 0 =? 1)
  &&
  (candidate 1 =? 1 * 1)
  &&
  (candidate 2 =? 2 * 1 * 1)
  &&
  (candidate 3 =? 3 * 2 * 1 * 1)
  &&
  (candidate 4 =? 4 * 3 * 2 * 1 * 1)
  &&
  (candidate 5 =? 5 * 4 * 3 * 2 * 1 * 1).

(* ***** *)

Fixpoint fac (n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    S n' * fac n'
  end.

Compute (test_fac fac).

Lemma fold_unfold_fac_O :
  fac 0 =
  1.
Proof.
  fold_unfold_tactic fac.
Qed.

Lemma fold_unfold_fac_S :
  forall n' : nat,
    fac (S n') =
    S n' * fac n'.
Proof.
  fold_unfold_tactic fac.
Qed.

Definition fac_gen (n : nat) : nat :=
  nat_parafold_right nat 1 (fun i ih => S i * ih) n.

Compute (test_fac fac_gen).

(* ***** *)

Fixpoint fac_acc (n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    fac_acc n' (S n' * a)
  end.

Definition fac_alt (n : nat) : nat :=
  fac_acc n 1.

Compute (test_fac fac_alt).

Lemma fold_unfold_fac_acc_O :
  forall a : nat,
    fac_acc 0 a =
    a.
Proof.
  fold_unfold_tactic fac_acc.
Qed.

Lemma fold_unfold_fac_acc_S :
  forall n' a : nat,
    fac_acc (S n') a =
    fac_acc n' (S n' * a).
Proof.
  fold_unfold_tactic fac_acc.
Qed.

Definition fac_alt_gen (n : nat) : nat :=
  nat_parafold_left nat 1 (fun i ih => S i * ih) n.

Compute (test_fac fac_alt_gen).

(* ********** *)

Fixpoint nat_fold_right (V : Type) (zero_case : V) (succ_case : V -> V) (n : nat) : V :=
  match n with
  | O =>
    zero_case
  | S n' =>
    succ_case (nat_fold_right V zero_case succ_case n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V),
    nat_fold_right V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n' : nat),
    nat_fold_right V zero_case succ_case (S n') =
    succ_case (nat_fold_right V zero_case succ_case n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Fixpoint nat_fold_left (V : Type) (zero_case : V) (succ_case : V -> V) (n : nat) : V :=
  match n with
  | O =>
    zero_case
  | S n' =>
    nat_fold_left V (succ_case zero_case) succ_case n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V),
    nat_fold_left V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n' : nat),
    nat_fold_left V zero_case succ_case (S n') =
    nat_fold_left V (succ_case zero_case) succ_case n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ********** *)

(* end of midterm-project.v *)
