(* week-11_a-family-of-programming-puzzles-about-lists.v *)
(* FPP 2023 - YSC3236 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 01 Nov 2023 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

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

Definition eqb_nat := Nat.eqb.

Definition eqb_pair (V : Type) (eqb_V : V -> V -> bool) (W : Type) (eqb_W : W -> W -> bool) (p1 p2 : V * W) : bool :=
  let (v1, w1) := p1 in
  let (v2, w2) := p2 in
  eqb_V v1 v2 && eqb_W w1 w2.

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
    list_fold_left V W nil_case cons_case vs =
      list_fold_right V W nil_case cons_case (list_reverse V vs).
Admitted.

Lemma correctness_of_list_index_rtl_left_aux :
   forall (V : Type)
          (vs : list V)
          (n : nat),
     list_fold_right V (nat -> option V) (fun _ : nat => None)
       (fun (a : V) (ih : nat -> option V) (v : nat) =>
          match v with
          | 0 => Some a
          | S n' => ih n'
          end) vs n = list_index_ltr V vs n.
Proof.
  intros V vs.
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

        Restart.

        intros V vs n.
        unfold list_index_rtl_left.
        rewrite -> relating_list_fold_left_and_list_fold_right_using_list_reverse.
        apply correctness_of_list_index_rtl_left_aux.
Qed.
        (*induction vs as [ | v vs' IHvs'].
  - rewrite -> fold_unfold_list_reverse_nil.
    rewrite -> fold_unfold_list_fold_right_nil.
    rewrite -> fold_unfold_list_index_ltr_nil.
    reflexivity.
  - rewrite ->*)
        
           
Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 0.

Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 1.

Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 2.

Compute list_index_rtl_left nat (2 :: 1 :: 0 :: nil) 3.

(* ********** *)

(* end of week-11_a-family-of-programming-puzzles-about-lists.v *)
