(* week-01_about-reversing-a-list-and-mirroring-a-tree.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 15 Aug 2024 *)

(* ********** *)

(* This warmup exercise is a study of list reversal and tree mirroring. *)

(* About style:

   - when you use the Light of Inductil,
     make sure to provide the argument(s) of the induction hypothesis when you apply it

   - there is no need to provide the arguments of most of the other lemmas you apply,
     unless you feel that

     + it is necessary, or

     + it makes the proof clearer. *)

(* Note:
   The point of this warmup exercise is not to do everything in a stressed hurry.
   The point is to do well what you have the time to do, and to re-acquire basic tCPA reflexes. *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

(* Background material, Part I/II: lists.

   list_append, list_reverse, and list_reverse_alt,
   their associated fold-unfold lemmas,
   and some of their properties *)

(* ***** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
    nil =>
      match v2s with
        nil =>
          true
      | v2 :: v2s' =>
          false
      end
  | v1 :: v1s' =>
      match v2s with
        nil =>
          false
      | v2 :: v2s' =>
          eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
      end
  end.

Definition test_list_append (candidate : forall V : Type, list V -> list V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate nat nil nil)
     nil)
  &&
    (eqb_list
       nat
       Nat.eqb
       (candidate nat (1 :: 2 :: nil) (3 :: 4 :: nil))
       (1 :: 2 :: 3 :: 4 :: nil))
(* etc. *)
.

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

Property nil_is_left_neutral_for_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V nil vs = vs.
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

Property nil_is_right_neutral_for_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V vs nil = vs.
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

Property list_append_is_associative :
  forall (V : Type)
         (v1s v2s v3s : list V),
    list_append V v1s (list_append V v2s v3s)
    =
      list_append V (list_append V v1s v2s) v3s.
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

Property about_applying_list_append_to_a_singleton_list :
  forall (V : Type)
         (v1 : V)
         (v2s : list V),
    list_append V (v1 :: nil) v2s = v1 :: v2s.
Proof.
  intros V v1 v2s.
  rewrite -> fold_unfold_list_append_cons.
  rewrite -> fold_unfold_list_append_nil.
  reflexivity.
Qed.

(* ***** *)

Definition test_list_reverse (candidate : forall V : Type, list V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate nat nil)
     nil)
  &&
    (eqb_list
       nat
       Nat.eqb
       (candidate nat (1 :: 2 :: nil))
       (2 :: 1 :: nil))
(* etc. *)
.

Fixpoint list_reverse (V : Type) (vs : list V) : list V :=
  match vs with
    nil =>
      nil
  | v :: vs' =>
      list_append V (list_reverse V vs') (v :: nil)
  end.

Compute (test_list_reverse list_reverse).

Lemma fold_unfold_list_reverse_nil :
  forall (V : Type),
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

Property about_applying_list_reverse_to_a_singleton_list :
  forall (V : Type)
         (v : V),
    list_reverse V (v :: nil) = v :: nil.
Proof.
  intros V v.
  rewrite -> fold_unfold_list_reverse_cons.
  rewrite -> fold_unfold_list_reverse_nil.
  rewrite -> fold_unfold_list_append_nil.
  reflexivity.
Qed.

Property list_append_and_list_reverse_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_reverse V (list_append V v1s v2s)
    =
      list_append V (list_reverse V v2s) (list_reverse V v1s).
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

(* ***** *)

Fixpoint list_reverse_acc (V : Type) (v1s a : list V) : list V :=
  match v1s with
    nil =>
      a
  | v1 :: v1s' =>
      list_reverse_acc V v1s' (v1 :: a)
  end.

Lemma fold_unfold_list_reverse_acc_nil :
  forall (V : Type)
         (a : list V),
    list_reverse_acc V nil a =
      a.
Proof.
  fold_unfold_tactic list_reverse_acc.
Qed.

Lemma fold_unfold_list_reverse_acc_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' a : list V),
    list_reverse_acc V (v1 :: v1s') a =
      list_reverse_acc V v1s' (v1 :: a).
Proof.
  fold_unfold_tactic list_reverse_acc.
Qed.

Definition list_reverse_alt (V : Type) (vs : list V) : list V :=
  list_reverse_acc V vs nil.

Compute (test_list_reverse list_reverse).

Property about_applying_list_reverse_acc_to_a_singleton_list :
  forall (V : Type)
         (v : V)
         (a : list V),
    list_reverse_acc V (v :: nil) a = v :: a.
Proof.
  intros V v a.
  rewrite -> fold_unfold_list_reverse_acc_cons.
  rewrite -> fold_unfold_list_reverse_acc_nil.
  reflexivity.
Qed.

Property list_append_and_list_reverse_acc_commute_with_each_other :
  forall (V : Type)
         (v1s v2s a : list V),
    list_reverse_acc V (list_append V v1s v2s) a
    =
      list_reverse_acc V v2s (list_reverse_acc V v1s a).
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

(* ********** *)

(* Background material, Part II/II: binary trees.

   mirror, flatten, and flatten_alt
   and their associated fold-unfold lemmas *)

(* ***** *)

Inductive binary_tree (V : Type) : Type :=
  Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

Fixpoint eqb_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : binary_tree V) : bool :=
  match t1 with
    Leaf _ v1 =>
      match t2 with
        Leaf _ v2 =>
          eqb_V v1 v2
      | Node _ t21 t22 =>
          false
      end
  | Node _ t11 t12 =>
      match t2 with
        Leaf _ v2 =>
          false
      | Node _ t21 t22 =>
          eqb_binary_tree V eqb_V t11 t21 && eqb_binary_tree V eqb_V t12 t22
      end
  end.

(* ***** *)

Definition test_binary_tree_mirror (candidate : forall V : Type, binary_tree V -> binary_tree V) : bool :=
  (eqb_binary_tree
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat (Leaf nat 1) (Leaf nat 2)))
     (Node nat (Leaf nat 2) (Leaf nat 1)))
(* etc. *)
.

Fixpoint binary_tree_mirror (V : Type) (t : binary_tree V) : binary_tree V :=
  match t with
    Leaf _ v =>
      Leaf V v
  | Node _ t1 t2 =>
      Node V (binary_tree_mirror V t2) (binary_tree_mirror V t1)
  end.

Compute (test_binary_tree_mirror binary_tree_mirror).

Lemma fold_unfold_binary_tree_mirror_Leaf :
  forall (V : Type)
         (v : V),
    binary_tree_mirror V (Leaf V v) =
      Leaf V v.
Proof.
  fold_unfold_tactic binary_tree_mirror.
Qed.

Lemma fold_unfold_binary_tree_mirror_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    binary_tree_mirror V (Node V t1 t2) =
      Node V (binary_tree_mirror V t2) (binary_tree_mirror V t1).
Proof.
  fold_unfold_tactic binary_tree_mirror.
Qed.

(* ***** *)

Definition test_binary_tree_flatten (candidate : forall V : Type, binary_tree V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat (Leaf nat 1) (Leaf nat 2)))
     (1 :: 2 :: nil))
(* etc. *)
.

Fixpoint binary_tree_flatten (V : Type) (t : binary_tree V) : list V :=
  match t with
    Leaf _ v =>
      v :: nil
  | Node _ t1 t2 =>
      list_append V (binary_tree_flatten V t1) (binary_tree_flatten V t2)
  end.

Compute (test_binary_tree_flatten binary_tree_flatten).

Lemma fold_unfold_binary_tree_flatten_Leaf :
  forall (V : Type)
         (v : V),
    binary_tree_flatten V (Leaf V v) =
      v :: nil.
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

Lemma fold_unfold_binary_tree_flatten_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    binary_tree_flatten V (Node V t1 t2) =
      list_append V (binary_tree_flatten V t1) (binary_tree_flatten V t2).
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

(* ***** *)

Fixpoint binary_tree_flatten_acc (V : Type) (t : binary_tree V) (a : list V) : list V :=
  match t with
    Leaf _ v =>
      v :: a
  | Node _ t1 t2 =>
      binary_tree_flatten_acc V t1 (binary_tree_flatten_acc V t2 a)
  end.

Lemma fold_unfold_binary_tree_flatten_acc_Leaf :
  forall (V : Type)
         (v : V)
         (a : list V),
    binary_tree_flatten_acc V (Leaf V v) a =
      v :: a.
Proof.
  fold_unfold_tactic binary_tree_flatten_acc.
Qed.

Lemma fold_unfold_binary_tree_flatten_acc_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V)
         (a : list V),
    binary_tree_flatten_acc V (Node V t1 t2) a =
      binary_tree_flatten_acc V t1 (binary_tree_flatten_acc V t2 a).
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

Definition binary_tree_flatten_alt (V : Type) (t : binary_tree V) : list V :=
  binary_tree_flatten_acc V t nil.

Compute (test_binary_tree_flatten binary_tree_flatten_alt).

Property about_binary_tree_flatten_acc :
  forall (V : Type)
         (t : binary_tree V)
         (a1 a2 : list V),
    binary_tree_flatten_acc V t (list_append V a1 a2) =
      list_append V (binary_tree_flatten_acc V t a1) a2.
Proof.
  Compute (let V := nat in
           let t := Node nat
                      (Node nat (Leaf nat 1) (Leaf nat 2))
                      (Node nat (Leaf nat 3) (Leaf nat 4)) in
           let a1 := 10 :: 20 :: nil in
           let a2 := 30 :: 40 :: nil in
           binary_tree_flatten_acc V t (list_append V a1 a2) =
             list_append V (binary_tree_flatten_acc V t a1) a2).
  Compute (let V := nat in
           let t := Node nat
                      (Leaf nat 1)
                      (Node nat (Leaf nat 2) (Leaf nat 3)) in
           let a1 := 10 :: 20 :: nil in
           let a2 := 30 :: nil in
           binary_tree_flatten_acc V t (list_append V a1 a2) =
             list_append V (binary_tree_flatten_acc V t a1) a2).
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2]; intros a1 a2.
  - rewrite ->2 fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> fold_unfold_list_append_cons.
    reflexivity.
  - rewrite ->2 fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> (IHt2 a1 a2).
    rewrite -> (IHt1 (binary_tree_flatten_acc V t2 a1) a2).
    reflexivity.
Qed. (* Time permitting, prove this helpful property. *)

(* ********** *)

(* 0. Concisely describe
      list_append, list_reverse, and list_reverse_alt
      and
      mirror, flatten, and flatten_alt
      as well as their associated properties. *)

(* ********** *)

(* list_append: Concatenates two lists
   Properties:
   - nil is left and right neutral
   - Associative
   - Appending a singleton list is equivalent to cons *)

(* list_reverse: Reverses a list (recursive implementation)
   Properties:
   - Reversing a singleton list returns the same list
   - Reversing and appending commute *)

(* list_reverse_alt: Reverses a list (tail-recursive implementation)
   Uses an accumulator for efficiency
   Equivalent to list_reverse in functionality *)

(* binary_tree_mirror: Swaps left and right subtrees recursively
   Properties:
   - Mirroring a leaf returns the same leaf *)

(* binary_tree_flatten: Converts a binary tree to a list (in-order traversal)
   Uses list_append to combine results *)

(* binary_tree_flatten_alt: Converts a binary tree to a list (tail-recursive)
   Uses an accumulator for efficiency
   Equivalent to binary_tree_flatten in functionality *)

(* 1.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v1 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse V (binary_tree_flatten V t).
Proof.
  Compute (let V := nat in
           let t := Node V (Leaf V 1) (Node V (Leaf V 2) (Leaf V 3)) in
           binary_tree_flatten V (binary_tree_mirror V t) =
             list_reverse V (binary_tree_flatten V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 1.b Prove Theorem about_mirroring_and_flattening_v1. *)

Theorem about_mirroring_and_flattening_v1 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse V (binary_tree_flatten V t).
Proof.
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2].
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_Leaf.
    rewrite -> about_applying_list_reverse_to_a_singleton_list.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite -> fold_unfold_binary_tree_flatten_Node.
    rewrite -> IHt1.
    rewrite -> IHt2.
    Check list_append_and_list_reverse_commute_with_each_other.
    rewrite <- (list_append_and_list_reverse_commute_with_each_other V (binary_tree_flatten V t1)
                  (binary_tree_flatten V t2)).
    rewrite <- fold_unfold_binary_tree_flatten_Node.
    reflexivity.
Qed.

(* ********** *)

(* 2.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten V t).
Proof.
  Compute (let V := nat in
           let t := Node V (Leaf V 1) (Node V (Leaf V 2) (Leaf V 3)) in
           binary_tree_flatten V (binary_tree_mirror V t) =
             list_reverse_alt V (binary_tree_flatten V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* This theorem states that for any binary tree:
   1. If you mirror the tree and then flatten it
   2. It's equivalent to flattening the original tree and then reversing it

   This theorem holds for any type V and any binary tree t of that type.
 *)

(* ***** *)

(* 2.b Prove Theorem about_mirroring_and_flattening_v2. *)

Lemma eureka_about_mirroring_and_flattening_v2_aux :
  forall (V : Type)
         (a1s a2s a3s : list V),
    list_append V (list_reverse_acc V a1s a3s) a2s =
      list_reverse_acc V a1s (list_append V a3s a2s).
Proof.
  Compute (let V := nat in
           let a1s := (1 :: 2 :: 3 :: nil) in
           let a2s := (4 :: 5 :: 6 :: nil) in
           let a3s := (10 :: 11 :: nil) in
           list_append V (list_reverse_acc V a1s a3s) a2s =
             list_reverse_acc V a1s (list_append V a3s a2s)).
  intros V a1s.
  induction a1s as [ | a1 a1s' IHa1s']; intros a2s a3s.
  - rewrite ->2 fold_unfold_list_reverse_acc_nil.
    reflexivity.
  - rewrite ->2 fold_unfold_list_reverse_acc_cons.
    rewrite -> (IHa1s' a2s (a1 :: a3s)).
    rewrite -> fold_unfold_list_append_cons.
    reflexivity.
Qed.

Lemma about_mirroring_and_flattening_v2_aux:
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse_acc V (binary_tree_flatten V t) nil.
Proof.
  induction t as [ v | t1 IHt1 t2 IHt2].
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite -> fold_unfold_binary_tree_flatten_Leaf.
    Check about_applying_list_reverse_acc_to_a_singleton_list.
    rewrite -> (about_applying_list_reverse_acc_to_a_singleton_list V v nil).
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite -> fold_unfold_binary_tree_flatten_Node.
    rewrite -> IHt1.
    rewrite -> IHt2.
    Check eureka_about_mirroring_and_flattening_v2_aux.
    rewrite -> (eureka_about_mirroring_and_flattening_v2_aux V (binary_tree_flatten V t2)
                  (list_reverse_acc V (binary_tree_flatten V t1) nil) nil).
    rewrite -> nil_is_left_neutral_for_list_append.
    rewrite -> fold_unfold_binary_tree_flatten_Node.
    Check list_append_and_list_reverse_acc_commute_with_each_other.
    rewrite -> (list_append_and_list_reverse_acc_commute_with_each_other V (binary_tree_flatten V t1)
                  (binary_tree_flatten V t2) nil).
    reflexivity.
Qed.

Theorem about_mirroring_and_flattening_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten V t).
Proof.
  intros V t.
  unfold list_reverse_alt.
  rewrite -> about_mirroring_and_flattening_v2_aux.
  reflexivity.
Qed.

(* Of course you can also prove about_mirroring_and_flattening_v2
   as a corollary of about_mirroring_and_flattening_v1
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* 3.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v3 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten_alt V t).
Proof.
  Compute (let V := nat in
           let t := Node V (Leaf V 1) (Node V (Leaf V 2) (Leaf V 3)) in
           binary_tree_flatten_alt V (binary_tree_mirror V t) =
             list_reverse_alt V (binary_tree_flatten_alt V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* Theorem about_mirroring_and_flattening_v3 states that:
   For any binary tree:
   1. If you mirror the tree and then flatten it using the alternative flatten method
   2. It's equivalent to flattening the original tree using the alternative flatten method
      and then reversing the resulting list using the alternative reverse method

   This theorem holds for any type V and any binary tree t of that type.

   Note that v2 uses list_append and list_reverse_acc, while v3 uses their alternative versions
   (binary_tree_flatten_alt and list_reverse_alt).
 *)

(* ***** *)

(* 3.b Prove Theorem about_mirroring_and_flattening_v3. *)

(* Lemma eureka_binary_tree_flatten_acc_append : *)
(*   forall (V : Type) (t : binary_tree V) (acc : list V), *)
(*     binary_tree_flatten_acc V t acc = *)
(*     list_append V (binary_tree_flatten_acc V t nil) acc. *)
(* Proof. *)
(*   intros V t acc. *)
(*   rewrite <- (about_binary_tree_flatten_acc V t nil acc). *)
(*   rewrite -> nil_is_left_neutral_for_list_append. *)
(*   reflexivity. *)
(* Qed. *)

Lemma about_mirroring_and_flattening_v3_aux :
  forall (V : Type) (t : binary_tree V) (acc : list V),
    binary_tree_flatten_acc V (binary_tree_mirror V t) acc =
      list_reverse_acc V (binary_tree_flatten_acc V t nil) acc.
Proof.
  intros V t.
  induction t as [v | t1' IHt1' t2' IHt2']; intro acc.
  - rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite ->2 fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> fold_unfold_list_reverse_acc_cons.
    rewrite -> fold_unfold_list_reverse_acc_nil.
    reflexivity.
  - rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite ->2 fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> (IHt1' acc).
    rewrite -> (IHt2' (list_reverse_acc V (binary_tree_flatten_acc V t1' nil) acc)).
    rewrite <- (nil_is_left_neutral_for_list_append V nil) at 2.
    rewrite -> (about_binary_tree_flatten_acc V t1' nil nil).
    rewrite <- list_append_and_list_reverse_acc_commute_with_each_other.
    Check (about_binary_tree_flatten_acc).
    rewrite <-2 about_binary_tree_flatten_acc.
    rewrite -> nil_is_left_neutral_for_list_append.
    reflexivity.
Qed.

Theorem about_mirroring_and_flattening_v3 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse_alt V (binary_tree_flatten_alt V t).
Proof.
  Compute (let V := nat in
           let t := Node V (Leaf V 1) (Node V (Leaf V 2) (Leaf V 3)) in
           binary_tree_flatten_alt V (binary_tree_mirror V t) =
             list_reverse_alt V (binary_tree_flatten_alt V t)).
  intros V t.
  unfold binary_tree_flatten_alt, list_reverse_alt.
  Check (about_mirroring_and_flattening_v3_aux).
  Check (about_mirroring_and_flattening_v3_aux V t).
  exact (about_mirroring_and_flattening_v3_aux V t nil).
Qed.

(* Of course you can also prove about_mirroring_and_flattening_v3
   as a corollary of about_mirroring_and_flattening_v1 or of about_mirroring_and_flattening_v2
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* 4.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v4 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse V (binary_tree_flatten_alt V t).
Proof.
  Compute (let V := nat in
           let t := Node V (Leaf V 1) (Node V (Leaf V 2) (Leaf V 3)) in
           binary_tree_flatten_alt V (binary_tree_mirror V t) =
             list_reverse V (binary_tree_flatten_alt V t)).
Abort. (* Don't prove this theorem, you will do that just below. *)

(* Theorem about_mirroring_and_flattening_v4 states that:
   For any binary tree:
   1. If you mirror the tree and then flatten it using the alternative flatten method
   2. It's equivalent to flattening the original tree using the alternative flatten method
      and then reversing the resulting list using the standard reverse method

   This theorem holds for any type V and any binary tree t of that type.

   In connection to about_mirroring_and_flattening_v3, v4 is almost identical to v3,
   except that v4 uses the standard list_reverse function, while v3 uses list_reverse_alt.
 *)

(* ***** *)

(* 4.b Prove Theorem about_mirroring_and_flattening_v4. *)

(*
Lemma about_mirroring_and_flattening_v4_aux :
 *)

Lemma about_mirroring_and_flattening_v4_aux :
  forall (V : Type) (t : binary_tree V) (acc : list V),
    binary_tree_flatten_acc V (binary_tree_mirror V t) acc =
      list_append V (list_reverse V (binary_tree_flatten_acc V t nil)) acc.
Proof.
  Compute (let V := nat in
           let t := Node V (Leaf V 1) (Node V (Leaf V 2) (Leaf V 3)) in
           let acc := (8 :: 10 :: 11 :: nil) in
           binary_tree_flatten_acc V (binary_tree_mirror V t) acc =
             list_append V (list_reverse V (binary_tree_flatten_acc V t nil)) acc).
  intros V t.
  induction t as [v | t1' IHt1' t2' IHt2'].
  + intro acc.
    rewrite -> fold_unfold_binary_tree_mirror_Leaf.
    rewrite ->2 fold_unfold_binary_tree_flatten_acc_Leaf.
    rewrite -> about_applying_list_reverse_to_a_singleton_list.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> nil_is_left_neutral_for_list_append.
    reflexivity.
  + intro acc.
    rewrite -> fold_unfold_binary_tree_mirror_Node.
    rewrite ->2 fold_unfold_binary_tree_flatten_acc_Node.
    rewrite -> (IHt1' acc).
    rewrite -> (IHt2' (list_append V (list_reverse V (binary_tree_flatten_acc V t1' nil)) acc)).
    Check (about_binary_tree_flatten_acc).
    rewrite <- (fold_unfold_list_append_nil V nil) at 1.
    rewrite -> about_binary_tree_flatten_acc.
    rewrite -> list_append_is_associative.
    rewrite <- list_append_and_list_reverse_commute_with_each_other.
    
    rewrite <- (fold_unfold_list_append_nil V nil) at 4.
    rewrite -> about_binary_tree_flatten_acc.
    rewrite -> about_binary_tree_flatten_acc.
    Check (about_binary_tree_flatten_acc).
    rewrite -> 2 nil_is_right_neutral_for_list_append.
    Check (about_binary_tree_flatten_acc).
    rewrite <- (about_binary_tree_flatten_acc V t1' nil (binary_tree_flatten_acc V t2' nil)).
    rewrite -> nil_is_left_neutral_for_list_append.
    reflexivity.
Qed.

Theorem about_mirroring_and_flattening_v4 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
      list_reverse V (binary_tree_flatten_alt V t).
Proof.
  Compute (let V := nat in
           let t := Node V (Leaf V 1) (Node V (Leaf V 2) (Leaf V 3)) in
           binary_tree_flatten_alt V (binary_tree_mirror V t) =
             list_reverse V (binary_tree_flatten_alt V t)).
  intros V t.
  unfold binary_tree_flatten_alt.
  Check about_mirroring_and_flattening_v4_aux.
  Check (about_mirroring_and_flattening_v4_aux V t nil).
  rewrite -> (about_mirroring_and_flattening_v4_aux V t nil).
  Check nil_is_right_neutral_for_list_append.
  rewrite -> (nil_is_right_neutral_for_list_append V (list_reverse V (binary_tree_flatten_acc V t nil))).
  reflexivity.
Qed.

(* Of course you can also prove about_mirroring_and_flattening_v4
   as a corollary of about_mirroring_and_flattening_v1 or of about_mirroring_and_flattening_v2 or of about_mirroring_and_flattening_v3
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* end of week-01_about-reversing-a-list-and-mirroring-a-tree.v *)
