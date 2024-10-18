(* week-09_summatorial_the-live-coding-session.v *)
(* was: *)
(* week-09_summatorial.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 27 Oct 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Definition test_summatorial (candidate : nat -> nat) : bool :=
  ((candidate 0) =? 0)
  &&
  ((candidate 1) =? 0 + 1)
  &&
  ((candidate 2) =? 0 + 1 + 2)
  &&
  ((candidate 3) =? 0 + 1 + 2 + 3)
  &&
  ((candidate 4) =? 0 + 1 + 2 + 3 + 4).

(* ***** *)

Definition summatorial_witness (n : nat) : nat :=
  (n * S n) / 2.

Compute (test_summatorial summatorial_witness).

(* ***** *)

Fixpoint summatorial_d (n : nat) : nat :=
  match n with
  | O =>
    0
  | S n' =>
    S n' + summatorial_d n'
  end.

Compute (test_summatorial summatorial_d).

Lemma fold_unfold_summatorial_d_O :
  summatorial_d 0 =
  0.
Proof.
  fold_unfold_tactic summatorial_d.
Qed.

Lemma fold_unfold_summatorial_d_S :
  forall n' : nat,
    summatorial_d (S n') =
    S n' + summatorial_d n'.
Proof.
  fold_unfold_tactic summatorial_d.
Qed.

(* ***** *)

Fixpoint summatorial_cps (Ans : Type) (n : nat) (k : nat -> Ans) : Ans :=
  match n with
  | O =>
    k 0
  | S n' =>
    summatorial_cps Ans n' (fun r => k (S n' + r))
  end.

Lemma fold_unfold_summatorial_cps_O :
  forall (Ans : Type) (k : nat -> Ans),
    summatorial_cps Ans O k =
    k 0.
Proof.
  fold_unfold_tactic summatorial_cps.
Qed.

Lemma fold_unfold_summatorial_cps_S :
  forall (Ans : Type) (n' : nat) (k : nat -> Ans),
    summatorial_cps Ans (S n') k =
    summatorial_cps Ans n' (fun r => k (S n' + r)).
Proof.
  fold_unfold_tactic summatorial_cps.
Qed.

Definition summatorial_c n :=
  summatorial_cps nat n (fun r => r).

Compute (test_summatorial summatorial_witness).

(* ***** *)

Proposition functional_equivalence_of_summatorial_cps_and_summatorial_d :
  forall (Ans : Type)
         (n : nat)
         (k : nat -> Ans),
    summatorial_cps Ans n k = k (summatorial_d n).
Proof.
  intros Ans n.
  induction n as [ | n' IH_n']; intro k.
  - rewrite -> fold_unfold_summatorial_cps_O.
    rewrite -> fold_unfold_summatorial_d_O.
    reflexivity.
  - rewrite -> fold_unfold_summatorial_cps_S.
    rewrite -> fold_unfold_summatorial_d_S.
    Check (IH_n' (fun r : nat => k (S n' + r))).
    rewrite -> (IH_n' (fun r : nat => k (S n' + r))).
    reflexivity.
Qed.

Theorem functional_equivalence_of_summatorial_d_and_summatorial_c :
  forall n : nat,
    summatorial_d n = summatorial_c n.
Proof.
  intro n.
  unfold summatorial_c.
  Check (functional_equivalence_of_summatorial_cps_and_summatorial_d nat n (fun r : nat => r)).
  exact (eq_sym (functional_equivalence_of_summatorial_cps_and_summatorial_d nat n (fun r : nat => r))).
Qed.

(* ***** *)

Proposition completeness_of_summatorial_cps_with_respect_to_summatorial_d :
  forall (n : nat)
         (m : nat),
    m = summatorial_d n ->
    forall (Ans : Type)
           (k : nat -> Ans),
      summatorial_cps Ans n k = k m.
Proof.
  intro n.
  induction n as [ | n' IHn']; intros m H_m Ans k.
  - rewrite -> fold_unfold_summatorial_cps_O.
    rewrite -> fold_unfold_summatorial_d_O in H_m.
    rewrite -> H_m.
    reflexivity.
  - rewrite -> fold_unfold_summatorial_cps_S.
    rewrite -> fold_unfold_summatorial_d_S in H_m.
    Check (IHn'
             (summatorial_d n')
             (eq_refl (summatorial_d n'))
             Ans
             (fun r : nat => k (S n' + r))).
    rewrite -> (IHn'
                  (summatorial_d n')
                  (eq_refl (summatorial_d n'))
                  Ans
                  (fun r : nat => k (S n' + r))).
    rewrite <- H_m.
    reflexivity.

  Restart.

  intros n m H_m Ans k.
  rewrite -> H_m.
  exact (functional_equivalence_of_summatorial_cps_and_summatorial_d Ans n k).
Qed.

(* ***** *)

Proposition soundness_of_summatorial_cps_with_respect_to_summatorial_d :
  forall (n : nat)
         (Ans : Type)
         (k : nat -> Ans)
         (m : nat),
    summatorial_cps Ans n k = k m ->
    m = summatorial_d n.
Proof.
  intros n Ans k m H_cps.
  Check (completeness_of_summatorial_cps_with_respect_to_summatorial_d n (summatorial_d n) (eq_refl (summatorial_d n)) Ans k).
  rewrite -> (completeness_of_summatorial_cps_with_respect_to_summatorial_d n (summatorial_d n) (eq_refl (summatorial_d n)) Ans k) in H_cps.
  (* And we are stuck because we know nothing about k in H_cps. *)
Abort.

(* Overall, we need to show that the continuation is injective: *)

Definition injective (A B : Type) (f : A -> B) : Prop :=
  forall a1 a2 : A,
    f a1 = f a2 -> a1 = a2.

(* To be able to reason about the continiuation,
   let us make it explicit how it is constructed,
   using the following relation: *)

Inductive cont (Ans : Type) (k_init : nat -> Ans) : (nat -> Ans) -> Prop :=
| cont_O :
    cont Ans k_init k_init
| cont_S :
    forall (k : nat -> Ans),
      cont Ans k_init k ->
      forall n' : nat,
        cont Ans k_init (fun r => k (S n' + r)).

(* The key point is that k_init and (fun r => k (S n' + r)) are in the relation cont,
   given Ans and k_init. *)

(* So now we can reason about k by induction, based on cont. *)

Proposition continuations_are_injective :
  forall (Ans : Type)
         (k_init : nat -> Ans),
    injective nat Ans k_init ->
    forall k : nat -> Ans,
      cont Ans k_init k ->
      injective nat Ans k.
Proof.
  intros Ans k_init I_k_init k C_k.
  (* Now we reason by induction on C_k: *)
  induction C_k as [ | k' C_k' IHC_k' n'].
  - exact I_k_init.
  - unfold injective.
    intros r1 r2 H_r1_r2.
    unfold injective in IHC_k'.
    Check (IHC_k' (S n' + r1) (S n' + r2)).
    Check (IHC_k' (S n' + r1) (S n' + r2) H_r1_r2).
    assert (H_tmp := IHC_k' (S n' + r1) (S n' + r2) H_r1_r2).
    Search (_ + _ = _ + _ -> _ = _).
    Check (plus_reg_l r1 r2 (S n') H_tmp).
    exact (plus_reg_l r1 r2 (S n') H_tmp).
Qed.
    
(* And now we can prove the soundness property: *)

Proposition soundness_of_summatorial_cps_with_respect_to_summatorial_d :
  forall (Ans : Type)
         (k_init : nat -> Ans),
    injective nat Ans k_init -> (* Assumption: k_init is injective. *)
    forall (n : nat)
           (k : nat -> Ans),
      cont Ans k_init k -> (* now k is both quantified and qualified. *)
      forall m : nat,
        summatorial_cps Ans n k = k m ->
        m = summatorial_d n.
Proof.
  intros Ans k_init I_k_init n k C_k m H_cps.
  Check (completeness_of_summatorial_cps_with_respect_to_summatorial_d n (summatorial_d n) (eq_refl (summatorial_d n)) Ans k).
  rewrite -> (completeness_of_summatorial_cps_with_respect_to_summatorial_d n (summatorial_d n) (eq_refl (summatorial_d n)) Ans k) in H_cps.
  (* We are no longer stuck: *)
  Check (continuations_are_injective Ans k_init I_k_init k C_k).
  assert (H_key := continuations_are_injective Ans k_init I_k_init k C_k).
  unfold injective in H_key.
  Check (H_key (summatorial_d n) m H_cps).
  exact (eq_sym (H_key (summatorial_d n) m H_cps)).
Qed.

(* ***** *)

Proposition completeness_of_summatorial_c_with_respect_to_summatorial_d :
  forall (n : nat)
         (m : nat),
    m = summatorial_d n ->
    summatorial_c n = m.
Proof.
  intros n m H_d.
  unfold summatorial_c.
  Check (completeness_of_summatorial_cps_with_respect_to_summatorial_d n m H_d nat (fun r => r)).
  exact (completeness_of_summatorial_cps_with_respect_to_summatorial_d n m H_d nat (fun r => r)).
Qed.

Proposition soundness_of_summatorial_c_with_respect_to_summatorial_d :
  forall (n : nat)
         (m : nat),
    summatorial_c n = m ->
    m = summatorial_d n.
Proof.
  intros n m H_c.
  unfold summatorial_c in H_c.
  Check (soundness_of_summatorial_cps_with_respect_to_summatorial_d nat (fun r => r)).
  assert (H_k_init : injective nat nat (fun r => r)).
  { unfold injective.
    intros a1 a2 H_tmp; exact H_tmp. }
  Check (soundness_of_summatorial_cps_with_respect_to_summatorial_d nat (fun r => r) H_k_init).
  Check (soundness_of_summatorial_cps_with_respect_to_summatorial_d nat (fun r => r) H_k_init n (fun r => r)).
  (* wanted : cont nat (fun r : nat => r) (fun r : nat => r) *)
  Check (cont_O nat (fun r => r)).
  Check (soundness_of_summatorial_cps_with_respect_to_summatorial_d nat (fun r => r) H_k_init n (fun r => r) (cont_O nat (fun r => r))).
  Check (soundness_of_summatorial_cps_with_respect_to_summatorial_d nat (fun r => r) H_k_init n (fun r => r) (cont_O nat (fun r => r)) m).
  exact (soundness_of_summatorial_cps_with_respect_to_summatorial_d nat (fun r => r) H_k_init n (fun r => r) (cont_O nat (fun r => r)) m H_c).
Qed.

(* ***** *)

(* end of week-09_summatorial_the-live-coding-session.v *)
