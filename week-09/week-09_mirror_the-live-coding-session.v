(* week-09_mirror_the-live-coding-session.v *)
(* was: *)
(* week-09_mirror.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 27 Oct 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Inductive binary_tree (V : Type) : Type :=
  Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

(* ********** *)

Fixpoint mirror_d (V : Type) (t : binary_tree V) : binary_tree V :=
  match t with
    Leaf _ v =>
    Leaf V v
  | Node _ t1 t2 =>
    Node V (mirror_d V t2) (mirror_d V t1)
  end.

Lemma fold_unfold_mirror_d_Leaf :
  forall (V : Type)
         (v : V),
    mirror_d V (Leaf V v) =
    Leaf V v.
Proof.
  fold_unfold_tactic mirror_d.
Qed.

Lemma fold_unfold_mirror_d_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    mirror_d V (Node V t1 t2) =
    Node V (mirror_d V t2) (mirror_d V t1).
Proof.
  fold_unfold_tactic mirror_d.
Qed.

(* ***** *)

Fixpoint mirror_cps (Ans V : Type) (t : binary_tree V) (k : binary_tree V -> Ans) : Ans :=
  match t with
    Leaf _ v     =>
    k (Leaf V v)
  | Node _ t1 t2 =>
    mirror_cps Ans V t1 (fun t1_m => mirror_cps Ans V t2 (fun t2_m => k (Node V t2_m t1_m)))
  end.

Lemma fold_unfold_mirror_cps_Leaf :
  forall (Ans V : Type) (v : V) (k : binary_tree V -> Ans),
    mirror_cps Ans V (Leaf V v) k =
    k (Leaf V v).
Proof.
  fold_unfold_tactic mirror_cps.
Qed.

Lemma fold_unfold_mirror_cps_Node :
  forall (Ans V : Type) (t1 t2 : binary_tree V) (k : binary_tree V -> Ans),
    mirror_cps Ans V (Node V t1 t2) k =
    mirror_cps Ans V t1 (fun t1_m => mirror_cps Ans V t2 (fun t2_m => k (Node V t2_m t1_m))).
Proof.
  fold_unfold_tactic mirror_cps.
Qed.

Definition mirror_c (V : Type) (t : binary_tree V) : binary_tree V :=
  mirror_cps (binary_tree V) V t (fun t_m => t_m).

(* ***** *)

Lemma completeness_of_mirror_cps_with_respect_to_mirror_d :
  forall (V : Type)
         (t t_m : binary_tree V),
    mirror_d V t = t_m ->
    forall (Ans : Type)
           (k : binary_tree V -> Ans),
      mirror_cps Ans V t k = k t_m.
Proof.
Admitted. (* routine induction *)

(* ***** *)

Lemma soundness_of_mirror_cps_with_respect_to_mirror_d :
  forall (V : Type)
         (t t_m : binary_tree V)
         (Ans : Type)
         (k : binary_tree V -> Ans),
    mirror_cps Ans V t k = k t_m ->
    mirror_d V t = t_m.
Proof.
  intros V t t_m Ans k H_cps.
  Check (completeness_of_mirror_cps_with_respect_to_mirror_d V t (mirror_d V t) (eq_refl (mirror_d V t)) Ans k).
  rewrite -> (completeness_of_mirror_cps_with_respect_to_mirror_d V t (mirror_d V t) (eq_refl (mirror_d V t)) Ans k) in H_cps.
  (* And we are stuck because we know nothing about k in H_cps. *)
Abort.

(* Overall, we need to show that the continuation is injective: *)

Definition injective (A B : Type) (f : A -> B) : Prop :=
  forall a1 a2 : A,
    f a1 = f a2 -> a1 = a2.

(* To be able to reason about the continuation,
   let us make it explicit how it is constructed,
   using the following relation: *)

Inductive cont (Ans V : Type) (k_init : binary_tree V -> Ans) : (binary_tree V -> Ans) -> Prop :=
| cont_0 :
    cont Ans V k_init k_init
| cont_1 :
    forall (k : binary_tree V -> Ans),
      cont Ans V k_init k ->
      forall t2 : binary_tree V,
        cont Ans V k_init (fun t1_m => mirror_cps Ans V t2 (fun t2_m => k (Node V t2_m t1_m)))
| cont_2 :
    forall (k : binary_tree V -> Ans),
      cont Ans V k_init k ->
      forall t1_m : binary_tree V,
        cont Ans V k_init (fun t2_m => k (Node V t2_m t1_m)).

(* The key point is that
     k_init
   and
     (fun t1_m => mirror_cps Ans V t2 (fun t2_m => k (Node V t2_m t1_m)))
   and
     (fun t2_m => k (Node V t2_m t1_m))
   are in the relation cont,
   given Ans and k_init. *)

(* So now we can reason about k by induction, based on cont. *)

(* Mandatory Eureka lemma: *)

Lemma totality_of_mirror_cps :
  forall (Ans V : Type)
         (t : binary_tree V)
         (k : binary_tree V -> Ans),
    exists t_m : binary_tree V,
      mirror_cps Ans V t k = k t_m.
Proof.
Admitted. (* routine induction *)

Proposition continuations_are_injective :
  forall (Ans V : Type)
         (k_init : binary_tree V -> Ans),
    injective (binary_tree V) Ans k_init ->
    forall k : binary_tree V -> Ans,
      cont Ans V k_init k ->
      injective (binary_tree V) Ans k.
Proof.
  intros Ans V k_init.
  unfold injective.
  intros I_k_init k C_k.
  induction C_k as [ | k' C_k' IHC_k' t2 | k' C_k' IHC_k' t1_m'];  intros t1_m t2_m H_t1_m_t2_m.
  - Check (I_k_init t1_m t2_m H_t1_m_t2_m).
    exact (I_k_init t1_m t2_m H_t1_m_t2_m).
  - Check (totality_of_mirror_cps Ans V t2 (fun t2_m : binary_tree V => k' (Node V t2_m t1_m))).
    destruct (totality_of_mirror_cps Ans V t2 (fun t2_m : binary_tree V => k' (Node V t2_m t1_m))) as [t2_m' H_t2_m'].
    rewrite -> H_t2_m' in H_t1_m_t2_m.
    destruct (totality_of_mirror_cps Ans V t2 (fun t2_m0 : binary_tree V => k' (Node V t2_m0 t2_m))) as [t2_m'' H_t2_m''].
    rewrite -> H_t2_m'' in H_t1_m_t2_m.
    Check (IHC_k'  (Node V t2_m'' t1_m)).
    Check (IHC_k' (Node V t2_m'' t1_m)
                  (Node V t2_m'' t2_m)).
    Check (IHC_k' (Node V t2_m' t1_m)
                  (Node V t2_m'' t2_m)
                  H_t1_m_t2_m).
    assert (H_tmp := IHC_k' (Node V t2_m' t1_m)
                  (Node V t2_m'' t2_m)
                  H_t1_m_t2_m).
    injection H_tmp as H1 ly.
    exact ly.
  - Check (IHC_k' (Node V t1_m t1_m') (Node V t2_m t1_m')).
    Check (IHC_k' (Node V t1_m t1_m') (Node V t2_m t1_m') H_t1_m_t2_m).
    assert (H_tmp := IHC_k' (Node V t1_m t1_m') (Node V t2_m t1_m') H_t1_m_t2_m).
    injection H_tmp as ly.
    exact ly.
Qed.

(* And now we can prove the soundness property: *)

Lemma soundness_of_mirror_cps_with_respect_to_mirror_d :
  forall (V : Type)
         (t t_m : binary_tree V)
         (Ans : Type)
         (k_init : binary_tree V -> Ans),
    injective (binary_tree V) Ans k_init ->
    forall k : binary_tree V -> Ans,
      cont Ans V k_init k ->
      mirror_cps Ans V t k = k t_m ->
      mirror_d V t = t_m.
Proof.
  intros V t t_m Ans k_init I_k_init k C_k H_cps.
  Check (completeness_of_mirror_cps_with_respect_to_mirror_d V t (mirror_d V t) (eq_refl (mirror_d V t)) Ans k).
  rewrite -> (completeness_of_mirror_cps_with_respect_to_mirror_d V t (mirror_d V t) (eq_refl (mirror_d V t)) Ans k) in H_cps.
  (* We are no longer stuck: *)
  Check (continuations_are_injective Ans V k_init I_k_init k C_k).
  assert (I_k := continuations_are_injective Ans V k_init I_k_init k C_k).
  unfold injective in I_k.
  Check (I_k (mirror_d V t) t_m H_cps).
  exact (I_k (mirror_d V t) t_m H_cps).
Qed.

(* ***** *)

Theorem functional_equivalence_of_mirror_c_and_mirror_d :
  forall (V : Type) (t : binary_tree V),
    mirror_c V t = mirror_d V t.
Proof.
  intros V t.
  unfold mirror_c.
  exact (completeness_of_mirror_cps_with_respect_to_mirror_d
           V t (mirror_d V t) (eq_refl (mirror_d V t)) (binary_tree V) (fun t_m => t_m)).
Qed.

Theorem soundness_and_completeness_of_mirror_c :
  forall (V : Type)
         (t t_m : binary_tree V),
    mirror_c V t = t_m <-> mirror_d V t = t_m.
Proof.
  intros V t t_m.
  unfold mirror_c.
  split.
  - intro H_mirror_cps.
    Check (soundness_of_mirror_cps V t t_m (binary_tree V) (fun t_m => t_m)).
    assert (I_k_init : injective (binary_tree V) (binary_tree V) (fun t_m : binary_tree V => t_m)).
    { unfold injective.
      intros t1 t2 H_t1_t2.
      exact H_t1_t2. }
    Check (soundness_of_mirror_cps V t t_m (binary_tree V) (fun t_m => t_m) I_k_init).
    Check (cont_0 (binary_tree V) V (fun t_m => t_m)).
    Check (soundness_of_mirror_cps V t t_m (binary_tree V) (fun t_m => t_m) I_k_init (fun t_m => t_m) (cont_0 (binary_tree V) V (fun t_m => t_m))).
    Check (soundness_of_mirror_cps V t t_m (binary_tree V) (fun t_m => t_m) I_k_init (fun t_m => t_m) (cont_0 (binary_tree V) V (fun t_m => t_m)) H_mirror_cps).
    exact (soundness_of_mirror_cps V t t_m (binary_tree V) (fun t_m => t_m) I_k_init (fun t_m => t_m) (cont_0 (binary_tree V) V (fun t_m => t_m)) H_mirror_cps).
  - intro H_mirror.
    Check (completeness_of_mirror_cps V t t_m H_mirror_d (binary_tree V) (fun t_m => t_m)).
    exact (completeness_of_mirror_cps V t t_m H_mirror_d (binary_tree V) (fun t_m => t_m)).
Qed.

(* ********** *)

(* end of week-09_mirror.v *)
