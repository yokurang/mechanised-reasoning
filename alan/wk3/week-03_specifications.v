(* week-03_specifications.v *)
(* FPP 2023 - CS3234 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 29 Aug 2023 *)

(* ********** *)

(* Paraphernalia: *)

Require Import Arith.

(* ********** *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

Proposition there_is_at_most_one_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    recursive_specification_of_addition add1 ->
    recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
Proof.
  intros add1 add2.
  unfold recursive_specification_of_addition.
  intros [H_add1_O H_add1_S] [H_add2_O H_add2_S].
  intro x.
  induction x as [ | x' IHx'].

  - intro y.
    rewrite -> (H_add2_O y).
    exact (H_add1_O y).

  - intro y.
    rewrite -> (H_add1_S x' y).
    rewrite -> (H_add2_S x' y).
    Check (IHx' y).
    rewrite -> (IHx' y).
    reflexivity.
Qed.

(* ********** *)

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = add x' (S y)).

(* ***** *)

(* Exercise 01 *)

Proposition there_is_at_most_one_tail_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    tail_recursive_specification_of_addition add1 ->
    tail_recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
Proof.
Abort.

(* ********** *)

Definition specification_of_the_predecessor_function (pred : nat -> nat) :=
  forall n : nat,
    pred (S n) = n.

Proposition there_is_at_most_one_predecessor_function :
  forall pred1 pred2 : nat -> nat,
    specification_of_the_predecessor_function pred1 ->
    specification_of_the_predecessor_function pred2 ->
    forall n : nat,
      pred1 n = pred2 n.
Proof.
  intros pred1 pred2.
  unfold specification_of_the_predecessor_function.
  intros H_pred1_S H_pred2_S.
  intro n.
  induction n as [ | n' IHn'].

  - 
Abort.

Definition make_predecessor_function (zero n : nat) :=
  match n with
  | 0 => zero
  | S n' => n'
  end.

Lemma about_make_predecessor_function :
  forall zero : nat,
    specification_of_the_predecessor_function (make_predecessor_function zero).
Proof.
  intro zero.
  unfold specification_of_the_predecessor_function.
  intros [ | n'].

  - unfold make_predecessor_function.
    reflexivity.

  - unfold make_predecessor_function.
    reflexivity.
Qed.  

Theorem there_are_at_least_two_predecessor_functions :
  exists pred1 pred2 : nat -> nat,
    specification_of_the_predecessor_function pred1 /\
    specification_of_the_predecessor_function pred2 /\
    exists n : nat,
      pred1 n <> pred2 n.
Proof.
  exists (make_predecessor_function 0).
  exists (make_predecessor_function 1).
  split.

  - exact (about_make_predecessor_function 0).

  - split.

    -- exact (about_make_predecessor_function 0).

    -- exists 0.
       unfold make_predecessor_function.
       Search (_ <> S _).
       Check (n_Sn 0).
       exact (n_Sn 0).
Qed.

(* ********** *)

Definition specification_of_the_total_predecessor_function (pred : nat -> option nat) :=
  (pred 0 = None)
  /\
  (forall n : nat,
      pred (S n) = Some n).

(* ***** *)

(* Exercise 02 *)

Proposition there_is_at_most_one_total_predecessor_function :
  forall pred1 pred2 : nat -> option nat,
    specification_of_the_total_predecessor_function pred1 ->
    specification_of_the_total_predecessor_function pred2 ->
    forall n : nat,
      pred1 n = pred2 n.
Proof.
  intros pred1 pred2.
  unfold specification_of_the_total_predecessor_function.
  intros [H_pred1_O H_pred1_S] [H_pred2_O H_pred2_S].
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> H_pred2_O.
    exact H_pred1_O.

  - rewrite -> (H_pred2_S n').
    exact (H_pred1_S n').

  Restart.

  intros pred1 pred2.
  unfold specification_of_the_total_predecessor_function.
  intros [H_pred1_O H_pred1_S] [H_pred2_O H_pred2_S].
  intros [ | n'].

  - rewrite -> H_pred2_O.
    exact H_pred1_O.

  - rewrite -> (H_pred2_S n').
    exact (H_pred1_S n').  
Qed.

(* ********** *)

Definition specification_of_the_predecessor_and_successor_function (ps : nat -> nat) :=
  (forall n : nat,
      ps (S n) = n)
  /\
  (forall n : nat,
      ps n = (S n)).

(* ***** *)

(* Exercise 03 *)

Theorem there_is_at_most_one_predecessor_and_successor_function :
  forall ps1 ps2 : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps1 ->
    specification_of_the_predecessor_and_successor_function ps2 ->
    forall n : nat,
      ps1 n = ps2 n.
Proof.
Abort.

(* ***** *)

Lemma a_contradictory_aspect_of_the_predecessor_and_successor_function :
  forall ps : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps ->
    ps 1 = 0 /\ ps 1 = 2.
Proof.
  intro ps.
  unfold specification_of_the_predecessor_and_successor_function.
  intros [H_ps_S H_ps].
  split.

  - rewrite -> (H_ps_S 0).
    reflexivity.

  - rewrite -> (H_ps 1).
    reflexivity.
Qed.

Theorem there_are_zero_predecessor_and_successor_functions :
  forall ps : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps ->
    exists n : nat,
      ps n <> ps n.
Proof.
  intros ps S_ps.
  Check (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps).
  destruct (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps) as [H_ps_0 H_ps_2].
  exists 1.
  rewrite -> H_ps_0.

  Restart.

  intros ps S_ps.
  Check (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps).
  destruct (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps) as [H_ps_0 H_ps_2].
  exists 1.
  rewrite -> H_ps_0 at 1.
  rewrite -> H_ps_2.
  Search (0 <> S _).
  Check (O_S 1).
  exact (O_S 1).
Qed.

(* ********** *)

Theorem the_resident_addition_function_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition Nat.add.
Proof.
  unfold recursive_specification_of_addition.
  split.
  - intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  - intros x' y.
    Search (S _ + _ = S (_ + _)).
    exact (Nat.add_succ_l x' y).
Qed.

(* ***** *)

(* Exercise 04 *)

Theorem the_resident_addition_function_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition Nat.add.
Proof.
Abort.

(* ********** *)

(* Exercise 05 *)

Theorem the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.
Proof.
Abort.

(* ********** *)

(* Exercise 06 *)

Theorem associativity_of_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [S_add_O S_add_S]. 
  intro x.
  induction x as [ | x' IHx'].
  - intros y z.
    Check (S_add_O (add y z)).
    rewrite -> (S_add_O (add y z)).
    rewrite -> (S_add_O y).
    reflexivity.
  - intros y z.
    Check (S_add_S x' (add y z)).
    rewrite -> (S_add_S x' (add y z)).
    Check (S_add_S x' y).
    rewrite -> (S_add_S x' y).
    Check (S_add_S (add x' y) z).
    rewrite -> (S_add_S (add x' y) z).
    rewrite <- IHx'.
    reflexivity.
Qed.

Theorem associativity_of_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [S_add_O S_add_S].
  intro x.
  induction x as [ | x' IHx'].
  - intros y z.
    Check (S_add_O (add y z)).
    rewrite -> (S_add_O (add y z)).
    rewrite -> (S_add_O y).
    reflexivity.
  - intros y z.
    Check (S_add_S x' (add y z)).
    rewrite -> (S_add_S x' (add y z)).
    rewrite -> (S_add_S x' y).
    Check (IHx' (S y) z).
    rewrite <- (IHx' (S y) z).
    assert (helpful:
             forall i j : nat,
               S (add i j) = add (S i) j).
    {
(*    intros i j.
      induction i as [ | i' IHi'].
      - rewrite -> (S_add_O j).
        rewrite -> (S_add_S 0 j).
        rewrite -> (S_add_O (S j)).
        reflexivity.
      - rewrite -> (S_add_S i' j).
        rewrite -> (S_add_S (S i') j).
        rewrite -> (S_add_S i' (S j)).
*)
      intro i.
      induction i as [ | i' IHi'].
      - intro j.
        rewrite -> (S_add_O j).
        rewrite -> (S_add_S 0 j).
        rewrite -> (S_add_O (S j)).
        reflexivity.
      - intro j.
        rewrite -> (S_add_S i' j).
        rewrite -> (S_add_S (S i') j).
        Check (IHi' (S j)).
        exact (IHi' (S j)).
    }
    rewrite <- (helpful y z).
    reflexivity.
Qed.


Lemma associativity_of_tail_recursive_addition_aux :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall i j : nat,
      S (add i j) = add (S i) j.
Proof.
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [S_add_O S_add_S].
  intro i.
  induction i as [ | i' IHi'].
  - intro j.
    rewrite -> (S_add_O j).
    rewrite -> (S_add_S 0 j).
    rewrite -> (S_add_O (S j)).
    reflexivity.
  - intro j.
    rewrite -> (S_add_S i' j).
    rewrite -> (S_add_S (S i') j).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

Theorem associativity_of_tail_recursive_addition' :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  intros add S_add.
  assert (H_tmp := S_add).
  unfold tail_recursive_specification_of_addition in H_tmp.
  destruct H_tmp as [S_add_O S_add_S].
  
  intro x.
  induction x as [ | x' IHx'].
  - intros y z.
    Check (S_add_O (add y z)).
    rewrite -> (S_add_O (add y z)).
    rewrite -> (S_add_O y).
    reflexivity.
  - intros y z.
    Check (S_add_S x' (add y z)).
    rewrite -> (S_add_S x' (add y z)).
    rewrite -> (S_add_S x' y).
    Check (IHx' (S y) z).
    rewrite <- (IHx' (S y) z).
    Check (associativity_of_tail_recursive_addition_aux add S_add).
    Check (associativity_of_tail_recursive_addition_aux add S_add y z).
    rewrite <- (associativity_of_tail_recursive_addition_aux add S_add y z).
    reflexivity.
Qed.

(* ********** *)

(* Exercise 07 *)

Lemma commutativity_of_recursive_addition_O :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n O = n.
Proof.
Admitted.

Lemma commutativity_of_recursive_addition_S :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 (S n2) = S (add n1 n2).
Proof.
Admitted.

Theorem commutativity_of_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 n2 = add n2 n1.
Proof.
  intros add S_add.
  assert (H_add_O := commutativity_of_recursive_addition_O add S_add).
  assert (H_add_S := commutativity_of_recursive_addition_S add S_add).
  unfold recursive_specification_of_addition in S_add.
  destruct S_add as [S_add_O S_add_S].
Abort.

(* ********** *)

(* Exercise 08a *)

Theorem O_is_left_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [S_add_O S_add_S].
  intro n.
  Check (S_add_O n).
  exact (S_add_O n).

  Restart.

(* There was actually no need to name the non-zero conjunt since the zero conjunct aligns with the goal. *)

  intro add.
  unfold recursive_specification_of_addition.
  intros [S_add_O _].
  intro n.
  Check (S_add_O n).
  exact (S_add_O n).

  Restart.
  
  (* We can also delay unfolding to reduce clutter in the goal window. *)
  
  intros add S_add.
  intro n.
  unfold recursive_specification_of_addition in S_add.
  destruct S_add as [S_add_O _].
  exact (S_add_O n). 
Qed.
  
(* ***** *)

(* Exercise 08b *)

Theorem O_is_right_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [S_add_O S_add_S].
  intro n.
  induction n as [ | n' IHn'].
  - exact (S_add_O 0).
  - rewrite -> (S_add_S n' 0).
    rewrite -> (IHn').
    reflexivity.

  Restart.

  (* Reducing number of named assumptions for clarity. Not significant now, but will be when proofs get bigger. *)

  intro add.
  intro S_add.
  intro n.
  induction n as [ | n' IHn'].
  - unfold recursive_specification_of_addition in S_add.
    destruct S_add as [S_add_O _].
    exact (S_add_O 0).
  - unfold recursive_specification_of_addition in S_add.
    destruct S_add as [_ S_add_S].
    rewrite -> (S_add_S n' 0).
    rewrite -> (IHn').
    reflexivity.
Qed.

(* ***** *)

(* Exercise 08c *)
Theorem O_is_left_neutral_for_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof.
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [S_add_O S_add_S].
  intro n.
  induction n as [ | n' IHn'].
  - exact (S_add_O 0).
  - Check (S_add_O (S n')).
    exact (S_add_O (S n')).

  Restart.

(* Previous proof is a proof by disguise!! There was no need to induct. Also we can delay the unfolding and destructing until we know what we might need. In this case, after intro n., we realise we only need the left conjunct of the recursive_specification_of_addition, so we only name that.*)

  intro add.
  intro S_add.
  intro n.
  unfold tail_recursive_specification_of_addition in S_add.
  destruct S_add as [S_add_O _].
  exact (S_add_O n).
Qed.

(* ***** *)

(* Exercise 08d *)
Lemma O_is_right_neutral_for_tail_recursive_addition_aux :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall x' y : nat,
      S (add x' y) = add x' (S y).
Proof.
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [S_add_O S_add_S].
  intro x'.
(* We resist the temptation to introduce y here. *)
  induction x' as [ | x'' IHx'].
  - intro y.
    rewrite -> (S_add_O y).
    rewrite -> (S_add_O (S y)).
    reflexivity.
  - intro y.
    rewrite -> (S_add_S x'' y).
    rewrite -> (S_add_S x'' (S y)).
(* No further simplifications obvious, move to further induction. *)
    induction y as [ |  y' IHy'].
    -- rewrite -> (IHx' 1).
(* The light of inductivity provides us with this extremely useful IHx' parameterised with y. *)
       reflexivity.
    -- Check (IHx' (S (S y'))).
       rewrite -> (IHx' (S (S y'))).
       reflexivity.

   Restart.

   intro add.
   unfold tail_recursive_specification_of_addition.
   intros [S_add_O S_add_S].
   intro x'.
   (* We resist the temptation to introduce y here. *)
   induction x' as [ | x'' IHx'].
  - intro y.
    rewrite -> (S_add_O y).
    rewrite -> (S_add_O (S y)).
    reflexivity.
  - intro y.
    rewrite -> (S_add_S x'' y).
    rewrite -> (S_add_S x'' (S y)).
    (* There was a further simplication possible!! *)
    Check (IHx' (S y)).
    rewrite -> (IHx' (S y)).
    reflexivity.
    (* Takeaway: If you are applying a further induction but never use the induction hypothesis, you don't need to further induct. Beware of inductive proofs that are just proof by cases in disguise!  *)              
Qed.

Theorem O_is_right_neutral_for_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof.
  intros add S_add.
  assert (H_tmp := S_add).
  unfold tail_recursive_specification_of_addition in H_tmp.
  destruct H_tmp as [S_add_O S_add_S].
  intro n.
  induction n as [ | n' IHn'].
  - exact (S_add_O 0).
  - Check (S_add_S n' 0).
    rewrite -> (S_add_S n' 0).
    Check (O_is_right_neutral_for_tail_recursive_addition_aux add S_add).
    Check (O_is_right_neutral_for_tail_recursive_addition_aux add S_add n' 0).
    rewrite <- (O_is_right_neutral_for_tail_recursive_addition_aux add S_add).
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ********** *)

(* end of week-03_specifications.v *)
