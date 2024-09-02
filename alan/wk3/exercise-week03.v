(* Exercise 04: reflecting on the tail-recursive specification of addition *)

Require Import Arith.

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = add x' (S y)).

Theorem the_resident_addition_function_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition Nat.add.

Proof.
  unfold tail_recursive_specification_of_addition.
  split.
  + intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  + intros x' y.
    Search (S _ + _ = S (_ + _)).
    rewrite -> (plus_Sn_m x' y).
    Search ( S (_ + _) = _).
    rewrite <- (plus_n_Sm x' y).
    reflexivity.

  Restart.

  unfold tail_recursive_specification_of_addition.  
  split.
  + intro y.      
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  + intros x' y.
    Search (S _ + _ = _ + S _).
    exact (Nat.add_succ_comm x' y). (* the nested application of the previous proof *) 
Qed.

(* Comfort zone of basic tactics in a systematic way *)
(* Everything is useful only if you reuse it *)



(* The resident addition function does satisfy the tail-recursive specification of addition *)

(* Exercise 05: reasoning about the recursive specification of addition and the tail-recursive one *)


(* From lecture slides *)

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
  intro add1.
  intro add2.
  intro S_add1.
  intro S_add2.
  intro x.
  induction x as [ | x' IHx'].
  (* light of inductil *)
  + intro y.
    destruct S_add1 as [S_add1_O _].
    destruct S_add2 as [S_add2_O _].
    Check (S_add1_O y).
    rewrite -> (S_add1_O y).
    Check (S_add2_O y).
    rewrite -> (S_add2_O y).
    reflexivity.
  + intro y.
    destruct S_add1 as [_ S_add1_S].
    destruct S_add2 as [_ S_add2_S].
    Check (S_add1_S x' y).
    rewrite -> (S_add1_S x' y).
    Check (S_add2_S x' y).
    rewrite -> (S_add2_S x' y).
    rewrite (IHx' y).
    reflexivity.
Qed.

Theorem the_resident_addition_function_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition Nat.add.

Proof.

  unfold recursive_specification_of_addition.
  split.
  + intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  + intros x' y.
    Search (S _ + _ = S (_ + _)).
    rewrite -> (plus_Sn_m x' y).
    reflexivity.
  
  Restart.
  
  unfold recursive_specification_of_addition.
  split.
  + intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  + intros x' y.
    Search (S _ + _ = S (_ + _)).
    exact (Nat.add_succ_l x' y).
Qed.

(* ***** *)

Theorem the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.

Proof.
  intro add.
  unfold recursive_specification_of_addition.
  unfold tail_recursive_specification_of_addition.
    
  split.
  + intros [S_add_O S_add_S].
    split.
    ++ intro y.
       Check (S_add_O y).
       rewrite (S_add_O y).
       reflexivity.
    ++ intro x'.
       induction x' as [ | x'' IHx''].
       +++ intro y.
           Check (S_add_S 0 y).
           rewrite -> (S_add_S 0 y).
           Check (S_add_O y).
           rewrite -> (S_add_O y).
           Check (S_add_O (S y)).
           rewrite -> (S_add_O (S y)).
           reflexivity.
       +++ intro y.
           Check (S_add_S (S x'') y).
           rewrite -> (S_add_S (S x'') y).
           Check (IHx'' y).
           rewrite (IHx'' y).
           Check (S_add_S x'' (S y)).
           rewrite -> (S_add_S x'' (S y)).
           reflexivity.
  + intros [S_add_O S_add_S].
    split.
    ++ intro y.
       Check (S_add_O y).
       rewrite -> (S_add_O y).
       reflexivity.
    ++ intro x'.
       induction x' as [ | x'' IHx''].
       intro y.
       +++
         Check (S_add_S 0 y).
         rewrite -> (S_add_S 0 y).
         Check (S_add_O (S y)).
         rewrite -> (S_add_O (S y)).
         
         Check (S_add_O y).
         rewrite -> (S_add_O y).

         reflexivity.
       +++ intro y.
           Check (S_add_S (S x'') y).
           rewrite -> (S_add_S (S x'') y).
           Check (IHx'' (S y)).
           rewrite -> (IHx'' (S y)).

           Check (S_add_S x'' y).
           rewrite -> (S_add_S x'' y).

           reflexivity.
Qed.

(*
  Exercise 09:
  Is the specification of mirror ambiguous?
  Is the specification of number_of_leaves ambiguous?
  Is the specification of number_of_nodes ambiguous?
 *)

(* From the lecture notes *)

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

(* ********** *)

Definition specification_of_mirror (mirror : forall V : Type, binary_tree V -> binary_tree V) : Prop :=
  (forall (V : Type)
          (v : V),
      mirror V (Leaf V v) =
      Leaf V v)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      mirror V (Node V t1 t2) =
      Node V (mirror V t2) (mirror V t1)).

(* ***** *)

(* Is the specification of mirror ambiguous? *)
Proposition there_is_at_most_one_mirror_function :
  forall mirror1 mirror2 : forall V : Type, binary_tree V -> binary_tree V,
    specification_of_mirror mirror1 ->
    specification_of_mirror mirror2 ->
    forall (V : Type)
           (t : binary_tree V),
      mirror1 V t = mirror2 V t.

Proof.
  intros mirror1 mirror2.
  intros S_mirror1 S_mirror2 V t.
  induction t as [n | t1 IHt1 t2 IHt2].
  + unfold specification_of_mirror in S_mirror1.
    unfold specification_of_mirror in S_mirror2.
    destruct S_mirror1 as [S_mirror1_Leaf _].
    destruct S_mirror2 as [S_mirror2_Leaf _].
    Check (S_mirror1_Leaf V n).
    rewrite -> (S_mirror1_Leaf V n).
    Check (S_mirror2_Leaf V n).
    rewrite -> (S_mirror2_Leaf V n).
    reflexivity.
  + unfold specification_of_mirror in S_mirror1.
    unfold specification_of_mirror in S_mirror2.
    destruct S_mirror1 as [_ S_mirror1_Node].
    destruct S_mirror2 as [_ S_mirror2_Node].

    Check (S_mirror1_Node V t1 t2).
    rewrite -> (S_mirror1_Node V t1 t2).

    Check (S_mirror2_Node V t1 t2).
    rewrite -> (S_mirror2_Node V t1 t2).

    Check IHt1.
    rewrite IHt1.

    Check IHt2.
    rewrite IHt2.
    reflexivity.
Qed.

Definition specification_of_number_of_leaves (number_of_leaves : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_leaves V (Leaf V v) =
      1)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_leaves V (Node V t1 t2) =
        number_of_leaves V t1 + number_of_leaves V t2).

Proposition there_is_at_most_one_number_of_leaves_function :
  forall number_of_leaves1 number_of_leaves2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_leaves number_of_leaves1 ->
    specification_of_number_of_leaves number_of_leaves2 ->
    forall (V : Type)
           (t : binary_tree V),
      number_of_leaves1 V t = number_of_leaves2 V t.
Proof.
  intros number_of_leaves1 number_of_leaves2.
  intros S_number_of_leaves1 S_number_of_leaves2 V t.
  induction t as [n | t1 IHt1 t2 IHt2].
  + unfold specification_of_number_of_leaves in S_number_of_leaves1.
    unfold specification_of_number_of_leaves in S_number_of_leaves2.
    destruct S_number_of_leaves1 as [S_number_of_leaves1_Leaf _].
    destruct S_number_of_leaves2 as [S_number_of_leaves2_Leaf _].
    Check (S_number_of_leaves1_Leaf V n).
    rewrite -> (S_number_of_leaves1_Leaf V n).
    Check (S_number_of_leaves2_Leaf V n).
    rewrite -> (S_number_of_leaves2_Leaf V n).
    reflexivity.
  + unfold specification_of_number_of_leaves in S_number_of_leaves1.
    unfold specification_of_number_of_leaves in S_number_of_leaves2.
    destruct S_number_of_leaves1 as [_ S_number_of_leaves1_Node].
    destruct S_number_of_leaves2 as [_ S_number_of_leaves2_Node].
    Check (S_number_of_leaves1_Node V t1 t2).
    rewrite -> (S_number_of_leaves1_Node V t1 t2).
    Check (S_number_of_leaves2_Node V t1 t2).
    rewrite -> (S_number_of_leaves2_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

Definition specification_of_number_of_nodes (number_of_nodes : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_nodes V (Leaf V v) =
      0)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_nodes V (Node V t1 t2) =
        S (number_of_nodes V t1 + number_of_nodes V t2)).

Proposition there_is_at_most_one_number_of_nodes_function :
  forall number_of_nodes1 number_of_nodes2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_nodes number_of_nodes1 ->
    specification_of_number_of_nodes number_of_nodes2 ->
    forall (V : Type)
           (t : binary_tree V),
      number_of_nodes1 V t = number_of_nodes2 V t.
Proof.
  intros number_of_nodes1 number_of_nodes2.
  intros S_number_of_nodes1 S_number_of_nodes2 V t.
  induction t as [n | t1 IHt1 t2 IHt2].
  + unfold specification_of_number_of_nodes in S_number_of_nodes1.
    unfold specification_of_number_of_nodes in S_number_of_nodes2.
    destruct S_number_of_nodes1 as [S_number_of_nodes1_Leaf _].
    destruct S_number_of_nodes2 as [S_number_of_nodes2_Leaf _].
    Check (S_number_of_nodes1_Leaf V n).
    rewrite -> (S_number_of_nodes1_Leaf V n).

    Check (S_number_of_nodes2_Leaf V n).
    rewrite -> (S_number_of_nodes2_Leaf V n).

    reflexivity.
  + unfold specification_of_number_of_nodes in S_number_of_nodes1.
    unfold specification_of_number_of_nodes in S_number_of_nodes2.
    destruct S_number_of_nodes1 as [_ S_number_of_nodes1_Node].
    destruct S_number_of_nodes2 as [_ S_number_of_nodes2_Node].
    
    Check (S_number_of_nodes1_Node V t1 t2).
    rewrite -> (S_number_of_nodes1_Node V t1 t2).

    Check (S_number_of_nodes2_Node V t1 t2).
    rewrite -> (S_number_of_nodes2_Node V t1 t2).
    
    rewrite -> IHt1.
    rewrite -> IHt2.

    reflexivity.
Qed.

 (*
  Exercise 06:
  If a function satisfies the recursive specification of addition, is it associative?
  If a function satisfies the tail-recursive specification of addition, is it associative?
 *)

Theorem associativity_of_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  
  (*intros add S_add.*) (* specification of add here introduced to minimise the

more constructors => bigger proof => minimise naming of specification through introduction of S_ + specification name *)
  intro add.
  intro S_add.
  unfold recursive_specification_of_addition in S_add.
  intro x'.
  induction x' as [ | x'' IHx''].
  + intros y z.
    destruct S_add as [H_add_O _].
    Check (H_add_O (add y z)).
    rewrite -> (H_add_O (add y z)).
    Check (H_add_O y).
    rewrite -> (H_add_O y).
    reflexivity.
  + intros y z.
    destruct S_add as [_ S_add_S].
    Check (S_add_S x'' (add y z)).
    rewrite -> (S_add_S x'' (add y z)).
    Check (S_add_S x'' y).
    rewrite -> (S_add_S x'' y).
    Check (S_add_S (add x'' y) z).
    rewrite -> (S_add_S (add x'' y) z). (* check the goal when choosing arrows *)
    Check (IHx'' y z).
    rewrite -> (IHx'' y z).
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

  intro x'.
  induction x' as [ | x'' IHx''].
  + intros y z.
    Check (S_add_O (add y z)).
    rewrite -> (S_add_O (add y z)).
    Check (S_add_O y).
    rewrite -> (S_add_O y).
    reflexivity.
  + intros y z.
    Check (S_add_S x'' (add y z)).
    rewrite -> (S_add_S x'' (add y z)).
    Check (S_add_S x'' y).
    rewrite -> (S_add_S x'' y).
    Check (IHx'' (S y) z).
    rewrite <- (IHx'' (S y) z).

    assert (helpful :
             forall i j : nat,
               S (add i j) = add (S i) j).
    {
      intro i.
      induction i as [ | i' IHi']. (* this will give forall j for stronger induction hypothesis *)
      + intro j.
        Check (S_add_O j).
        rewrite -> (S_add_O j).
        Check (S_add_S 0 j).
        rewrite -> (S_add_S 0 j).
        Check (S_add_O (S j)).
        rewrite -> (S_add_O (S j)).
        reflexivity.
      + intro j.
        Check (S_add_S i' j).
        rewrite -> (S_add_S i' j).
        Check (S_add_S (S i') j).
        rewrite -> (S_add_S (S i') j).
        Check (IHi' (S j)).
        exact (IHi' (S j)). 
    }

    rewrite -> (helpful y z).
    reflexivity.
Qed.
(* aux lemma of theorem is name of theorem + _aux *) 
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
  induction i as [ | i' IHi']. (* this will give forall j for stronger induction hypothesis *)
  + intro j.
    Check (S_add_O j).
    rewrite -> (S_add_O j).
    Check (S_add_S 0 j).
    rewrite -> (S_add_S 0 j).
    Check (S_add_O (S j)).
    rewrite -> (S_add_O (S j)).
    reflexivity.
  + intro j.
    Check (S_add_S i' j).
    rewrite -> (S_add_S i' j).
    Check (S_add_S (S i') j).
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
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [S_add_O S_add_S].

  intro x'.
  induction x' as [ | x'' IHx''].
  + intros y z.
    Check (S_add_O (add y z)).
    rewrite -> (S_add_O (add y z)).
    Check (S_add_O y).
    rewrite -> (S_add_O y).
    reflexivity.
  + intros y z.
    Check (S_add_S x'' (add y z)).
    rewrite -> (S_add_S x'' (add y z)).
    Check (S_add_S x'' y).
    rewrite -> (S_add_S x'' y).
    Check (IHx'' (S y) z).
    rewrite <- (IHx'' (S y) z).
    Check (associativity_of_tail_recursive_addition_aux).
    Check (associativity_of_tail_recursive_addition_aux add).
    Check (associativity_of_tail_recursive_addition_aux add (conj S_add_O S_add_S)).
    Check (associativity_of_tail_recursive_addition_aux add (conj S_add_O S_add_S) y z).
    rewrite -> (associativity_of_tail_recursive_addition_aux add (conj S_add_O S_add_S) y z).
    reflexivity.

  Restart.

  intros add S_add.
  assert (H_tmp := S_add).
  unfold tail_recursive_specification_of_addition in H_tmp.
  destruct H_tmp as [S_add_O S_add_S].
  

  intro x'.
  induction x' as [ | x'' IHx''].
  + intros y z.
    Check (S_add_O (add y z)).
    rewrite -> (S_add_O (add y z)).
    Check (S_add_O y).
    rewrite -> (S_add_O y).
    reflexivity.
  + intros y z.
    Check (S_add_S x'' (add y z)).
    rewrite -> (S_add_S x'' (add y z)).
    Check (S_add_S x'' y).
    rewrite -> (S_add_S x'' y).
    Check (IHx'' (S y) z).
    rewrite <- (IHx'' (S y) z).
    Check (associativity_of_tail_recursive_addition_aux).
    Check (associativity_of_tail_recursive_addition_aux add).
    Check (associativity_of_tail_recursive_addition_aux add S_add).
    Check (associativity_of_tail_recursive_addition_aux add S_add y z).
    rewrite -> (associativity_of_tail_recursive_addition_aux add S_add y z).
    reflexivity.
Qed.

(*
  Exercise 08:
  If a function satisfies the recursive specification of addition, is O left-neutral for it?
  If a function satisfies the recursive specification of addition, is O right-neutral for it?
  If a function satisfies the tail-recursive specification of addition, is O left-neutral for it?
  If a function satisfies the tail-recursive specification of addition, is O right-neutral for it?
 *)

(* Exercise 08a *)

Theorem O_is_left_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [S_add_O _].
  intro n.
  Check (S_add_O n).
  exact (S_add_O n).

  Restart.
  intros add S_add.
  unfold recursive_specification_of_addition in S_add.
  intro n.

  destruct S_add as [S_add_O _].
  Check (S_add_O n).
  exact (S_add_O n).
Qed.

(* Yes *)

(* ***** *)

(* Exercise 08b *)

Theorem O_is_right_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof.
  (*
  intros add S_add.
  destruct S_add as [H_add_0 H_add_S].
  intro n.
  induction n as [ | n' IHn'].
  + apply (H_add_0 0).
  + rewrite -> (H_add_S n' 0).
    Search (S _ = _).
    rewrite (IHn').
    reflexivity.
  *)
  Restart.
  intro add.
  unfold recursive_specification_of_addition.
  intros [S_add_O S_add_S].
  intro n.
  induction n as [ | n' IHn'].
  + Check (S_add_O 0).
    exact (S_add_O 0).
  + Check (S_add_S n' 0).
    rewrite -> (S_add_S n' 0).
    rewrite -> IHn'.
    reflexivity.
  Restart.
  intro add.
  intro S_add.
  intro n.
  induction n as [ | n' IHn'].
  + unfold recursive_specification_of_addition in S_add.
    destruct S_add as [S_add_O _].
    exact (S_add_O 0).
  + (* unfold in the bullet points for easier / minimalist viewing *)
    unfold recursive_specification_of_addition in S_add.
    destruct S_add as [_ S_add_S].
    rewrite -> (S_add_S n' 0).
    rewrite -> IHn'.
    reflexivity.     
Qed. 

(* ********** *)

(* Exercise 08c *)

Theorem O_is_left_neutral_for_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof.
  intros add S_add.
  destruct S_add as [H_add_0 _].
  intro n.
  apply (H_add_0 n).
Qed.
(* ***** *)

(* Exercise 08d *)

Theorem O_is_right_neutral_for_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof.
  intros add S_add.
  destruct S_add as [H_add_0 H_add_S].
  intro n.
  induction n as [ | n' IHn'].
  + apply (H_add_0 0).
  + rewrite -> (H_add_S n' 0).
    rewrite (IHn').
    reflexivity.
Qed.

(* ********** *)
