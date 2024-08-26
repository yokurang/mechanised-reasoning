This email is about the remainder of the homework for Week 02.

Could you also prove the following proposition about refactor:
[x] - Proved
Proposition equivalence_of_the_two_lemmas :

[x]
Likewise, could you state and prove a similar proposition about super_refactor?

[ ]
Food for thought:
Restrict super_refactor to source arithmetic expressions with only Literal and Plus,
and compare this restricted version and mystery_function_19 in Week 05 of FPP/LPP.

Happy MR,
[x]
P.S.: Would it make sense for refactoring to be idempotent?
If so, is that the case here?

Refactor is idempotent if you evaluate. Super refactor is idempotent if you evaluate. Proven.
Just missing explanation in the report.

Feeback

[x] Proposition equivalence_of_the_two_lemmas :
The proof does not systematically focus on the current subgoal, which it should.

[X] Proposition equivalence_of_the_two_lemmas_case :

The first implication is not proved as such since it does not use the premises of the implication to prove its conclusion.
One needs to write something like

  intro ae.
  split.
  { intros [A [B C]].
    intro a.
    rewrite -> fold_unfold_evaluate_Plus.

and then, depending on (evaluate ae) and (evaluate a),
one can use A, B, and C to conclude.

Likewise, the proof of the converse implication should also be goal directed:

    intros E.
    split.
    { intros s E_ae_S a.
      ... }
    split.
    { intros n s E_ae_N a E_a_S.
      ... }
    intros n1 n2 E_ae_N a E_a_N.
    ...

[X] The proof of Lemma super_refactoring_preserves_evaluation_aux is fine.

[X] Ditto for Theorem super_refactoring_preserves_evaluation.

[X] The following names would be more straightforward:
  Proposition equivalence_of_the_two_lemmas_for_refactor
  Proposition equivalence_of_the_two_lemmas_for_super_refactor

-----

[X] Proposition equivalence_of_the_two_lemmas_super_refactor :

The statement is spot on.

Like the proof of Proposition equivalence_of_the_two_lemmas_case,
the proof of equivalence_of_the_two_lemmas_super_refactor
can be rewritten so that the proof of the first implication uses its premiss
rather than things proved earlier,
and so that the proof of the converse implication is more goal-directed.

Concretely, the proof of the first implication could start as follows:

  intro ae.
  split.
  { intros [A [B C]].
    case (evaluate ae) as [n1 | s1] eqn:E_ae.
    - split.
      + Check (C n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)).
        destruct (C n1 0 (eq_refl (Expressible_nat n1)) (Literal 0) (fold_unfold_evaluate_Literal 0)) as [ly _].
        exact ly.

Likewise, the proof of the converse implication could start as follows:

  intros [ESR_ae ESR_aux_ae_a].
  split.
  { intros s E_ae_S a.
    split.
    - rewrite -> E_ae_S in ESR_ae.
      exact ESR_ae.

Report
[X] Introduction
[X] Task 1: What does refactor do?
[X] Task 2: Prove that refactoring preserves evaluation
[X] Task 2b: Equivalence of the two lemmas ind vs case (No need to go through induction in depth, go through case in depth),
    explain why they differ and why cases is a much shorter proof
[X] Task 3: What does super_refactor do?
[X] Task 4: Prove that super-refactoring preserves evaluation
[] Task 4b: equivalence_of_the_two_lemmas_super_refactor
[] Task 5: Compare super_refactor and mystery_function_19
[X] Task 6: Idempotence of refactoring
[X] Task 7: Idempotence of super-refactoring
[] Conclusion
