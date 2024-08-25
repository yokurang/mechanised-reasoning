This email is about the remainder of the homework for Week 02.

Could you also prove the following proposition about refactor:
[x] - Proved
Proposition equivalence_of_the_two_lemmas :
forall ae : arithmetic_expression,
  (forall s : string,
      evaluate ae = Expressible_msg s ->
      forall a : arithmetic_expression,
        evaluate (refactor_aux ae a) = Expressible_msg s)
  /\
  (forall (n : nat)
          (s : string),
      evaluate ae = Expressible_nat n ->
      forall a : arithmetic_expression,
        evaluate a = Expressible_msg s ->
        evaluate (refactor_aux ae a) = Expressible_msg s)
  /\
  (forall n1 n2 : nat,
      evaluate ae = Expressible_nat n1 ->
      forall a : arithmetic_expression,
        evaluate a = Expressible_nat n2 ->
        evaluate (refactor_aux ae a) = Expressible_nat (n1 + n2))
  <->
  forall a : arithmetic_expression,
    evaluate (refactor_aux ae a) = evaluate (Plus ae a).

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

Report
[] Introduction
[] Task 1: What does refactor do?
[] Task 2: Prove that refactoring preserves evaluation
[] Task 2b: Equivalence of the two lemmas ind vs case (No need to go through induction in depth, go through case in depth),
    explain why they differ and why cases is a much shorter proof
[] Task 3: What does super_refactor do?
[] Task 4: Prove that super-refactoring preserves evaluation
[] Task 4b: equivalence_of_the_two_lemmas_super_refactor
[] Task 5: Compare super_refactor and mystery_function_19
[] Task 6: Idempotence of refactoring
[] Task 7: Idempotence of super-refactoring
[] Conclusion
