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

[ ]
Likewise, could you state and prove a similar proposition about super_refactor?

[ ]
Food for thought:
Restrict super_refactor to source arithmetic expressions with only Literal and Plus,
and compare this restricted version and mystery_function_19 in Week 05 of FPP/LPP.

Happy MR,
[ ]
P.S.: Would it make sense for refactoring to be idempotent?
If so, is that the case here?
