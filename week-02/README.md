Hi guys,

Thanks for your handin.  Here are some comments.

----------

week2_refactoring.v

-----

(* Task 2: Prove that refactoring preserves evaluation. *)


Proposition refactor_is_idempotent :
  forall (ae : arithmetic_expression),
      evaluate (refactor ae) = evaluate (refactor (refactor ae)).

That's not the definition of idempotency.

-----

(* Task 3: What does super_refactor do?
   Capture your observations into a unit-test function. *)
ASSIGNMENT_TWO_ALAN.pdf
good analysis but that stops too soon

(* Minus of two expressios does nothing, original expression is preserved. *)

except that the two operands are refactored

-----

(* Minus is similar to list_append, (Literal 0) as the accumulator *)

Minus is similar to list_append?!?

-----

(* Task 4: Prove that super-refactoring preserves evaluation. *)


Proposition super_refactor_is_idempotent :
  forall (ae : arithmetic_expression),
    evaluate (super_refactor ae) = evaluate (super_refactor (super_refactor ae)).

That's not the definition of idempotency.

----------

week-02.pdf

-----

the title needs more mindfulness:

- languages are not refactored; programs are

- a refactoring that does not preserve evaluation is pointless, so preserving evaluation should be implicit

- the grammar of the title suggests that the language is refactored with idempotence?

the picture is generically funny, not specific to this report

-----

S1

good but incomplete: flattening and reassociation are not mentioned

the quote is gratuitous

(Note that if you were to rename S1 to be S0, then the section numbers would aligned with the exercise numbers, a sign of mindfulness that makes you stand out.)

-----

2.1

good but incomplete (the introduction needs to give a complete picture of the section) and inaccurate ("During the proof" -> "In the course of proving that refactoring preserves the result of evaluation")

-----

2.3

> This is the aha! moment in the proof. Remember how in section 2.2,
> we discussed how refactoring is applying right-associativity to chained plus
> operations? Now we see the right-association in action in the goal because
> we’re in the case where ae1, ae2, and the accumulator a all evaluate to
> a natural number.

Very good.  This indeed the heart of the matter.


> We see that
> a 0 is added to the RHS of n1 such that Plus always stays on the top of
> the refactored binary tree and another 0 is added to the RHS of n2 because
> the right-most leaf for the refactored binary tree must be 0.

Very good.  This indeed the heart of the matter, and it is explained properly (note how no lists are mentioned).
This proper explanation should occur earlier in the report too.

-----

2.4

Also, it would have been a learning experience to actually carry out of the proof
of the lemma with the conjunction, not with (Plus ae a), because this shortcut
is not always possible.  Otherwise, next time, if the shorcut is not possible,
you won't be prepared to state the lemma nor to prove it.

-----

2.5

> We can take it a step further and show
> that refactor is idempotent, that is performing an operation multiple
> times has the same effect as doing it once.

This narrative is not consistent with the statement of the proposition
nor with its subsequent description:

> The proposition states that for all arithmetic expressions, evaluating
> the refactored arithmetic expression yields the same result as evaluating an
> arithmetic expression that has been refactored twice.

-----

2.6

> When reasoning about premises and conclusions, use the premises
> of the implication to prove its conclusions, rather than relying on
> previous lemmas that lets us override the premises.

But that is true in general, there is nothing specific about that here.

-----

S3 E2

3.1

this introduction is incomplete; it also needs to be more definite (so "most likely" needs to go)

"to deal with" is overly familiar for an academic report

-----

3.2

this section needs to be rewritten; for example, super-refactor does not map a subtraction to the same subtraction

the words "the right-most leaf instead of (Literal 0)" would come handy in this rewrite

-----

3.3

the analysis is OK

-----

"match cases become ugly really quickly"

what does this mean?

-----

3.4

OK

An explanation of the LHS of the bi-implication would be nice.

-----

3.5

same as in 2.5

-----

3.6

same as in 2.6

-----

4

> Mutual recursion in functions like super_refactor requires careful
> consideration in proofs, often necessitating conjunctive lemmas.

Not "often": "always", as seen for even/odd and ternary/post_ternary/pre_ternary in FPP.

> When proving equivalence, it’s crucial to consider all possible evalua-
> tion outcomes and their interactions, but it is equivalently important
> to be mindful of whether the sub-branch of the proof occurs in prac-
> tice of not (ex: in an ltr programme, if the ae1 evaluates to an error,
> we do not have to consider the what ae2 evaluates to).

That is true.
However, in the proof of
  Proposition equivalence_of_the_two_lemmas_for_refactor_case :
you wrote
  case (evaluate ae) as [ n | s ] eqn:E_ae;
    case (evaluate a) as [ n' | s' ] eqn:E_a.
which forced you to consider all cases, even when ae evaluated to an error.

> Idempotence in the context of program transformations can be nu-
> anced, applying to evaluation outcomes rather than structural equal-
> ity.

Of course I don't know who wrote this sentence,
and so the following message is for the two other authors:
whenever you see a sentence that waxes lyrical (here: "nuanced")
in the first draft of your report,
convey appreciation for the style,
and then rewrite this sentence in a tighter form.

The quote is overly general, and considering that it arises
from something wrong (idempotence is not what what formalized),
it should be omitted.

----------

Overall, this handin includes multiples hints that
there is a shorter, tighter, and more accurate version
that is begging to come into existence.
Could you mindfully rewrite this handin in a "less is more" sort of way
as well as in a more consistent and accurate way?

Thanks for attending MR,

-- Olivier
