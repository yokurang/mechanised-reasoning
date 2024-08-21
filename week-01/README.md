TODO: Submission 1:

## term-project.v

-----
Proposition Plus_is_conditionally_commutative:
  forall ae1 ae2 : arithmetic_expression,
  forall n1 n2 : nat,

should be

Proposition Plus_is_conditionally_commutative :
  forall (ae1 ae2 : arithmetic_expression)
         (n1 n2 : nat),

(with an extra space before ":", with only one forall, and with a standard indentation).

Also,

  destruct (evaluate ae2) as [m1 | s2]
doesn't make sense logically.
-> Made changes to make it more logical. Most likely a typo.

-----

Still about Proposition Plus_is_conditionally_commutative,
could you make the implication an equivalence?
(Consider this question a challenge.)

-----

Proposition Literal_0_is_conditionally_absorbing_for_Times_on_the_left :

same: could you state this proposition as an equivalence,
not as an implication?

Proposition Literal_0_is_not_absorbing_for_Times_on_the_right :
Proposition Literal_0_is_conditionally_absorbing_for_Times_on_the_right :

ditto

Proposition Times_is_associative :

good

Proposition Times_is_not_commutative :
Proposition Times_is_conditionally_commutative  :

ditto

Proposition Times_is_conditionally_distributive_over_Plus_on_the_right :
  forall ae1 ae2 ae3 : arithmetic_expression,
  forall n1 n2 n3 : nat,
  (evaluate ae1 = Expressible_nat n1 /\
   evaluate ae2 = Expressible_nat n2 /\
   evaluate ae3 = Expressible_nat n3) ->
    evaluate (Times (Plus ae1 ae2) ae3) =
    evaluate (Plus (Times ae1 ae3) (Times ae2 ae3)).

What a massive overkill.
The issue is that

* in the LHS, ae1, and then ae2, and then ae3 are evaluated, whereas

* in the RHS, ae1, and then ae3, and then ae2, and then ae3 are evaluated.

Since ae1 is evaluated first, it is unconstrained.

If ae2 evaluates to a nat, then the property holds.

If ae3 evaluates to a nat, then the property holds.

So the conditional property should be restated,
and while you are at it, why don't you state it as an equivalence?

-----

Proposition Times_distributive_over_Plus_on_the_left :

OK

----------

## week-01_about-reversing-a-list-and-mirroring-a-tree.v

-----

[x]
Lemma about_mirroring_and_flattening_v2_aux :
  forall (V : Type)
         (a1s a2s prefix : list V),
    list_append V (list_reverse_acc V a1s prefix) a2s =
      list_reverse_acc V a1s (list_append V prefix a2s).
Proof.
  Compute (let V := nat in
           let a1s := (1 :: 2 :: 3 :: nil) in
           let a2s := (4 :: 5 :: 6 :: nil) in
           let prefix := (10 :: 11 :: nil) in
           list_append V (list_reverse_acc V a1s prefix) a2s =
             list_reverse_acc V a1s (list_append V prefix a2s)).

The name "prefix" is confusing.
Why don't you stick to a1s, a2s, and a3s, in a logical order.

-----

[x]
Theorem about_mirroring_and_flattening_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
    list_reverse_alt V (binary_tree_flatten V t).
Proof.
  intros V t.
  unfold list_reverse_alt.
  induction t as [ v | t1 IHt1 t2 IHt2].

No because of
  https://delimited-continuation.github.io/CS3234/2023-2024_Sem2/week-05_structuring-programs-structuring-proofs.html

It is possible to state one auxiliary lemma that is proved by induction,
and that is such that the theorem is a simple corollary of this lemma.
You have done it for _v3, you can do it too for _v2.

-----

Lemma eureka_binary_tree_flatten_acc_append :

this lemma is just a wrapper around about_binary_tree_flatten_acc,
it is not really needed

----------

## ASSIGNMENT_ONE_MR_ALAN_VIBILAN_YOUNG.pdf

-----

S2.4

"In particular, Plus is not commutative if the error message from the first
evaluate is different from the latter evaluate."
What is meant is indeed crucial, but how it is stated is very confusing.
Choose a uniform way to describe how evaluation is carried out
and use it uniformly throughout, as in Intro to CS.

Regarding the logic of the narrative:

"In particular, Plus is not commutative if the error message from the first
evaluate is different from the latter evaluate. We can capture this property in the
following Proposition:"

Actually, you don't capture this property since there is nothing in this property about any error messages,
and there is no explanation mentioning error messages, nor in the subsequent conditional proposition.
(That is why it is a learning experience to (re)state this property as an equivalence, as suggested in my comments about your .v file.)

S2.5

The conclusion is more about the messengers than about the message.

-----

S3

3.1

Ditto: mention observational equivalence, and provide some perspective.
Maybe it wasn't, like, obvious, that Plus is not commutative,
but it is even less obvious that Times distribute over Plus in one direction
but not in the other.  All of that warrants elaboration and reflection

3.2

Yes, the associativity properties and proofs are remarkably similar for Plus and Times,
so the narrative should either be similarly similar, or use the magic words "mutatis mutandis",
not be gratuitously different.

3.3

The point just above applies even more here,
since the commutativity properties (or lack of) and proofs are remarkably similar for Plus and Times.
How about also using the magic words here too?

3.4

"as the order of evaluation affects which error message is propagated."
is the heart of the matter and it should be spelled out as outlined in my comments above.

This section needs to be reworked with an equivalence instead of only with an implication.

3.5

Item 2 at the bottom of page 14 is crucial.
A similar point should be made everywhere else.
For example, for associativity, the three sub-expressions are evaluated in the same order in the LHS and in the RHS,
so both Plus and Times should be associative, which you have proved.

The top of page 15 could be editorialized some more:
what you write also applies for programming languages with expressions whose evaluation can provoke computational effects
(errors, non-termination, side effects).

Regarding the very end of 3.6:
I notice that you have evaluate_rtl in your .v file.
Do you think that for this dual order of evaluation,
Times distributes to the right of Plus unconditionally,
but not to the left?
(Darn, that could have been a question for the first oral exam.  Oh, well, it is useful here.)

3.6

This section could be presented as a mutatis-mutandis counterpart of Section 2.2, no?

3.7

Well, here, an expression occurs on the LHS but not on the RHS,
so surely the equivalence doesn't hold if evaluating this expression yields an error.
Saying that upfront would yield a shorter section,
instead of as a repetitive one.

3.8

"Commutativity: Times is conditionally commutative. It holds when at least one
operand evaluates to a number, but fails when both operands produce errors due
to the order-dependent nature of error propagation."

This part illustrates what happens when one stops investigating too early and when one writes too fast:
if both operands produce the same error, then Times commute.

------

S4

4.1

"some interesting properties"
-> [no value judgment is needed]
"some properties"

4.2

"is the same as"
-> [for accuracy]
"yields the same result as"

"This theorem is intuitive but let’s test this statement with the usefully provided Compute statement."
If you have made similar tests on your own, that would be a good thing to mention in the report.

The rest is fine.

4.3

"Appending a singleton is cons:"
-> [cringe]
"Appending a singleton list to another list is equivalent to adding the element of the singleton list in front of the second list:"

"a recursive, non-tail-recursive implementation" is a bit heavy handed.

---

"* Reversing a singleton: reverse [v] = [v]"
But that's not the base case.  The empty list is the base case.

And the next item is not an inductive step.

This explanation is not consistent with what is in the .v file.

---

Ditto for list_reverse_alt / list_reverse_acc.

(And for consistency, write list_reverse_acc, not reverse_acc; ditto for reverse and list_reverse.)

---

"binary_tree_flatten converts a binary tree to a list via in-order traversal."

Are you sure about that?
(The payloads are in the leaves, not in the nodes.)

---

"binary_tree_flatten_alt is a tail-recursive tree flattening using an accumulator."

Wow, this report has been written at full speed: binary_tree_flatten_acc is not tail-recursive.

---

the rest of the section reflects what is in the .v file,
and should be revised based on my comments on the said .v file.

---

4.8

That's not the point of the mini-project:
the point is to rebuild your familiarity with reasoning about accumulator-based functions.

------

S5

OK, but what is "Type-Checked Program Analysis"?

----------

Overall, this handin contains many good things but also many things that need improvement,
to create a baseline for the next handins and projects:

* go to the end of your thoughts;

* be consistent in your reflections;

* less is more: your narrative doesn't need to be torrential (but it needs to be thought-out).

Care to revise and resubmit?

Thanks for attending MR,

-- Olivier
