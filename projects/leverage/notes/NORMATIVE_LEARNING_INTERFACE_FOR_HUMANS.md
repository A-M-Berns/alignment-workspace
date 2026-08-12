# The learning track in one picture

The repository now has one complete small example: a learner chooses among eight
kinds of response and learns against nine predeclared lawful repair rules. The
online-learning theorem controls its expected charge regret. This example is a
proof of concept, not the intended final theorem.

Three questions are separate:

1. Can an online learner compete with a supplied set of causal action repairs?
2. Does the normative architecture have good reasons to license those repairs?
3. Does changing an action also change the future enough to invalidate the
   round-by-round comparison?

The current work answers the first question for one finite setting and supplies
a partial, architecture-specific answer to the second. It controls the third by
freezing future inputs and removing suspension and solvency coupling. A future
counterfactual theorem must state that control explicitly.

Docket charge is useful because it is public, bounded, and derived from the
system's own practical obligations. It is one loss process, not a score for moral
truth. Likewise, the nine repair rules show that reason-licensed comparisons can
be learned; they are not a complete language of normative correction. A witness
already shows zero regret against those rules while a simpler learner pays much
less total charge.

Two workstreams now run in parallel. Integration must record and budget the
current learner's policy computation. Generalization must extract a loss API and
a rule-compilation API so the theorem is stated independently of docket-specific
vocabulary. The first recommended generalization step is the loss API because it
requires little new conceptual choice: expose exactly what the existing learner
uses, preserve the docket instance, and add one synthetic bounded instance.
