# Path inventory

What remains before this is the flagship normative-learning theorem.
`BLOCKING` is reserved for what is needed to **state or justify** the theorem.

## Theorem-critical

| item | status |
|---|---|
| bounded prospective loss interface | DONE for the fixture; **abstract parameterization OPEN** — the loss is one concrete defect count |
| exposure / coverage condition | **BLOCKING** — stated as H6, not proved; `COVERAGE_INTERFACE.md` |
| repair-language adequacy | **BLOCKING** — legitimate as a hypothesis, but a paper needs a generated grammar |
| compiler soundness | **BLOCKING** — nothing connects a certificate's presence to normative appropriateness |
| source-action surgical compiler | DONE |
| margin derivation | PARTIAL — derived for one schema, hypothesis for the class |
| comparator complexity model | OPEN — `log K` is where it enters; unchosen |
| multiple simultaneous reasons | DONE — P2 |
| conflicting repairs | DONE — P3; a compiler question, not a theorem question |
| recurrence adequacy of the class | OPEN, newly identified — `REPAIR_LANGUAGE.md` |

## Paper-critical

| item | status |
|---|---|
| expected sampled count `E[N_T] = Q_T` | DONE, one line |
| anytime construction | ROUTINE EXTENSION — standard doubling |
| pathwise concentration | OPEN — level 5 |
| the conditional-rate statement as the headline | DONE — this round |
| replay stated as strictly stronger and not needed | DONE |

## Implementation

| item | status |
|---|---|
| existing BM learner on an endogenous process | DONE |
| regret measured against its own bound | OPEN |
| learner computation cost | OPEN — unpriced, carried from the interface note |
| learner-state answerability | OPEN — carried |
| alternative non-fixed-point learner | **REQUIRES NEW IDEA** — the dynamics question |

## Formalization

| item | status |
|---|---|
| Lean port of the surgical lower bound | OPEN — short; the existing `recurrentFailure_lowerBound` takes the bound as a hypothesis rather than deriving it |
| Lean port of the conditional-rate corollary | OPEN — one division on top of the above |

## Optional strengthening

| item | status |
|---|---|
| replay / policy-regret domination | REFUTED under current assumptions; not needed |
| ontology migration and selector reference | OPEN |
| multi-scorekeeper aggregation | OPEN |
| coordinated drift | OPEN — a substrate limit, not a learning-theorem limit |
| corrigibility supplying coverage | OPEN — shape match established, exercise rate missing |

## The three blocking items, and why

**Coverage.** Without it the theorem is conditional on being asked and is
satisfiable by never being asked. This is the one to do first: it is where the
merged corrigibility work plausibly composes, and the composition needs one extra
assumption (an exercise rate) rather than a new formalism.

**Repair-language adequacy.** Regret against a hand-built class is a theorem about
that class. A paper needs a grammar, a complexity model, a stated adequacy
hypothesis, and the recurrence check.

**Compiler soundness.** Until a certificate's presence implies something, "lawful"
names a discipline this round imposed rather than a proved property. This is what
makes the difference between normative learning and loss reduction with good
manners.

## Sequencing

Coverage, then compiler soundness, then the grammar — in that order, because the
grammar's shape depends on what the first two turn out to demand. The Lean port is
short and independent. The dynamics question is worth separating out entirely: it
does not block the theorem, only the word.
