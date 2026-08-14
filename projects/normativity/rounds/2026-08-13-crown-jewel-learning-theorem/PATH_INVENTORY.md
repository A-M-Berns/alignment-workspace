# Path inventory

What remains before this is the flagship normative-learning theorem.

Categories, sharpened after the refinement pass. The distinction that matters is
between something the **abstract theorem** cannot be stated without, and something
a **substantive instantiation** needs. The first pass conflated them and called
three things blocking; on the corrected reading only one is.

```
BLOCKING THE ABSTRACT THEOREM        cannot state or prove it
BLOCKING A SUBSTANTIVE INSTANTIATION theorem stands; application is empty without it
PAPER-CRITICAL                       needed to write it up honestly
FORMALIZATION                        kernel-checking
OPTIONAL STRENGTHENING               strictly stronger, not required
```

## Theorem-critical

| item | status |
|---|---|
| bounded prospective loss interface | DONE for the fixture; **abstract parameterization OPEN** — the loss is one concrete defect count |
| exposure / coverage condition | **BLOCKING A SUBSTANTIVE INSTANTIATION** — a legitimate theorem hypothesis, stated non-circularly against the learning scale. The theorem is provable with it; an application is empty without it |
| repair-language adequacy | **BLOCKING A SUBSTANTIVE INSTANTIATION** — likewise a legitimate hypothesis (`for every failure class in the target family, some `g` repairs it`). Not a hole in the theorem |
| compiler **interface discipline** (protocol-legal, causal, loss-blind, non-laundering) | **DONE** — stated, and checkable of any implementation |
| compiler **substantive soundness** (reason-connected, scope-correct, defeater-respecting) | **BLOCKING A SUBSTANTIVE INSTANTIATION** — reclassified. It is a property of a particular `Licensed`, not a gap in the abstract theorem |
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
| a regenerating fixture that sustains coverage | **DONE** — `src/regenerating.py` |
| feedback-driven mass shedding | **WITNESSED** — mass `1/2 -> <10^-4`, control flat; a witness, not a convergence theorem |
| alternative non-fixed-point learner | **NOT REQUIRED** on current evidence — the fixed point does not block the dynamics |
| a convergence proof for `p_t(b) -> 0` | OPTIONAL STRENGTHENING — the witness is four horizons on one process |

## Formalization

| item | status |
|---|---|
| Lean port of the surgical lower bound | **DONE** — `SurgicalRepairBound.margin_mul_mass_le_regret`, `mass_le_regret_div_margin` |
| Lean port of the conditional-rate corollary | **DONE** — `rate_le_bound_div_margin_mul_exposure` |
| Lean inhabitation and necessity witnesses | **DONE** — `mass_bound_is_nonvacuous`, `margin_positivity_is_necessary` |
| Lean port of the Blum–Mansour bound itself | NOT INTENDED — it enters as a hypothesis, which is where an external result belongs |

## Optional strengthening

| item | status |
|---|---|
| replay / policy-regret domination | REFUTED under current assumptions; not needed |
| ontology migration and selector reference | OPEN |
| multi-scorekeeper aggregation | OPEN |
| coordinated drift | OPEN — a substrate limit, not a learning-theorem limit |
| corrigibility supplying coverage | OPEN — shape match established, exercise rate missing |

## What actually blocks what

**Nothing blocks the abstract theorem.** After the interface refactor, every
remaining item is either a property of a substantive instantiation or an optional
strengthening. `H4` and `H6` are typed sockets with stated discipline, not gaps.

**Three block a substantive instantiation**, and all three are properties of the
three interfaces rather than of the regret machinery:

- `Due` — a relational-answerability derivation, and with it coverage;
- `Licensed` — substantive soundness: reason-connection, scope, defeater-respect;
- the repair family's expressivity against a target family of failure classes.

**None blocks the dynamics claim any more.** The regenerating fixture settled it
as a witness.

## Sequencing

All three remaining items are upstream, in the normative interfaces rather than in
the learning theory. That is the handoff: the next round should work on `Due`,
`Licensed` and performance, and should not need to reopen the regret machinery.
