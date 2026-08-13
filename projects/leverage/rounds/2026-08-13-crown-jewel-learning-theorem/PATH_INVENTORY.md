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
| compiler soundness | **BLOCKING THE ABSTRACT THEOREM** — the one that really is. Until `certified` means something stronger than "a certificate string exists", H4 quantifies over a set defined by a label, and the word `lawful` carries no weight |
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
| a regenerating fixture that sustains coverage | **OPEN — now the first dynamics requirement.** A finite content set cannot keep a reason recurring with a positive margin |
| alternative non-fixed-point learner | OPEN, and **downgraded** — with the coherence inference withdrawn there is no longer a reason to think the fixed point blocks the dynamics |

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

**One item blocks the abstract theorem: compiler soundness.** H4 quantifies over a
*certified* repair family. If `certified` means only that a string is present, the
theorem is about an arbitrary finite family of surgical maps and the word
`normative` is decoration. This is the item to do first, and it is smaller than it
sounds — `COMPILER_SOUNDNESS.md` gives the signature and separates what relational
scorekeeping already delivers from what remains an interface.

**Two block a substantive instantiation, and are legitimate hypotheses.** Coverage
and repair-language adequacy. A paper may state both and remain a paper; what it
may not do is state them silently. Coverage additionally has a plausible external
supplier — the corrigibility arc — which is why it is worth doing second.

**One blocks the dynamics claim only:** a fixture that can sustain coverage. That
does not touch levels 0–2.

## Sequencing

Compiler soundness, then coverage, then the grammar. The dynamics question needs a
regenerating fixture before it can be asked at all, and is worth separating
entirely: it does not block the theorem, only the word.
