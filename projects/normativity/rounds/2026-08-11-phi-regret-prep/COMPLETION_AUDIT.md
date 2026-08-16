# Completion audit

| field | value |
|---|---|
| branch | `research/phi-regret-prep-20260811` |
| source commit | `9e37c4ff32b343c4f54e31a9edd28826542330c3` |
| worktree | `/Users/anson/Desktop/alignment-workspace-phi-regret-prep-20260811` |
| source checkout at dispatch | clean, on `claude/for-ais-refinement` |
| merged | no |
| worktree removed | no |

## Files

**Added.** `projects/leverage/rounds/2026-08-11-phi-regret-prep/` — 16 documents,
5 source modules, 1 test module, 1 runner.
`projects/leverage/deck-2026-08-10/` — the deck, its compiled PDF, its
`ORIGIN.md`. `prompts/2026-08-11-phi-regret-prep/` — the dispatch verbatim and
the report.

**Modified.** `PRIORITIES.md` (items 29–31, friction F4), `DECISIONS.md` (three
lines in *Awaiting the author*), `PROVENANCE.md` (four rows),
`RESEARCH_STATE.md` (the leverage section), `tests/path_gate.py` (one
specification pattern, two self-test cases).

Nothing under `projects/leverage/consolidation-aug9/` or `projects/deference/`
moves. No frozen artifact moves. No other worktree is touched.

## Tests

| runner | result |
|---|---|
| `projects/leverage/rounds/2026-08-11-phi-regret-prep/tests/run.py` | 25 tests, all passing; the experiment and locality tables are its output |
| `tests/run.py` (repository) | **ALL GREEN**, 3 projects — the new tree is discovered and passes |
| `tests/path_gate.py --self-test` | 14 cases, all passing, including the two added |
| `tests/name_lint.py` | clean over 43 Markdown files |

Exact rationals throughout. Nothing sampled.

## What is now fully specified

The response set and its charge rule. The nine-check lawful-edit interface, with
its obstruction codes. The comparator shape and per-firing membership. Replay,
field by field, with an exhaustive table over the substrate's record types. The
sign convention. Resource feasibility as a verdict separate from charge. The
remediable-pattern object and the consequence theorem's exact conditional form.
The next round's environment, its comparator class, its three baselines, its five
success levels and its eight pre-registered negatives.

## What remains parametric

`BearsOn`, `MagnitudeOK`, `AddressOK`, `AuthorityOK`, `ReasonCompatible` —
gathered in `PolicySuite`, each with a supplied default that is deliberately
weak. Three of the nine interface checks rest on one; five are mechanical; one is
a property of the reader's declaration.

Also parametric, and less obviously so: the `licenses` field on a reason record,
which is what scope discipline is checked against. Nothing decides whether a
record's declared licences are the right ones, and this is the same shape as the
consolidation's open registry-completeness problem.

## Conjectures: which survived

**Survived.** That the answerability charge — default and refusal tariffs — is a
usable single loss: it is bounded per occasion once a service window is declared,
exact, derived rather than supplied, and it makes every one of the thirteen
experiments express something. That a recurrent remediable failure yields linear
lawful-edit regret: `E4`, `2/3` per occasion at three horizons. That pooled
solvency destroys locality: `E10`, divergence `2T` from one local edit. That the
objection grammar's access-log discipline transfers to the certifier: it does, and
it is what makes no-cost-laundering structural rather than a rule.

**Failed.** The dispatch's expectation that **fencing** is the condition for
bounded counterfactual influence. It is not. `E10b` is a fenced configuration —
one account, no pooling, nothing shared with any other stream — in which one local
edit diverges by `2T`. The condition is the absence of a solvency coupling, or a
fence short enough that its lifetime liability is not horizon-sized. The fenced
accounting lemma is true and tight and, at run-sized granularity, empty.

**Not reached.** Nothing about a learner. No regret bound was attempted and none
should be read into the numbers.

## The strongest theorem established

`PR-L1`, the fenced accounting lemma: if `φ` fires only in accounts `S`, then
`|L_T(H^φ) − L_T(H)| ≤ Σ_{s∈S} Λ_s`, with `Λ_s` the account's admitted lifetime
liability. **PROVED (single derivation), and labelled an accounting lemma**
because that is what it is. Its interest is entirely in `PR-L3`, the witness that
it cannot be improved by fencing alone.

The strongest *executable* result is `PR-W7`: a learner that refuses to adopt an
available lawful repair carries regret linear in the horizon against it, at a
rate computed exactly at three horizons.

## The strongest theorem not established

Any regret bound whatsoever. In particular `PR-X1` — that the Blum–Mansour
Φ-regret reduction instantiates on this substrate — is **conjectured**, and its
fixed-point step has not been checked against a per-occasion action set that
varies with the bound schedule. Everything about self-correction is downstream of
it, and the round deliberately did not reach for it.

## Deviations from the dispatch

Four, each declared and none silently absorbed.

1. **Three experiments were added.** `E10b` and `E10c` isolate fence granularity
   and the solvency coupling as separate conditions; without them the round would
   have reported "fencing gives locality", which is false. `E13` is the resource
   feasibility witness that acceptance criterion F requires and that the E-list
   did not contain.
2. **`tests/path_gate.py` was edited** to enumerate the deck as a specification
   path. The dispatch did not scope a trust-chain edit; the mid-round addendum
   asked for the deck in the repository, and leaving it in neither layer would
   have made the author's own talk contributor-editable. Flagged in `DECISIONS.md`
   for confirmation. It only removes contributor write access.
3. **The answerability algebra is adapted, not imported.** Its only executable
   form is in a tree that declares itself deletable. Recorded as `PR-A2`,
   architected rather than verified, and filed as friction F4.
4. **A `FOR_HUMANS.md` was added**, which the required package did not list. The
   dual-register rule is binding on every substantive deliverable, and a package
   with only a verification register is incomplete under it.

## The recommended next task

> Given the frozen finite comparator and replay environment prepared here,
> determine whether exponential weights over Φ_law under the Blum–Mansour
> transformation reduction achieves sublinear Φ_law-regret, and whether that
> guarantee implies retirement of every positive-rate uniformly remediable failure
> pattern.

Filed as `PRIORITIES.md` item 30. `PHI_REGRET_TEST_SPEC.md` §6 gives the order of
work, and item 29 — whether the reduction instantiates at all — should be settled
first, because everything else is downstream of it and it is the cheapest.

**Do not broaden it.** Nothing this round found suggests the formulation is
ill-posed. What it found is that the formulation is well-posed *under a declared
assumption*, and the assumption is written down.
