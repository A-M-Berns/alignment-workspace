# Report — final pass

**Prompt-author model:** GPT-5.6 Sol (OpenAI)
**Executor model:** Claude Opus 5 (Anthropic)
**Date:** 2026-08-13

## Verdicts

**A. Crown-jewel theorem — `NORMATIVE-RESPONSE-LEARNING-THEOREM-SETTLED`.**

**B. Substantive normative instantiation:**

| interface | status |
|---|---|
| `Due` | **no satisfactory instantiation.** The merged scorekeeping model supplies exposure as a coordinate; deriving due-ness from standing, challenge and inquiry is the next programme |
| `Licensed` | **interface discipline yes, substantive soundness no.** Protocol-legality, causality, loss-blindness and non-laundering are delivered and checkable; reason-connection, scope-correctness and defeater-respect are not |
| performance / loss | **yes, for the fixtures.** Bounded, prospective, self-laundering-resistant, exposure-gated. An abstract parameterization over arbitrary bounded generators remains open |
| coverage | **remains a hypothesis**, stated non-circularly against the learning scale |

**C. Dynamics — `BM-FEEDBACK-DYNAMICS-WITNESSED`.**

**D. Merge — `MERGE PR #31`.** No defect was found in levels 0–2. Subsequent work
moves to a new round on the three interfaces.

## What the final pass did

**Froze the abstraction boundary.** `INTERFACES.md` states the three interfaces
the theorem actually consumes — `Due`, `Licensed`, performance — and makes
`CertifiedSurgicalRepair` explicitly what the compiler *produces* rather than the
primitive normative object. `src/interfaces.py` carries the typed version; the
compiler consults `Due` and `Licensed` and never a loss, which is asserted against
the code body rather than the docstring.

**Corrected the compiler-soundness verdict.** The refinement pass called it the
one abstract blocker. That was wrong, and the correction is the pass's main
conceptual result: the theorem quantifies over a `Licensed` relation meeting
stated **interface discipline**, which is evaluable and non-vacuous;
**substantive soundness** is a property of a particular implementation and belongs
to an instantiation theorem. Treating "the certificate might be decoration" as a
defect in the theorem confused a candidate instantiation with the conditional.

**Ran the one decisive dynamics prosecution, and it came out positive.**

## The dynamics experiment

`src/regenerating.py`. One demand type regenerating each date; two responses, so
the active repair chain is **irreducible** — removing both earlier confounds at
once (one-way graphs, and reducible chains whose stationary distribution the
implementation had to disambiguate). `answer` discharges the demand, `hold` leaves
it; the margin is uniformly `1`; the loss stays bounded. The return edge is `hold`
licensed against a *standing incoherence* demand — a different reason,
independently certified.

| `T` | `p_1(hold)` | early | late | `Q_T` | `Q_T/M_T` | control |
|---|---|---|---|---|---|---|
| 16 | 1/2 | 0.469 | 0.011 | 2.74 | 0.171 | 0.500 → 0.500 |
| 64 | 1/2 | 0.394 | 0.000 | 5.23 | 0.082 | 0.500 → 0.500 |
| 256 | 1/2 | 0.281 | 0.000 | 10.17 | 0.040 | 0.500 → 0.500 |
| 1024 | 1/2 | 0.156 | 0.000 | 20.06 | 0.020 | 0.500 → 0.500 |

Every B3 clause met: substantial initial mass; the reason recurs at every date;
uniform positive margin; `Q_T` doubling as `T` quadruples; the conditional rate
falling monotonically; and the matched uninformative control **exactly flat at
`1/2`** at both ends, at every horizon. No exploration schedule, no warm start, no
graph change over time. The surgical bound holds with equality.

**Claimed at witness strength only.** There exist coherent recurrent
answerability processes on which the construction begins with substantial mass on
an inferior response and sheds it because of informative feedback. `p_t(b) -> 0`
is **not** claimed: four horizons on one process is not a convergence proof.

Consequence for the earlier open question: the alternative-learner search is
**not needed** on this evidence. The fixed point does not block the dynamics.

## Preserved corrections (§V)

All intact and covered by tests: `M_T, Q_T, N_T` random with
`E[N_T] = E[Q_T]` and `N_T - Q_T` a martingale-difference sum; determination /
observability / computability separated, with the learner committing `p_t` before
reading `ell_t`; `M = 1` and `K_eff = K + 1`; coverage against the learning scale;
local rather than replay; the licensed negative-margin witness — now joined by its
converse, an unlicensed response with lower loss.

## Lean (§VI)

`SurgicalRepairBound.lean` unchanged and rebuilt. Full `lake build` clean;
`audit_axioms` reports **327 results across 16 files, all within
`[propext, Classical.choice, Quot.sound]`**. No new Lean was added: the interface
refactor is a typing change, and encoding `Due`/`Licensed` as Lean predicates
would have been philosophy in Lean rather than a kernel-checked bridge.

## Kill criteria (§VII)

K1–K12 all prosecuted. Two are worth naming: **K1** now has witnesses in *both*
directions — a licensed response with negative margin, and an unlicensed response
with lower loss — so licence and performance cannot be identified either way. And
**K9**'s control is exact rather than approximate: the uninformative run sits at
`1/2` to the last digit.

## Deviations from the dispatch

1. **No new Lean**, per §VI's own allowance that the abstraction is optional.
2. **`Due` and `Licensed` are not derived from scorekeeping**, per §A1's explicit
   instruction to leave that to the next programme.
3. The dispatch's §II sketch of a residual-burden loss factorization is recorded
   in `INTERFACES.md` as a natural way to build such a loss and **not** made
   mandatory, since the proof does not use it.

## What this pass does not establish

- `p_t(b) -> 0` as a theorem.
- Any instantiation of `Due` or of substantive `Licensed` soundness.
- Coverage, which remains a hypothesis with an exact quantifier interface and a
  plausible external supplier in the corrigibility arc — where "can raise" is
  still not "does raise often enough".
- Repair-family expressivity against a target family of failure classes.
- Concentration, anytime tuning, computation cost, multi-scorekeeper aggregation,
  ontology migration.

## New names introduced

All **provisional**, new in this pass: `answerability process`, `demand`,
`certified response`, `compiled repair`, `interface discipline`, `substantive
soundness`, `regenerating fixture`, `dynamics witness`.

## Structural defects found

None.

## Outstanding maintainer actions

Nothing is reserved. No `PRIORITIES.md` item filed, nothing appended to
`DECISIONS.md`, no claim registered.

**Merge recommendation: merge PR #31.** The next round should work upstream on
`Due`, `Licensed` and performance, and should not need to reopen the regret
machinery — the socket is now clean and the remaining questions plug into it.
