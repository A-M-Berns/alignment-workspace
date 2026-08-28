# Legitimate Improvement

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

NO-FREE-EVASION-SURVIVES-BUT-EVIDENCE-INTERFACE-OPEN — Theorem C survives the prosecution and is now stated over the right objects, and what blocks a clean merge is not the theorem but the meaning of *demonstrated*. The pass's main repair is separating three things the round had run together: evidence, which says r is an improvement relative to some baseline; uptake regret, which asks whether the played policy leaves that advantage unused while r is live; and answerability, which governs what remains after r is withdrawn. Evidence and uptake regret are the same functional on different distributions and are independent in both directions — a process that has adopted the repair has exactly zero uptake regret and may still have a large demonstrated improvement, and a process leaving advantage unused may never reach the threshold that makes a challenge eligible. So the challenge is grounded by the demonstration and never by the failure to act on it, and the challenge module names no regret quantity at all. Two implementation bugs are fixed: the Khot-Ponnuswami fixed point was computed by power iteration justified by stochasticity alone, which is false for periodic kernels and returned a vector off stationarity by two thirds on an exhibited period-2 chain; and AdaNormalHedge's auxiliary B was computed from one expert's own accumulated regret rather than the paper's global prior-weighted quantity. One headline claim is corrected: a surgical repair empties the diagnosed action only when no active comparator maps another action into it, since stationarity carries an inflow term the round had dropped, and the corrected version is what made the first genuine exercise of Theorem B constructible. The open seam is the baseline: one trace run against two admissible baselines gives contested against escaped, so the baseline is doing substantive normative work that the round supplies rather than derives.

## The question

Legitimate Evolution gives integrity without improvement. The obvious
composition fails for an obvious reason: let a repair prove itself, legitimately
retire it, and the old conduct continues forever with repair regret going to zero
because there is nothing left to compare against.

Something weaker and true survives. Once an improvement has been **demonstrated**
on the process's own record, withdrawing the comparison does not end the matter:
every later diagnosed occasion is one the process is either still answerable for
or has explicitly answered.

## Three mechanisms, kept apart

The prosecution pass's main repair.

```text
EVIDENCE       why r is an improvement, relative to a supplied baseline
UPTAKE REGRET  while r is live, is the played policy leaving that unused
ANSWERABILITY  after r is withdrawn, what remains normatively live
```

Evidence and uptake regret are the same functional `<d,l> - <d M_r,l>` on
different distributions — the played `p_t` for one, a baseline `b_t` for the
other — and only the first is bounded by any theorem. A process that has
**adopted** a repair has zero uptake regret and may still have a large
demonstrated improvement. The challenge is grounded by the demonstration, never
by the failure to act on it.

## What the prosecution found

**Power iteration was the wrong solver.** A finite stochastic matrix may be
periodic; the shipped code returned a vector two thirds off stationarity on an
exhibited period-2 kernel. Replaced by an exact solve, with a recurrent-class
route when the system is singular.

**The AdaNormalHedge bound was not the theorem.** Its auxiliary `B` is global and
prior-weighted; the round computed it from one expert's own `C`. The old
expression understated the bound, so no test was wrong — but the code claimed to
be the theorem and was not.

**The surgical claim dropped a term.** Stationarity is `pi(d) = sum_a pi(a)
M(a,d)`. With inflow the conclusion is false, and the corrected version is what
made the first genuine exercise of Theorem B constructible.

**The baseline is doing normative work.** One trace, two admissible baselines,
opposite verdicts. That is the open seam and the reason this is not
`PR60-CLEAN-MERGEABLE`.

## Contents

- `LEGITIMATE_IMPROVEMENT.md` — problem, result, the three mechanisms, Theorems
  A/B/C, boundaries, literature, freeze recommendation.
- `src/regret.py` — Theorem A and the stationary solve.
- `src/evidence.py` — the baseline and `ImprovementEvidence` interfaces.
- `src/surface.py` — the comparison surface and the four-cell accounting.
- `src/challenge.py` — the canonical constitution over frozen `Due`/`Resolve`.
- `src/cases.py` — CM1-CM18. `src/consumers.py` — two positive, one negative.
- `tests/` — 68 cases. `python3 tests/run.py`.

## What this does not establish

No Lean and no registered claim.

That recurrent defects disappear: CM8 contests forever and satisfies everything.

Anything about delay, evaluator manipulation, or policy effects. Those are named
boundaries with executed fixtures, not gaps left quiet.

Which baseline is the right one. Two admissible choices give opposite verdicts on
one trace, and the round supplies the baseline rather than deriving it.
