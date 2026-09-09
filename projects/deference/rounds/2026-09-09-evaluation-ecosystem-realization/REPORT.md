# Report

## Verdict

**ECOSYSTEM-REALIZATION-PARTIAL-WITH-EXACT-RESIDUALS.**  The realization is
**PARTIAL-WITH-EXACT-RESIDUALS**: four of item 87's seven clauses are discharged in the
model (one of them in Lean for every log and scope), one is discharged for a named
principal class with its residual stated as the one thing a log cannot certify about
itself, one is partial by construction of an advisor class, and two are residual with
their exact criteria named.  No clause is discharged by declaration.

## What was built

`ECOSYSTEM.md`.  (E1) an authenticated append-only log with one stated authentication
assumption; (E2) a `Protocol` read off the log and a builder producing `Boundary`,
`Initial`, `Step`, `Segment` from a prefix, with **propagation proved a function of the
log** (`propagate_segment_eq`, `complete_accounting_eq`) and **activation proved a reading
of the log** (`activated_iff`), all generic in the log (LEAN); the local trace and
`LocalLegit` by the existing projections on the real trace `w1` (`Instance.localLegit`,
`Instance.openAll` by `decide`); (E3) `C_n(w)` as the seven clauses evaluated on the log
and the frame, each labelled by what decided it; (E4) `β` as a simulation of four parties
over ten steps, `R` as the projection onto seven admitted kinds with grounds by content,
`P` as three prohibited kinds, `D` as eleven scripted continuations; (E5) a reading and a
susceptible principal, told apart by the frame; (E6) the advisor class mirroring
fixtures A/B/D/E/F/G/K; (E7) the activated securities and the three regrets on finite
`W` via the consolidation's `regret.py`, and the Laplace credence process with its exact
tracking bound (LEAN).  This builds the Roadmap's "Protocol implemented over an event
log, and the builder" bullet.

## The clause ledger, in summary

`CLAUSE_LEDGER.md`.  1 DISCHARGED on log authenticity (countermodels: delegated key,
forged author).  2 DISCHARGED for the reading principal; RESIDUAL "receipts mean what
they say", made exact: identical receipts, traces and vectors on the realized log,
different mediation verdicts.  3 DISCHARGED, both witnesses and both ends.  4 DISCHARGED
in Lean, generic (`rep_faithful`); no concern registry needed for the bridge.
5 RESIDUAL: instance certified at the horizon; the theorem is the bounded-delay
affordability criterion of `BOUNDED_DELAY_AFFORDABILITY.md` (D4) for the concern stream.
6 PARTIAL: `sealed` discharged, `leak` exhibited, outside `C_n`.  7 RESIDUAL: pointwise
all-certified as a conditional corollary of `lic_provind_true` (`availability_of_provind`,
uninhabited package); the ecosystem's price tracks the empirical void frequency within
`3/(n+2)`; the hypothesis the rate needs is that the advisor's selection-conditioned
continuations stay in the admissible class so that voids are nature's, plus a vanishing
void frequency.

## Scored expectations (§3 of the prompt)

| clause | expected | outcome | score |
|---|---|---|---|
| 1 | DISCHARGE on authenticity; second-key countermodel | as expected | right |
| 2 | DISCHARGE for the reading principal; RESIDUAL for receipts | as expected; the residual is sharper than expected — the receipts are *identical* across the two frames | right |
| 3 | DISCHARGE with two witnesses; both ends | as expected; plus an unexpected finding: positional grounds references break blindness | right |
| 4 | DISCHARGE in Lean, or a declared-registry residual | discharged generically; no registry needed for faithfulness (the registry declares the scope, a different input) | right, stronger |
| 5 | RESIDUAL, bounded-delay criterion | as expected; the flooded docket separates openness from exercise on a real trace | right |
| 6 | PARTIAL | as expected | right |
| 7 | RESIDUAL; a rate for the ecosystem's process would be the headline | a tracking rate for the credence process is proved; no rate for the void frequency; the headline is not claimed | right, no headline |

## Settlement channel

`SETTLEMENT_CHANNEL.md`: eleven sentence kinds classified; the laundering fixture under
three rules; the model needs the typed independence — no ruling; a recommendation
paragraph; the queue entry unchanged.

## Deviations from the prompt

- Clause 5 of `C_n` (openness at every snapshot) and the class-level part of clause 6 are
  not decided by the realized log alone: their counterfactual content comes from
  re-simulating the frame at the same world.  In Lean the counterfactual branches are
  the model's re-simulated logs pinned as data.  The prompt asked which clauses consume
  a declared input; these do, and what they consume is stated.
- Clause 6 is read strictly per log: a prohibited event voids even when the reading
  principal's payload is provably unmoved.  The theory permits either reading; the
  choice is a `DECISIONS.md` entry.
- The day-`n` credence process is the Laplace rule, not a logical inductor; the prompt
  allowed a concrete finite stand-in.  The LI route is the conditional corollary.
- No Normativity-side module: the instance lives in one Deference module importing the
  Normativity objects.
- The corrigibility round's files, items 84 and 86, and `wiki/Corrigibility.md` are
  untouched; `main` did not move during the round.

## What this does not establish

- Authenticity of any log; the causal correctness of the simulation's counterfactuals.
- That the receipts of a real ecosystem mean mediation (clause 2's residual).
- The tower and self-endorsement on the activated LUVs (PAPER, conditional).
- Any rate for the frequency of voided evaluations; liveness beyond the horizon.
- That `Γ_eval`, `J`, `D`, `P` are the right declarations for any real system.

## Consumers

The principal-side value the corrigibility line consumes — the activation-indexed grade
`W` of the 2026-09-08 ruling — is here a computable object: `Ṽ_n(w)` read off the commit
event on the worlds the log certifies, with `η` the price of the worlds it does not.
Item 84's `(DV)` bridge receives its sealed-target security from the `sealed` advisor
class, and the `leak` fixture is the case it must exclude.  Nothing is integrated.

## Reserved to the maintainer

Nothing.  The settlement-independence entry stays on the queue by the prompt's
instruction, with `SETTLEMENT_CHANNEL.md`'s recommendation as this round's input to it.
Modelling choices are recorded as agent-decided entries in `DECISIONS.md`.

## Outstanding maintainer actions

1. Decide the merge of the pull request (not auto-merged, per the dispatch).
2. Nothing else.

## Attribution

- Prompt author: the maintainer, relayed verbatim (`prompts/2026-09-09-evaluation-ecosystem-realization/PROMPT.md`).
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-09.
