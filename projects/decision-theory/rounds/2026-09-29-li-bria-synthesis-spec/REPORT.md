# Report — the LI/BRIA synthesis specification round

## 1. What was added and reorganized

- A new line, `projects/decision-theory/`, with its entry README, registered in
  `state/projects.json`; this round under `rounds/`.
- Three specification documents: `PROBLEM_STATEMENT.md`, `TEST_SUITE.md`, `AUDIT.md`.
- Fixtures in `src/` and `tests/` (23 tests, exact arithmetic): the paper's first-price
  auction; repeated counterfactual mugging under three scorings and three predictors;
  the troll family; Newcomb under a lease-reading and a frequency predictor, per round
  and per block; rewards decided by logic with a blind and a market-reading class.
- Continuation BRIA is **not moved**.  It is the deference line's learning layer,
  consumes that line's gate, and is cited by pinned path from the wiki, the round
  index, the ledger and the priority items; moving it would rewrite those pointers for
  no gain in organization.  The line's README cross-links it and says why
  (`DECISIONS.md`, 2026-09-29, agent-decided).
- Two items filed (`PRIORITIES.md` 105, 106); four choices queued for the maintainer.
  The numbers 103 and 104 are taken by the open corrigibility-kernel phase-2 pull
  request, whose item 103 asks for a decision theory for logical inductors without
  the split between a belief market and a choice learner; that item is the closest
  antecedent of this specification and is cited in `PROBLEM_STATEMENT.md` §1 and
  `AUDIT.md` §3.
- The wiki is untouched; the dispatch did not grant it.

## 2. The recommended core specification

The **minimum credible synthesis** of `PROBLEM_STATEMENT.md` §4: a computable agent of
the type "publish a market, select `(continuation, claim)` at a system-scheduled block
contract" for which R1 (existence, comparison classes named), R2(c) (the LI criterion
relative to the deductive process and the observation stream on every environment), R3
(the duration-weighted BRIA criterion over the market-reading class `H^P` at a
non-dominant schedule), R4 (belief–decision compatibility, as a theorem from R2(c) and
R3 or with its countermodel), R5 (coverage as the accountability clause, menu safety
named) hold, and the criterion-level rows of the suite pass.  R4 is the interaction
requirement: it is derivable — its upper half from no overestimation and unbiasedness
from feedback, its lower half from coverage with market-reading hypotheses — and a
side-by-side LI and BRIA fails it by the cross-subsidy witness.  Its consequence is the
statement logical-inductor decision theory wanted: the claim is asymptotically the
market's expectation of the chosen continuation and at least that of every e.c.
selector, obtained through accountable claims and never through the conditional
expectation of an untaken action.

## 3. Requirements weakened, rejected, or unresolved

- **Weakened.**  BRIA recovery is stated at block granularity with the class relative to
  the published prices, not at the paper's unit rounds with a blind class; LI recovery
  is stated on the active trajectory relative to the stream, with the passive form as a
  declared fallback.
- **Rejected.**  R2(a), a compatible LI component (vacuous).  Regret against all
  legitimate policies (false; the irreversible-branch witness of the continuation-BRIA
  round).  Per-round belief–decision compatibility as a requirement on environments
  with cross-round payoff (Proposition P1: it forces asymptotic refusal in repeated
  counterfactual mugging where paying averages `1/2` against `1/4`).  Hindsight
  re-scoring of executed blocks (needs a rollout evaluator the realized register does
  not have).
- **Unresolved, with the missing object named.**  R7(c) cross-block commitment: the
  allocation rule for duration.  R8 hindsight: the rollout evaluator `Ĝ_k(π; H)`.  S2
  the counterfactual-dependence register: a value for unexecuted continuations that
  agrees with realized feedback wherever both apply.  The observation-relative inductor
  (item 91), on which R2(c) and R4 rest.  The exact reading power of `H^P`.

## 4. The most discriminating benchmarks

T6 (repeated counterfactual mugging: per round the criterion with compatibility excludes
paying, per block with a lease-reading predictor it selects paying, per block with a
lagging predictor it selects refusing); T3(d) (the tentative troll: the paper's auction
is stuck while the criterion is met; a full-confidence bidding rule crosses); T3(e) (the
belief-disagreement troll: two self-consistent pairs, the criterion does not select);
T4(ii) (a frequency predictor: two-box per round, one-box per block, and the auction
cycles at finite horizons); T8 (Agent Simulates Predictor reduces to lease publicity);
T10 (rewards decided by logic: a blind class stays below `9/10`, a market-reading class
reaches above `99/100`).

## 5. Decisions requiring research judgment before a construction round

1. Who sets the block schedule, and whether bidders may request horizons (T6, T7).
2. Lease publicity: which of the selection, the estimate, the winning index, or a bounded
   simulation of the agent predictors may read (T3(d), T4, T7, T8).
3. Whether a private random source is a menu option, and which randomness notion the
   random-reward clause uses (T5).
4. Whether one-shot verdicts are wanted from a synthesis at all, or left to S2.

Each is in `DECISIONS.md`, *Awaiting the author*, with what it turns on.

## 6. Deviations from the dispatch

- The dispatch asked for the location of the section to be "appropriate" and offered
  moving continuation BRIA; the round created a top-level line and did not move it, for
  the reasons in §1.
- The dispatch's requirement list treats "LI recovery" as recovery on a passive
  restriction; the round makes the active form the core and the passive form the
  fallback, because the interaction requirement consumes the active form.
- The literature audit relied on fetching the sources; one remembered attribution (of
  asymptotic decision theory) did not check out and `AUDIT.md` says so; the post's own
  credits are recorded instead.
- A maintainer ruling taken in the same conversation retired the name lint and moved
  the naming rule to `AGENTS.md`; it is a separate commit on this branch and is
  recorded in `DECISIONS.md` (2026-09-29).  It is not part of the dispatch.

## 7. What is not shown

- Every "criterion" verdict in `TEST_SUITE.md` is an asymptotic statement about the
  criterion; the fixtures check finite prefixes on the paper's auction and on fixed
  agents, and are `test-supported` illustrations, not proofs.  The prefix conditions
  checked are the paper's own (cumulative overestimation bounded by the allowance
  through the round; records; rejection counts).
- R4's derivation is a proof sketch with its hypotheses named (deferral of settlement,
  `P`-generable weightings, `P`-generable test and rejection sets, the
  observation-relative inductor); it is not a theorem of record and is filed as item 105.
- T10's environment assumption — a truth sequence unpredictable with vanishing error by
  any `O(g)`-computable function of the history — is asserted by a diagonalization
  sketch; the fixture instantiates three blind predictors.
- Proposition P1 is derived at the criterion level from R2(c), R3, R4; its fixture
  checks the coverage failure on a prefix for one agent, and the block resolution on
  the auction.  The claim that the paying-tails subsequence is `P`-generable is argued,
  not proved.
- Nothing about rates; nothing about the one-shot register; nothing registered.

## 8. Outstanding maintainer actions

1. Rule on the four *Awaiting the author* entries of 2026-09-29 (schedule authority,
   lease publicity, randomization, the scope of register (iii)), or leave them queued
   until a construction round needs them.
2. Merge, or hold, the pull request; the merge is reserved as a note on it.
3. At the next naming audit, settle the provisional names listed in `PROBLEM_STATEMENT.md`
   (*minimum credible synthesis*, *market-relative hypothesis class*, *belief–decision
   compatibility*, *scoring granularity*, *lease publicity*, *realized-feedback
   register*).
