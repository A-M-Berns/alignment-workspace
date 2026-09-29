# Report — the LI/BRIA synthesis specification round

Two passes: the first delivered the section and the specification; the second, against
the review in `prompts/2026-09-29-li-bria-synthesis-spec/REVISION.md`, corrected its
mathematics and separated the general target from the block specialization.  What
follows is the state after the second pass; §9 lists what the second pass changed.

## 1. What was added and reorganized

- A new line, `projects/decision-theory/`, registered in `state/projects.json`; this
  round under `rounds/`.
- Three specification documents: `PROBLEM_STATEMENT.md` (general requirements G1–G7,
  the conflict, the continuation-BRIA specialization, the compatibility audit, two
  levels of achievement with diagnostics D1–D4, the checklist), `TEST_SUITE.md`,
  `AUDIT.md`.
- Fixtures in `src/` and `tests/` (26 tests, exact arithmetic): the paper's first-price
  auction; repeated counterfactual mugging (fixed agents against fixed bidders, the
  per-round auction under a frequency predictor, block scoring under a lease-reading
  and a lagging predictor); the troll family; Newcomb under two predictors; rewards
  decided by logic (an interface illustration).
- Continuation BRIA is **not moved**: it is the deference line's learning layer and is
  cited by pinned path everywhere; the line's README cross-links it (`DECISIONS.md`,
  2026-09-29, agent-decided).
- Two items filed (`PRIORITIES.md` 105, 106; numbers 103–104 are taken by the open
  corrigibility-kernel phase-2 pull request, whose item 103 — a decision theory for
  logical inductors without the belief-market/choice-learner split — is the closest
  antecedent and is cited); four choices queued for the maintainer.
- The wiki is untouched.

## 2. The recommended core specification

**General acceptance requirements** (`PROBLEM_STATEMENT.md` §2), for any computable
agent with a published market and a decision component learning from realized feedback:
G1 existence with the comparison classes named; G2(c) the LI criterion on the active
trajectory relative to the observation stream (G2(b) the declared fallback); G3 the
BRIA criterion over a named class with *witness estimates* that need not be public,
test sets responding to outpromising; G4 one proved interaction result — (a) a
market-informed decision guarantee unreachable by a blind decision component of runtime
below the deductive process, or (b) belief–decision compatibility in its strong form;
G5 coverage as accountability, with menu safety named; G6 the commitment source
declared (external contract, self-entered, or self-stability); G7 market-relative
hypotheses and LI on settled scores.  **Level 1** = G1–G5 proved with G4 in one form.
**Level 2** = an advance on a recognized obstacle under a matched environment (D1–D4).

**The continuation-BRIA specialization** (§4): system-scheduled blocks, a published
claim, an external execution contract, the weighted criterion with existence iff
non-dominance.  One way to instantiate G3 and G6; marked as such; a candidate may
reject any of its choices.

## 3. Corrected mathematical findings

- **P2 retracted as a BRIA witness.**  The cross-subsidy agent satisfies global
  no-overestimation only; the hypothesis `(noop, 1)` on heads, `(pay, 0)` on tails
  outpromises it on every heads round with least record `0` (**FIX**
  `test_heads_tracker_breaks_coverage`).  Retained content: no overestimation alone is a
  whole-sequence average and permits cross-subsidy.
- **P1′ (DERIVED from the paper's definitions).**  At unit granularity, whenever the
  heads reward is an e.c. function of the history, every BRIA covering the e.c. class
  pays on a density-zero set of tails rounds — coverage of the heads tracker and of the
  exact refuser, then global no-overestimation.  No compatibility requirement is used.
  The first pass's "exactly between compatibility and commitment" is retracted; the
  conflict is between action-level coverage of the full class and a commitment paying
  outside the scored unit.  Where the subsidizing reward is not e.c.-trackable, the
  exclusion by a fixed bidder fails and the general case is open.
- **Fixed test schedules are never BRIAs** (DERIVED; **FIX** `FixedSchedules`,
  `test_two_boxing_agent_with_a_fixed_schedule_is_not_a_bria`): the off-schedule
  attacker is never matched and outpromises forever with record `0`.  Every
  "criterion-level" fixture in this round checks fixed bidders on a prefix and says so.
- **R4 is not derivable** from G2(c) and G3 (§5): the subsequence gap (global
  no-overestimation says nothing on a weighting), the cumulative-loss gap (repaired by
  `ε`-shifted bidders, the device of the paper's Thm 4), the computational-access gap
  (repaired only by publicity of the selection and the stream-relative inductor), the
  semantic gap (a forecast for an unselected option settles against nothing —
  Garrabrant's first obstacle relocated; not repaired), the timing gap (repaired by the
  stated order).  **Established**: W1, the whole-sequence one-sided statement that
  claims do not on average exceed post-selection forecasts.  R4 strong is a proposed
  requirement; a countermodel to its derivability passes nothing.
- **T10 is an interface illustration**, not a separation: three fixed blind predictors;
  the full e.c. class can approach the diagonal's accuracy.  The theorem needed is a
  runtime separation between the decision component and the deductive process, with
  the deductive process deciding the sentence *before* the decision.
- **T8(a) is not Agent Simulates Predictor**: a predictor reading a supplied commitment
  channel is a different environment.  Under bounded simulation (T8(b)) the original
  obstruction is preserved at criterion level: the synthesis two-boxes because its
  decision is `O(g q)`-computable (Thm 2), the same structural reason the proof-based
  agent loses.
- **The tentative troll** (T3(d)) stands: the paper's auction is a BRIA on every reward
  sequence (Thm 1) and is stuck at `1/2`; the confident agent is a BRIA at `1`; a
  full-confidence bidding rule crosses.  Criterion silent; applies only to
  specializations that publish estimates.

## 4. The substantive-advance diagnostics

D1 untested optimism (Garrabrant's obstacle 1 with a logic-determined option and a low
forecast on unselected decisions); D2 the tentative troll as a criterion refinement with
its cost quantified; D3 Agent Simulates Predictor under bounded simulation, no channel;
D4 per-round counterfactual mugging under the original access, paying with density 1
while BRIA recovery holds on the cross-round-free subclass.  Each with its success
condition and why existing guarantees do not deliver it (`PROBLEM_STATEMENT.md` §6).

## 5. Requirements weakened, rejected, or unresolved

- **Weakened.**  BRIA recovery no longer requires published claims (witness estimates);
  compatibility demoted from core-derived to one of two interaction forms, its
  established content W1 only; T10 demoted from criterion-level to a theorem target.
- **Rejected.**  G2(a); regret against all legitimate policies; the derivability of R4
  strong; the reduction of ASP to publicity; "exactly compatibility versus commitment".
- **Unresolved, with the missing object named.**  Weighted no-overestimation (needed
  for gap 1); the sound market-reading bidder for the selected option (gap 4, D1); the
  runtime-separation theorem for G4(a); the self-entered contract (duration
  allocation); hindsight scoring (a rollout evaluator); the observation-relative
  inductor (item 91); the exact class `H`.

## 6. Decisions requiring research judgment before a construction round

1. The scored unit and who sets it; whether a self-entered contract is wanted.
2. Publicity of the selection and of any estimate (T3(d)'s cost; gap 3's need).
3. The commitment source a candidate is held to (G6).
4. Whether a private random source is a menu option.
5. Whether one-shot verdicts are wanted at all.

Each is in `DECISIONS.md`, *Awaiting the author*, with what it turns on (the first four
were queued by the first pass; the third is folded into the first pass's schedule
entry and the publicity entry by the second).

## 7. Deviations from the dispatch

- The section is a top-level line; continuation BRIA is cross-linked, not moved.
- The second pass edited the first pass's unlanded ledger entries and priority items in
  place (they had not reached `main`), rather than appending superseding entries; the
  history is the pull request's commits.
- One remembered attribution (asymptotic decision theory) did not check out;
  `AUDIT.md` says so.
- A maintainer ruling in the same session retired the name lint; separate commit,
  recorded in `DECISIONS.md`.

## 8. What is not shown

- Every quantified statement (P1′, the fixed-schedule lemma, W1) is a paper-level
  derivation with named hypotheses; the fixtures check fixed bidders and fixed agents
  on prefixes and are `test-supported` illustrations.  Passing fixtures prove nothing
  asymptotic.
- P1′'s hypothesis — the heads reward e.c.-trackable — is what the argument uses and
  is not removable by the fixed bidders exhibited; the general case is open.
- W1 assumes G2(c) relative to the stream (item 91), a published post-selection
  forecast, and settlement within a computable deferral; it is not a theorem of record.
- T10's two halves are stated, not proved; the diagonal construction is a sketch.
- Nothing about rates; nothing in register (iii); nothing registered.

## 9. What the second pass changed

Retracted P2 as a BRIA; added the heads-tracker regression and the fixed-schedule
attacker (`test_cm`, `test_newcomb`); replaced P1 by P1′ with the direct argument;
rewrote the requirements as G1–G7 with witness estimates and the three commitment
sources; separated the specialization; audited R4 into the five gaps, W1, and three
separated statements; rewrote T4(ii), T6, T8, T10, T11 with access models against
primary sources and the channel/oracle discipline; added D1–D4 and the two levels;
corrected the checklist's "theorem or countermodel"; updated the verdict, the ledgers,
the items and the pull request.

## 10. Outstanding maintainer actions

1. Rule on the *Awaiting the author* entries of 2026-09-29, or leave them queued until
   a construction round needs them.
2. Merge, or hold, the pull request; the merge is reserved as a note on it.
3. At the next naming audit, settle the provisional names listed in
   `PROBLEM_STATEMENT.md`.
