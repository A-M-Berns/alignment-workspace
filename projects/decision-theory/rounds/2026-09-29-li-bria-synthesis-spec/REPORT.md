# Report — the LI/BRIA synthesis specification round

Three passes: the first delivered the section and the specification; the second, against
the review in `prompts/2026-09-29-li-bria-synthesis-spec/REVISION.md`, corrected its
mathematics and separated the general target from the block specialization; the third,
against `REVISION2.md`, encoded the maintainer's endpoint, fixed the recovery domains,
made integration an obligation with three separated achievements, corrected the
remaining overclaims, and reduced the advance diagnostics; the fourth, against
`REVISION3.md`, removed A1 from the definition of success, gave the advance a
qualification standard, marked A1 provisional with its missing semantics, corrected
T10's control, and made active LI the endpoint's requirement with passive recovery a
weaker milestone.  This is the state after the fourth pass; §9 lists what each later
pass changed.

## 1. The final recommended acceptance standard

`PROBLEM_STATEMENT.md` §0, in one sentence: a candidate is a **successful outcome** if it
establishes the **supporting milestones** (M1 computable existence with named classes;
M2 LI on the **active** trajectory — passive recovery is a weaker supporting milestone,
not an alternative; M3 BRIA recovery with its four domains declared; M4 coverage as
accountability with menu safety named), meets the **integration obligation** — I1
(market information improves decision performance, T10 with explicit accounting), I2
at least as W1, and I3 (a formal result that its integrated process excludes a
precisely specified failure mode of the belief–decision coupling) — passes the recovery
and integration rows of the suite under their assumptions, and demonstrates **one
advance** on a recognized obstruction by a diagnostic meeting the qualification
standard (complete semantics, quantified success condition, justified relationship to
the obstruction, matched assumptions, what existing guarantees fail to establish).
One theorem may discharge both I3 and the advance; an information-transfer theorem
alone is not an advance.  A1 is one proposed diagnostic and is provisional.
**Updatelessness is an ideal extension** (A2), and its recovery domain is an open
specification question.  A candidate with the milestones and I1 alone has a publishable
integration theorem and is not the endpoint.  Architecture is not specified; a modular
implementation qualifies.

## 2. The most discriminating formal tests

- **A1 / T3(e)**, the belief-disagreement troll: a precise success condition (crossing
  with density 1 from every M2-consistent initial market) on a target that is not yet
  defined — the semantics of the pre-selection forecast the troll reads (conditional
  expectation, contract price, selectively evaluated forecast, or an outside report)
  is open, the two configurations are proposed failure configurations unchecked against
  M1–M4, and a favourable report changes the environment.  **Provisional.**
- **T10**, rewards decided by logic: the integration theorem I1, with its four steps
  named (pointwise pre-decision accuracy; the `ε`-shifted market-reading bidder's
  refutation resistance; adoption; the blind lower bound by a density diagonal against
  clocked machines) and its fixture marked as an illustration.
- **T6 per round**, the recovery boundary P1′ — and the same environment as A2's target
  with the opposite success condition, which is where the extension's recovery domain
  is undefined.
- **T4(ii)**, the scored unit flipping the verdict, with the conditional fixed-schedule
  obstruction.
- **T11**, W1 against the strong compatibility form.

## 3. Corrected or withdrawn claims

- **P2** (first pass): withdrawn as a BRIA witness; the heads tracker refutes it.
  Retained as the witness that global no-overestimation alone permits cross-subsidy.
- **P1′**: stated at the strength proved — hypothesis (e.c.-trackable heads reward)
  sufficient, not shown necessary; one environment family, not a universal obstruction
  on cross-round commitment.  The first pass's "exactly compatibility versus
  commitment" is withdrawn.
- **"Fixed test schedules are never BRIAs"** (second pass): withdrawn.  The valid
  statement is conditional — an agent taking an option only on a fixed schedule, with
  estimate below 1 on infinitely many off-schedule rounds, is not a BRIA; an agent
  estimating 1 where every option pays 1 is the warning example (**FIX**
  `test_estimate_one_everywhere_is_not_attacked`).  "All valid testing must be
  adaptive" is withdrawn as unproved.
- **R4** (first pass "derivable"; second pass "not derivable"): the correct status is
  that the supplied derivation fails and the implication "M2(c) and M3 imply the strong
  form" is **unresolved** — no countermodel has been exhibited.  What is established is
  W1.  The repairs are stated with their conditions: `ε`-shifted bidders for the
  cumulative-loss gap; for feedback theorems, the weighting must be computable at
  forecast time, so a selection-based weighting serves post-selection forecasts and
  serves pre-selection forecasts only where the selection is predictable from the
  market state; publicity of the selection does not make an internal test set
  recognizable.
- **T8 / D3**: the inference "the synthesis two-boxes under bounded simulation because
  its decision is above `O(g)`" is withdrawn (Thm 2 is worst-case and says nothing about
  runtime on the benchmark); equivalence to Agent Simulates Predictor is not claimed;
  the success condition is joint (prediction one, action one) with density 1 under a
  faithfulness assumption; the row is an incomplete diagnostic.
- **D1** (second pass): withdrawn.  The constant bidder `(b, 1)` is in the full class,
  so coverage already excludes self-confirming pessimism about a claimable option
  (T2); the live forms are the identification problem (T10) and the self-referential
  one (A1).
- **T10** (first pass "criterion-level separation"): an interface illustration; the
  theorem target's distinct properties — eventual settlement, pre-decision
  predictability, vanishing average error, pointwise convergence, accuracy on
  endogenous test sets, refutation resistance — are separated, and the separation is
  stated with comparable access and explicit accounting.
- **The tentative troll** result stands, marked construction-level and conditional on
  published estimates.

## 4. Genuinely blocking specification choices

- **The recovery domain of the updateless extension** (M3, domain 4): the property of
  the reward process under which myopic and policy optimality coincide is not defined;
  `E_hist` is too large (frequency-predictor mugging is in it and P1′ forces refusal
  there) and choice-independent rewards too small.  It blocks the judgment "recovered
  BRIA where it should" for any updateless candidate.  It blocks nothing for the
  updateful endpoint, whose recommended domain is the full class at the declared unit.
- **The commitment source** a candidate is held to (M5): decides whether the
  channel-dependent rows (T4(i), T6(iii), T7) are conditional results or advances.
  Recorded in `DECISIONS.md`, *Awaiting the author*.

The other queued choices (the scored unit and self-entered contracts; publicity;
randomization; the scope of one-shot verdicts) shape the specialization and the suite
but block no endpoint judgment.

## 5. What was added and reorganized

- A new line, `projects/decision-theory/`, registered in `state/projects.json`; this
  round under `rounds/`; continuation BRIA cross-linked, not moved (`DECISIONS.md`,
  2026-09-29, agent-decided).
- `PROBLEM_STATEMENT.md` (the acceptance statement; milestones with recovery domains;
  the integration obligation; boundary results; compatibility status; the
  specialization; advance diagnostics; checklist), `TEST_SUITE.md` (eleven families
  with role, status and supplied structure per row), `AUDIT.md` (prior approaches;
  compatibility; ten open choices).
- Fixtures in `src/` and `tests/` (27 tests, exact arithmetic, every one a finite
  prefix check against fixed bidders or fixed agents).
- Items 105 and 106 filed (103–104 are taken by the open corrigibility-kernel phase-2
  pull request, whose item 103 is the closest antecedent); the *Awaiting* entries.
- The wiki is untouched.

## 6. Deviations from the dispatches

- The section is a top-level line; continuation BRIA is cross-linked rather than
  moved.
- Later passes edited the earlier passes' unlanded ledger entries and items in place;
  the pull request's commits are the history.
- One remembered attribution (asymptotic decision theory) did not check out;
  `AUDIT.md` says so.
- The third pass names the timely-learning property T10 step 1 needs without citing
  its exact label in the pinned formalization, which is to be verified by the round
  that proves it; citing a remembered label would violate the citation rule.
- A maintainer ruling in the same session retired the name lint; separate commit,
  recorded in `DECISIONS.md`.

## 7. What is not shown

- Every quantified statement (P1′, the conditional fixed-schedule obstruction, W1) is a
  paper-level derivation with named hypotheses; the fixtures are `test-supported`
  illustrations.
- Nothing passes A1; T10's four steps are unproved; the strong compatibility form is
  neither proved nor refuted; A2's recovery domain is undefined.
- Whether the milestones, I1, I3 and A1 are *jointly* achievable by any computable
  agent is not known.  The specification is a destination, not an existence claim.
- Nothing about rates; nothing in register (iii); nothing registered.

## 8. Verification performed

`python3 tests/run.py` green (71 project runners; this round's 27 tests);
`python3 -m checkers.workspace_state --check` valid; dead-pointer, untracked-pointer,
wiki-link and wiki-binding gates clean; CI green on the pull request at each pushed
pass.  The pull request is ready for review; the merge is the maintainer's.

## 9. What the later passes changed

*Second pass*: retracted P2 as a BRIA; added the heads-tracker regression and the
off-schedule attacker; replaced P1 by P1′; rewrote the requirements with witness
estimates and three commitment sources; separated the specialization; audited R4;
rewrote T4(ii), T6, T8, T10, T11; added two levels of achievement; corrected the
checklist.  *Third pass*: the acceptance statement (§0) with milestones / endpoint /
ideal extension; the four recovery domains and the open domain question; the
integration obligation with I1–I3 separated; the conditional fixed-schedule
obstruction with its warning example; the R4 status corrected to "derivation fails,
implication unresolved" with the timing and generability conditions for feedback
theorems; D3 demoted and D1 withdrawn; A1 as the proposed advance and A2 as the
extension; role, status and supplied structure on every suite row; the verdict, the
ledgers, the items and the pull request updated.

**Fourth pass.**  Removed A1 from the acceptance statement; I3 is now a formal result on
a failure mode the candidate specifies to a qualification standard, and the advance is
by any diagnostic meeting that standard, one theorem being allowed to discharge both;
A1 marked provisional with its three missing elements (forecast semantics, witness
status of its configurations, report-changes-environment); T10's control corrected to
"the stated pre-decision deduction argument no longer guarantees an advantage"; active
LI required for the endpoint and passive recovery a weaker milestone in §0, M2, the
checklist and T0.

**Remaining provisional items.**  A1 (three missing elements); D3 (runtime accounting);
D2 (construction-level, published estimates); A2 (the recovery domain).  Every
acceptance judgment that depends on them is listed in §0 of the problem statement.

## 10. Outstanding maintainer actions

1. Rule on the *Awaiting the author* entries of 2026-09-29, in particular the
   commitment source (M5) and the recovery-domain question (M3, domain 4), or leave
   them queued until a construction round needs them.
2. Merge, or hold, the pull request; the merge is reserved as a note on it.
3. At the next naming audit, settle the provisional names listed in
   `PROBLEM_STATEMENT.md`.
